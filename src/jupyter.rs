//! Jupyter notebook integration (protocol + kernel helpers).

use crate::repl::Repl;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use hmac::{Hmac, Mac};
use sha2::Sha256;

const DELIM: &[u8] = b"<IDS|MSG>";

type HmacSha256 = Hmac<Sha256>;

/// Jupyter connection file contents.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ConnectionInfo {
    pub transport: String,
    pub ip: String,
    pub shell_port: u16,
    pub iopub_port: u16,
    pub stdin_port: u16,
    pub control_port: u16,
    pub hb_port: u16,
    pub signature_scheme: String,
    pub key: String,
}

impl ConnectionInfo {
    pub fn from_json_str(input: &str) -> Result<Self, String> {
        serde_json::from_str(input).map_err(|e| format!("Invalid connection file: {}", e))
    }
}

/// Jupyter message header.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct JupyterHeader {
    pub msg_id: String,
    pub session: String,
    pub username: String,
    pub date: String,
    pub msg_type: String,
    pub version: String,
}

/// Decoded Jupyter message.
#[derive(Debug, Clone, PartialEq)]
pub struct JupyterMessage {
    pub ids: Vec<Vec<u8>>,
    pub header: JupyterHeader,
    pub parent_header: Value,
    pub metadata: Value,
    pub content: Value,
    pub buffers: Vec<Vec<u8>>,
}

impl JupyterMessage {
    pub fn encode(&self, key: &str) -> Result<Vec<Vec<u8>>, String> {
        let header = serde_json::to_vec(&self.header)
            .map_err(|e| format!("Serialize header failed: {}", e))?;
        let parent = serde_json::to_vec(&self.parent_header)
            .map_err(|e| format!("Serialize parent header failed: {}", e))?;
        let metadata = serde_json::to_vec(&self.metadata)
            .map_err(|e| format!("Serialize metadata failed: {}", e))?;
        let content = serde_json::to_vec(&self.content)
            .map_err(|e| format!("Serialize content failed: {}", e))?;

        let sig = sign_frames(
            key,
            [&header[..], &parent[..], &metadata[..], &content[..]],
        );

        let mut frames = Vec::new();
        frames.extend(self.ids.iter().cloned());
        frames.push(DELIM.to_vec());
        frames.push(sig.into_bytes());
        frames.push(header);
        frames.push(parent);
        frames.push(metadata);
        frames.push(content);
        frames.extend(self.buffers.iter().cloned());
        Ok(frames)
    }

    pub fn decode(frames: Vec<Vec<u8>>, key: &str) -> Result<Self, String> {
        let delim_pos = frames
            .iter()
            .position(|frame| frame.as_slice() == DELIM)
            .ok_or_else(|| "Missing Jupyter delimiter".to_string())?;

        if frames.len() < delim_pos + 6 {
            return Err("Incomplete Jupyter message".to_string());
        }

        let ids = frames[..delim_pos].to_vec();
        let sig = &frames[delim_pos + 1];
        let header = &frames[delim_pos + 2];
        let parent = &frames[delim_pos + 3];
        let metadata = &frames[delim_pos + 4];
        let content = &frames[delim_pos + 5];
        let buffers = frames[delim_pos + 6..].to_vec();

        let expected = sign_frames(key, [&header[..], &parent[..], &metadata[..], &content[..]]);
        if !key.is_empty() && sig != expected.as_bytes() {
            return Err("Invalid Jupyter message signature".to_string());
        }

        let header: JupyterHeader = serde_json::from_slice(header)
            .map_err(|e| format!("Invalid header: {}", e))?;
        let parent_header: Value = serde_json::from_slice(parent)
            .map_err(|e| format!("Invalid parent header: {}", e))?;
        let metadata: Value = serde_json::from_slice(metadata)
            .map_err(|e| format!("Invalid metadata: {}", e))?;
        let content: Value = serde_json::from_slice(content)
            .map_err(|e| format!("Invalid content: {}", e))?;

        Ok(Self {
            ids,
            header,
            parent_header,
            metadata,
            content,
            buffers,
        })
    }
}

fn sign_frames<'a>(key: &str, frames: impl IntoIterator<Item = &'a [u8]>) -> String {
    if key.is_empty() {
        return String::new();
    }

    let mut mac = HmacSha256::new_from_slice(key.as_bytes())
        .expect("HMAC can take key of any size");
    for frame in frames {
        mac.update(frame);
    }
    let digest = mac.finalize().into_bytes();
    hex::encode(digest)
}

fn now_string() -> String {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    format!("{}", secs)
}

/// Kernel spec payload for installation.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct KernelSpec {
    pub argv: Vec<String>,
    pub display_name: String,
    pub language: String,
    pub interrupt_mode: String,
}

pub fn kernel_spec(name: &str, argv0: &str) -> KernelSpec {
    KernelSpec {
        argv: vec![
            argv0.to_string(),
            "kernel".to_string(),
            "--connection-file".to_string(),
            "{connection_file}".to_string(),
        ],
        display_name: name.to_string(),
        language: "rwlog".to_string(),
        interrupt_mode: "message".to_string(),
    }
}

pub fn kernel_spec_json(name: &str, argv0: &str) -> Result<String, String> {
    let spec = kernel_spec(name, argv0);
    serde_json::to_string_pretty(&spec).map_err(|e| format!("Kernel spec serialize failed: {}", e))
}

pub fn default_kernel_dir() -> Result<PathBuf, String> {
    let home = std::env::var("HOME").map_err(|_| "HOME not set".to_string())?;
    Ok(PathBuf::from(home).join(".local/share/jupyter/kernels"))
}

pub fn install_kernel_spec(dir: &Path, name: &str, argv0: &str) -> Result<PathBuf, String> {
    let spec_dir = dir.join(name);
    fs::create_dir_all(&spec_dir)
        .map_err(|e| format!("Failed to create kernel dir: {}", e))?;
    let spec = kernel_spec_json(name, argv0)?;
    let path = spec_dir.join("kernel.json");
    fs::write(&path, spec.as_bytes())
        .map_err(|e| format!("Failed to write kernel.json: {}", e))?;
    Ok(path)
}

/// Kernel response bundle.
pub struct KernelResponse {
    pub shell: Option<JupyterMessage>,
    pub iopub: Vec<JupyterMessage>,
    pub shutdown: bool,
}

/// Minimal Jupyter kernel handler.
pub struct Kernel {
    repl: Repl,
    session: String,
    username: String,
    msg_counter: u64,
    execution_count: u64,
    key: String,
}

impl Kernel {
    pub fn new(session: String, username: String, key: String) -> Self {
        Self {
            repl: Repl::new(),
            session,
            username,
            msg_counter: 0,
            execution_count: 0,
            key,
        }
    }

    fn next_msg_id(&mut self) -> String {
        self.msg_counter += 1;
        format!("rwlog-{}", self.msg_counter)
    }

    fn make_header(&mut self, msg_type: &str) -> JupyterHeader {
        JupyterHeader {
            msg_id: self.next_msg_id(),
            session: self.session.clone(),
            username: self.username.clone(),
            date: now_string(),
            msg_type: msg_type.to_string(),
            version: "5.3".to_string(),
        }
    }

    fn make_reply(
        &mut self,
        msg_type: &str,
        parent: &JupyterMessage,
        content: Value,
    ) -> JupyterMessage {
        JupyterMessage {
            ids: parent.ids.clone(),
            header: self.make_header(msg_type),
            parent_header: json!(parent.header),
            metadata: json!({}),
            content,
            buffers: Vec::new(),
        }
    }

    fn status_message(&mut self, parent: &JupyterMessage, state: &str) -> JupyterMessage {
        self.make_reply("status", parent, json!({ "execution_state": state }))
    }

    fn error_message(&mut self, parent: &JupyterMessage, ename: &str, evalue: &str) -> JupyterMessage {
        self.make_reply(
            "error",
            parent,
            json!({
                "ename": ename,
                "evalue": evalue,
                "traceback": [],
            }),
        )
    }

    fn execute_input_message(
        &mut self,
        parent: &JupyterMessage,
        code: &str,
    ) -> JupyterMessage {
        self.make_reply(
            "execute_input",
            parent,
            json!({ "code": code, "execution_count": self.execution_count }),
        )
    }

    fn execute_result_message(
        &mut self,
        parent: &JupyterMessage,
        text: &str,
    ) -> JupyterMessage {
        self.make_reply(
            "execute_result",
            parent,
            json!({
                "execution_count": self.execution_count,
                "data": { "text/plain": text },
                "metadata": {},
            }),
        )
    }

    pub fn handle_message(&mut self, msg: &JupyterMessage) -> KernelResponse {
        match msg.header.msg_type.as_str() {
            "kernel_info_request" => KernelResponse {
                shell: Some(self.make_reply(
                    "kernel_info_reply",
                    msg,
                    json!({
                        "protocol_version": "5.3",
                        "implementation": "rwlog",
                        "implementation_version": "0.1.0",
                        "language_info": {
                            "name": "rwlog",
                            "mimetype": "text/plain",
                            "file_extension": ".rwlog",
                        },
                        "banner": "rwlog kernel",
                        "help_links": [],
                    }),
                )),
                iopub: vec![
                    self.status_message(msg, "busy"),
                    self.status_message(msg, "idle"),
                ],
                shutdown: false,
            },
            "is_complete_request" => KernelResponse {
                shell: Some(self.make_reply(
                    "is_complete_reply",
                    msg,
                    json!({
                        "status": "complete",
                        "indent": "",
                    }),
                )),
                iopub: vec![self.status_message(msg, "idle")],
                shutdown: false,
            },
            "shutdown_request" => {
                let restart = msg.content.get("restart").and_then(Value::as_bool).unwrap_or(false);
                KernelResponse {
                    shell: Some(self.make_reply(
                        "shutdown_reply",
                        msg,
                        json!({ "restart": restart }),
                    )),
                    iopub: vec![self.status_message(msg, "idle")],
                    shutdown: true,
                }
            }
            "comm_info_request" => KernelResponse {
                shell: Some(self.make_reply(
                    "comm_info_reply",
                    msg,
                    json!({ "comms": {} }),
                )),
                iopub: vec![self.status_message(msg, "idle")],
                shutdown: false,
            },
            "complete_request" => KernelResponse {
                shell: Some(self.make_reply(
                    "complete_reply",
                    msg,
                    json!({
                        "status": "ok",
                        "matches": [],
                        "cursor_start": 0,
                        "cursor_end": 0,
                        "metadata": {},
                    }),
                )),
                iopub: vec![self.status_message(msg, "idle")],
                shutdown: false,
            },
            "execute_request" => self.handle_execute_request(msg),
            _ => KernelResponse {
                shell: Some(self.make_reply(
                    "error",
                    msg,
                    json!({
                        "ename": "UnsupportedMessage",
                        "evalue": format!("Unsupported message type: {}", msg.header.msg_type),
                        "traceback": [],
                    }),
                )),
                iopub: vec![self.status_message(msg, "idle")],
                shutdown: false,
            },
        }
    }

    fn handle_execute_request(&mut self, msg: &JupyterMessage) -> KernelResponse {
        let code = msg
            .content
            .get("code")
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();

        self.execution_count += 1;

        let mut iopub = vec![
            self.status_message(msg, "busy"),
            self.execute_input_message(msg, &code),
        ];

        match self.repl.process_cell(&code) {
            Ok(Some(output)) => {
                iopub.push(self.execute_result_message(msg, &output));
                iopub.push(self.status_message(msg, "idle"));
                KernelResponse {
                    shell: Some(self.make_reply(
                        "execute_reply",
                        msg,
                        json!({
                            "status": "ok",
                            "execution_count": self.execution_count,
                            "payload": [],
                            "user_expressions": {},
                        }),
                    )),
                    iopub,
                    shutdown: false,
                }
            }
            Ok(None) => {
                iopub.push(self.status_message(msg, "idle"));
                KernelResponse {
                    shell: Some(self.make_reply(
                        "execute_reply",
                        msg,
                        json!({
                            "status": "ok",
                            "execution_count": self.execution_count,
                            "payload": [],
                            "user_expressions": {},
                        }),
                    )),
                    iopub,
                    shutdown: false,
                }
            }
            Err(err) => {
                iopub.push(self.error_message(msg, "Error", &err));
                iopub.push(self.status_message(msg, "idle"));
                KernelResponse {
                    shell: Some(self.make_reply(
                        "execute_reply",
                        msg,
                        json!({
                            "status": "error",
                            "ename": "Error",
                            "evalue": err,
                            "traceback": [],
                        }),
                    )),
                    iopub,
                    shutdown: false,
                }
            }
        }
    }

    pub fn key(&self) -> &str {
        &self.key
    }
}

#[cfg(feature = "jupyter")]
pub fn run_kernel(connection_file: &Path) -> Result<(), String> {
    let content = fs::read_to_string(connection_file)
        .map_err(|e| format!("Failed to read connection file: {}", e))?;
    let info = ConnectionInfo::from_json_str(&content)?;
    let username = std::env::var("USER").unwrap_or_else(|_| "rwlog".to_string());
    let session = format!("rwlog-{}", std::process::id());
    let mut kernel = Kernel::new(session, username, info.key.clone());

    let ctx = zmq::Context::new();
    let shell = ctx.socket(zmq::ROUTER).map_err(|e| e.to_string())?;
    let control = ctx.socket(zmq::ROUTER).map_err(|e| e.to_string())?;
    let stdin = ctx.socket(zmq::ROUTER).map_err(|e| e.to_string())?;
    let iopub = ctx.socket(zmq::PUB).map_err(|e| e.to_string())?;
    let hb = ctx.socket(zmq::REP).map_err(|e| e.to_string())?;

    shell
        .bind(&endpoint(&info.transport, &info.ip, info.shell_port))
        .map_err(|e| e.to_string())?;
    control
        .bind(&endpoint(&info.transport, &info.ip, info.control_port))
        .map_err(|e| e.to_string())?;
    stdin
        .bind(&endpoint(&info.transport, &info.ip, info.stdin_port))
        .map_err(|e| e.to_string())?;
    iopub
        .bind(&endpoint(&info.transport, &info.ip, info.iopub_port))
        .map_err(|e| e.to_string())?;
    hb.bind(&endpoint(&info.transport, &info.ip, info.hb_port))
        .map_err(|e| e.to_string())?;

    loop {
        let mut items = [
            shell.as_poll_item(zmq::POLLIN),
            control.as_poll_item(zmq::POLLIN),
            hb.as_poll_item(zmq::POLLIN),
        ];
        zmq::poll(&mut items, 100).map_err(|e| e.to_string())?;

        if items[2].is_readable() {
            if let Ok(frames) = hb.recv_multipart(0) {
                let _ = hb.send_multipart(frames, 0);
            }
        }

        let mut handle_socket = |socket: &zmq::Socket| -> Result<bool, String> {
            let frames = socket
                .recv_multipart(0)
                .map_err(|e| format!("Receive failed: {}", e))?;
            let msg = match JupyterMessage::decode(frames, kernel.key()) {
                Ok(msg) => msg,
                Err(err) => {
                    eprintln!("Kernel decode error: {}", err);
                    return Ok(false);
                }
            };
            let resp = kernel.handle_message(&msg);

            for iopub_msg in resp.iopub {
                let frames = iopub_msg.encode(kernel.key())?;
                iopub
                    .send_multipart(frames, 0)
                    .map_err(|e| format!("IOPub send failed: {}", e))?;
            }

            if let Some(shell_msg) = resp.shell {
                let frames = shell_msg.encode(kernel.key())?;
                socket
                    .send_multipart(frames, 0)
                    .map_err(|e| format!("Reply send failed: {}", e))?;
            }

            Ok(resp.shutdown)
        };

        if items[0].is_readable() && handle_socket(&shell)? {
            return Ok(());
        }
        if items[1].is_readable() && handle_socket(&control)? {
            return Ok(());
        }
    }
}

#[cfg(feature = "jupyter")]
fn endpoint(transport: &str, ip: &str, port: u16) -> String {
    format!("{}://{}:{}", transport, ip, port)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn connection_info_parses() {
        let json = r#"{
            "transport": "tcp",
            "ip": "127.0.0.1",
            "shell_port": 5555,
            "iopub_port": 5556,
            "stdin_port": 5557,
            "control_port": 5558,
            "hb_port": 5559,
            "signature_scheme": "hmac-sha256",
            "key": "secret"
        }"#;

        let info = ConnectionInfo::from_json_str(json).expect("parse connection info");
        assert_eq!(info.transport, "tcp");
        assert_eq!(info.shell_port, 5555);
        assert_eq!(info.key, "secret");
    }

    #[test]
    fn message_roundtrip_with_signature() {
        let header = JupyterHeader {
            msg_id: "1".to_string(),
            session: "s".to_string(),
            username: "u".to_string(),
            date: "0".to_string(),
            msg_type: "execute_request".to_string(),
            version: "5.3".to_string(),
        };
        let msg = JupyterMessage {
            ids: vec![b"abc".to_vec()],
            header,
            parent_header: json!({}),
            metadata: json!({}),
            content: json!({"code": "help"}),
            buffers: Vec::new(),
        };

        let frames = msg.encode("secret").expect("encode");
        let decoded = JupyterMessage::decode(frames, "secret").expect("decode");
        assert_eq!(decoded.header.msg_type, "execute_request");
        assert_eq!(decoded.content["code"], "help");
        assert_eq!(decoded.ids.len(), 1);
    }

    #[test]
    fn message_decode_rejects_bad_signature() {
        let header = JupyterHeader {
            msg_id: "1".to_string(),
            session: "s".to_string(),
            username: "u".to_string(),
            date: "0".to_string(),
            msg_type: "execute_request".to_string(),
            version: "5.3".to_string(),
        };
        let msg = JupyterMessage {
            ids: vec![],
            header,
            parent_header: json!({}),
            metadata: json!({}),
            content: json!({"code": "help"}),
            buffers: Vec::new(),
        };

        let mut frames = msg.encode("secret").expect("encode");
        let delim_pos = frames
            .iter()
            .position(|frame| frame.as_slice() == DELIM)
            .expect("delimiter");
        frames[delim_pos + 1] = b"deadbeef".to_vec();
        let err = JupyterMessage::decode(frames, "secret").unwrap_err();
        assert!(err.contains("Invalid Jupyter message signature"));
    }

    #[test]
    fn kernel_spec_json_contains_argv() {
        let json = kernel_spec_json("rwlog", "/bin/rwlog").expect("json");
        assert!(json.contains("--connection-file"));
    }

    #[test]
    fn install_kernel_spec_writes_file() {
        let dir = std::env::temp_dir().join(format!("rwlog-kernel-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create temp");

        let path = install_kernel_spec(&dir, "rwlog-test", "/bin/rwlog").expect("install");
        let spec = std::fs::read_to_string(path).expect("read kernel.json");
        assert!(spec.contains("\"argv\""));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn kernel_execute_request_emits_execute_result_only() {
        let mut kernel = Kernel::new("s".to_string(), "u".to_string(), String::new());
        let header = JupyterHeader {
            msg_id: "1".to_string(),
            session: "s".to_string(),
            username: "u".to_string(),
            date: "0".to_string(),
            msg_type: "execute_request".to_string(),
            version: "5.3".to_string(),
        };
        let msg = JupyterMessage {
            ids: vec![],
            header,
            parent_header: json!({}),
            metadata: json!({}),
            content: json!({"code": "rel f { a -> b }\n?- f"}),
            buffers: Vec::new(),
        };

        let response = kernel.handle_message(&msg);
        let result = response
            .iopub
            .iter()
            .find(|m| m.header.msg_type == "execute_result")
            .expect("execute_result output");
        assert!(
            result.content["data"]["text/plain"]
                .as_str()
                .unwrap_or("")
                .contains("1."),
            "Expected query output in execute_result"
        );
        assert!(
            !response.iopub.iter().any(|m| m.header.msg_type == "stream"),
            "Expected no stream output when execute_result is present"
        );
    }

    #[test]
    fn kernel_info_request_emits_idle_status() {
        let mut kernel = Kernel::new("s".to_string(), "u".to_string(), String::new());
        let header = JupyterHeader {
            msg_id: "1".to_string(),
            session: "s".to_string(),
            username: "u".to_string(),
            date: "0".to_string(),
            msg_type: "kernel_info_request".to_string(),
            version: "5.3".to_string(),
        };
        let msg = JupyterMessage {
            ids: vec![],
            header,
            parent_header: json!({}),
            metadata: json!({}),
            content: json!({}),
            buffers: Vec::new(),
        };

        let response = kernel.handle_message(&msg);
        assert!(
            response.iopub.iter().any(|m| {
                m.header.msg_type == "status"
                    && m.content.get("execution_state") == Some(&json!("idle"))
            }),
            "kernel_info_request must emit idle status on iopub"
        );
    }

    #[test]
    fn comm_info_request_returns_empty_comms() {
        let mut kernel = Kernel::new("s".to_string(), "u".to_string(), String::new());
        let header = JupyterHeader {
            msg_id: "1".to_string(),
            session: "s".to_string(),
            username: "u".to_string(),
            date: "0".to_string(),
            msg_type: "comm_info_request".to_string(),
            version: "5.3".to_string(),
        };
        let msg = JupyterMessage {
            ids: vec![],
            header,
            parent_header: json!({}),
            metadata: json!({}),
            content: json!({}),
            buffers: Vec::new(),
        };

        let response = kernel.handle_message(&msg);
        let shell = response.shell.expect("comm_info_reply");
        assert_eq!(shell.header.msg_type, "comm_info_reply");
        assert_eq!(shell.content.get("comms"), Some(&json!({})));
    }

    #[test]
    fn kernel_execute_request_emits_error_only() {
        let mut kernel = Kernel::new("s".to_string(), "u".to_string(), String::new());
        let header = JupyterHeader {
            msg_id: "1".to_string(),
            session: "s".to_string(),
            username: "u".to_string(),
            date: "0".to_string(),
            msg_type: "execute_request".to_string(),
            version: "5.3".to_string(),
        };
        let msg = JupyterMessage {
            ids: vec![],
            header,
            parent_header: json!({}),
            metadata: json!({}),
            content: json!({"code": "?- (cons z z)"}),
            buffers: Vec::new(),
        };

        let response = kernel.handle_message(&msg);
        assert!(
            response.iopub.iter().any(|m| m.header.msg_type == "error"),
            "Expected error output for invalid query"
        );
        assert!(
            !response.iopub.iter().any(|m| m.header.msg_type == "stream"),
            "Expected no stream output for errors"
        );
    }
}
