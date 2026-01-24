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
        content: json!({"code": "rel f { a -> b }\nf"}),
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
        content: json!({"code": "rel { invalid"}),
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
