//! One-way matching and instantiation, on the base machine.

use crate::store::{Node, Store, TermId};

/// A partial substitution: the bindings made so far, oldest first.
pub struct Subst {
    binds: Vec<(u32, TermId)>,
}

impl Default for Subst {
    fn default() -> Self {
        Self::new()
    }
}

impl Subst {
    pub fn new() -> Subst {
        Subst { binds: Vec::new() }
    }

    /// The newest binding of `v`. One word comparison for each binding
    /// looked at.
    pub fn lookup(&self, s: &mut Store, v: u32) -> Option<TermId> {
        let mut i = self.binds.len();
        while i > 0 {
            i -= 1;
            let (w, t) = self.binds[i];
            if s.word_eq(w, v) {
                return Some(t);
            }
        }
        None
    }

    pub fn bind(mut self, v: u32, t: TermId) -> Subst {
        self.binds.push((v, t));
        self
    }
}

/// Are the two terms the same term, as written?
pub fn term_eq(s: &mut Store, a: TermId, b: TermId) -> bool {
    match (s.read(a), s.read(b)) {
        (Node::Var(x), Node::Var(y)) => s.word_eq(x, y),
        (Node::Sym(f), Node::Sym(g)) => s.word_eq(f, g),
        (Node::App(a1, a2), Node::App(b1, b2)) => term_eq(s, a1, b1) && term_eq(s, a2, b2),
        _ => false,
    }
}

/// Extend `th` so that the pattern `p` instantiated by it is `t`. The
/// variables of `t` are rigid.
pub fn match_into(s: &mut Store, p: TermId, t: TermId, th: Subst) -> Option<Subst> {
    match s.read(p) {
        Node::Var(v) => match th.lookup(s, v) {
            Some(u) => {
                if term_eq(s, u, t) {
                    Some(th)
                } else {
                    None
                }
            }
            None => Some(th.bind(v, t)),
        },
        Node::Sym(f) => match s.read(t) {
            Node::Sym(g) => {
                if s.word_eq(f, g) {
                    Some(th)
                } else {
                    None
                }
            }
            _ => None,
        },
        Node::App(p1, p2) => match s.read(t) {
            Node::App(t1, t2) => match match_into(s, p1, t1, th) {
                Some(th1) => match_into(s, p2, t2, th1),
                None => None,
            },
            _ => None,
        },
    }
}

/// The term `t` with every bound variable replaced by its binding.
pub fn instantiate(s: &mut Store, th: &Subst, t: TermId) -> TermId {
    match s.read(t) {
        Node::Var(v) => match th.lookup(s, v) {
            Some(u) => u,
            None => t,
        },
        Node::Sym(_) => t,
        Node::App(a, b) => {
            let a2 = instantiate(s, th, a);
            let b2 = instantiate(s, th, b);
            s.alloc(Node::App(a2, b2))
        }
    }
}
