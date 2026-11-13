//! The base machine: a store of term nodes that counts what is done to it.
//!
//! A term is an identifier of a node. A node is a variable, a symbol, or an
//! application of two terms. Variables and symbols are words. The fields of
//! `TermId` and `Store` are private, so code outside this module can look at
//! a term only with `read`, build one only with `alloc`, compare two only
//! with `same`, and compare two words only by spending a tick with `word_eq`
//! (a word taken out of a node is a plain `u32`; `matching` compares them in
//! no other way, and the Lean proofs are about that source). Each of these
//! is one tick, and nothing outside this module can lower the count.

/// The identifier of a node.
#[derive(Clone, Copy)]
pub struct TermId(usize);

#[derive(Clone, Copy)]
pub enum Node {
    Var(u32),
    Sym(u32),
    App(TermId, TermId),
}

pub struct Store {
    nodes: Vec<Node>,
    ticks: u64,
}

impl Default for Store {
    fn default() -> Self {
        Self::new()
    }
}

impl Store {
    pub fn new() -> Store {
        Store { nodes: Vec::new(), ticks: 0 }
    }

    /// The ticks spent so far.
    pub fn ticks(&self) -> u64 {
        self.ticks
    }

    fn tick(&mut self) {
        self.ticks += 1;
    }

    /// Read a node. One tick.
    pub fn read(&mut self, id: TermId) -> Node {
        self.tick();
        self.nodes[id.0]
    }

    /// Allocate a node. One tick. The arguments of an application must
    /// already be in the store, so a node only ever refers to older nodes.
    pub fn alloc(&mut self, n: Node) -> TermId {
        self.tick();
        let id = self.nodes.len();
        if let Node::App(a, b) = n {
            assert!(a.0 < id && b.0 < id);
        }
        self.nodes.push(n);
        TermId(id)
    }

    /// Are the two identifiers the same identifier? One tick.
    pub fn same(&mut self, a: TermId, b: TermId) -> bool {
        self.tick();
        a.0 == b.0
    }

    /// Are the two words the same word? One tick.
    pub fn word_eq(&mut self, a: u32, b: u32) -> bool {
        self.tick();
        a == b
    }
}
