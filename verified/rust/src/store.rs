//! The base machine: a store of nodes that counts what is done to it.
//!
//! # Nodes
//!
//! A node is a variable, a symbol, an application of two nodes, or the end
//! of a list. An identifier is the position of a node. Nodes are only added,
//! never changed, and an application refers to older nodes only.
//!
//! No node is stored twice: `alloc` returns the identifier of the node if
//! the store has it. So two identifiers stand for the same term exactly when
//! they are the same identifier.
//!
//! A variable is a number, written in binary as a chain of nodes: `V0` is
//! the variable `0`, `VL(v)` is the variable `2 v` and `VR(v)` is the
//! variable `2 v + 1`. Renaming a variable into the left or the right half
//! of the variables is therefore one allocation, and numbers never overflow.
//! `V0` is the node at position `0`, and `VL(V0)` is `V0`.
//!
//! A list is `Nil`, or an application of its first member to the rest.
//!
//! # Tables
//!
//! There are two tables, `Tbl::A` and `Tbl::B`. A table maps identifiers to
//! identifiers (`get`, `set`) or to flags (`get_flag`, `set_flag`), and
//! `clear` empties it. Every node has a cell in each table from the moment
//! it is allocated, so an access never has to grow anything.
//!
//! # The stack
//!
//! There is one stack of frames (`push`, `pop`, `drop_stack`). A function
//! that walks a term keeps on it the nodes it has still to do, so no function
//! of this crate calls itself and the depth of a term costs room on this
//! stack, which is counted, and none on the call stack. A function that uses
//! the stack starts with it empty and leaves it empty.
//!
//! # Cost
//!
//! `read`, `alloc`, `same`, `word_eq`, `word_lt`, `clear`, `get`, `set`,
//! `get_flag`, `set_flag`, `push`, `pop` and `drop_stack` each spend one tick, and
//! nothing else spends any. Each does an
//! amount of work bounded by a constant of this file: `alloc` finds the node
//! in a trie whose depth is at most two machine words in base sixteen.
//!
//! The fields of `TermId` and `Store` are private. Code outside this module
//! can therefore learn about a term, build one, or remember anything about
//! one only by spending ticks, and cannot lower the count.

/// The identifier of a node.
#[derive(Clone, Copy)]
pub struct TermId(usize);

#[derive(Clone, Copy)]
pub enum Node {
    /// The variable `0`.
    V0,
    /// The variable `2 v`.
    VL(TermId),
    /// The variable `2 v + 1`.
    VR(TermId),
    Sym(u32),
    App(TermId, TermId),
    /// The empty list.
    Nil,
}

/// The name of a table.
#[derive(Clone, Copy)]
pub enum Tbl {
    A,
    B,
}

/// What a walk over a term has still to do. A frame names a node, and a
/// second one: the node of the other term when two terms are walked together,
/// and the same node again otherwise.
#[derive(Clone, Copy)]
pub enum Frame {
    /// Do the node.
    Visit(TermId, TermId),
    /// The parts of the node are done: finish the node.
    Build(TermId, TermId),
}

/// The cells of one node: for each table, the value and the number of the
/// clearing it was written after. A cell written before the last clearing is
/// empty.
#[derive(Clone, Copy)]
struct Slot {
    ea: u64,
    va: usize,
    eb: u64,
    vb: usize,
}

/// A node of the trie that finds a node by its content. `kids[d]` is the
/// position of the trie node reached by the digit `d`, or `0` if there is
/// none (the root is at `0` and is nobody's child). `val` is one more than
/// the identifier of the node whose key ends here, or `0`.
#[derive(Clone, Copy)]
struct Trie {
    kids: [usize; 17],
    val: usize,
}

pub struct Store {
    nodes: Vec<Node>,
    slots: Vec<Slot>,
    trie: Vec<Trie>,
    /// The frames of the stack are `stack[..sp]`; the last is the top.
    stack: Vec<Frame>,
    sp: usize,
    ea: u64,
    eb: u64,
    ticks: u64,
}

impl Default for Store {
    fn default() -> Self {
        Self::new()
    }
}

impl Store {
    /// The store that holds the variable `0` and nothing else.
    pub fn new() -> Store {
        let mut s = Store {
            nodes: Vec::new(),
            slots: Vec::new(),
            trie: Vec::new(),
            stack: Vec::new(),
            sp: 0,
            ea: 1,
            eb: 1,
            ticks: 0,
        };
        s.trie.push(Trie { kids: [0; 17], val: 0 });
        s.intern(Node::V0);
        s
    }

    /// The ticks spent so far.
    pub fn ticks(&self) -> u64 {
        self.ticks
    }

    fn tick(&mut self) {
        self.ticks += 1;
    }

    /// The variable `0`.
    pub fn root(&self) -> TermId {
        TermId(0)
    }

    /// Read a node. One tick.
    pub fn read(&mut self, id: TermId) -> Node {
        self.tick();
        self.nodes[id.0]
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

    /// Is the first word below the second? One tick. Words are in a linear
    /// order, which a canonical form may list symbols by; the order says
    /// nothing about the names the words stand for.
    pub fn word_lt(&mut self, a: u32, b: u32) -> bool {
        self.tick();
        a < b
    }

    /// The trie node reached from `p` by the digit `d`. It is added if it is
    /// not there.
    fn kid(&mut self, p: usize, d: usize) -> usize {
        let c = self.trie[p].kids[d];
        if c != 0 {
            c
        } else {
            let n = self.trie.len();
            self.trie.push(Trie { kids: [0; 17], val: 0 });
            self.trie[p].kids[d] = n;
            n
        }
    }

    /// The trie node reached from `p` by the digits of `x` in base sixteen,
    /// the least significant first.
    fn digits(&mut self, p: usize, x: usize) -> usize {
        let mut q = p;
        let mut y = x;
        while y != 0 {
            q = self.kid(q, y % 16);
            y /= 16;
        }
        q
    }

    /// The trie node reached from `p` by the digits of `x` and the mark that
    /// ends a number.
    fn word(&mut self, p: usize, x: usize) -> usize {
        let q = self.digits(p, x);
        self.kid(q, 16)
    }

    fn is_var(&self, a: TermId) -> bool {
        match self.nodes[a.0] {
            Node::V0 => true,
            Node::VL(_) => true,
            Node::VR(_) => true,
            Node::Sym(_) => false,
            Node::App(_, _) => false,
            Node::Nil => false,
        }
    }

    /// The node as it is stored (`VL(V0)` is `V0`) and the trie node its key
    /// leads to. The parts of the node must be in the store, and the part of
    /// a variable must be a variable.
    fn path(&mut self, n: Node) -> (Node, usize) {
        let len = self.nodes.len();
        match n {
            Node::V0 => (Node::V0, self.kid(0, 0)),
            Node::Nil => (Node::Nil, self.kid(0, 1)),
            Node::VL(a) => {
                assert!(a.0 < len);
                assert!(self.is_var(a));
                if a.0 == 0 {
                    (Node::V0, self.kid(0, 0))
                } else {
                    let p = self.kid(0, 2);
                    (n, self.word(p, a.0))
                }
            }
            Node::VR(a) => {
                assert!(a.0 < len);
                assert!(self.is_var(a));
                let p = self.kid(0, 3);
                (n, self.word(p, a.0))
            }
            Node::Sym(f) => {
                let p = self.kid(0, 4);
                (n, self.word(p, f as usize))
            }
            Node::App(a, b) => {
                assert!(a.0 < len);
                assert!(b.0 < len);
                let p = self.kid(0, 5);
                let p1 = self.word(p, a.0);
                (n, self.word(p1, b.0))
            }
        }
    }

    /// The identifier of a node. The node is added if the store does not
    /// have it.
    fn intern(&mut self, n: Node) -> TermId {
        let (m, q) = self.path(n);
        let v = self.trie[q].val;
        if v != 0 {
            TermId(v - 1)
        } else {
            let len = self.nodes.len();
            self.nodes.push(m);
            self.slots.push(Slot { ea: 0, va: 0, eb: 0, vb: 0 });
            self.trie[q].val = len + 1;
            TermId(len)
        }
    }

    /// The identifier of a node, which is added if the store does not have
    /// it. One tick. The parts of the node must be in the store, and the
    /// part of a variable must be a variable.
    pub fn alloc(&mut self, n: Node) -> TermId {
        self.tick();
        self.intern(n)
    }

    /// Empty a table. One tick.
    pub fn clear(&mut self, t: Tbl) {
        self.tick();
        match t {
            Tbl::A => self.ea += 1,
            Tbl::B => self.eb += 1,
        }
    }

    /// Whether the cell of `k` was written since the table was last
    /// cleared, and what it holds.
    fn cell(&self, t: Tbl, k: TermId) -> (bool, usize) {
        let sl = self.slots[k.0];
        match t {
            Tbl::A => (sl.ea == self.ea, sl.va),
            Tbl::B => (sl.eb == self.eb, sl.vb),
        }
    }

    fn set_cell(&mut self, t: Tbl, k: TermId, v: usize) {
        match t {
            Tbl::A => {
                self.slots[k.0].ea = self.ea;
                self.slots[k.0].va = v;
            }
            Tbl::B => {
                self.slots[k.0].eb = self.eb;
                self.slots[k.0].vb = v;
            }
        }
    }

    /// The identifier a table holds for `k`. One tick.
    pub fn get(&mut self, t: Tbl, k: TermId) -> Option<TermId> {
        self.tick();
        let (live, v) = self.cell(t, k);
        if live {
            Some(TermId(v))
        } else {
            None
        }
    }

    /// Make a table hold `v` for `k`. One tick.
    pub fn set(&mut self, t: Tbl, k: TermId, v: TermId) {
        self.tick();
        self.set_cell(t, k, v.0)
    }

    /// The flag a table holds for `k`. One tick.
    pub fn get_flag(&mut self, t: Tbl, k: TermId) -> Option<bool> {
        self.tick();
        let (live, v) = self.cell(t, k);
        if live {
            Some(v != 0)
        } else {
            None
        }
    }

    /// Make a table hold the flag `b` for `k`. One tick.
    pub fn set_flag(&mut self, t: Tbl, k: TermId, b: bool) {
        self.tick();
        let v = if b { 1 } else { 0 };
        self.set_cell(t, k, v)
    }

    /// Put a frame on the stack. One tick.
    pub fn push(&mut self, f: Frame) {
        self.tick();
        if self.sp < self.stack.len() {
            self.stack[self.sp] = f;
        } else {
            self.stack.push(f);
        }
        self.sp += 1;
    }

    /// Take the top frame off the stack. Nothing, when the stack is empty.
    /// One tick.
    pub fn pop(&mut self) -> Option<Frame> {
        self.tick();
        if self.sp == 0 {
            None
        } else {
            self.sp -= 1;
            Some(self.stack[self.sp])
        }
    }

    /// Empty the stack. One tick.
    pub fn drop_stack(&mut self) {
        self.tick();
        self.sp = 0;
    }
}
