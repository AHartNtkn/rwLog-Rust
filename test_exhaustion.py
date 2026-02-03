#!/usr/bin/env python3
"""
Test exhaustion detection with the Python prototype from NEW_DESIGN.md.

This reproduces the failing test case: querying @nil ; listlen where
listlen = Or(nil->z, Seq(cons h t -> t, call(listlen), n -> s n))

Expected behavior:
- First answer: nil -> z
- Second call: None (exhausted)

Actual behavior in Rust: runs out of fuel instead of detecting exhaustion.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Tuple, List, Dict, Optional, Set, Deque, Callable
from collections import deque

# ----------------------------
# Terms, boundaries, and NFs
# ----------------------------

@dataclass(frozen=True)
class Term:
    pass

@dataclass(frozen=True)
class Var(Term):
    vid: int

@dataclass(frozen=True)
class Con(Term):
    name: str
    args: Tuple[Term, ...] = ()

@dataclass(frozen=True)
class NF:
    match: Tuple[Term, ...]
    build: Tuple[Term, ...]

def pp_term(t: Term) -> str:
    if isinstance(t, Var):
        return f"${t.vid}"
    if not t.args:
        return t.name
    return f"({t.name} {' '.join(pp_term(a) for a in t.args)})"

def pp_bnd(b: Tuple[Term, ...]) -> str:
    if len(b) == 0:
        return "[]"
    return "[" + " ".join(pp_term(t) for t in b) + "]"

def pp_nf(nf: NF) -> str:
    return f"Rw {pp_bnd(nf.match)} {pp_bnd(nf.build)}"

# ----------------------------
# Matching with disjoint scopes
# ----------------------------

Subst = Dict[int, Term]

def apply_subst_term(subst: Subst, t: Term) -> Term:
    if isinstance(t, Var):
        if t.vid in subst:
            return apply_subst_term(subst, subst[t.vid])
        return t
    if not t.args:
        return t
    return Con(t.name, tuple(apply_subst_term(subst, a) for a in t.args))

def occurs(v: int, t: Term, subst: Subst) -> bool:
    t = apply_subst_term(subst, t)
    if isinstance(t, Var):
        return t.vid == v
    return any(occurs(v, a, subst) for a in t.args)

def unify(t1: Term, t2: Term, subst: Subst) -> Optional[Subst]:
    t1 = apply_subst_term(subst, t1)
    t2 = apply_subst_term(subst, t2)

    if isinstance(t1, Var):
        if isinstance(t2, Var) and t1.vid == t2.vid:
            return subst
        if occurs(t1.vid, t2, subst):
            return None
        subst2 = dict(subst)
        subst2[t1.vid] = t2
        return subst2

    if isinstance(t2, Var):
        return unify(t2, t1, subst)

    if isinstance(t1, Con) and isinstance(t2, Con):
        if t1.name != t2.name or len(t1.args) != len(t2.args):
            return None
        for a, b in zip(t1.args, t2.args):
            subst = unify(a, b, subst)
            if subst is None:
                return None
        return subst

    return None

def unify_lists(xs: Tuple[Term, ...], ys: Tuple[Term, ...], subst: Subst) -> Optional[Subst]:
    if len(xs) != len(ys):
        return None
    for a, b in zip(xs, ys):
        subst = unify(a, b, subst)
        if subst is None:
            return None
    return subst

# ----------------------------
# Canonicalization (alpha-normalize)
# ----------------------------

def canon_term(t: Term, ren: Dict[int, int], next_id: List[int]) -> Term:
    if isinstance(t, Var):
        if t.vid not in ren:
            ren[t.vid] = next_id[0]
            next_id[0] += 1
        return Var(ren[t.vid])
    if not t.args:
        return t
    return Con(t.name, tuple(canon_term(a, ren, next_id) for a in t.args))

def canon_nf(nf: NF) -> NF:
    ren: Dict[int, int] = {}
    next_id = [0]
    m = tuple(canon_term(t, ren, next_id) for t in nf.match)
    b = tuple(canon_term(t, ren, next_id) for t in nf.build)
    return NF(m, b)

# ----------------------------
# Kernel ops: compose, meet
# ----------------------------

def compose_nf_raw(l: NF, r: NF) -> Optional[NF]:
    subst: Subst = {}
    subst = unify_lists(l.build, r.match, subst)
    if subst is None:
        return None
    m = tuple(apply_subst_term(subst, t) for t in l.match)
    b = tuple(apply_subst_term(subst, t) for t in r.build)
    return NF(m, b)

def meet_nf_raw(a: NF, b: NF) -> Optional[NF]:
    subst: Subst = {}
    subst = unify_lists(a.match, b.match, subst)
    if subst is None:
        return None
    subst = unify_lists(
        tuple(apply_subst_term(subst, t) for t in a.build),
        tuple(apply_subst_term(subst, t) for t in b.build),
        subst
    )
    if subst is None:
        return None
    m = tuple(apply_subst_term(subst, t) for t in a.match)
    bd = tuple(apply_subst_term(subst, t) for t in a.build)
    return NF(m, bd)

# ----------------------------
# Goals and compatibility
# ----------------------------

@dataclass(frozen=True)
class Goal:
    match: Optional[Tuple[Term, ...]]
    build: Optional[Tuple[Term, ...]]

def canon_goal(g: Goal) -> Goal:
    if g.match is None and g.build is None:
        return g
    ren: Dict[int, int] = {}
    next_id = [0]
    m = None
    b = None
    if g.match is not None:
        m = tuple(canon_term(t, ren, next_id) for t in g.match)
    if g.build is not None:
        b = tuple(canon_term(t, ren, next_id) for t in g.build)
    return Goal(m, b)

def rename_term(t: Term, mapping: Dict[int, int], next_id: List[int]) -> Term:
    if isinstance(t, Var):
        if t.vid not in mapping:
            mapping[t.vid] = next_id[0]
            next_id[0] += 1
        return Var(mapping[t.vid])
    if not t.args:
        return t
    return Con(t.name, tuple(rename_term(a, mapping, next_id) for a in t.args))

def rename_nf_disjoint(nf: NF, start: int) -> Tuple[NF, int]:
    mapping: Dict[int, int] = {}
    next_id = [start]
    m = tuple(rename_term(t, mapping, next_id) for t in nf.match)
    b = tuple(rename_term(t, mapping, next_id) for t in nf.build)
    return NF(m, b), next_id[0]

def rename_boundary(bnd: Tuple[Term, ...], start: int) -> Tuple[Tuple[Term, ...], int]:
    mapping: Dict[int, int] = {}
    next_id = [start]
    out = tuple(rename_term(t, mapping, next_id) for t in bnd)
    return out, next_id[0]

def goal_matches(goal: Goal, nf: NF) -> bool:
    nf2, nxt = rename_nf_disjoint(nf, 0)
    subst: Subst = {}
    if goal.match is not None:
        gm, nxt = rename_boundary(goal.match, nxt)
        subst = unify_lists(nf2.match, gm, subst)
        if subst is None:
            return False
    if goal.build is not None:
        gb, nxt = rename_boundary(goal.build, nxt)
        subst = unify_lists(nf2.build, gb, subst)
        if subst is None:
            return False
    return True

# ----------------------------
# Rel AST
# ----------------------------

class Rel:
    pass

@dataclass(frozen=True)
class AtomRel(Rel):
    nf: NF

@dataclass(frozen=True)
class CallRel(Rel):
    name: str

@dataclass(frozen=True)
class OrRel(Rel):
    left: Rel
    right: Rel

@dataclass(frozen=True)
class AndRel(Rel):
    left: Rel
    right: Rel

@dataclass(frozen=True)
class SeqRel(Rel):
    parts: Tuple[Rel, ...]

# ----------------------------
# Engine
# ----------------------------

class OutOfFuel(Exception):
    pass

class Engine:
    def __init__(self):
        self.nodes: List[Node] = []
        self.worklist: Deque[int] = deque()
        self.scheduled: Set[int] = set()
        self.var_counter: int = 0
        self.root_id: Optional[int] = None
        self.root_read_idx: int = 0

    def fresh_var(self) -> int:
        v = self.var_counter
        self.var_counter += 1
        return v

    def freshen_term(self, t: Term, ren: Dict[int, int]) -> Term:
        if isinstance(t, Var):
            if t.vid not in ren:
                ren[t.vid] = self.fresh_var()
            return Var(ren[t.vid])
        if not t.args:
            return t
        return Con(t.name, tuple(self.freshen_term(a, ren) for a in t.args))

    def freshen_nf(self, nf: NF) -> NF:
        ren: Dict[int, int] = {}
        m = tuple(self.freshen_term(t, ren) for t in nf.match)
        b = tuple(self.freshen_term(t, ren) for t in nf.build)
        return NF(m, b)

    def freshen_boundary(self, bnd: Tuple[Term, ...]) -> Tuple[Term, ...]:
        ren: Dict[int, int] = {}
        return tuple(self.freshen_term(t, ren) for t in bnd)

    def add_node(self, node: "Node") -> int:
        nid = len(self.nodes)
        node.nid = nid
        self.nodes.append(node)
        return nid

    def add_edge(self, src: int, dst: int) -> None:
        self.nodes[src].dependents.add(dst)

    def enqueue(self, nid: int) -> None:
        if nid not in self.scheduled:
            self.scheduled.add(nid)
            self.worklist.append(nid)

    def activate(self, nid: int) -> None:
        self.nodes[nid].active = True
        self.enqueue(nid)

    def run_with_fuel(self, fuel: int, stop_when: Callable[[], bool]) -> int:
        while fuel > 0:
            if stop_when():
                break
            if not self.worklist:
                break
            nid = self.worklist.popleft()
            self.scheduled.discard(nid)
            self.nodes[nid].step(self)
            fuel -= 1
        return fuel

    def next_with_fuel(self, fuel: int) -> Optional[NF]:
        if self.root_id is None:
            raise ValueError("root_id not set")
        root = self.nodes[self.root_id]

        if self.root_read_idx < len(root.out_vec):
            ans = root.out_vec[self.root_read_idx]
            self.root_read_idx += 1
            return ans

        self.activate(self.root_id)

        def stop():
            return self.root_read_idx < len(root.out_vec)

        fuel_left = self.run_with_fuel(fuel, stop)

        if self.root_read_idx < len(root.out_vec):
            ans = root.out_vec[self.root_read_idx]
            self.root_read_idx += 1
            return ans

        if not self.worklist:
            return None

        raise OutOfFuel(f"Out of fuel; remaining={fuel_left}")

class Node:
    def __init__(self):
        self.nid: int = -1
        self.active: bool = False
        self.out_set: Set[NF] = set()
        self.out_vec: List[NF] = []
        self.dependents: Set[int] = set()
        self.demand_goals: Set[Goal] = set()

    def add_output(self, eng: Engine, nf: NF) -> bool:
        cnf = canon_nf(nf)
        if cnf in self.out_set:
            return False
        self.out_set.add(cnf)
        self.out_vec.append(cnf)
        for d in self.dependents:
            eng.enqueue(d)
        return True

    def add_demand(self, eng: Engine, goal: Goal) -> bool:
        cgoal = canon_goal(goal)
        if cgoal in self.demand_goals:
            return False
        self.demand_goals.add(cgoal)
        eng.enqueue(self.nid)
        return True

    def step(self, eng: Engine) -> None:
        raise NotImplementedError

class AtomNode(Node):
    def __init__(self, nf: NF):
        super().__init__()
        self.nf = canon_nf(nf)
        self.emitted = False

    def step(self, eng: Engine) -> None:
        if not self.active:
            return
        if not self.emitted:
            self.emitted = True
            self.add_output(eng, self.nf)

class OrNode(Node):
    def __init__(self, left: int, right: int):
        super().__init__()
        self.left = left
        self.right = right
        self.lpos = 0
        self.rpos = 0
        self.turn = 0

    def step(self, eng: Engine) -> None:
        if not self.active:
            return

        for g in self.demand_goals:
            eng.nodes[self.left].add_demand(eng, g)
            eng.nodes[self.right].add_demand(eng, g)

        left = eng.nodes[self.left]
        right = eng.nodes[self.right]

        def availL() -> bool:
            return self.lpos < len(left.out_vec)

        def availR() -> bool:
            return self.rpos < len(right.out_vec)

        if self.turn == 0:
            if availL():
                nf = left.out_vec[self.lpos]
                self.lpos += 1
                self.add_output(eng, nf)
                self.turn = 1
            elif availR():
                nf = right.out_vec[self.rpos]
                self.rpos += 1
                self.add_output(eng, nf)
                self.turn = 0
            else:
                eng.activate(self.left)
                eng.activate(self.right)
                return
        else:
            if availR():
                nf = right.out_vec[self.rpos]
                self.rpos += 1
                self.add_output(eng, nf)
                self.turn = 0
            elif availL():
                nf = left.out_vec[self.lpos]
                self.lpos += 1
                self.add_output(eng, nf)
                self.turn = 1
            else:
                eng.activate(self.right)
                eng.activate(self.left)
                return

        if availL() or availR():
            eng.enqueue(self.nid)

@dataclass
class _Task:
    side: str
    idx: int
    j: int
    limit: int

class JoinNode(Node):
    def __init__(self, left: int, right: int, op: str):
        super().__init__()
        assert op in ("compose", "meet")
        self.left = left
        self.right = right
        self.op = op

        self.lseen = 0
        self.rseen = 0
        self.tasksL: Deque[_Task] = deque()
        self.tasksR: Deque[_Task] = deque()
        self.turn = 0

        self.seed_turn = 0
        self.max_pairs = 32

    def _combine(self, eng: Engine, l: NF, r: NF) -> Optional[NF]:
        lf = eng.freshen_nf(l)
        rf = eng.freshen_nf(r)
        if self.op == "compose":
            out = compose_nf_raw(lf, rf)
        else:
            out = meet_nf_raw(lf, rf)
        if out is None:
            return None
        return canon_nf(out)

    def _refine_left_build(self, eng: Engine, l: NF, goal_match: Tuple[Term, ...]) -> Optional[Tuple[Term, ...]]:
        lf = eng.freshen_nf(l)
        gm = eng.freshen_boundary(goal_match)
        subst = unify_lists(lf.match, gm, {})
        if subst is None:
            return None
        return tuple(apply_subst_term(subst, t) for t in lf.build)

    def _refine_right_match(self, eng: Engine, r: NF, goal_build: Tuple[Term, ...]) -> Optional[Tuple[Term, ...]]:
        rf = eng.freshen_nf(r)
        gb = eng.freshen_boundary(goal_build)
        subst = unify_lists(rf.build, gb, {})
        if subst is None:
            return None
        return tuple(apply_subst_term(subst, t) for t in rf.match)

    def _propagate_demands(self, eng: Engine) -> None:
        left = eng.nodes[self.left]
        right = eng.nodes[self.right]

        if self.op == "meet":
            for g in self.demand_goals:
                left.add_demand(eng, g)
                right.add_demand(eng, g)
            return

        # compose
        for g in self.demand_goals:
            if g.match is not None:
                left.add_demand(eng, Goal(match=g.match, build=None))
            if g.build is not None:
                right.add_demand(eng, Goal(match=None, build=g.build))

        goals = list(self.demand_goals) if self.demand_goals else [Goal(None, None)]

        for g in goals:
            for lnf in left.out_vec:
                if g.match is not None:
                    rm = self._refine_left_build(eng, lnf, g.match)
                    if rm is None:
                        continue
                else:
                    rm = eng.freshen_nf(lnf).build
                right.add_demand(eng, Goal(match=rm, build=g.build))

            for rnf in right.out_vec:
                if g.build is not None:
                    lb = self._refine_right_match(eng, rnf, g.build)
                    if lb is None:
                        continue
                else:
                    lb = eng.freshen_nf(rnf).match
                left.add_demand(eng, Goal(match=g.match, build=lb))

    def step(self, eng: Engine) -> None:
        if not self.active:
            return

        self._propagate_demands(eng)

        left = eng.nodes[self.left]
        right = eng.nodes[self.right]

        # block on emptiness
        if not left.out_vec and not right.out_vec:
            if self.seed_turn == 0:
                eng.activate(self.left)
                self.seed_turn = 1
            else:
                eng.activate(self.right)
                self.seed_turn = 0
            return

        if not left.out_vec:
            eng.activate(self.left)
            return

        if not right.out_vec:
            eng.activate(self.right)
            return

        # ingest deltas
        while self.lseen < len(left.out_vec):
            i = self.lseen
            self.lseen += 1
            if self.rseen > 0:
                self.tasksL.append(_Task("L", i, 0, self.rseen))

        while self.rseen < len(right.out_vec):
            j = self.rseen
            self.rseen += 1
            if self.lseen > 0:
                self.tasksR.append(_Task("R", j, 0, self.lseen))

        # process chunk, alternating L/R queues
        pairs = 0
        while pairs < self.max_pairs:
            q = self.tasksL if self.turn == 0 else self.tasksR
            if not q:
                other = self.tasksR if self.turn == 0 else self.tasksL
                if other:
                    self.turn = 1 - self.turn
                    continue
                break

            task = q.popleft()

            if task.side == "L":
                lnf = left.out_vec[task.idx]
                while task.j < task.limit and pairs < self.max_pairs:
                    rnf = right.out_vec[task.j]
                    task.j += 1
                    out = self._combine(eng, lnf, rnf)
                    pairs += 1
                    if out is not None:
                        self.add_output(eng, out)
                if task.j < task.limit:
                    q.appendleft(task)
                else:
                    self.turn = 1
            else:
                rnf = right.out_vec[task.idx]
                while task.j < task.limit and pairs < self.max_pairs:
                    lnf = left.out_vec[task.j]
                    task.j += 1
                    out = self._combine(eng, lnf, rnf)
                    pairs += 1
                    if out is not None:
                        self.add_output(eng, out)
                if task.j < task.limit:
                    q.appendleft(task)
                else:
                    self.turn = 0

        if self.tasksL or self.tasksR:
            eng.enqueue(self.nid)

class TableNode(Node):
    def __init__(self, name: str):
        super().__init__()
        self.name = name
        self.body_root: Optional[int] = None
        self.body_pos = 0
        self.goals: Set[Goal] = set()

    def set_body_root(self, rid: int) -> None:
        self.body_root = rid

    def register_goal(self, eng: Engine, goal: Goal) -> bool:
        cgoal = canon_goal(goal)
        if cgoal in self.goals:
            return False
        self.goals.add(cgoal)
        self.active = True
        eng.enqueue(self.nid)
        if self.body_root is not None:
            eng.activate(self.body_root)
        return True

    def step(self, eng: Engine) -> None:
        if not self.active or self.body_root is None or not self.goals:
            return

        body = eng.nodes[self.body_root]
        for g in self.goals:
            body.add_demand(eng, g)

        eng.activate(self.body_root)

        while self.body_pos < len(body.out_vec):
            nf = body.out_vec[self.body_pos]
            self.body_pos += 1
            self.add_output(eng, nf)

class CallNode(Node):
    def __init__(self, table_id: int):
        super().__init__()
        self.table_id = table_id
        self.table_pos = 0
        self.registered: Set[Goal] = set()

    def step(self, eng: Engine) -> None:
        if not self.active:
            return

        table: TableNode = eng.nodes[self.table_id]  # type: ignore
        goals = self.demand_goals if self.demand_goals else {Goal(None, None)}

        for g in goals:
            if g not in self.registered:
                self.registered.add(g)
                table.register_goal(eng, g)

        eng.activate(self.table_id)

        while self.table_pos < len(table.out_vec):
            nf = table.out_vec[self.table_pos]
            self.table_pos += 1
            if any(goal_matches(g, nf) for g in goals):
                self.add_output(eng, nf)

# ----------------------------
# Compilation
# ----------------------------

def compile_rel(rel: Rel, env: Dict[str, int], eng: Engine) -> int:
    if isinstance(rel, AtomRel):
        return eng.add_node(AtomNode(rel.nf))

    if isinstance(rel, CallRel):
        tid = env[rel.name]
        nid = eng.add_node(CallNode(tid))
        eng.add_edge(tid, nid)
        return nid

    if isinstance(rel, OrRel):
        l = compile_rel(rel.left, env, eng)
        r = compile_rel(rel.right, env, eng)
        nid = eng.add_node(OrNode(l, r))
        eng.add_edge(l, nid)
        eng.add_edge(r, nid)
        return nid

    if isinstance(rel, AndRel):
        l = compile_rel(rel.left, env, eng)
        r = compile_rel(rel.right, env, eng)
        nid = eng.add_node(JoinNode(l, r, "meet"))
        eng.add_edge(l, nid)
        eng.add_edge(r, nid)
        return nid

    if isinstance(rel, SeqRel):
        parts = rel.parts
        if not parts:
            raise ValueError("empty Seq")
        cur = compile_rel(parts[0], env, eng)
        for p in parts[1:]:
            nxt = compile_rel(p, env, eng)
            nid = eng.add_node(JoinNode(cur, nxt, "compose"))
            eng.add_edge(cur, nid)
            eng.add_edge(nxt, nid)
            cur = nid
        return cur

    raise TypeError(type(rel))

def build_engine(defs: Dict[str, Rel], query: Rel) -> Engine:
    eng = Engine()
    env: Dict[str, int] = {}

    for name in defs.keys():
        env[name] = eng.add_node(TableNode(name))

    for name, body in defs.items():
        table: TableNode = eng.nodes[env[name]]  # type: ignore
        body_id = compile_rel(body, env, eng)
        table.set_body_root(body_id)
        eng.add_edge(body_id, env[name])

    root_id = compile_rel(query, env, eng)
    eng.root_id = root_id
    eng.activate(root_id)
    return eng

# ----------------------------
# Test: listlen with @nil query
# ----------------------------

def Nil() -> Term:
    return Con("nil")

def Cons(h: Term, t: Term) -> Term:
    return Con("cons", (h, t))

def Z() -> Term:
    return Con("z")

def S(t: Term) -> Term:
    return Con("s", (t,))

def test_listlen_exhaustion():
    """
    listlen = Or(
        nil -> z,                           # base case
        Seq(cons h t -> t, listlen, n -> s n)  # recursive case
    )

    Query: @nil ; listlen

    Expected:
    - First answer: nil -> z
    - Second call: None (exhausted) because cons h t cannot match nil
    """
    v0 = Var(0)
    v1 = Var(1)

    # Base case: nil -> z
    nf_base = NF(match=(Nil(),), build=(Z(),))

    # Recursive step 1: (cons $h $t) -> $t
    nf_step1 = NF(match=(Cons(v0, v1),), build=(v1,))

    # Recursive step 2: $n -> (s $n)
    nf_step2 = NF(match=(v0,), build=(S(v0),))

    # listlen = Or(base, Seq(step1, call(listlen), step2))
    listlen_body = OrRel(
        AtomRel(nf_base),
        SeqRel((AtomRel(nf_step1), CallRel("listlen"), AtomRel(nf_step2)))
    )

    defs = {"listlen": listlen_body}

    # Query: @nil ; listlen
    # @nil means: match=nil, build=nil (identity on nil)
    nf_query = NF(match=(Nil(),), build=(Nil(),))
    query = SeqRel((AtomRel(nf_query), CallRel("listlen")))

    eng = build_engine(defs, query)

    print("Test: @nil ; listlen")
    print("=" * 50)

    # First answer should be nil -> z
    print("\nCalling next_with_fuel(1000) for first answer...")
    try:
        ans1 = eng.next_with_fuel(1000)
        if ans1 is not None:
            print(f"First answer: {pp_nf(ans1)}")
        else:
            print("First answer: None (unexpected!)")
    except OutOfFuel as e:
        print(f"First answer: OUT OF FUEL - {e}")

    # Second call should return None (exhausted)
    print("\nCalling next_with_fuel(1000) for second answer...")
    try:
        ans2 = eng.next_with_fuel(1000)
        if ans2 is not None:
            print(f"Second answer: {pp_nf(ans2)} (unexpected - should be None!)")
        else:
            print("Second answer: None (CORRECT - exhausted)")
    except OutOfFuel as e:
        print(f"Second answer: OUT OF FUEL - {e}")
        print("\n*** BUG: Should have detected exhaustion, not run out of fuel! ***")

if __name__ == "__main__":
    test_listlen_exhaustion()
