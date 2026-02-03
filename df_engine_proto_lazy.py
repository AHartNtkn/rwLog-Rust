
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional, Tuple, List, Dict, Deque, Set, Union, Iterable
from collections import deque

###############################################################################
# Terms
###############################################################################

@dataclass(frozen=True)
class Term:
    pass

@dataclass(frozen=True)
class Var(Term):
    i: int

@dataclass(frozen=True)
class Con(Term):
    name: str
    args: Tuple[Term, ...] = ()

def V(i: int) -> Var:
    return Var(i)

def C(name: str, *args: Term) -> Con:
    return Con(name, tuple(args))

def term_key(t: Term):
    if isinstance(t, Var):
        return ("v", t.i)
    assert isinstance(t, Con)
    return ("c", t.name, tuple(term_key(a) for a in t.args))

def max_var_term(t: Term) -> int:
    if isinstance(t, Var):
        return t.i
    assert isinstance(t, Con)
    m = -1
    for a in t.args:
        m = max(m, max_var_term(a))
    return m

def has_var_term(t: Term) -> bool:
    if isinstance(t, Var):
        return True
    assert isinstance(t, Con)
    return any(has_var_term(a) for a in t.args)

def shift_term(t: Term, off: int) -> Term:
    if isinstance(t, Var):
        return Var(t.i + off)
    assert isinstance(t, Con)
    if not t.args:
        return t
    return Con(t.name, tuple(shift_term(a, off) for a in t.args))

Subst = Dict[int, Term]

def apply_subst_term(t: Term, s: Subst) -> Term:
    # Fully chase substitutions.
    if isinstance(t, Var):
        v = t.i
        if v in s:
            return apply_subst_term(s[v], s)
        return t
    assert isinstance(t, Con)
    if not t.args:
        return t
    return Con(t.name, tuple(apply_subst_term(a, s) for a in t.args))

def occurs(v: int, t: Term, s: Subst) -> bool:
    t2 = apply_subst_term(t, s)
    if isinstance(t2, Var):
        return t2.i == v
    assert isinstance(t2, Con)
    return any(occurs(v, a, s) for a in t2.args)

def bind(v: int, t: Term, s: Subst) -> Optional[Subst]:
    t2 = apply_subst_term(t, s)
    if isinstance(t2, Var) and t2.i == v:
        return s
    if occurs(v, t2, s):
        return None
    s2 = dict(s)
    s2[v] = t2
    return s2

def unify_terms(a: Term, b: Term, s: Subst) -> Optional[Subst]:
    a2 = apply_subst_term(a, s)
    b2 = apply_subst_term(b, s)
    if a2 == b2:
        return s
    if isinstance(a2, Var):
        return bind(a2.i, b2, s)
    if isinstance(b2, Var):
        return bind(b2.i, a2, s)
    if isinstance(a2, Con) and isinstance(b2, Con):
        if a2.name != b2.name or len(a2.args) != len(b2.args):
            return None
        s2 = s
        for x, y in zip(a2.args, b2.args):
            s2 = unify_terms(x, y, s2)
            if s2 is None:
                return None
        return s2
    return None

Boundary = Tuple[Term, ...]

def max_var_boundary(b: Boundary) -> int:
    m = -1
    for t in b:
        m = max(m, max_var_term(t))
    return m

def shift_boundary(b: Boundary, off: int) -> Boundary:
    return tuple(shift_term(t, off) for t in b)

def apply_subst_boundary(b: Boundary, s: Subst) -> Boundary:
    return tuple(apply_subst_term(t, s) for t in b)

def unify_boundaries(a: Boundary, b: Boundary, s: Subst) -> Optional[Subst]:
    if len(a) != len(b):
        return None
    s2 = s
    for x, y in zip(a, b):
        s2 = unify_terms(x, y, s2)
        if s2 is None:
            return None
    return s2

###############################################################################
# Minimal constraints (normalization-only): NoCon(name, term)
###############################################################################

@dataclass(frozen=True)
class NoCon:
    name: str
    term: Term

Constraint = NoCon

def contains_con(name: str, t: Term) -> bool:
    if isinstance(t, Var):
        return False
    assert isinstance(t, Con)
    if t.name == name:
        return True
    return any(contains_con(name, a) for a in t.args)

def apply_subst_constraint(c: Constraint, s: Subst) -> Constraint:
    return NoCon(c.name, apply_subst_term(c.term, s))

def normalize_constraints(cs: Tuple[Constraint, ...]) -> Optional[Tuple[Constraint, ...]]:
    # Reject if any constraint already violated structurally.
    out: List[Constraint] = []
    seen = set()
    for c in cs:
        if contains_con(c.name, c.term):
            return None
        # Drop if ground and satisfied.
        if not has_var_term(c.term):
            continue
        key = (c.name, term_key(c.term))
        if key in seen:
            continue
        seen.add(key)
        out.append(c)
    out.sort(key=lambda c: (c.name, term_key(c.term)))
    return tuple(out)

###############################################################################
# NF and kernel ops (compose/meet/dual/canon)
###############################################################################

@dataclass(frozen=True)
class NF:
    match: Boundary
    build: Boundary
    constraints: Tuple[Constraint, ...] = ()

def alpha_norm_terms(seq: Iterable[Term], env: Dict[int,int], next_i: int):
    def norm(t: Term):
        nonlocal next_i
        if isinstance(t, Var):
            v = t.i
            if v in env:
                return Var(env[v])
            env[v] = next_i
            next_i += 1
            return Var(env[v])
        assert isinstance(t, Con)
        if not t.args:
            return t
        return Con(t.name, tuple(norm(a) for a in t.args))
    out = [norm(t) for t in seq]
    return tuple(out), env, next_i

def canon_nf(nf: NF) -> Optional[NF]:
    # Alpha-normalize match then build then constraints terms, and normalize constraints.
    env: Dict[int,int] = {}
    next_i = 0
    m_norm, env, next_i = alpha_norm_terms(nf.match, env, next_i)
    b_norm, env, next_i = alpha_norm_terms(nf.build, env, next_i)
    # Normalize constraints under same env.
    cs_norm: List[Constraint] = []
    for c in nf.constraints:
        t_norm, env, next_i = alpha_norm_terms((c.term,), env, next_i)
        cs_norm.append(NoCon(c.name, t_norm[0]))
    cs_tup = tuple(cs_norm)
    cs2 = normalize_constraints(cs_tup)
    if cs2 is None:
        return None
    return NF(m_norm, b_norm, cs2)

def dual_nf(nf: NF) -> NF:
    return NF(nf.build, nf.match, nf.constraints)

def shift_nf(nf: NF, off: int) -> NF:
    return NF(shift_boundary(nf.match, off),
              shift_boundary(nf.build, off),
              tuple(NoCon(c.name, shift_term(c.term, off)) for c in nf.constraints))

def max_var_nf(nf: NF) -> int:
    m = max_var_boundary(nf.match)
    m = max(m, max_var_boundary(nf.build))
    for c in nf.constraints:
        m = max(m, max_var_term(c.term))
    return m

def apply_subst_nf(nf: NF, s: Subst) -> NF:
    return NF(apply_subst_boundary(nf.match, s),
              apply_subst_boundary(nf.build, s),
              tuple(apply_subst_constraint(c, s) for c in nf.constraints))

def compose_nf(a: NF, b: NF) -> Optional[NF]:
    if len(a.build) != len(b.match):
        return None
    off = max_var_nf(a) + 1
    b2 = shift_nf(b, off)
    s0: Subst = {}
    s = unify_boundaries(a.build, b2.match, s0)
    if s is None:
        return None
    out = NF(
        match=apply_subst_boundary(a.match, s),
        build=apply_subst_boundary(b2.build, s),
        constraints=tuple(apply_subst_constraint(c, s) for c in (a.constraints + b2.constraints)),
    )
    return canon_nf(out)

def meet_nf(a: NF, b: NF) -> Optional[NF]:
    if len(a.match) != len(b.match) or len(a.build) != len(b.build):
        return None
    off = max_var_nf(a) + 1
    b2 = shift_nf(b, off)
    s0: Subst = {}
    s = unify_boundaries(a.match, b2.match, s0)
    if s is None:
        return None
    s = unify_boundaries(apply_subst_boundary(a.build, s), apply_subst_boundary(b2.build, s), s)
    if s is None:
        return None
    out = NF(
        match=apply_subst_boundary(a.match, s),
        build=apply_subst_boundary(a.build, s),
        constraints=tuple(apply_subst_constraint(c, s) for c in (a.constraints + b2.constraints)),
    )
    return canon_nf(out)

###############################################################################
# Goal and compatibility
###############################################################################

@dataclass(frozen=True)
class Goal:
    gmatch: Optional[Boundary]
    gbuild: Optional[Boundary]

def canon_goal(g: Goal) -> Goal:
    # Alpha-normalize across both sides, preserving sharing.
    env: Dict[int,int] = {}
    next_i = 0
    if g.gmatch is None:
        m_norm = None
    else:
        m_norm, env, next_i = alpha_norm_terms(g.gmatch, env, next_i)
    if g.gbuild is None:
        b_norm = None
    else:
        b_norm, env, next_i = alpha_norm_terms(g.gbuild, env, next_i)
    return Goal(m_norm, b_norm)

def max_var_goal(g: Goal) -> int:
    m = -1
    if g.gmatch is not None:
        m = max(m, max_var_boundary(g.gmatch))
    if g.gbuild is not None:
        m = max(m, max_var_boundary(g.gbuild))
    return m

def goal_compatible(g: Goal, nf: NF) -> bool:
    # Two-scope unification for each constrained side.
    s: Subst = {}
    # Unify match side if constrained.
    off_nf = 0
    off_goal = max_var_nf(nf) + 1
    nf_m = shift_boundary(nf.match, off_nf)
    nf_b = shift_boundary(nf.build, off_nf)
    if g.gmatch is not None:
        gm = shift_boundary(g.gmatch, off_goal)
        s = unify_boundaries(nf_m, gm, s)
        if s is None:
            return False
    if g.gbuild is not None:
        gb = shift_boundary(g.gbuild, off_goal)
        s = unify_boundaries(nf_b, gb, s)
        if s is None:
            return False
    return True

###############################################################################
# Rel AST
###############################################################################

@dataclass(frozen=True)
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
    a: Rel
    b: Rel

@dataclass(frozen=True)
class AndRel(Rel):
    a: Rel
    b: Rel

@dataclass(frozen=True)
class SeqRel(Rel):
    parts: Tuple[Rel, ...]

def dual_rel(r: Rel) -> Rel:
    if isinstance(r, AtomRel):
        return AtomRel(dual_nf(r.nf))
    if isinstance(r, CallRel):
        return r
    if isinstance(r, OrRel):
        return OrRel(dual_rel(r.a), dual_rel(r.b))
    if isinstance(r, AndRel):
        return AndRel(dual_rel(r.a), dual_rel(r.b))
    if isinstance(r, SeqRel):
        return SeqRel(tuple(reversed([dual_rel(p) for p in r.parts])))
    raise TypeError(r)

###############################################################################
# Engine and scheduler
###############################################################################

class OutOfFuel(Exception):
    pass

@dataclass
class Stats:
    goal_add_calls: int = 0
    goal_inserts: int = 0
    output_inserts: int = 0
    steps: int = 0

class Engine:
    def __init__(self):
        self.nodes: List[Node] = []
        self.worklist: Deque[int] = deque()
        self.scheduled: Set[int] = set()
        self.stats = Stats()
        self.root: Optional[int] = None
        self.root_read: int = 0

    def add_node(self, n: 'Node') -> int:
        nid = len(self.nodes)
        n.nid = nid
        n.engine = self
        self.nodes.append(n)
        return nid

    def enqueue(self, nid: int) -> None:
        if nid not in self.scheduled:
            self.scheduled.add(nid)
            self.worklist.append(nid)

    def add_edge(self, src: int, dst: int) -> None:
        self.nodes[src].dependents.add(dst)

    def notify_output(self, src: int) -> None:
        for d in self.nodes[src].dependents:
            self.enqueue(d)

    def notify_exhausted(self, src: int) -> None:
        # Exhaustion can unblock parents (e.g. joins waiting for a side to finish).
        for d in self.nodes[src].dependents:
            self.enqueue(d)

    def step(self) -> None:
        if not self.worklist:
            return
        nid = self.worklist.popleft()
        self.scheduled.discard(nid)
        self.stats.steps += 1
        self.nodes[nid].step()

    def next_with_fuel(self, fuel: int) -> Optional[NF]:
        assert self.root is not None
        root_node = self.nodes[self.root]
        # Ensure root has at least top goal.
        root_node.add_goal(Goal(None, None))
        while True:
            # Return next unread published output from root.
            if self.root_read < len(root_node.out_vec):
                ans = root_node.out_vec[self.root_read]
                self.root_read += 1
                return ans
            if not self.worklist:
                return None
            if fuel <= 0:
                raise OutOfFuel("fuel exhausted")
            fuel -= 1
            self.step()

###############################################################################
# Node base class
###############################################################################

class Node:
    def __init__(self):
        self.nid: int = -1
        self.engine: Engine = None  # type: ignore
        self.dependents: Set[int] = set()

        self.goals_set: Set[Goal] = set()
        self.goals_vec: List[Goal] = []
        self.goals_q: Deque[int] = deque()  # indices into goals_vec for newly added goals

        self.out_set: Set[NF] = set()
        self.out_vec: List[NF] = []

        self.exhausted: bool = False

    def add_goal(self, g: Goal) -> None:
        eng = self.engine
        eng.stats.goal_add_calls += 1
        g2 = canon_goal(g)
        if g2 in self.goals_set:
            return
        self.goals_set.add(g2)
        self.goals_vec.append(g2)
        self.goals_q.append(len(self.goals_vec) - 1)
        eng.stats.goal_inserts += 1
        self.exhausted = False
        eng.enqueue(self.nid)

    def emit(self, nf: NF) -> None:
        eng = self.engine
        nf2 = canon_nf(nf)
        if nf2 is None:
            return
        if nf2 in self.out_set:
            return
        self.out_set.add(nf2)
        self.out_vec.append(nf2)
        eng.stats.output_inserts += 1
        # Keep producing if more work remains, and wake any dependents.
        eng.enqueue(self.nid)
        eng.notify_output(self.nid)

    def mark_exhausted(self) -> None:
        if not self.exhausted:
            self.exhausted = True
            self.engine.notify_exhausted(self.nid)

    def step(self) -> None:
        raise NotImplementedError

###############################################################################
# Atom node
###############################################################################

class AtomNode(Node):
    def __init__(self, nf: NF):
        super().__init__()
        self.nf = canon_nf(nf)
        if self.nf is None:
            # Unsat -> empty relation.
            self.nf = None
        self.done_for_current_goals: bool = False

    def step(self) -> None:
        # If no goals, nothing to do.
        if not self.goals_set or self.nf is None:
            self.mark_exhausted()
            return
        # Attempt emission once per current goal set.
        # If already emitted, or incompatible with all current goals, exhausted.
        if self.done_for_current_goals:
            self.mark_exhausted()
            return
        can = any(goal_compatible(g, self.nf) for g in self.goals_set)
        if can:
            self.emit(self.nf)
        self.done_for_current_goals = True
        self.mark_exhausted()

    def add_goal(self, g: Goal) -> None:
        before = len(self.goals_set)
        super().add_goal(g)
        if len(self.goals_set) != before:
            # New goal => reconsider compatibility.
            self.done_for_current_goals = False

###############################################################################
# Or node (lazy interleaving)
###############################################################################

class OrNode(Node):
    def __init__(self, left: int, right: int):
        super().__init__()
        self.left = left
        self.right = right
        self.lpos = 0
        self.rpos = 0
        self.turn_left = True  # structural fairness

    def step(self) -> None:
        eng = self.engine
        if not self.goals_set:
            self.mark_exhausted()
            return

        # Propagate newly added goals to both children (delta-driven)
        while self.goals_q:
            gi = self.goals_q.popleft()
            g = self.goals_vec[gi]
            eng.nodes[self.left].add_goal(g)
            eng.nodes[self.right].add_goal(g)

        # Try to pull one new output, alternating sides.
        for _ in range(2):
            if self.turn_left:
                produced = self._pull_from(self.left, True)
            else:
                produced = self._pull_from(self.right, False)
            self.turn_left = not self.turn_left
            if produced:
                break

        # Exhaustion if both children exhausted and no unread outputs.
        ln = eng.nodes[self.left]
        rn = eng.nodes[self.right]
        if ln.exhausted and rn.exhausted and self.lpos >= len(ln.out_vec) and self.rpos >= len(rn.out_vec):
            self.mark_exhausted()
        else:
            self.exhausted = False

    def _pull_from(self, cid: int, is_left: bool) -> bool:
        eng = self.engine
        child = eng.nodes[cid]
        pos_attr = 'lpos' if is_left else 'rpos'
        pos = getattr(self, pos_attr)
        if pos < len(child.out_vec):
            nf = child.out_vec[pos]
            setattr(self, pos_attr, pos + 1)
            self.emit(nf)
            return True
        # No unread outputs. Wait for the child to emit (which will schedule us),
        # or to become exhausted.
        return False

###############################################################################
# Join node (Compose or Meet) with semi-naive goal synthesis and pairing
###############################################################################

@dataclass
class PairTask:
    side: str   # 'L' or 'R'  (fixed item from that side)
    i: int      # index into that side's out_vec
    j: int      # next index into other side's out_vec to try
    other_limit: int  # snapshot limit at creation

@dataclass
class GoalTask:
    kind: str   # 'L_OUT_to_R', 'R_OUT_to_L', 'G_to_R', 'G_to_L'
    idx: int    # index of the "new" thing: output index or goal index
    j: int      # cursor into the other stream
    limit: int  # snapshot length of the other stream at creation

class JoinNode(Node):
    def __init__(self, op: str, left: int, right: int):
        super().__init__()
        assert op in ("compose", "meet")
        self.op = op
        self.left = left
        self.right = right

        # Ingestion cursors.
        self.lpos_in = 0
        self.rpos_in = 0

        # Pairing tasks.
        self.ql: Deque[PairTask] = deque()
        self.qr: Deque[PairTask] = deque()
        self.turn_L = True

        # Goal synthesis tasks (to constrain children).
        self.gtasks: Deque[GoalTask] = deque()
        self.turn_goal = True

    def step(self) -> None:
        eng = self.engine
        if not self.goals_set:
            self.mark_exhausted()
            return

        # Process new goals: propagate projected demands and create semi-naive goal tasks.
        while self.goals_q:
            gi = self.goals_q.popleft()
            g = self.goals_vec[gi]
            self._propagate_goal_projection(g)
            # Pair this new goal with already-seen outputs to generate join-key goals.
            l_seen = len(eng.nodes[self.left].out_vec)
            r_seen = len(eng.nodes[self.right].out_vec)
            if l_seen:
                self.gtasks.append(GoalTask("G_to_R", gi, 0, l_seen))
            if r_seen:
                self.gtasks.append(GoalTask("G_to_L", gi, 0, r_seen))

        # Ingest at most one new output from each side per step (fairness via alternation).
        self._ingest_one()

        # Do bounded pairing work first (prefer producing outputs over expanding demands).
        _emitted = self._process_pair_tasks(budget=8)

        # Lazier goal synthesis: only expand demands aggressively when we're blocked.
        ln = eng.nodes[self.left]
        rn = eng.nodes[self.right]
        blocked = ((len(ln.out_vec) > 0 and len(rn.out_vec) == 0 and not rn.exhausted) or
                   (len(rn.out_vec) > 0 and len(ln.out_vec) == 0 and not ln.exhausted) or
                   (not self.ql and not self.qr))
        g_budget = 8 if blocked else 2
        self._process_goal_tasks(budget=g_budget)

        # Demand policy: if join cannot make progress due to empty side, drive that side.
        self._drive_children_if_needed()

        # Compute exhaustion: key cases.
        self._update_exhausted()

        # If there is still internal work (pending inputs/tasks), keep running.
        if (not self.exhausted) and (
            self.goals_q or
            self.lpos_in < len(ln.out_vec) or
            self.rpos_in < len(rn.out_vec) or
            self.ql or self.qr or self.gtasks
        ):
            eng.enqueue(self.nid)

    def _propagate_goal_projection(self, g: Goal) -> None:
        # Demand seeding policy (critical for laziness / avoiding deadlock):
        #
        # compose(A;B):
        #   The outer goal can constrain output match (=> A.match) and/or output build (=> B.build).
        #   If neither side is constrained (top goal), we seed exactly one side using a structural
        #   cheapness heuristic to preserve dual-invariance (seed the cheaper child).
        #
        # meet(A & B):
        #   Symmetric: seed both sides with the outer goal.
        eng = self.engine
        if self.op == "compose":
            # --- Join-ordering / goal projection for compose ---
            #
            # Key idea: avoid registering *weak* goals that omit the join key.
            #
            # Example: (A ; Call(Fix)) where the outer goal constrains only the final
            # build boundary.  Eagerly projecting that build-only goal to the Call side
            # forces the table to enumerate answers for Call(Fix) without knowing what
            # it must join against, which can explode or prevent exhaustion detection.
            #
            # Instead, we pick a driver side and let join-key-derived goals activate the
            # other side.  This preserves correctness (the join key is *required* for
            # any successful pair) and is symmetric under duality.

            # Choose a driver side for this goal.
            #
            # We prefer the side whose *outer* constraint is more structurally specific
            # (more constructor symbols), because it prunes earlier. If specificity ties,
            # prefer the structurally cheaper node type.
            def rank(nid: int) -> int:
                n = eng.nodes[nid]
                if isinstance(n, AtomNode):
                    return 0
                if isinstance(n, OrNode):
                    return 1
                if isinstance(n, JoinNode):
                    return 2
                if isinstance(n, CallNode):
                    return 3
                if isinstance(n, TableNode):
                    return 4
                return 5

            def ctor_count_term(t: Term) -> int:
                if isinstance(t, Var):
                    return 0
                assert isinstance(t, Con)
                return 1 + sum(ctor_count_term(a) for a in t.args)

            def ctor_count_boundary(b: Optional[Boundary]) -> int:
                if b is None:
                    return 0
                return sum(ctor_count_term(t) for t in b)

            spec_left = ctor_count_boundary(g.gmatch)
            spec_right = ctor_count_boundary(g.gbuild)

            # Higher spec is better; lower rank is better.
            score_left = (spec_left, -rank(self.left))
            score_right = (spec_right, -rank(self.right))
            drive_left = score_left >= score_right

            if drive_left:
                # Seed left with the match-side projection if present, otherwise top.
                if g.gmatch is not None:
                    eng.nodes[self.left].add_goal(Goal(g.gmatch, None))
                else:
                    eng.nodes[self.left].add_goal(Goal(None, None))
            else:
                # Seed right with the build-side projection if present, otherwise top.
                if g.gbuild is not None:
                    eng.nodes[self.right].add_goal(Goal(None, g.gbuild))
                else:
                    eng.nodes[self.right].add_goal(Goal(None, None))
        else:  # meet
            eng.nodes[self.left].add_goal(g)
            eng.nodes[self.right].add_goal(g)

    def _ingest_one(self) -> None:
        eng = self.engine
        ln = eng.nodes[self.left]
        rn = eng.nodes[self.right]

        # Alternate ingestion side each step for fairness.
        if self.turn_L:
            self._ingest_from_left(ln, rn)
            self._ingest_from_right(ln, rn)
        else:
            self._ingest_from_right(ln, rn)
            self._ingest_from_left(ln, rn)
        self.turn_L = not self.turn_L

    def _ingest_from_left(self, ln: Node, rn: Node) -> None:
        if self.lpos_in < len(ln.out_vec):
            i = self.lpos_in
            self.lpos_in += 1
            # Pair task: new left item with all right items seen so far.
            self.ql.append(PairTask('L', i, 0, len(rn.out_vec)))
            # Goal synthesis: new left output with all goals seen so far.
            self.gtasks.append(GoalTask("L_OUT_to_R", i, 0, len(self.goals_vec)))

    def _ingest_from_right(self, ln: Node, rn: Node) -> None:
        if self.rpos_in < len(rn.out_vec):
            i = self.rpos_in
            self.rpos_in += 1
            self.qr.append(PairTask('R', i, 0, len(ln.out_vec)))
            self.gtasks.append(GoalTask("R_OUT_to_L", i, 0, len(self.goals_vec)))

    def _process_pair_tasks(self, budget: int) -> bool:
        eng = self.engine
        ln = eng.nodes[self.left]
        rn = eng.nodes[self.right]

        emitted_any = False

        for _ in range(budget):
            q = None
            if self.ql and self.qr:
                q = self.ql if self.turn_L else self.qr
            elif self.ql:
                q = self.ql
            elif self.qr:
                q = self.qr
            else:
                break

            task = q.popleft()

            if task.side == 'L':
                lnf = ln.out_vec[task.i]
                # Pair with right[task.j .. task.other_limit)
                if task.j >= task.other_limit:
                    continue
                rnf = rn.out_vec[task.j]
                task.j += 1
                if task.j < task.other_limit:
                    q.append(task)
                out = compose_nf(lnf, rnf) if self.op == "compose" else meet_nf(lnf, rnf)
            else:
                rnf = rn.out_vec[task.i]
                if task.j >= task.other_limit:
                    continue
                lnf = ln.out_vec[task.j]
                task.j += 1
                if task.j < task.other_limit:
                    q.append(task)
                out = compose_nf(lnf, rnf) if self.op == "compose" else meet_nf(lnf, rnf)

            self.turn_L = not self.turn_L

            if out is not None:
                # Filter by current goals to remain demand-driven.
                if any(goal_compatible(g, out) for g in self.goals_set):
                    emitted_any = True
                    self.emit(out)

        return emitted_any

    def _process_goal_tasks(self, budget: int) -> None:
        eng = self.engine
        ln = eng.nodes[self.left]
        rn = eng.nodes[self.right]

        for _ in range(budget):
            if not self.gtasks:
                break
            task = self.gtasks.popleft()

            if task.kind == "L_OUT_to_R":
                if task.j >= task.limit:
                    continue
                lnf = ln.out_vec[task.idx]
                g = self.goals_vec[task.j]
                task.j += 1
                if task.j < task.limit:
                    self.gtasks.append(task)
                self._derive_right_goal_from(lnf, g)

            elif task.kind == "R_OUT_to_L":
                if task.j >= task.limit:
                    continue
                rnf = rn.out_vec[task.idx]
                g = self.goals_vec[task.j]
                task.j += 1
                if task.j < task.limit:
                    self.gtasks.append(task)
                self._derive_left_goal_from(rnf, g)

            elif task.kind == "G_to_R":
                if task.j >= task.limit:
                    continue
                g = self.goals_vec[task.idx]
                lnf = ln.out_vec[task.j]
                task.j += 1
                if task.j < task.limit:
                    self.gtasks.append(task)
                self._derive_right_goal_from(lnf, g)

            elif task.kind == "G_to_L":
                if task.j >= task.limit:
                    continue
                g = self.goals_vec[task.idx]
                rnf = rn.out_vec[task.j]
                task.j += 1
                if task.j < task.limit:
                    self.gtasks.append(task)
                self._derive_left_goal_from(rnf, g)

    def _derive_right_goal_from(self, lnf: NF, g: Goal) -> None:
        eng = self.engine
        # For compose: right goal uses join key = left.build refined by goal.match;
        #             and inherits goal.build (also refined to preserve shared vars).
        # For meet: right goal is conjunction of goal and left output boundaries.
        if self.op == "compose":
            if g.gmatch is None:
                # No refinement; still gate by compatibility if goal has build only?
                # If goal has match None, any left matches.
                s = {}
                lnf2 = lnf
                # Shift goal build into left namespace? We'll build derived goal in unified namespace:
                # match = left.build (as-is), build = goal.build (shifted disjoint) unless shares via s (none).
                join_key = lnf2.build
                if g.gbuild is None:
                    rg = Goal(join_key, None)
                    eng.nodes[self.right].add_goal(rg)
                else:
                    # Disjoint-union namespaces: shift goal.build by offset.
                    off = max_var_boundary(join_key) + 1
                    gb = shift_boundary(g.gbuild, off)
                    rg = Goal(join_key, gb)
                    eng.nodes[self.right].add_goal(rg)
                return
            # Need unification between left.match and goal.match to refine left.build.
            off = max_var_nf(lnf) + 1
            gm = shift_boundary(g.gmatch, off)
            gb = shift_boundary(g.gbuild, off) if g.gbuild is not None else None
            s0: Subst = {}
            s = unify_boundaries(lnf.match, gm, s0)
            if s is None:
                return
            join_key = apply_subst_boundary(lnf.build, s)
            if gb is None:
                rg = Goal(join_key, None)
            else:
                rg = Goal(join_key, apply_subst_boundary(gb, s))
            eng.nodes[self.right].add_goal(rg)
        else:
            # meet
            off = max_var_nf(lnf) + 1
            s: Subst = {}
            if g.gmatch is not None:
                gm = shift_boundary(g.gmatch, off)
                s = unify_boundaries(lnf.match, gm, s)
                if s is None:
                    return
            if g.gbuild is not None:
                gb = shift_boundary(g.gbuild, off)
                s = unify_boundaries(lnf.build, gb, s)
                if s is None:
                    return
            rg = Goal(apply_subst_boundary(lnf.match, s), apply_subst_boundary(lnf.build, s))
            eng.nodes[self.right].add_goal(rg)

    def _derive_left_goal_from(self, rnf: NF, g: Goal) -> None:
        eng = self.engine
        if self.op == "compose":
            if g.gbuild is None:
                # No refinement from build; left goal uses goal.match and join key from right.match.
                join_key = rnf.match
                if g.gmatch is None:
                    lg = Goal(None, join_key)
                    eng.nodes[self.left].add_goal(lg)
                else:
                    off = max_var_boundary(join_key) + 1
                    gm = shift_boundary(g.gmatch, off)
                    lg = Goal(gm, join_key)
                    eng.nodes[self.left].add_goal(lg)
                return
            # Unify right.build with goal.build to refine right.match and goal.match.
            off = max_var_nf(rnf) + 1
            gb = shift_boundary(g.gbuild, off)
            gm = shift_boundary(g.gmatch, off) if g.gmatch is not None else None
            s0: Subst = {}
            s = unify_boundaries(rnf.build, gb, s0)
            if s is None:
                return
            join_key = apply_subst_boundary(rnf.match, s)
            if gm is None:
                lg = Goal(None, join_key)
            else:
                lg = Goal(apply_subst_boundary(gm, s), join_key)
            eng.nodes[self.left].add_goal(lg)
        else:
            off = max_var_nf(rnf) + 1
            s: Subst = {}
            if g.gmatch is not None:
                gm = shift_boundary(g.gmatch, off)
                s = unify_boundaries(rnf.match, gm, s)
                if s is None:
                    return
            if g.gbuild is not None:
                gb = shift_boundary(g.gbuild, off)
                s = unify_boundaries(rnf.build, gb, s)
                if s is None:
                    return
            lg = Goal(apply_subst_boundary(rnf.match, s), apply_subst_boundary(rnf.build, s))
            eng.nodes[self.left].add_goal(lg)

    def _drive_children_if_needed(self) -> None:
        # Event-driven scheduling:
        #  - children are scheduled when they receive new goals
        #  - this join is scheduled when children emit outputs or exhaust
        # Avoid unconditional polling-based driving, which can livelock.
        return

    def _update_exhausted(self) -> None:
        eng = self.engine
        ln = eng.nodes[self.left]
        rn = eng.nodes[self.right]

        # If either side is exhausted and produced zero outputs, join output is empty and exhausted.
        if ln.exhausted and len(ln.out_vec) == 0:
            self.mark_exhausted()
            return
        if rn.exhausted and len(rn.out_vec) == 0:
            self.mark_exhausted()
            return

        # Exhausted if no pending work, no unread inputs, and both children exhausted.
        no_unread = (self.lpos_in >= len(ln.out_vec)) and (self.rpos_in >= len(rn.out_vec))
        if not self.ql and not self.qr and not self.gtasks and no_unread and ln.exhausted and rn.exhausted:
            self.mark_exhausted()
        else:
            self.exhausted = False

###############################################################################
# Table and Call
###############################################################################

class TableNode(Node):
    def __init__(self, name: str):
        super().__init__()
        self.name = name
        self.body_root: Optional[int] = None
        self.body_pos: int = 0

    def step(self) -> None:
        eng = self.engine
        if not self.goals_set:
            self.mark_exhausted()
            return
        assert self.body_root is not None
        body = eng.nodes[self.body_root]

        # Propagate newly added goals to body.
        while self.goals_q:
            gi = self.goals_q.popleft()
            g = self.goals_vec[gi]
            body.add_goal(g)

        # Ingest new outputs from body into table answers.
        progressed = False
        while self.body_pos < len(body.out_vec):
            nf = body.out_vec[self.body_pos]
            self.body_pos += 1
            # Table stores only answers matching at least one registered goal (to stay query-bounded).
            if any(goal_compatible(g, nf) for g in self.goals_set):
                self.emit(nf)
                progressed = True

        # Exhaustion.
        if body.exhausted and self.body_pos >= len(body.out_vec):
            self.mark_exhausted()
        else:
            self.exhausted = False

class CallNode(Node):
    def __init__(self, table_id: int):
        super().__init__()
        self.table_id = table_id
        self.tpos: int = 0

    def step(self) -> None:
        eng = self.engine
        if not self.goals_set:
            self.mark_exhausted()
            return
        tab = eng.nodes[self.table_id]

        # Register new goals with table.
        while self.goals_q:
            gi = self.goals_q.popleft()
            g = self.goals_vec[gi]
            tab.add_goal(g)

        # Pull new matching answers from table.
        progressed = False
        while self.tpos < len(tab.out_vec):
            nf = tab.out_vec[self.tpos]
            self.tpos += 1
            if any(goal_compatible(g, nf) for g in self.goals_set):
                self.emit(nf)
                progressed = True
                break  # one per step

        if tab.exhausted and self.tpos >= len(tab.out_vec):
            self.mark_exhausted()
        else:
            self.exhausted = False

###############################################################################
# Compiler
###############################################################################

def build_engine(defs: Dict[str, Rel], query: Rel) -> Engine:
    eng = Engine()

    # Create tables first for mutual recursion.
    tables: Dict[str, int] = {}
    for name in defs.keys():
        tid = eng.add_node(TableNode(name))
        tables[name] = tid

    def compile_rel(r: Rel) -> int:
        if isinstance(r, AtomRel):
            nid = eng.add_node(AtomNode(r.nf))
            return nid
        if isinstance(r, CallRel):
            if r.name not in tables:
                raise KeyError(f"unknown relation {r.name}")
            nid = eng.add_node(CallNode(tables[r.name]))
            eng.add_edge(tables[r.name], nid)  # table answers drive this call
            return nid
        if isinstance(r, OrRel):
            a = compile_rel(r.a)
            b = compile_rel(r.b)
            nid = eng.add_node(OrNode(a, b))
            eng.add_edge(a, nid)
            eng.add_edge(b, nid)
            return nid
        if isinstance(r, AndRel):
            a = compile_rel(r.a)
            b = compile_rel(r.b)
            nid = eng.add_node(JoinNode("meet", a, b))
            eng.add_edge(a, nid)
            eng.add_edge(b, nid)
            return nid
        if isinstance(r, SeqRel):
            parts = list(r.parts)
            assert parts
            nid = compile_rel(parts[0])
            for p in parts[1:]:
                rhs = compile_rel(p)
                jnid = eng.add_node(JoinNode("compose", nid, rhs))
                eng.add_edge(nid, jnid)
                eng.add_edge(rhs, jnid)
                nid = jnid
            return nid
        raise TypeError(r)

    # Compile bodies and assign to tables.
    for name, body in defs.items():
        tid = tables[name]
        body_nid = compile_rel(body)
        eng.add_edge(body_nid, tid)  # body outputs schedule table.
        tab = eng.nodes[tid]
        assert isinstance(tab, TableNode)
        tab.body_root = body_nid

    root_id = compile_rel(query)
    eng.root = root_id
    return eng

###############################################################################
# Pretty printing
###############################################################################

def pp_term(t: Term) -> str:
    if isinstance(t, Var):
        return f"${t.i}"
    assert isinstance(t, Con)
    if not t.args:
        return t.name
    return "(" + " ".join([t.name] + [pp_term(a) for a in t.args]) + ")"

def pp_boundary(b: Boundary) -> str:
    return "[" + ", ".join(pp_term(t) for t in b) + "]"

def pp_nf(nf: NF) -> str:
    cs = ""
    if nf.constraints:
        cs = " {" + ", ".join(f"no_{c.name} {pp_term(c.term)}" for c in nf.constraints) + "}"
    return f"Rw {pp_boundary(nf.match)} {pp_boundary(nf.build)}{cs}"

###############################################################################
# Tests
###############################################################################

def test_listlen_exhaustion() -> None:
    # Constructors
    Nil = lambda: C("nil")
    Cons = lambda h, t: C("cons", h, t)
    Z = lambda: C("z")
    S = lambda n: C("s", n)

    v0 = V(0)
    v1 = V(1)

    nf_base  = NF(match=(Nil(),), build=(Z(),))
    nf_step1 = NF(match=(Cons(v0, v1),), build=(v1,))
    nf_step2 = NF(match=(v0,), build=(S(v0),))

    listlen_body = OrRel(
        AtomRel(nf_base),
        SeqRel((AtomRel(nf_step1), CallRel("listlen"), AtomRel(nf_step2)))
    )
    defs = {"listlen": listlen_body}

    nf_query = NF(match=(Nil(),), build=(Nil(),))
    query = SeqRel((AtomRel(nf_query), CallRel("listlen")))

    eng = build_engine(defs, query)

    a1 = eng.next_with_fuel(10_000)
    assert a1 is not None, "expected first answer"
    assert pp_nf(a1) == "Rw [nil] [z]", f"unexpected first answer: {pp_nf(a1)}"

    a2 = eng.next_with_fuel(10_000)
    assert a2 is None, f"expected exhaustion, got {pp_nf(a2)}"

def test_add_stream_prefix() -> None:
    # add: [cons n x] -> [n + x] in Peano-ish, but we use rule:
    # base: [cons z y] -> [y]
    # rec:  [cons (s x) y] -> [s r] where r from add on [cons x y]
    Z = lambda: C("z")
    S = lambda n: C("s", n)
    Cons = lambda a,b: C("cons", a,b)

    x = V(0)
    y = V(1)
    r = V(2)

    base = NF(match=(Cons(Z(), y),), build=(y,))
    step1 = NF(match=(Cons(S(x), y),), build=(Cons(x, y),))
    step2 = NF(match=(r,), build=(S(r),))

    add_body = OrRel(
        AtomRel(base),
        SeqRel((AtomRel(step1), CallRel("add"), AtomRel(step2)))
    )
    defs = {"add": add_body}

    # Query: add (no @) means just Call(add) demanded at top.
    query = CallRel("add")
    eng = build_engine(defs, query)

    # Pull first 5 answers (should exist, infinite stream)
    outs = []
    for _ in range(5):
        nf = eng.next_with_fuel(200_000)
        assert nf is not None
        outs.append(pp_nf(nf))
    assert outs[0].startswith("Rw [(cons z"), outs[0]

def test_dual_listlen() -> None:
    Nil = lambda: C("nil")
    Cons = lambda h, t: C("cons", h, t)
    Z = lambda: C("z")
    S = lambda n: C("s", n)

    v0 = V(0)
    v1 = V(1)
    nf_base  = NF(match=(Nil(),), build=(Z(),))
    nf_step1 = NF(match=(Cons(v0, v1),), build=(v1,))
    nf_step2 = NF(match=(v0,), build=(S(v0),))

    listlen_body = OrRel(
        AtomRel(nf_base),
        SeqRel((AtomRel(nf_step1), CallRel("listlen"), AtomRel(nf_step2)))
    )
    defs = {"listlen": listlen_body}

    nf_query = NF(match=(Nil(),), build=(Nil(),))
    query = SeqRel((AtomRel(nf_query), CallRel("listlen")))

    # dual program & query
    defs_d = {k: dual_rel(v) for k,v in defs.items()}
    query_d = dual_rel(query)

    eng1 = build_engine(defs, query)
    eng2 = build_engine(defs_d, query_d)

    a1 = eng1.next_with_fuel(50_000)
    b1 = eng2.next_with_fuel(50_000)
    assert a1 is not None and b1 is not None
    assert pp_nf(dual_nf(a1)) == pp_nf(b1), (pp_nf(a1), pp_nf(b1))

    a2 = eng1.next_with_fuel(50_000)
    b2 = eng2.next_with_fuel(50_000)
    assert a2 is None and b2 is None

if __name__ == "__main__":
    test_listlen_exhaustion()
    test_dual_listlen()
    test_add_stream_prefix()
    print("OK")