"""R005 outside Lean: a port of the top rung of epoch 1 that counts the same ticks.

lean/SYMMETRIC_ENGINE_SIMULATION.md needs what R005 pays on inputs that Lean does not
evaluate in reasonable time (Lean evaluates both sides of every race to the end). This
file is the text of the machine at the tag `epoch-1`, definition for definition, for
programs with an empty theory and no constraint stores:

  Trusted/Charged.lean, Trusted/CostMonad.lean        the charges, `within`, `race`
  Kernel/Solve.lean, Span.lean, Match.lean, Canon.lean, Iface.lean
  Rungs/Tabled/Gen.lean                               the tabled round machine
  Rungs/R002/Gen.lean, R003/Gen.lean, R004/Gen.lean   the three unfolders and their races
  Rungs/Mirror/Gen.lean                               the query and its mirror image, raced

A race is run under the doubling budgets of `Cost.raceFrom`; a side that is over its
budget is abandoned at the budget instead of being evaluated to the end, and what was
learned about it is kept, so the ticks are Lean's and the time is proportional to them.

`python3 scripts/r005_interpreter.py check` compares with the numbers that Lean has
guarded for these inputs (Tests/SimulationRuns.lean, Tests/MiddleRuns.lean).
`python3 scripts/r005_interpreter.py ladder 0 8` prints the ladder family.

Variables are numbered as Lean numbers them (a composition sends the variables of its
left span to even numbers and of its right span to odd ones), because R003 compares
spans as written.

This is a measurement aid, not part of any engine.
"""
import sys
from functools import cmp_to_key

# ---------------------------------------------------------------- terms, interned
class T:
    __slots__ = ('k', 'a', 'b', 'size', 'vars')
_terms = {}
def _mk(k, a, b):
    key = (k, a if k != 'a' else id(a), id(b) if k == 'a' else None)
    t = _terms.get(key)
    if t is None:
        t = T(); t.k, t.a, t.b = k, a, b
        if k == 'a':
            t.size = a.size + b.size + 1; t.vars = a.vars | b.vars
        else:
            t.size = 1; t.vars = frozenset([a]) if k == 'v' else frozenset()
        _terms[key] = t
    return t
def var(n): return _mk('v', n, None)
def sym(f): return _mk('s', f, None)
def app(f, x): return _mk('a', f, x)
def ap(f, *xs):
    t = sym(f)
    for x in xs: t = app(t, x)
    return t

def rename(t, f, memo):
    """t with every variable n replaced by var (f n)."""
    if not t.vars: return t
    r = memo.get(t)
    if r is None:
        r = var(f(t.a)) if t.k == 'v' else app(rename(t.a, f, memo), rename(t.b, f, memo))
        memo[t] = r
    return r

def show(t):
    if t.k == 'v': return '$%d' % t.a
    if t.k == 's': return t.a
    parts = []
    while t.k == 'a': parts.append(show(t.b)); t = t.a
    return '(' + ' '.join([show(t)] + parts[::-1]) + ')'

def pat_cmp(x, y):
    if x is y: return 0
    if x.k == 'v':
        return (x.a > y.a) - (x.a < y.a) if y.k == 'v' else -1
    if y.k == 'v': return 1
    if x.k == 's':
        return (x.a > y.a) - (x.a < y.a) if y.k == 's' else -1
    if y.k == 's': return 1
    return pat_cmp(x.a, y.a) or pat_cmp(x.b, y.b)

# ---------------------------------------------------------------- spans (no stores)
class Span:
    __slots__ = ('l', 'r', 'size', '_swap')
_spans = {}
def span(l, r):
    key = (id(l), id(r))
    s = _spans.get(key)
    if s is None:
        s = Span(); s.l, s.r, s.size, s._swap = l, r, l.size + r.size, None
        _spans[key] = s
    return s
def swap(s):
    if s._swap is None: s._swap = span(s.r, s.l)
    return s._swap
def show_span(s): return '%s -> %s' % (show(s.l), show(s.r))

def solve(eqs):
    """Kernel/Solve.lean `solve`, as a triangular substitution: the bindings in the order
    Lean eliminates variables. Returns the function that applies the solution, or None."""
    b = {}
    def head(t):
        while t.k == 'v' and t.a in b: t = b[t.a]
        return t
    def occurs(x, t):
        t = head(t)
        if t.k == 'v': return t.a == x
        if t.k == 's' or not t.vars: return False
        return occurs(x, t.a) or occurs(x, t.b)
    stack = list(eqs)[::-1]
    while stack:
        p, q = stack.pop()
        p, q = head(p), head(q)
        if p.k == 'v':
            if q.k == 'v':
                if p.a != q.a: b[p.a] = q
            else:
                if q.k == 'a' and occurs(p.a, q): return None
                b[p.a] = q
        elif q.k == 'v':
            if p.k == 'a' and occurs(q.a, p): return None
            b[q.a] = p
        elif p.k == 's' or q.k == 's':
            if p is not q: return None
        else:
            stack.append((p.b, q.b)); stack.append((p.a, q.a))
    memo = {}
    def resolve(t):
        if not t.vars: return t
        r = memo.get(t)
        if r is None:
            if t.k == 'v': r = resolve(b[t.a]) if t.a in b else t
            else: r = app(resolve(t.a), resolve(t.b))
            memo[t] = r
        return r
    return resolve

_L, _R = (lambda n: 2 * n), (lambda n: 2 * n + 1)
_compose = {}
def compose_raw(x, y):
    """Span.compose: match x.r against y.l in two namespaces; None when there is no match."""
    key = (x, y)
    if key in _compose: return _compose[key]
    ml, mr = {}, {}
    th = solve([(rename(x.r, _L, ml), rename(y.l, _R, mr))])
    z = None if th is None else span(th(rename(x.l, _L, ml)), th(rename(y.r, _R, mr)))
    _compose[key] = z
    return z
_meet = {}
def meet_raw(x, y):
    key = (x, y)
    if key in _meet: return _meet[key]
    ml, mr = {}, {}
    th = solve([(rename(x.l, _L, ml), rename(y.l, _R, mr)), (rename(x.r, _L, ml), rename(y.r, _R, mr))])
    z = None if th is None else span(th(rename(x.l, _L, ml)), th(rename(x.r, _L, ml)))
    _meet[key] = z
    return z

def match_into(p, t, th):
    if p.k == 'v':
        u = th.get(p.a)
        if u is None: th[p.a] = t; return True
        return u is t
    if p.k == 's': return p is t
    return t.k == 'a' and match_into(p.a, t.a, th) and match_into(p.b, t.b, th)
_covers = {}
def covers_raw(a, s):
    key = (a, s)
    r = _covers.get(key)
    if r is None:
        th = {}
        r = match_into(a.l, s.l, th) and match_into(a.r, s.r, th)
        _covers[key] = r
    return r

def bound_of(t):
    """`bound` of the interface `t -> t`: no boundary when it restricts nothing."""
    return None if t.k == 'v' else span(t, t)

# ---------------------------------------------------------------- expressions, interned
class Rel:
    __slots__ = ('k', 'a', 'b', 'size', 'calls', '_canon', '_dual')
_rels = {}
def _rel(k, a=None, b=None):
    key = (k, a if k == 'call' else id(a), id(b))
    e = _rels.get(key)
    if e is None:
        e = Rel(); e.k, e.a, e.b, e._canon, e._dual = k, a, b, None, None
        if k == 'zero': e.size, e.calls = 1, False
        elif k == 'span': e.size, e.calls = 1 + a.size, False
        elif k == 'call': e.size, e.calls = 1, True
        elif k == 'conv': e.size, e.calls = 1 + a.size, a.calls
        else: e.size, e.calls = 1 + a.size + b.size, a.calls or b.calls
        _rels[key] = e
    return e
ZERO = _rel('zero')
def rspan(s): return _rel('span', s)
def rw(l, r): return rspan(span(l, r))
def at(t): return rw(t, t)
def r_or(a, b): return _rel('or', a, b)
def r_and(a, b): return _rel('and', a, b)
def seq(a, b): return _rel('seq', a, b)
def conv(a): return _rel('conv', a)
def call(n): return _rel('call', n)

_ORD = {'zero': 0, 'span': 1, 'or': 2, 'and': 3, 'seq': 4, 'conv': 5, 'call': 6}
def rel_cmp(x, y):
    if x is y: return 0
    if x.k != y.k: return -1 if _ORD[x.k] < _ORD[y.k] else 1
    if x.k == 'span': return pat_cmp(x.a.l, y.a.l) or pat_cmp(x.a.r, y.a.r)
    if x.k == 'call': return (x.a > y.a) - (x.a < y.a)
    if x.k == 'conv': return rel_cmp(x.a, y.a)
    return rel_cmp(x.a, y.a) or rel_cmp(x.b, y.b)
def or_branches(e):
    return or_branches(e.a) + or_branches(e.b) if e.k == 'or' else [e]
def mk_or(es):
    if not es: return ZERO
    out = es[-1]
    for e in es[-2::-1]: out = r_or(e, out)
    return out
def canon(e):
    if e._canon is None:
        if e.k in ('zero', 'span', 'call'): c = e
        elif e.k == 'or':
            bs = [x for x in or_branches(canon(e.a)) + or_branches(canon(e.b)) if x is not ZERO]
            bs.sort(key=cmp_to_key(rel_cmp))
            out = []
            for x in bs:
                if x not in out: out.append(x)
            c = mk_or(out)
        elif e.k == 'conv': c = conv(canon(e.a))
        else: c = _rel(e.k, canon(e.a), canon(e.b))
        e._canon = c
    return e._canon
def dual(e):
    if e._dual is None:
        if e.k in ('zero', 'call'): d = e
        elif e.k == 'span': d = rspan(swap(e.a))
        elif e.k == 'seq': d = seq(dual(e.b), dual(e.a))
        elif e.k == 'conv': d = conv(dual(e.a))
        else: d = _rel(e.k, dual(e.a), dual(e.b))
        e._dual = d
    return e._dual

class Program:
    def __init__(P, defs): P.defs = dict(defs); P.order = [n for n, _ in defs]
    def body(P, n): return P.defs.get(n, ZERO)
    def dual(P): return Program([(n, dual(P.defs[n])) for n in P.order])

# ---------------------------------------------------------------- the cost monad
class Exceeded(Exception): pass
class Meter:
    __slots__ = ('t', 'limit')
M = Meter(); M.t = 0; M.limit = float('inf')
def tick(n):
    M.t += n
    if M.t > M.limit: raise Exceeded()

class Comp:
    """A charged computation that may be run under a budget more than once. What a run
    learned is kept: the value and the ticks, or a budget that was not enough."""
    __slots__ = ('f', 'known', 'val', 'ticks', 'over')
    def __init__(c, f): c.f, c.known, c.over = f, False, -1
    def within(c, b):
        """Cost.within: (True, value) charged the ticks of the computation if they are at
        most b; otherwise (False, None) charged b."""
        if c.known:
            if c.ticks <= b: tick(c.ticks); return True, c.val
            tick(b); return False, None
        if c.over >= b: tick(b); return False, None
        t0, outer = M.t, M.limit
        if t0 + b >= outer:
            # the budget reaches past what the enclosing computation may spend: if this
            # is given up on, so is that
            v = c.f()
            c.known, c.val, c.ticks = True, v, M.t - t0
            return True, v
        M.limit = t0 + b
        try:
            v = c.f()
        except Exceeded:
            M.t = t0 + b; c.over = b
            return False, None
        finally:
            M.limit = outer
        c.known, c.val, c.ticks = True, v, M.t - t0
        return True, v
    def run(c):
        if c.known: tick(c.ticks); return c.val
        t0 = M.t
        v = c.f()
        c.known, c.val, c.ticks = True, v, M.t - t0
        return v

def race(x, y):
    """Cost.race: budgets 0, 1, 3, 7, ... for x and then y, until one finishes."""
    b = 0
    while True:
        ok, v = x.within(b)
        if ok: return v
        ok, v = y.within(b)
        if ok: return v
        b = 2 * b + 1

# ---------------------------------------------------------------- charged primitives
def compose(x, y):
    z = compose_raw(x, y)
    tick(x.size + y.size + (z.size if z is not None else 0))
    return z
def meet(x, y):
    z = meet_raw(x, y)
    tick(x.size + y.size + (z.size if z is not None else 0))
    return z
def composable(xs):
    t = 0
    for s in xs: t += s.size
    tick(t)
    acc = xs[0]
    for s in xs[1:]:
        acc = compose_raw(acc, s)
        if acc is None: return False
    return True
def covers(a, s):
    tick(a.size + s.size)
    return covers_raw(a, s)
def eq_span(x, y):
    tick(x.size + y.size)
    return x is y
def eq_rel(a, b):
    tick(a.size + b.size)
    return a is b
def right_bound(s):
    tick(s.size); return bound_of(s.r)
def left_bound(s):
    tick(s.size); return bound_of(s.l)
def live(s):
    """Simplification by the empty theory: the span itself, charged its size and one."""
    tick(s.size + 1); return [s]

# ---------------------------------------------------------------- goals and tables
def goal_rel(g):
    lb, e, rb = g
    core = e if rb is None else seq(e, rspan(rb))
    return core if lb is None else seq(rspan(lb), core)
def bsize(b): return 0 if b is None else b.size
def goal_size(g): return g[1].size + bsize(g[0]) + bsize(g[2])
def oswap(b): return None if b is None else swap(b)

def strip_conv(lb, e, rb):
    flip = False
    while e.k == 'conv':
        lb, e, rb = oswap(rb), e.a, oswap(lb); flip = not flip
    return flip, (lb, e, rb)
def norm(g):
    tick(g[1].size); tick(bsize(g[0]) + bsize(g[2]))
    return strip_conv(g[0], canon(g[1]), g[2])
def same_bound(a, b):
    if a is None and b is None: return True
    if a is None or b is None: return False
    return covers(a, b) and covers(b, a)
def same(g, h):
    return eq_rel(g[1], h[1]) and same_bound(g[0], h[0]) and same_bound(g[2], h[2])

class Table:
    __slots__ = ('goal', 'answers', 'done')
    def __init__(t, goal, answers, done): t.goal, t.answers, t.done = goal, answers, done

def index_of(ts, g):
    for i, t in enumerate(ts):
        if same(t.goal, g): return i
    return None
def find_table(ts, g):
    i = index_of(ts, g)
    return None if i is None else ts[i]
def orient(flip, xs): return [swap(x) for x in xs] if flip else list(xs)
def answers_of(ts, g):
    flip, k = norm(g)
    t = find_table(ts, k)
    return [] if t is None else orient(flip, t.answers)
def done_of(ts, g):
    _, k = norm(g)
    t = find_table(ts, k)
    return t is not None and t.done

def compose_live(x, y):
    z = compose(x, y)
    return live(z) if z is not None else []
def meet_live(x, y):
    z = meet(x, y)
    return live(z) if z is not None else []
def span_answer(lb, s, rb):
    left = s if lb is None else compose(lb, s)
    if left is None: both = None
    elif rb is None: both = left
    else: both = compose(left, rb)
    return live(both) if both is not None else []

def maxima(xs):
    top = []
    for x in xs:
        b = False
        for y in xs:
            if covers(y, x) and not covers(x, y): b = True; break
        if not b: top.append(x)
    acc = []
    for x in top:
        if not any(covers(y, x) for y in acc): acc.append(x)
    return acc
def fresh(old, cands):
    cs = [c for c in cands if not any(covers(t, c) for t in old)]
    return maxima(cs)

def seq_push_l(g, b, x): return (right_bound(x), b, g[2])
def seq_push_r(g, a, y): return (g[0], a, left_bound(y))
def and_push(e, x):
    l = left_bound(x); r = right_bound(x)
    return (l, e, r)

def produce_strategies(P, ts, g):
    lb, e, rb = g
    k = e.k
    if k == 'zero': return [], []
    if k == 'span': return span_answer(lb, e.a, rb), []
    if k == 'or':
        gs = [(lb, c, rb) for c in or_branches(e)]
        xs = []
        for h in gs: xs += answers_of(ts, h)
        return xs, gs
    if k == 'call':
        gb = (lb, P.body(e.a), rb)
        return answers_of(ts, gb), [gb]
    if k == 'conv':
        g2 = (oswap(rb), e.a, oswap(lb))
        return [swap(x) for x in answers_of(ts, g2)], [g2]
    a, b = e.a, e.b
    if k == 'seq':
        L, R = (lb, a, None), (None, b, rb)
        comb = compose_live
        pushl = lambda x: seq_push_l(g, b, x)
        pushr = lambda y: seq_push_r(g, a, y)
    else:
        L, R = (lb, a, rb), (lb, b, rb)
        comb = meet_live
        pushl = lambda x: and_push(b, x)
        pushr = lambda y: and_push(a, y)
    xs = answers_of(ts, L); ys = answers_of(ts, R)
    out = []
    for x in xs:
        for y in ys: out += comb(x, y)
    pl = [(x, pushl(x)) for x in maxima(xs)] if done_of(ts, L) else []
    pr = [(y, pushr(y)) for y in maxima(ys)] if done_of(ts, R) else []
    for x, p in pl:
        for y in answers_of(ts, p): out += comb(x, y)
    for y, p in pr:
        for x in answers_of(ts, p): out += comb(x, y)
    return out, [L, R] + [p for _, p in pl] + [p for _, p in pr]

def table_strategies(P, ts, g):
    lb, e, rb = g
    k = e.k
    if k in ('zero', 'span'): return [[]]
    if k == 'or': return [[(lb, c, rb) for c in or_branches(e)]]
    if k == 'call': return [[(lb, P.body(e.a), rb)]]
    if k == 'conv': return [[(oswap(rb), e.a, oswap(lb))]]
    a, b = e.a, e.b
    if k == 'seq':
        L, R = (lb, a, None), (None, b, rb)
        pushl = lambda x: seq_push_l(g, b, x)
        pushr = lambda y: seq_push_r(g, a, y)
    else:
        L, R = (lb, a, rb), (lb, b, rb)
        pushl = lambda x: and_push(b, x)
        pushr = lambda y: and_push(a, y)
    sl = []
    if done_of(ts, L):
        sl = [[L] + [pushl(x) for x in maxima(answers_of(ts, L))]]
    sr = []
    if done_of(ts, R):
        sr = [[R] + [pushr(y) for y in maxima(answers_of(ts, R))]]
    return [[L, R]] + sl + sr

def completing(P, finals, ts, ts1):
    gained = [len(t1.answers) != len(t.answers) for t, t1 in zip(ts, ts1)]
    S = [i for i, t in enumerate(ts) if not t.done and not gained[i]]
    def ok(S, i):
        strats = ([[]] if finals[i] else []) + table_strategies(P, ts, ts[i].goal)
        for deps in strats:
            good = True
            for d in deps:
                _, k = norm(d)
                j = index_of(ts, k)
                if j is None or gained[j] or not (ts[j].done or j in S):
                    good = False; break
            if good: return True
        return False
    for _ in range(len(S)):
        S2 = [i for i in S if ok(S, i)]
        if len(S2) == len(S): return S
        S = S2
    return S

class State:
    __slots__ = ('P', 'tables', 'flip', 'depth', '_step')
    def __init__(s, P, tables, flip, depth): s.P, s.tables, s.flip, s.depth, s._step = P, tables, flip, depth, None

def tabled_round(U, st):
    ts, P = st.tables, st.P
    tick(1)
    us = []
    for t in ts:
        if t.done: us.append((False, []))
        else:
            tick(goal_size(t.goal))
            us.append(U(P, st.depth, t.goal))
    outs = []
    for t, u in zip(ts, us):
        if t.done: outs.append(([], []))
        else:
            c, gs = produce_strategies(P, ts, t.goal)
            outs.append((u[1] + c, gs))
    ts1 = [Table(t.goal, t.answers + fresh(t.answers, o[0]), t.done) for t, o in zip(ts, outs)]
    reqs = [norm(g)[1] for o in outs for g in o[1]]
    new = []
    for g in reqs:
        if any(same(t.goal, g) for t in ts): continue
        if any(same(h, g) for h in new): continue
        new.append(g)
    S = set(completing(P, [u[0] for u in us], ts, ts1))
    for i in S: ts1[i].done = True
    root_new = ts1[0].answers[len(ts[0].answers):] if ts else []
    return State(P, ts1 + [Table(g, [], False) for g in new], st.flip, st.depth + 1), orient(st.flip, root_new)

def tabled_step(U, st):
    if not st.tables or st.tables[0].done: return ('done',)
    s2, out = tabled_round(U, st)
    return ('emit', out, s2)
def tabled_init(P, q):
    flip, k = norm((None, q, None))
    return State(P, [Table(k, [], False)], flip, 0)

# ---------------------------------------------------------------- R002: the walk on demand
def to_rel_calls(p): return any(f.calls for f in p)
def closed(N): return [p[0].a for p in N if len(p) == 1 and p[0].k == 'span']

def join_seq(p, q):
    if p and p[-1].k == 'span' and q and q[0].k == 'span':
        c = compose(p[-1].a, q[0].a)
        return None if c is None else p[:-1] + [rspan(c)] + q[1:]
    return p + q
def to_rel(p):
    if not p: return rspan(span(var(0), var(0)))
    out = p[-1]
    for f in p[-2::-1]: out = seq(f, out)
    return out
def mk_and(p, q):
    if len(p) == 1 and p[0].k == 'span' and len(q) == 1 and q[0].k == 'span':
        c = meet(p[0].a, q[0].a)
        return None if c is None else [rspan(c)]
    return [r_and(to_rel(p), to_rel(q))]

def eager_norm(neg, e):
    k = e.k
    if k == 'zero': tick(1); return []
    if k == 'span':
        tick(1 + e.a.size); return [[rspan(swap(e.a) if neg else e.a)]]
    if k == 'or':
        tick(1); xs = eager_norm(neg, e.a); return xs + eager_norm(neg, e.b)
    if k == 'seq':
        tick(1)
        first, second = (e.b, e.a) if neg else (e.a, e.b)
        out = []
        for p in eager_norm(neg, first):
            for q in eager_norm(neg, second):
                r = join_seq(p, q)
                if r is not None: out.append(r)
        return out
    if k == 'and':
        tick(1)
        out = []
        for p in eager_norm(neg, e.a):
            for q in eager_norm(neg, e.b):
                r = mk_and(p, q)
                if r is not None: out.append(r)
        return out
    if k == 'conv': tick(1); return eager_norm(not neg, e.a)
    tick(1); return [[conv(e) if neg else e]]

def head_span(p): return p[0].a if p and p[0].k == 'span' else None
def last_span(p): return p[-1].a if p and p[-1].k == 'span' else None
def alive_l(L, p):
    s = head_span(p)
    return composable(L + [s]) if L and s is not None else True
def alive_r(p, R):
    s = last_span(p)
    return composable([s] + R) if R and s is not None else True
def alive(L, p, R): return alive_l(L, p) and alive_r(p, R)
def static_first(neg, e):
    if e.k == 'span': return (swap(e.a) if neg else e.a, True)
    if e.k == 'seq':
        r = static_first(neg, e.b if neg else e.a)
        return None if r is None else (r[0], False)
    if e.k == 'conv': return static_first(not neg, e.a)
    return None
def right_of(neg, e, R):
    r = static_first(neg, e)
    if r is None: return []
    return [r[0]] + R if r[1] else [r[0]]
def left_after(L, p):
    if len(p) == 1 and p[0].k == 'span': return L + [p[0].a]
    s = last_span(p)
    return [] if s is None else [s]

def walk(P, d, neg, e, L, R, k, acc):
    """Returns (stop, acc). `k p acc` is handed each product that is alive."""
    kd = e.k
    tick(1)
    if kd == 'zero': return False, acc
    if kd == 'span':
        p = [rspan(swap(e.a) if neg else e.a)]
        return k(p, acc) if alive(L, p, R) else (False, acc)
    if kd == 'or':
        r = walk(P, d, neg, e.a, L, R, k, acc)
        return r if r[0] else walk(P, d, neg, e.b, L, R, k, r[1])
    if kd == 'seq':
        first, second = (e.b, e.a) if neg else (e.a, e.b)
        def k1(p, acc):
            def k2(q, acc):
                r = join_seq(p, q)
                if r is None: return False, acc
                return k(r, acc) if alive_r(r, R) else (False, acc)
            return walk(P, d, neg, second, left_after(L, p), R, k2, acc)
        return walk(P, d, neg, first, L, right_of(neg, second, R), k1, acc)
    if kd == 'and':
        def k1(p, acc):
            def k2(q, acc):
                r = mk_and(p, q)
                if r is None: return False, acc
                return k(r, acc) if alive(L, r, R) else (False, acc)
            return walk(P, d, neg, e.b, [], [], k2, acc)
        return walk(P, d, neg, e.a, [], [], k1, acc)
    if kd == 'conv': return walk(P, d, not neg, e.a, L, R, k, acc)
    if d == 0: return k([conv(e) if neg else e], acc)
    return walk(P, d - 1, neg, P.body(e.a), L, R, k, acc)

def on_demand(P, d, g):
    def k(p, acc):
        if to_rel_calls(p): return True, acc
        return False, acc + [p]
    stop, acc = walk(P, d, False, goal_rel(g), [], [], k, [])
    if stop: return False, []
    xs = []
    for s in closed(acc): xs += live(s)
    return True, xs

# ---------------------------------------------------------------- R003: the shared evaluation
def same_ctx(a, b): return same_bound(a, b)
def add_span(xs, x):
    for y in xs:
        if eq_span(y, x): return xs
    return xs + [x]
def eq_opt(a, b):
    if a is None and b is None: tick(2); return True
    if a is not None and b is not None: return eq_span(a, b)
    tick((a.size if a is not None else b.size) + 1); return False
def add_open(xs, x):
    for y in xs:
        if eq_opt(y, x): return xs
    return xs + [x]
def alive_ctx(ctx, s): return True if ctx is None else composable([ctx, s])
def extend(ctx, a):
    if ctx is None: return right_bound(a)
    z = compose(ctx, a)
    return None if z is None else right_bound(z)

def shared_eval(P, d, neg, e, ctx, m):
    """Returns ((spans, opens), memo). The memo is a list, newest first, of (key, summary);
    it is passed along and never changed in place."""
    kd = e.k
    if kd == 'zero': tick(1); return ([], []), m
    if kd == 'span':
        tick(1)
        s = swap(e.a) if neg else e.a
        return ([s] if alive_ctx(ctx, s) else [], []), m
    if kd == 'conv': tick(1); return shared_eval(P, d, not neg, e.a, ctx, m)
    if kd == 'call' and d == 0: tick(1); return ([], [None]), m
    # memo lookup
    node = m
    while node is not None:
        (kneg, ke, kdep, kctx), summ = node[0]
        tick(1)
        if kneg == neg and kdep == d and eq_rel(ke, e) and same_ctx(kctx, ctx):
            return summ, m
        node = node[1]
    tick(1)
    if kd == 'or':
        x, m1 = shared_eval(P, d, neg, e.a, ctx, m)
        y, m2 = shared_eval(P, d, neg, e.b, ctx, m1)
        spans = x[0]
        for s in y[0]: spans = add_span(spans, s)
        opens = x[1]
        for o in y[1]: opens = add_open(opens, o)
        res = (spans, opens)
    elif kd == 'seq':
        first, second = (e.b, e.a) if neg else (e.a, e.b)
        x, m1 = shared_eval(P, d, neg, first, ctx, m)
        spans, opens, m2 = [], [], m1
        for xs in x[0]:
            c = extend(ctx, xs)
            r, m2 = shared_eval(P, d, neg, second, c, m2)
            zs = []
            for y in r[0]:
                z = compose(xs, y)
                if z is not None: zs.append(z)
            for z in zs: spans = add_span(spans, z)
            for o in r[1]: opens = add_open(opens, o)
        for c in x[1]:
            r, m2 = shared_eval(P, d, neg, second, c, m2)
            os = [extend(c, y) for y in r[0]]
            for o in os + r[1]: opens = add_open(opens, o)
        res = (spans, opens)
    elif kd == 'and':
        x, m1 = shared_eval(P, d, neg, e.a, None, m)
        y, m2 = shared_eval(P, d, neg, e.b, None, m1)
        zs = []
        for a in x[0]:
            for b in y[0]:
                z = meet(a, b)
                if z is not None: zs.append(z)
        ws = [z for z in zs if alive_ctx(ctx, z)]
        spans = []
        for w in ws: spans = add_span(spans, w)
        some = lambda s: bool(s[0]) or bool(s[1])
        open_ = (bool(x[1]) and some(y)) or (some(x) and bool(y[1]))
        res = (spans, [None] if open_ else [])
    else:
        res, m2 = shared_eval(P, d - 1, neg, P.body(e.a), ctx, m)
    return res, (((neg, e, d, ctx), res), m2)

def shared(P, d, g):
    r, _ = shared_eval(P, d, False, goal_rel(g), None, None)
    if r[1]: return False, []
    xs = []
    for s in r[0]: xs += live(s)
    ys = []
    for x in xs: ys = add_span(ys, x)
    return True, ys

def r003_unfolder(P, d, g):
    return race(Comp(lambda: on_demand(P, d, g)), Comp(lambda: shared(P, d, g)))

# ---------------------------------------------------------------- R004: pruned from the right
LEAF = ('leaf',)
_ksize = {}
def key_size(k):
    r = _ksize.get(id(k))
    if r is None:
        r = 1 if k[0] == 'leaf' else (1 + key_size(k[1]) if k[0] != 'pair' else 1 + key_size(k[1]) + key_size(k[2]))
        _ksize[id(k)] = r; _keep.append(k)
    return r
_keep = []
def key_lt(a, b):
    if a[0] == 'inl': return key_lt(a[1], b[1]) if b[0] == 'inl' else b[0] == 'inr'
    if a[0] == 'inr': return b[0] == 'inr' and key_lt(a[1], b[1])
    if a[0] == 'pair' and b[0] == 'pair':
        return key_lt(a[1], b[1]) or (a[1] == b[1] and key_lt(a[2], b[2]))
    return False

def front(e, R):
    if e.k == 'span': return [e.a] + R
    if e.k == 'seq': return front(e.a, front(e.b, R))
    return []
def fits(s, R): return composable([s] + R) if R else True

def walk_r(P, d, neg, e, R, k, acc):
    """Returns (stop, acc). `k (key, pe) acc`."""
    kd = e.k
    if kd == 'zero': tick(1); return False, acc
    if kd == 'span':
        s = swap(e.a) if neg else e.a
        tick(1 + s.size)
        return k((LEAF, rspan(s)), acc) if fits(s, R) else (False, acc)
    tick(1)
    if kd == 'or':
        r = walk_r(P, d, neg, e.a, R, lambda x, acc: k((('inl', x[0]), x[1]), acc), acc)
        return r if r[0] else walk_r(P, d, neg, e.b, R, lambda y, acc: k((('inr', y[0]), y[1]), acc), r[1])
    if kd == 'seq':
        first, second = (e.b, e.a) if neg else (e.a, e.b)
        def k1(q, acc):
            return walk_r(P, d, neg, first, front(q[1], R),
                          lambda p, acc: k((('pair', p[0], q[0]), seq(p[1], q[1])), acc), acc)
        return walk_r(P, d, neg, second, R, k1, acc)
    if kd == 'and':
        def k1(x, acc):
            return walk_r(P, d, neg, e.b, [],
                          lambda y, acc: k((('pair', x[0], y[0]), r_and(x[1], y[1])), acc), acc)
        return walk_r(P, d, neg, e.a, [], k1, acc)
    if kd == 'conv': return walk_r(P, d, not neg, e.a, R, k, acc)
    if d == 0: return k((LEAF, conv(e) if neg else e), acc)
    return walk_r(P, d - 1, neg, P.body(e.a), R, k, acc)

def collect(x, acc):
    ps = eager_norm(False, x[1])
    if all(not to_rel_calls(p) for p in ps): return False, [(x[0], p) for p in ps] + acc
    return True, acc
def pruned(P, d, g):
    stop, found = walk_r(P, d, False, goal_rel(g), [], collect, [])
    if stop: return False, []
    ys = []
    for x in found:
        i = 0
        while i < len(ys):
            tick(key_size(x[0]) + key_size(ys[i][0]))
            if key_lt(x[0], ys[i][0]): break
            i += 1
        ys = ys[:i] + [x] + ys[i:]
    zs = []
    for s in closed([p for _, p in ys]): zs += live(s)
    ws = []
    for z in zs: ws = add_span(ws, z)
    return True, ws

def r004_unfolder(P, d, g):
    return race(Comp(lambda: r003_unfolder(P, d, g)), Comp(lambda: pruned(P, d, g)))

# ---------------------------------------------------------------- machines
class Machine:
    """A costed runtime: init (P, q) -> state, step state -> ('done',) | ('emit', answers, state)."""
    def __init__(m, init, step): m.init, m.step = init, step

def tabled_machine(U):
    return Machine(tabled_init, lambda st: tabled_step(U, st))
R001 = tabled_machine(lambda P, d, g: eager_oracle(P, d, g))
R002 = tabled_machine(on_demand)
R003 = tabled_machine(r003_unfolder)
R004 = tabled_machine(r004_unfolder)

def eager_unfold(P, e):
    tick(1)
    if e.k in ('zero', 'span'): return e
    if e.k == 'call': return P.body(e.a)
    if e.k == 'conv': return conv(eager_unfold(P, e.a))
    a = eager_unfold(P, e.a)
    return _rel(e.k, a, eager_unfold(P, e.b))
def eager_oracle(P, d, g):
    e = goal_rel(g)
    for _ in range(d): e = eager_unfold(P, e)
    ps = eager_norm(False, e)
    if all(not to_rel_calls(p) for p in ps):
        xs = []
        for s in closed(ps): xs += live(s)
        return True, xs
    return False, []

class MState:
    __slots__ = ('lead', 'lag', 'fwd', 'gap')
    def __init__(s, lead, lag, fwd, gap): s.lead, s.lag, s.fwd, s.gap = lead, lag, fwd, gap

def mirrored(C):
    """Mirror.machine C: C on the query and on its mirror image, raced step by step."""
    def step_of(x):
        if x._step is None: x._step = Comp(lambda: C.step(x))
        return x._step
    def init(P, q):
        x = C.init(P, q)
        y = C.init(P.dual(), dual(q))
        return MState(x, y, True, 0)
    def go(g, f, x, y):
        while True:
            tick(1)
            cx, cy = step_of(x), step_of(y)
            if g == 0:
                r = race(Comp(lambda: ('l', cx.run())), Comp(lambda: ('r', cy.run())))
                r2 = race(Comp(lambda: ('r', cy.run())), Comp(lambda: ('l', cx.run())))
                a, b = r, r2
                if a[0] == 'l' and a[1][0] == 'emit' and b[0] == 'l':
                    return ('emit', orient(not f, a[1][1]), MState(a[1][2], y, f, 1))
                if a[0] == 'r' and a[1][0] == 'emit' and b[0] == 'r':
                    return ('emit', orient(f, a[1][1]), MState(a[1][2], x, not f, 1))
                if a[1][0] == 'emit' and b[1][0] == 'emit' and a[0] != b[0]:
                    xs, ys = (a, b) if a[0] == 'l' else (b, a)
                    return ('emit', orient(not f, xs[1][1]), MState(xs[1][2], ys[1][2], f, 0))
                return ('done',)
            r = race(Comp(lambda: ('l', cx.run())), Comp(lambda: ('r', cy.run())))
            if r[1][0] == 'done': return ('done',)
            if r[0] == 'l': return ('emit', orient(not f, r[1][1]), MState(r[1][2], y, f, g + 1))
            y = r[1][2]; g -= 1
    return Machine(init, lambda st: go(st.gap, st.fwd, st.lead, st.lag))
R005 = mirrored(R004)

def cost_of(C, P, q, fuel, trace=None):
    """Tests/SimulationRuns.lean `costOf`: steps taken, whether the machine halted, ticks paid.
    `trace`, if a list, receives (ticks so far, answers emitted) for each step."""
    M.t = 0; M.limit = float('inf')
    s = C.init(P, q)
    i = 0
    while i < fuel:
        r = C.step(s)
        if r[0] == 'done': return i, True, M.t
        if trace is not None: trace.append((M.t, r[1]))
        s = r[2]; i += 1
    return i, False, M.t

# ---------------------------------------------------------------- inputs
def num(n):
    t = sym('z')
    for _ in range(n): t = ap('s', t)
    return t
V0, V1 = var(0), var(1)
GEN = r_or(rw(V0, sym('z')), seq(call('gen'), rw(V0, ap('s', V0))))
IDS = rw(V0, V0)
CLASH_P = Program([('gen', GEN), ('p', seq(call('gen'), rw(V0, ap('t', V0)))),
                   ('q', seq(rw(ap('u', V0), V0), call('gen'))),
                   ('pi', seq(call('p'), IDS)), ('qi', seq(IDS, call('q')))])
CLASH, CLASH_ID = seq(call('p'), call('q')), seq(call('pi'), call('qi'))
DOWN_P = Program([('q', r_or(seq(rw(ap('s', V0), V0), call('q')), at(sym('z'))))])
def down(k): return seq(at(num(k)), call('q'))

def st(x): return ap('st', x)
def pr(x, y): return ap('pair', x, y)
LAD_G = r_or(rw(st(V0), pr(V0, sym('z'))), seq(call('G'), rw(pr(V0, V1), pr(V0, ap('s', V1)))))
LAD_F = r_or(rw(pr(V0, sym('z')), st(ap('c0', V0))), rw(pr(V0, ap('s', sym('z'))), st(ap('c1', V0))))
def lad_target(n):
    t = sym('nil')
    for _ in range(n): t = ap('c1', t)
    return t
def lad_p(n, writing='right'):
    """r_i = G ; (F ; r_(i-1)) as the note writes it; 'left' is (G ; F) ; r_(i-1)."""
    defs = [('G', LAD_G), ('r0', rw(st(lad_target(n)), sym('done')))]
    for i in range(1, n + 1):
        r = call('r%d' % (i - 1))
        defs.append(('r%d' % i, seq(call('G'), seq(LAD_F, r)) if writing == 'right' else seq(seq(call('G'), LAD_F), r)))
    return Program(defs)
def ladder(n): return seq(at(st(sym('nil'))), call('r%d' % n))

BIT = r_or(rw(V0, ap('0', V0)), rw(V0, ap('1', V0)))
UNBIT = r_or(rw(ap('0', V0), V0), rw(ap('1', V0), V0))
def mid_target(k):
    t = sym('z')
    for _ in range(k): t = ap('0', t)
    return t
def mid_factors(k): return [BIT] * k + [rw(V0, mid_target(k))] + [UNBIT] * k
def nest_right(xs):
    out = xs[-1]
    for a in xs[-2::-1]: out = seq(a, out)
    return out
def nest_left(xs):
    out = xs[0]
    for a in xs[1:]: out = seq(out, a)
    return out
def nest_balanced(xs):
    if len(xs) == 1: return xs[0]
    h = len(xs) // 2
    return seq(nest_balanced(xs[:h]), nest_balanced(xs[h:]))
def nest_middle(k):
    core = rw(V0, mid_target(k))
    for _ in range(k): core = seq(BIT, seq(core, UNBIT))
    return core
def mid_writings(k):
    f = mid_factors(k)
    return [nest_right(f), nest_left(f), nest_balanced(f), nest_middle(k)]
EMPTY = Program([])

# ---------------------------------------------------------------- checks against Lean
def check():
    ok = True
    def expect(name, got, want):
        nonlocal ok
        good = got == want
        ok = ok and good
        print('%-4s %s: %s%s' % ('ok' if good else 'FAIL', name, got, '' if good else '   Lean: %s' % (want,)))
    # Tests/SimulationRuns.lean
    expect('clash', cost_of(R005, CLASH_P, CLASH, 10), (2, True, 3571))
    expect('clashId', cost_of(R005, CLASH_P, CLASH_ID, 10), (3, True, 27340))
    for k, want in zip([1, 2, 3, 4, 6, 8], [(4, True, 70783), (5, True, 135988), (6, True, 278543),
                                           (7, True, 537596), (9, True, 821008), (11, True, 2329233)]):
        expect('down %d' % k, cost_of(R005, DOWN_P, down(k), 60), want)
    for n, want in enumerate([(3, True, 12788), (5, True, 265798), (6, True, 1304050), (7, True, 1400644), (8, True, 2975637)]):
        expect('ladder %d' % n, cost_of(R005, lad_p(n), ladder(n), 40), want)
    # Tests/MiddleRuns.lean
    r4 = [[129, 129, 129, 129], [4497, 4756, 4497, 4497], [13708, 15755, 14775, 13950],
          [43112, 50907, 46355, 43556], [138816, 156667, 156610, 139806], [323318, 392393, 353034, 325942]]
    for k, want in enumerate(r4):
        expect('mid %d on R004' % k, [cost_of(R004, EMPTY, q, 12)[2] for q in mid_writings(k)], want)
    r5 = [[969, 969, 969, 969], [33540, 34064, 33540, 33540], [126308, 133287, 131045, 126619],
          [276012, 562939, 280358, 276661], [397884, 1123954, 1071841, 398622]]
    for k, want in enumerate(r5):
        expect('mid %d on R005' % k, [cost_of(R005, EMPTY, q, 12)[2] for q in mid_writings(k)], want)
    print('all agree with Lean' if ok else 'DISAGREEMENT')
    return ok

def main(argv):
    if not argv or argv[0] == 'check':
        sys.exit(0 if check() else 1)
    if argv[0] == 'ladder':
        lo, hi = int(argv[1]), int(argv[2])
        writing = argv[3] if len(argv) > 3 else 'right'
        print('  n | rounds | halted | ticks      (R005 on @(st nil) ; r_n, %s-nested bodies)' % writing)
        for n in range(lo, hi + 1):
            i, h, t = cost_of(R005, lad_p(n, writing), ladder(n), 10 * n + 40)
            print('%3d | %6d | %6s | %d' % (n, i, h, t), flush=True)
    elif argv[0] == 'down':
        for k in range(int(argv[1]), int(argv[2]) + 1):
            print(k, cost_of(R005, DOWN_P, down(k), 10 * k + 40), flush=True)

if __name__ == '__main__':
    import threading
    sys.setrecursionlimit(1_000_000)
    threading.stack_size(512 * 1024 * 1024)
    th = threading.Thread(target=main, args=(sys.argv[1:],))
    th.start(); th.join()
