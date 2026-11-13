"""Prototype for lean/SYMMETRIC_ENGINE.md, section 5.

A flat chain of factors, each a finite set of spans, with no calls and an empty
theory. Two ways to evaluate it are costed in the same unit (the sizes of the
two spans of every composition attempted):

* tables on one fixed bracketing, each pair of answers joined once;
* a table on every interval of the chain, every split of an interval a
  strategy of its table, and the strategies of a table balanced by what they
  have spent. A strategy with nothing to join passes its turn to the child it
  has fed less. A table is complete when one of its strategies has joined two
  complete tables, and nothing more is spent on it.

This is a measurement aid, not part of any engine. Run: python3 scripts/symmetric_engine_prototype.py

Terms: ('v', n) | ('s', name) | ('a', f, x). Span: (l, r)."""
import sys
sys.setrecursionlimit(100000)

def size(t): return 1 if t[0] != 'a' else 1 + size(t[1]) + size(t[2])
def walk(t, s):
    while t[0] == 'v' and t[1] in s: t = s[t[1]]
    return t
def unify(a, b, s):
    a, b = walk(a, s), walk(b, s)
    if a == b: return s
    if a[0] == 'v': s = dict(s); s[a[1]] = b; return s
    if b[0] == 'v': s = dict(s); s[b[1]] = a; return s
    if a[0] == 'a' and b[0] == 'a':
        s = unify(a[1], b[1], s)
        return None if s is None else unify(a[2], b[2], s)
    return None
def subst(t, s):
    t = walk(t, s)
    return ('a', subst(t[1], s), subst(t[2], s)) if t[0] == 'a' else t
def shift(t, k):
    if t[0] == 'v': return ('v', t[1] + k)
    return ('a', shift(t[1], k), shift(t[2], k)) if t[0] == 'a' else t
def maxvar(t):
    if t[0] == 'v': return t[1] + 1
    return max(maxvar(t[1]), maxvar(t[2])) if t[0] == 'a' else 0
def canon(sp):
    m = {}
    def go(t):
        if t[0] == 'v': return ('v', m.setdefault(t[1], len(m)))
        return ('a', go(t[1]), go(t[2])) if t[0] == 'a' else t
    return (go(sp[0]), go(sp[1]))
def compose(x, y):
    k = max(maxvar(x[0]), maxvar(x[1]))
    y = (shift(y[0], k), shift(y[1], k))
    s = unify(x[1], y[0], {})
    return None if s is None else canon((subst(x[0], s), subst(y[1], s)))
def cost(x, y): return size(x[0]) + size(x[1]) + size(y[0]) + size(y[1])

V = ('v', 0)
def ap(f, x): return ('a', ('s', f), x)
bit = [(V, ap('0', V)), (V, ap('1', V))]
unbit = [(ap('0', V), V), (ap('1', V), V)]
def tk(k):
    t = ('s', 'z')
    for _ in range(k): t = ap('0', t)
    return t

# ---- fixed bracketing: every pair of each node joined once (semi-naive tables) ----
LIMIT = 3_000_000
def rnest(i, j): return i if j - i == 1 else (i, rnest(i + 1, j))
def lnest(i, j): return i if j - i == 1 else (lnest(i, j - 1), j - 1)
def bal(i, j):
    if j - i == 1: return i
    h = (i + j) // 2; return (bal(i, h), bal(h, j))
def fixed_cost(fs, tree):
    spent = 0
    def ev(t):
        nonlocal spent
        if isinstance(t, int): return list(dict.fromkeys(canon(s) for s in fs[t]))
        xs, ys = ev(t[0]), ev(t[1]); out = {}
        for x in xs:
            for y in ys:
                spent += cost(x, y)
                if spent > LIMIT: raise OverflowError
                z = compose(x, y)
                if z is not None: out[z] = 1
        return list(out)
    try: ev(tree); return spent
    except OverflowError: return None

# ---- every interval, strategies balanced by ticks ----
class Goal:
    def __init__(s, M, i, j):
        s.M, s.i, s.j = M, i, j; s.ans = []; s.seen = set(); s.done = False; s.strats = None
        if j - i == 1:
            for sp in M.fs[i]: s.add(canon(sp))
            s.done = True
    def add(s, a):
        if a not in s.seen: s.seen.add(a); s.ans.append(a)
    def give(s):
        """Spend one unit of work somewhere below this goal. Returns ticks used."""
        if s.done: return 0
        if s.strats is None:
            s.strats = [Strat(s, s.M.goal(s.i, k), s.M.goal(k, s.j)) for k in range(s.i + 1, s.j)]
        st = min(s.strats, key=lambda t: t.spent)
        return st.run()
class Strat:
    def __init__(s, g, a, b): s.g, s.a, s.b = g, a, b; s.na = s.nb = 0; s.inner = 0; s.spent = 0; s.sa = s.sb = 0
    def run(s):
        a, b, g = s.a, s.b, s.g
        u = None
        if len(a.ans) > s.na:
            if s.inner < s.nb: u = (a.ans[s.na], b.ans[s.inner]); s.inner += 1
            else: s.na += 1; s.inner = 0; return s.run()
        elif len(b.ans) > s.nb:
            if s.inner < s.na: u = (a.ans[s.inner], b.ans[s.nb]); s.inner += 1
            else: s.nb += 1; s.inner = 0; return s.run()
        if u is not None:
            c = cost(*u); z = compose(*u)
            if z is not None: g.add(z)
            s.spent += c; return c
        if a.done and b.done: g.done = True; return 0
        # nothing to join yet: pass the work to the child this strategy has fed less
        first, second = (a, b) if (s.sa <= s.sb or b.done) and not a.done else (b, a)
        c = first.give()
        if first is a: s.sa += c
        else: s.sb += c
        s.spent += c
        return c
class Machine:
    def __init__(s, fs): s.fs = fs; s.goals = {}
    def goal(s, i, j):
        if (i, j) not in s.goals: s.goals[(i, j)] = Goal(s, i, j)
        return s.goals[(i, j)]
    def run(s):
        root = s.goal(0, len(s.fs)); total = 0; first = None
        while not root.done:
            total += root.give()
            if first is None and root.ans: first = total
            if total > LIMIT: return None, None, len(s.goals)
        return first, total, len(s.goals)

def show(name, mk, ks):
    print(f"\n{name}\n  k   n | right-nested  left-nested     balanced | balanced-intervals: first answer, halt, goals opened")
    for k in ks:
        fs = mk(k); n = len(fs)
        f = lambda v: f"{v:>12}" if v is not None else "      >limit"
        r, l, b = (fixed_cost(fs, t(0, n)) for t in (rnest, lnest, bal))
        first, tot, ng = Machine(fs).run()
        print(f"{k:>3} {n:>3} | {f(r)} {f(l)} {f(b)} | {f(first)} {f(tot)} {ng:>5}")

ks = range(1, 13)
show("A. bit^k ; @t_k  (restricted on the right)", lambda k: [bit] * k + [[(tk(k), tk(k))]], ks)
show("B. @t_k ; unbit^k  (mirror image of A)", lambda k: [[(tk(k), tk(k))]] + [unbit] * k, ks)
show("C. bit^k ; ($x -> t_k) ; unbit^k  (restricted in the middle)", lambda k: [bit] * k + [[(V, tk(k))]] + [unbit] * k, ks)
show("D. unbit^k ; @z ; bit^k  (restricted in the middle, both halves are tests)", lambda k: [unbit] * k + [[(('s','z'), ('s','z'))]] + [bit] * k, range(1, 9))
show("E. bit^k  (no restriction: 2^k answers are owed)", lambda k: [bit] * k, range(2, 11))
show("F. @t_k ; unbit^k ; bit^k ; @t_k  (restricted at both ends, wide in the middle)", lambda k: [[(tk(k), tk(k))]] + [unbit] * k + [bit] * k + [[(tk(k), tk(k))]], range(1, 9))
