"""Prototype for lean/SYMMETRIC_ENGINE_SIMULATION.md (open point O1 of the design note).

The engine of lean/SYMMETRIC_ENGINE.md on programs with calls, with an empty theory:
normal-form nodes, goals with boundaries, a table per goal, the strategies of the design
note (join at every split, push from a complete side at every split and from both ends,
one goal per pushed answer), completion of goals that depend on themselves, and the
request rules. Costs are in the unit of scripts/symmetric_engine_prototype.py: the sizes
of the two spans of every composition attempted, and one tick for copying an answer or
opening a goal.

This is a measurement aid, not part of any engine.
Run: python3 scripts/symmetric_engine_tables.py            (prints every table of the note)

Terms: ('v', n) | ('s', name) | ('a', f, x). Span: (l, r).
Nodes: ('span', sp) | ('call', name) | ('chain', (nodes)) | ('union', (nodes))."""
import sys
sys.setrecursionlimit(1000000)

# ---------------------------------------------------------------- terms and spans
def size(t): return 1 if t[0] != 'a' else 1 + size(t[1]) + size(t[2])
def walk(t, s):
    while t[0] == 'v' and t[1] in s: t = s[t[1]]
    return t
def occurs(v, t, s):
    t = walk(t, s)
    if t[0] == 'v': return t[1] == v
    return t[0] == 'a' and (occurs(v, t[1], s) or occurs(v, t[2], s))
def unify(a, b, s):
    a, b = walk(a, s), walk(b, s)
    if a == b: return s
    if a[0] == 'v':
        if occurs(a[1], b, s): return None
        s = dict(s); s[a[1]] = b; return s
    if b[0] == 'v':
        if occurs(b[1], a, s): return None
        s = dict(s); s[b[1]] = a; return s
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
def bound(t):
    """A boundary from an interface term; a bare variable restricts nothing."""
    if t[0] == 'v': return None
    return canon((t, t))[0]

V, W = ('v', 0), ('v', 1)
def S(n): return ('s', n)
def ap(f, *xs):
    t = S(f)
    for x in xs: t = ('a', t, x)
    return t
def span(l, r): return ('span', canon((l, r)))
def at(t): return span(t, t)
def call(n): return ('call', n)
def chain(*ns):
    out = []
    for n in ns: out.extend(n[1] if n[0] == 'chain' else [n])
    return out[0] if len(out) == 1 else ('chain', tuple(out))
def union(*ns):
    out = []
    for n in ns: out.extend(n[1] if n[0] == 'union' else [n])
    out = sorted(set(out), key=repr)
    return out[0] if len(out) == 1 else ('union', tuple(out))

def has_call(n):
    """Does the node contain a call? A node with none has finitely many answers."""
    return n[0] == 'call' or (n[0] in ('chain', 'union') and any(has_call(m) for m in n[1]))

# ---------------------------------------------------------------- the machine
class Goal:
    def __init__(g, M, lb, node, rb, structural):
        g.M, g.lb, g.node, g.rb = M, lb, node, rb
        g.ans, g.seen, g.by = [], set(), {}       # all answers; answers by producing strategy
        g.done = False; g.strats = None; g.onstack = False
        g.structural = structural                 # not opened by a push or by opening a call
        g.own = 0                                 # ticks of this goal's own work
        g.stamp, g.delta, g.level = -1, 0, {}     # for the split balance
    def add(g, a, producer):
        g.by.setdefault(producer, []).append(a)
        if a not in g.seen: g.seen.add(a); g.ans.append(a)
    def expand(g):
        if g.strats is not None: return
        M, n = g.M, g.node
        if n[0] == 'span': g.strats = [SpanS(g)]
        elif n[0] == 'call': g.strats = [Copy(g, [(g.lb, M.prog[n[1]], g.rb)])]
        elif n[0] == 'union': g.strats = [Copy(g, [(g.lb, m, g.rb) for m in n[1]])]
        else:
            es = n[1]; g.strats = []
            for k in range(1, len(es)):
                a, b = chain(*es[:k]), chain(*es[k:])
                first = len(g.strats)
                g.strats.append(Join(g, a, b))
                if M.push:
                    g.strats.append(Push(g, a, b, True))
                    g.strats.append(Push(g, a, b, False))
                if M.cover:
                    for left in (True, False):
                        if M.check_calls and not has_call(a if left else b): continue
                        pats = M.edge(a if left else b, left)
                        if pats: g.strats.append(Cover(g, a, b, left, pats))
                for s in g.strats[first:]: s.split = 'check' if (M.check_apart and isinstance(s, Cover)) else k
            if M.open_calls:
                for i, e in enumerate(es):
                    if e[0] == 'call':
                        body = M.prog[e[1]]
                        ms = body[1] if body[0] == 'union' else (body,)
                        g.strats.append(Copy(g, [(g.lb, chain(*es[:i], m, *es[i + 1:]), g.rb) for m in ms], False))
    def check(g):
        if not g.done and g.strats is not None and any(s.complete() for s in g.strats): g.done = True
    def advance(g):
        """The split balance: one round of this goal. The strategies of one split of a chain (its
        join, its two pushes, its interface checks) are one group. Only the groups that stand lowest
        work (if none of them can do anything, the next lowest, and so on): each strategy of such a
        group does one unit, or everything its inputs allow where the goal has only one group, and each
        goal the group reads has its own round. A group's level rises by what its strategies did and by what the
        levels of the goals it reads rose; the level of a goal is the lowest level among its groups.
        Returns how much the level of this goal rose. A goal has one round per round of the machine,
        whoever asks, and a goal met again below itself adds nothing."""
        M = g.M
        if g.done: return 0
        if g.stamp == M.round: return g.delta
        g.stamp, g.delta = M.round, 0
        g.expand()
        groups = {}
        for i, s in enumerate(g.strats): groups.setdefault(i if M.each else s.split, []).append(s)
        for k in groups: g.level.setdefault(k, 0)
        low = min(g.level[k] for k in groups)
        whole = M.units == 'all' or (M.units == 'alone' and len(groups) == 1)
        for lv in sorted(set(g.level.values())):
            moved = False
            for k, ss in groups.items():
                if g.level[k] != lv: continue
                d = 0; subs = []
                for s in ss:
                    t = s.step()
                    while t:
                        s.spent += t; s.own += t; g.own += t; d += t; M.round_ticks += t
                        t = s.step() if whole else 0
                    for h in s.feeds():
                        if h not in subs: subs.append(h)
                for h in subs: d += h.advance()
                g.level[k] += d
                moved = moved or d > 0
            if moved: break      # a group that can do nothing passes its turn to the next lowest
        g.check()
        g.delta = min(g.level[k] for k in groups) - low
        return g.delta
    def give(g):
        """The share rule: pass one request to the strategy that has spent least."""
        if g.done or g.onstack: return 0
        if g.M.rule == 'sim3' and (g.lb is not None or g.rb is not None): return 0
        g.expand(); g.onstack = True; t = 0
        for s in sorted(g.strats, key=lambda s: s.spent):
            t = s.run()
            if t: break
        g.onstack = False; g.check()
        return t
    def unit(g):
        """One unit of this goal's own work, by the strategy that has done least of it
        (with units='strategy', one unit by each of its strategies; with units='all', each strategy
        does everything its inputs allow, which makes the flat round a round of R005's machine that
        does not repeat work)."""
        if g.done: return 0
        g.expand(); total = 0
        for s in sorted(g.strats, key=lambda s: s.own):
            t = s.step()
            while t:
                s.spent += t; s.own += t; g.own += t; total += t
                t = s.step() if g.M.units == 'all' else 0
            if total and g.M.units == 'goal': break
        g.check()
        return total

class Strat:
    def __init__(s, g): s.g = g; s.spent = 0; s.own = 0; s.fed = {}; s.split = 0
    def sub(s, key, structural=True):
        h = s.g.M.goal(*key, structural and s.g.structural)
        s.fed.setdefault(h, 0); return h
    def run(s):
        t = s.step()
        if t: s.spent += t; s.own += t; s.g.own += t; return t
        for h in sorted((h for h in s.feeds() if not h.done), key=lambda h: s.fed[h]):
            t = h.give()
            if t: s.fed[h] += t; s.spent += t; return t
        return 0

class SpanS(Strat):
    def __init__(s, g): super().__init__(g); s.ran = False
    def step(s):
        if s.ran: return 0
        s.ran = True; g = s.g; x = g.node[1]; t = 1
        if g.lb is not None and x is not None: t += cost((g.lb, g.lb), x); x = compose((g.lb, g.lb), x)
        if g.rb is not None and x is not None: t += cost(x, (g.rb, g.rb)); x = compose(x, (g.rb, g.rb))
        if x is not None: g.add(x, s)
        return t
    def feeds(s): return []
    def complete(s): return s.ran
    def pending(s): return not s.ran

class Reader:
    """A cursor into a goal's answers: one list, or one list per producer (billboard E1)."""
    def __init__(r, h, e1): r.h, r.e1, r.pos = h, e1, {}
    def lists(r): return list(r.h.by.items()) if r.e1 else [(None, r.h.ans)]

class Copy(Strat):
    """A call reads its body; a union reads its members; an opened call reads the chains it gives."""
    def __init__(s, g, keys, structural=True):
        super().__init__(g); s.subs = [s.sub(k, structural) for k in keys]; s.pos = [0] * len(s.subs); s.turn = 0
    def step(s):
        n = len(s.subs)
        for d in range(n):
            i = (s.turn + d) % n
            if s.pos[i] < len(s.subs[i].ans):
                s.g.add(s.subs[i].ans[s.pos[i]], s); s.pos[i] += 1; s.turn = i + 1; return 1
        return 0
    def feeds(s): return s.subs
    def pending(s): return any(p < len(h.ans) for p, h in zip(s.pos, s.subs))
    def complete(s): return all(h.done for h in s.subs) and not s.pending()

class Pairs:
    """Every pair of two growing lists, once."""
    def __init__(p, xs, ys): p.xs, p.ys = xs, ys; p.na = p.nb = p.inner = 0; p.spent = 0
    def next(p):
        while True:
            if len(p.xs) > p.na:
                if p.inner < p.nb: p.inner += 1; return p.xs[p.na], p.ys[p.inner - 1]
                p.na += 1; p.inner = 0
            elif len(p.ys) > p.nb:
                if p.inner < p.na: p.inner += 1; return p.xs[p.inner - 1], p.ys[p.nb]
                p.nb += 1; p.inner = 0
            else: return None
    def pending(p):
        return len(p.xs) > p.na or len(p.ys) > p.nb

class Join(Strat):
    def __init__(s, g, a, b):
        super().__init__(g); s.a = s.sub((g.lb, a, None)); s.b = s.sub((None, b, g.rb)); s.pairs = {}
    def streams(s):
        if not s.g.M.e1: return [s.pairs.setdefault(0, Pairs(s.a.ans, s.b.ans))]
        for pa, xs in list(s.a.by.items()):
            for pb, ys in list(s.b.by.items()):
                if (pa, pb) not in s.pairs: s.pairs[(pa, pb)] = Pairs(xs, ys)
        return sorted(s.pairs.values(), key=lambda p: p.spent)
    def step(s):
        for p in s.streams():
            u = p.next()
            if u is not None:
                z = compose(*u); c = cost(*u); p.spent += c
                if z is not None: s.g.add(z, s)
                return c
        return 0
    def feeds(s): return [s.a, s.b]
    def pending(s): return any(p.pending() for p in s.streams())
    def complete(s): return s.a.done and s.b.done and not s.pending()

class Push(Strat):
    """Once one side is complete, each of its answers opens the other side under that answer's interface."""
    def __init__(s, g, a, b, left):
        super().__init__(g); s.left, s.other = left, (b if left else a)
        s.side = s.sub((g.lb, a, None) if left else (None, b, g.rb))
        s.opened = 0; s.subs = []       # (answer, goal, cursor)
    def step(s):
        if not s.side.done: return 0
        g = s.g
        if s.opened < len(s.side.ans):
            x = s.side.ans[s.opened]; s.opened += 1
            key = (bound(x[1]), s.other, g.rb) if s.left else (g.lb, s.other, bound(x[0]))
            s.subs.append([x, s.sub(key, False), 0]); return 1
        for e in s.subs:
            x, h, pos = e
            if pos < len(h.ans):
                y = h.ans[pos]; e[2] += 1; u = (x, y) if s.left else (y, x)
                z = compose(*u)
                if z is not None: g.add(z, s)
                return cost(*u)
        return 0
    def feeds(s): return [s.side] if not s.side.done else [e[1] for e in s.subs]
    def pending(s):
        return s.side.done and (s.opened < len(s.side.ans) or any(e[2] < len(e[1].ans) for e in s.subs))
    def complete(s):
        return s.side.done and s.opened == len(s.side.ans) and all(e[1].done and e[2] == len(e[1].ans) for e in s.subs)

class Cover(Strat):
    """The interface check across a split. Every answer of one side ends (or begins) with one of
    finitely many spans of the program, known from the text. The other side is opened under each of
    their interfaces. If all of those goals complete with no answer, the chain has none. The side read
    from the text need not be complete, or even opened."""
    def __init__(s, g, a, b, left, pats):
        super().__init__(g)
        s.keys = [(p, b, g.rb) if left else (g.lb, a, p) for p in pats]; s.subs = None
    def step(s):
        # opening the goals is work: one tick each, when the strategy first runs
        if s.subs is not None: return 0
        s.subs = [s.sub(k, False) for k in s.keys]
        return len(s.subs)
    def live(s): return s.subs is None or not any(h.ans for h in s.subs)
    def feeds(s): return s.subs if (s.subs is not None and s.live()) else []
    def pending(s): return s.subs is None or not s.live()
    def complete(s): return s.subs is not None and all(h.done and not h.ans for h in s.subs)

class Machine:
    """rule: 'share' | 'flat' (every opened goal) | 'sflat' (goals not opened by a push or an opened call)
             | 'alt' (share and flat in turn, as the design note has it) | 'alt-s' (share and sflat in turn)
             | 'bal' (share and flat, whichever has spent fewer ticks) | 'bal-s' (the same with sflat).
    units: 'goal' (a flat round is one unit per goal, as designed) | 'strategy' (one unit per strategy) | 'all'
           (whole rounds) | 'alone' (the split balance: a unit where a goal has several groups, all where one).
    cover: the interface check. check_calls: only for a side that contains a call. check_apart: the checks of
           a goal are one group of their own instead of belonging to the group of their split.
    each: every strategy is a group of its own (measured and rejected)."""
    def __init__(M, prog, query, rule='alt', push=True, open_calls=False, e1=False, units='goal', cover=False, each=False, check_apart=False, check_calls=False):
        M.each = each; M.check_apart = check_apart; M.check_calls = check_calls
        M.prog, M.rule, M.push, M.open_calls, M.e1, M.units, M.cover = prog, rule, push, open_calls, e1, units, cover
        M.edges = {}
        M.by_rule = {'share': 0, 'flat': 0}
        M.goals = {}; M.order = []
        M.root = M.goal(None, query, None, True)
        M.ticks = 0; M.requests = 0; M.first = None; M.first_req = None
    def goal(M, lb, node, rb, structural):
        k = (lb, node, rb)
        if k not in M.goals: M.goals[k] = Goal(M, lb, node, rb, structural); M.order.append(M.goals[k])
        elif structural: M.goals[k].structural = True
        return M.goals[k]
    def edge(M, node, last):
        """The interfaces with which a product of `node` can end (last) or begin, read from the text.
        Spans at the edge are composed inwards until a call that is already being read is met, so an
        identity span at the edge hides nothing. None if one of the interfaces restricts nothing."""
        def runs(n, seen):
            # pairs (span, whole): the composed run of spans at the edge of one product of n,
            # and whether that run is the whole product
            if n[0] == 'span': return {(n[1], True)}
            if n[0] == 'union': return set().union(*[runs(m, seen) for m in n[1]])
            if n[0] == 'call':
                if n[1] in seen: return {(None, False)}
                return runs(M.prog[n[1]], seen | {n[1]})
            es = n[1] if last else n[1][::-1]
            acc = runs(es[-1], seen)
            for e in es[-2::-1]:
                if not any(w for _, w in acc): break
                new = {(x, w) for x, w in acc if not w}
                for x, _ in (r for r in acc if r[1]):
                    for y, w in runs(e, seen):
                        if y is None: new.add((x, False)); continue
                        z = compose(y, x) if last else compose(x, y)
                        if z is not None: new.add((z, w))
                acc = new
            return acc
        k = (node, last)
        if k not in M.edges:
            pats = {None if x is None else bound(x[1] if last else x[0]) for x, _ in runs(node, frozenset())}
            M.edges[k] = None if None in pats else sorted(pats, key=repr)
        return M.edges[k]
    def closure(M):
        """R001's exact check: the largest set of open goals each of which has a strategy with nothing
        left to do whose sub-goals are complete or in the set."""
        S = {g for g in M.order if not g.done and g.strats is not None}
        def quiet(s, S):
            if s.pending(): return False
            if isinstance(s, SpanS): return s.ran
            if isinstance(s, Cover): return s.subs is not None and all(h.done or h in S for h in s.subs)
            if isinstance(s, Copy): return all(h.done or h in S for h in s.subs)
            if isinstance(s, Join): return all(h.done or h in S for h in (s.a, s.b))
            return s.side.done and all(e[1].done or e[1] in S for e in s.subs)
        # a Cover is quiet only while its goals have no answer, which `pending` already says
        while True:
            T = {g for g in S if any(quiet(s, S) for s in g.strats)}
            if T == S: break
            S = T
        for g in S: g.done = True
        return bool(S)
    def flat(M, structural_only, bounded_only=False):
        t = 0
        for g in list(M.order):
            if g.done or (structural_only and not g.structural): continue
            if bounded_only and g.lb is None and g.rb is None: continue
            t += g.unit()
        return t
    def request(M):
        M.requests += 1
        r = M.rule
        if r == 'level':
            M.round = M.requests; M.round_ticks = 0
            M.root.advance(); M.closure()
            return M.round_ticks
        if r == 'sim3':
            # whole rounds for the goals that carry a boundary, the share rule for the rest
            t = M.flat(False, True) + M.root.give()
            M.closure()
            return t
        if r in ('alt', 'alt-s'): r = ('share' if M.requests % 2 else ('flat' if r == 'alt' else 'sflat'))
        if r in ('bal', 'bal-s'):
            r = 'share' if M.by_rule['share'] <= M.by_rule['flat'] else ('flat' if r == 'bal' else 'sflat')
        t = M.root.give() if r == 'share' else M.flat(r == 'sflat')
        M.by_rule['share' if r == 'share' else 'flat'] += max(t, 1)
        if r != 'share' or t == 0: M.closure()
        return t
    def run(M, limit=3_000_000, want=None, stop_at_first=False):
        """Returns (ticks at the first answer covering `want`, requests then, ticks at halt, goals opened)."""
        idle = 0
        while not M.root.done and M.ticks <= limit:
            t = M.request(); M.ticks += t
            idle = 0 if t else idle + 1
            if M.first is None and (want in M.root.seen if want is not None else M.root.ans):
                M.first, M.first_req = M.ticks, M.requests
                if stop_at_first: break
            if idle > 4: break            # nothing left to do anywhere: the run never halts
        return M.first, M.first_req, (M.ticks if M.root.done else None), len(M.goals)

# ---------------------------------------------------------------- families
def num(n):
    t = S('z')
    for _ in range(n): t = ap('s', t)
    return t
GEN = union(span(V, S('z')), chain(call('gen'), span(V, ap('s', V))))            # $x -> any number

def ce1():
    """p ; q with p = gen ; ($x -> t $x) and q = (u $x -> $x) ; gen: empty, and R005 halts at once."""
    prog = {'gen': GEN, 'p': chain(call('gen'), span(V, ap('t', V))), 'q': chain(span(ap('u', V), V), call('gen'))}
    return prog, chain(call('p'), call('q')), None

def ladder(n):
    """@(st nil) ; r_n, with r_i = G ; F ; r_(i-1), r_0 = (st (c1^n nil) -> done).
    G ; F adds a bit to the state; G alone offers every number, F keeps 0 and 1."""
    st, pair = (lambda x: ap('st', x)), (lambda x, y: ap('pair', x, y))
    target = S('nil')
    for _ in range(n): target = ap('c1', target)
    prog = {'G': union(span(st(V), pair(V, S('z'))), chain(call('G'), span(pair(V, W), pair(V, ap('s', W))))),
            'r0': span(st(target), S('done'))}
    F = union(span(pair(V, S('z')), st(ap('c0', V))), span(pair(V, ap('s', S('z'))), st(ap('c1', V))))
    for i in range(1, n + 1): prog['r%d' % i] = chain(call('G'), F, call('r%d' % (i - 1)))
    return prog, chain(at(st(S('nil'))), call('r%d' % n)), canon((st(S('nil')), S('done')))

def countdown(k):
    """@(s^k z) ; q with q = ((s $x) -> $x) ; q | (z -> z): halts by pushing the boundary down."""
    prog = {'q': union(chain(span(ap('s', V), V), call('q')), at(S('z')))}
    return prog, chain(at(num(k)), call('q')), canon((num(k), S('z')))

def fair(k, m=1):
    """q = inf | ... | inf | ((s $x) -> $x ; q) | (z -> z) asked at s^k z, with m members that never finish.
    The roadmap's example for the fairness bound (L36). inf_j = gen ; ($x -> (w_j $x)) never finishes."""
    prog = {'gen': GEN}
    infs = [chain(call('gen'), span(V, ap('w%d' % j, V))) for j in range(m)]
    prog['q'] = union(*infs, chain(span(ap('s', V), V), call('q')), at(S('z')))
    return prog, chain(at(num(k)), call('q')), canon((num(k), S('z')))

def fair_alone(k):
    """The alternative of `fair k` with every choice made: @(s^k z) ; S ; ... ; S ; (z -> z)."""
    return {}, chain(at(num(k)), *[span(ap('s', V), V)] * k, at(S('z'))), canon((num(k), S('z')))

def bits(k):
    t = S('nil')
    for i in range(k): t = ap('b%d' % (i % 2), t)
    return t
def strings(k):
    """q = inf | ((b0 $x) -> $x ; q) | ((b1 $x) -> $x ; q) | (nil -> nil), asked at a string of k bits.
    Asked with no boundary, q has 2^i answers of length i, so only the pushed boundary finds the answer."""
    prog = {'gen': GEN}
    prog['q'] = union(chain(call('gen'), span(V, ap('w', V))), chain(span(ap('b0', V), V), call('q')),
                      chain(span(ap('b1', V), V), call('q')), at(S('nil')))
    return prog, chain(at(bits(k)), call('q')), canon((bits(k), S('nil')))
def strings_alone(k):
    """The alternative of `strings k` with every choice made."""
    return {}, chain(at(bits(k)), *[span(ap('b%d' % ((k - 1 - i) % 2), V), V) for i in range(k)], at(S('nil'))), canon((bits(k), S('nil')))

def mid(k):
    """bit^k ; ($x -> t_k) ; unbit^k: family C of the design note."""
    bit = union(span(V, ap('0', V)), span(V, ap('1', V)))
    unbit = union(span(ap('0', V), V), span(ap('1', V), V))
    t = S('z')
    for _ in range(k): t = ap('0', t)
    return {}, chain(*[bit] * k, span(V, t), *[unbit] * k), None

def table(title, mk, ks, variants, cols=('first', 'halt', 'goals'), limit=3_000_000):
    print('\n' + title)
    print('  k | ' + ' | '.join('%-28s' % name for name, _ in variants))
    print('    | ' + ' | '.join('%-28s' % ' '.join('%8s' % c for c in cols) for _ in variants))
    for k in ks:
        row = []
        for _, opts in variants:
            prog, q, want = mk(k)
            first, req, halt, goals = Machine(prog, q, **opts).run(limit=limit, want=want)
            d = {'first': first, 'req': req, 'halt': halt, 'goals': goals}
            row.append('%-28s' % ' '.join('%8s' % ('-' if d[c] is None else d[c]) for c in cols))
        print('%3d | ' % k + ' | '.join(row))

def clash(with_ids=False):
    prog, q, _ = ce1()
    if with_ids:
        prog['p'] = chain(prog['p'], span(V, V)); prog['q'] = chain(span(V, V), prog['q'])
    return prog, chain(call('p'), call('q')), None

SH, FL, ALT = ('share', dict(rule='share')), ('flat', dict(rule='flat')), ('share and flat in turn', dict(rule='alt'))
BAL = ('share and flat by ticks', dict(rule='bal'))
CHECK = ('in turn, interface check', dict(rule='alt', cover=True))
FAIR = [SH, FL, ALT, ('flat, a unit per strategy', dict(rule='flat', units='strategy'))]
NP = lambda r: dict(rule=r, push=False)
WHOLE = ('whole rounds', dict(rule='flat', units='all'))
WCHECK = ('whole rounds, interface check', dict(rule='flat', units='all', cover=True))
BALW = ('share and whole rounds by ticks', dict(rule='bal', units='all'))

def t7():
    print('\n7. Whole rounds with the interface check: p ; q, and the same with identity spans')
    for ids in (False, True):
        prog, q, _ = clash(ids); M = Machine(prog, q, **WCHECK[1]); r = M.run(limit=300_000)
        print('    halt: %-6s requests: %-4d goals: %d' % (r[2], M.requests, r[3]))

def t1():
    print('\n1. p ; q (no answers; R005 halts in its second round at 3571 ticks)')
    rows = [SH, FL, ALT, ('in turn, calls opened in place', dict(rule='alt', open_calls=True)), CHECK]
    for title, ids in (('p ; q', False), ('the same with an identity span at the end of p and at the start of q (R005 halts in its third round at 27340)', True)):
        print('  ' + title)
        for name, opts in rows:
            prog, q, _ = clash(ids); M = Machine(prog, q, **opts); r = M.run(limit=300_000)
            print('    %-32s halt: %-6s ticks spent: %-7d goals: %d' % (name, r[2], M.ticks, r[3]))
TABLES = {
 '1': t1,
 '2': lambda: table('2. Counting down: @(s^k z) ; q   (R005 halts at 135988, 537596, 821008, 2329233 for k = 2, 4, 6, 8)',
                    countdown, (2, 4, 6, 8, 12, 16), [SH, FL, ALT, BAL, CHECK]),
 '3': lambda: table('3. The ladder @(st nil) ; r_n   (R005 halts at 1304050, 2975637 for n = 2, 4)', ladder, (2, 4, 6, 8, 10, 12), [SH, FL, ALT, BAL]),
 '3b': lambda: table('3b. The ladder with a way to see across calls', ladder, (2, 3, 4),
                     [('in turn, calls opened in place', dict(rule='alt', open_calls=True)), CHECK], limit=1_000_000),
 '4': lambda: table('4. Fair OR: q asked at s^k z, one member that never finishes', lambda k: fair(k, 1), (2, 4, 6, 8, 10, 12), FAIR, cols=('first', 'req', 'goals')),
 '4b': lambda: table('4b. The same with three such members', lambda k: fair(k, 3), (2, 4, 6, 8, 10, 12), FAIR, cols=('first', 'req', 'goals')),
 '4c': lambda: table('4c. The alternative of 4 run alone', fair_alone, (2, 4, 6, 8, 10, 12), [ALT], cols=('first', 'req', 'goals')),
 '4d': lambda: table('4d. Fair OR where only the pushed boundary finds the answer: q asked at a string of k bits', strings, (2, 4, 6, 8, 10), FAIR, cols=('first', 'req', 'goals')),
 '4e': lambda: table('4e. The alternative of 4d run alone', strings_alone, (2, 4, 6, 8, 10), [ALT], cols=('first', 'req', 'goals')),
 '5': lambda: table('5. Exhaustion of bit^k ; ($x -> t_k) ; unbit^k without pushes (open point O2)', mid, range(2, 11),
                    [('share', NP('share')), ('flat', NP('flat')), ('share and flat in turn', NP('alt'))]),
 '5b': lambda: table('5b. The same with pushes', mid, range(2, 9), [SH, FL, ALT, BAL]),
 '6': lambda: [table('6. Whole rounds on the fair OR families: %s' % n, f, ks, [WHOLE, BALW], cols=('first', 'req', 'goals'), limit=1_000_000)
              for n, f, ks in (('4, one member that never finishes', lambda k: fair(k, 1), (2, 4, 6, 8, 10, 12)),
                               ('4b, three such members', lambda k: fair(k, 3), (2, 4, 6, 8, 10, 12)),
                               ('4d, strings of k bits', strings, (2, 4, 6, 8, 10)))],
 '6b': lambda: [table('6b. Share and unit flat rounds balanced by ticks on the fair OR families: %s' % n, f, ks, [BAL, ('the same, a unit per strategy', dict(rule='bal', units='strategy'))], cols=('first', 'req', 'goals'), limit=1_000_000)
              for n, f, ks in (('4, one member that never finishes', lambda k: fair(k, 1), (2, 4, 6, 8, 10, 12)),
                               ('4b, three such members', lambda k: fair(k, 3), (2, 4, 6, 8, 10, 12)),
                               ('4d, strings of k bits', strings, (2, 4, 6, 8, 10)))],
 '7': lambda: [t7()] + [table('7. Whole rounds with the interface check: %s' % n, f, ks, [WHOLE, WCHECK, BALW], limit=1_000_000)
              for n, f, ks in (('counting down', countdown, (2, 4, 8, 16)), ('the ladder', ladder, (2, 4, 6, 8, 10, 12)),
                               ('bit^k ; ($x -> t_k) ; unbit^k with pushes', mid, range(2, 9)))],
}
# ---------------------------------------------------------------- the second attack (section 9 of the note)
SB = ('split balance', dict(rule='level', units='alone'))
SBC = ('split balance, check on sides with a call', dict(rule='level', units='alone', cover=True, check_apart=True, check_calls=True))
SBF = ('split balance, check on every side', dict(rule='level', units='alone', cover=True))
SIM3 = ('whole rounds for bounded goals, share for the rest', dict(rule='sim3', units='all'))
def t9():
    print('\n9. p ; q and the same with identity spans')
    for name, opts in (SB, SBC, SBF, WCHECK, ('share, interface check', dict(rule='share', cover=True))):
        for ids in (False, True):
            prog, q, _ = clash(ids); M = Machine(prog, q, **opts); r = M.run(limit=300_000)
            print('    %-44s halt: %-6s requests: %-4d goals: %d' % (name, r[2], M.requests, r[3]))
TABLES.update({
 '8': lambda: [table('8. The split balance: %s' % n, f, ks, [SB, SBC], cols=c, limit=lim)
               for n, f, ks, c, lim in (
                   ('counting down', countdown, (2, 4, 8, 16, 32), ('halt', 'req', 'goals'), 3_000_000),
                   ('the ladder', ladder, (4, 8, 12, 16, 20, 24, 28, 32, 40), ('halt', 'req', 'goals'), 30_000_000),
                   ('bit^k ; ($x -> t_k) ; unbit^k with pushes', mid, range(2, 11), ('halt', 'req', 'goals'), 30_000_000),
                   ('fair OR, one member that never finishes', lambda k: fair(k, 1), (2, 4, 6, 8, 10, 12), ('first', 'req', 'goals'), 1_000_000),
                   ('fair OR, three such members', lambda k: fair(k, 3), (2, 4, 6, 8, 10, 12), ('first', 'req', 'goals'), 1_000_000),
                   ('strings of k bits', strings, (2, 4, 6, 8, 10), ('first', 'req', 'goals'), 5_000_000))],
 '9': t9,
 '10': lambda: [table('10. The interface check on every side: %s' % n, f, ks,
                      [SBF, WCHECK, ('share, interface check', dict(rule='share', cover=True))], cols=('halt', 'req', 'goals'), limit=30_000_000)
                for n, f, ks in (('bit^k ; ($x -> t_k) ; unbit^k with pushes', mid, range(2, 8)), ('the ladder', ladder, (8, 16, 24, 32)))],
 '11': lambda: [table('11. Whole rounds only for goals that carry a boundary (billboard SIM3): %s' % n, f, ks, [SIM3], cols=c, limit=5_000_000)
                for n, f, ks, c in (('counting down', countdown, (2, 4, 8, 16, 32), ('halt', 'req', 'goals')),
                                    ('the ladder', ladder, (4, 8, 12, 16), ('halt', 'req', 'goals')),
                                    ('bit^k ; ($x -> t_k) ; unbit^k with pushes', mid, range(2, 8), ('halt', 'req', 'goals')),
                                    ('fair OR, three members that never finish', lambda k: fair(k, 3), (2, 4, 6, 8), ('first', 'req', 'goals')))],
 '12': lambda: table('12. The ladder past n = 12 under the rules of sections 3 and 4', ladder, (12, 16, 20, 24, 28),
                     [SH, FL, WHOLE], cols=('halt', 'goals'), limit=30_000_000),
})
if __name__ == '__main__':
    print('Ticks at the first answer, ticks at halt, goals opened; "req" is requests to the root at the first')
    print('answer. "-" is: not within the tick limit (3,000,000; 1,000,000 in 3b, 6, 6b and 7), or never.')
    for name in (sys.argv[1:] or TABLES): TABLES[name]()
