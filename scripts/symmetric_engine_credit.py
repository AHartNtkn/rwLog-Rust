"""Prototype: sharing work by ticks instead of rounds (design question for rung 2).

The machine of scripts/symmetric_engine_tables.py with one more request rule, 'credit'. A request
is one tick of credit that goes from the root to one consumer. At a goal the group that has been
given least takes it; in the group the consumer that has been given least takes it. The consumers
of a group are the own work of each of its strategies that has something to do, and each goal its
strategies read that is not complete. The members of a union are compared by all the credit they
have been given, whoever gave it. A strategy saves what it is given, and does a unit only when it
has saved what the unit costs: a unit is tried when the strategy has saved twice what it last gave
up at, and a unit that costs more than is saved is given up and what was saved is spent. So what a
goal and everything under it spend is never more than they have been given.

With weights=True a consumer that is a goal counts for the strategies under it, as the turns of
the engine as built do.

This is a measurement aid, not part of any engine.
Run: python3 scripts/symmetric_engine_credit.py"""
import sys
import symmetric_engine_tables as T
from symmetric_engine_tables import (Machine, Goal, SpanS, Copy, Join, Push, Cover, Race, span, at, call,
                                     chain, union, canon, S, ap, V, num, countdown, strings, fair, line,
                                     beside, beside_endless, mid, ladder)

# ---------------------------------------------------------------- a unit that can be taken back
def snap(s):
    if isinstance(s, SpanS): return ('span', s.ran)
    if isinstance(s, Copy): return ('copy', list(s.pos), s.turn)
    if isinstance(s, Join): return ('join', {k: (p.na, p.nb, p.inner, p.spent, p.col) for k, p in s.pairs.items()})
    if isinstance(s, Push): return ('push', s.opened, len(s.subs), [e[2] for e in s.subs])
    if isinstance(s, Cover): return ('cover', s.subs)
    return ('race', s.depth, s.fin)

def restore(s, z):
    if z[0] == 'span': s.ran = z[1]
    elif z[0] == 'copy': s.pos, s.turn = z[1], z[2]
    elif z[0] == 'join':
        for k, v in z[1].items(): p = s.pairs[k]; p.na, p.nb, p.inner, p.spent, p.col = v
        for k in [k for k in s.pairs if k not in z[1]]: del s.pairs[k]
    elif z[0] == 'push':
        s.opened = z[1]; del s.subs[z[2]:]
        for e, pos in zip(s.subs, z[3]): e[2] = pos
    elif z[0] == 'cover': s.subs = z[1]
    else: s.depth, s.fin = z[1], z[2]

def attempt(s, M):
    """Try one unit of `s` within what it has saved. Returns 'none' (nothing to do), 'done', 'gave up'
    or 'wait' (it has not saved enough to try)."""
    if s.bank < max(1, 2 * s.gave): return 'wait'
    g = s.g; z = snap(s); buf = []; add = g.add
    g.add = lambda a, producer: buf.append((a, producer))
    try: c = s.step()
    finally: g.add = add
    if not c: restore(s, z); return 'none'
    if c > s.bank:
        restore(s, z); M.spent += s.bank; s.gave = s.bank; s.bank = 0; return 'gave up'
    for a, producer in buf: g.add(a, producer)
    s.bank -= c; s.gave = 0; s.spent += c; s.own += c; g.own += c; M.spent += c; M.worked = True
    return 'done'

def groups_of(g):
    M = g.M; groups = {}
    for s in g.strats: groups.setdefault(s.split, []).append(s)
    if g.race is not None: groups['race'] = [g.race]
    for k in groups: g.level.setdefault(k, 0)
    return groups

def can_work(s):
    if isinstance(s, Race): return not s.fin
    return s.pending()

def grant(g):
    """One tick of credit for the goal `g`. Returns whether anything under it took it."""
    M = g.M
    if g.done or g.cstamp == M.requests: return False
    g.cstamp = M.requests
    g.expand()
    groups = groups_of(g)
    is_union = g.node[0] == 'union'
    for k in sorted(groups, key=lambda k: g.level[k]):
        cons = []
        for s in groups[k]:
            if can_work(s): cons.append(('own', s))
            if not isinstance(s, Race):
                for h in s.feeds():
                    if not h.done and all(c[1] is not h for c in cons): cons.append(('goal', h))
        def given(c):
            if c[0] == 'own': x, w = c[1].given, 1
            else:
                x = c[1].credit if is_union else g.acct.get((k, c[1]), 0)
                w = 1 + (M.weight_of(c[1]) if (M.weights and not is_union) else 0)
            return x / w
        for c in sorted(cons, key=given):
            if c[0] == 'own':
                s = c[1]; s.bank += 1; s.given += 1
                r = attempt(s, M)
                if r == 'none': s.bank -= 1; s.given -= 1; continue
                while r == 'done' and can_work(s): r = attempt(s, M)
                g.level[k] += 1; return True
            h = c[1]
            if grant(h):
                h.credit += 1; g.acct[(k, h)] = g.acct.get((k, h), 0) + 1; g.level[k] += 1; return True
    return False

class CMachine(Machine):
    def __init__(M, prog, query, weights=False, **kw):
        super().__init__(prog, query, rule='credit', **kw)
        M.weights = weights; M.spent = 0; M.worked = False; M.wcache = {}
    def goal(M, lb, node, rb, structural):
        g = super().goal(lb, node, rb, structural)
        if not hasattr(g, 'credit'): g.credit = 0; g.cstamp = -1; g.acct = {}
        return g
    def weight_of(M, h):
        if h not in M.wcache:
            seen, stack, n = {h}, [h], 0
            while stack:
                x = stack.pop()
                if x.strats is None: continue
                n += len(x.strats)
                for u in x.strats:
                    for y in u.feeds():
                        if y not in seen: seen.add(y); stack.append(y)
            M.wcache[h] = n
        return M.wcache[h]
    def run(M, limit=3_000_000, want=None, stop_at_first=False):
        """Ticks are one for each request and what the units cost. Returns as `Machine.run`."""
        idle = 0
        while not M.root.done and M.ticks <= limit:
            M.requests += 1; M.worked = False; M.wcache = {}; before = M.spent
            used = grant(M.root)
            M.ticks += 1 + (M.spent - before)
            if M.worked or not used: M.closure()
            idle = 0 if used else idle + 1
            if M.first is None and (want in M.root.seen if want is not None else M.root.ans):
                M.first, M.first_req = M.ticks, M.requests
                if stop_at_first: break
            if idle > 2: break
        return M.first, M.first_req, (M.ticks if M.root.done else None), len(M.goals)

def new_strat_fields():
    init = T.Strat.__init__
    def patched(s, g):
        init(s, g); s.bank = 0; s.gave = 0; s.given = 0
    T.Strat.__init__ = patched
new_strat_fields()

# ---------------------------------------------------------------- families
I = span(V, V)
A, B = S('a'), S('b')
def fan(m):
    """The fan of lean/RwLog/Rungs/Symmetric/Fan.lean: h := id;id;id;id;(g | u^(m+2));c, c := id | c;id."""
    u = union(span(V, ap('s', V)), span(V, ap(ap('s', V), S('s'))))
    prog = {'h': chain(I, I, I, I, union(span(A, B), chain(*[u] * (m + 2))), call('c')),
            'c': union(I, chain(call('c'), I))}
    return prog, call('h'), canon((A, B))

def gen_j(j):
    """A member that never finishes, with names of its own: every number, then tagged."""
    return {'g%d' % j: union(span(V, S('z')), chain(call('g%d' % j), span(V, ap('s', V))))}, \
        chain(call('g%d' % j), span(V, ap('w%d' % j, V)))

def nest(d, inner, prog):
    """((inner | E_1) ; id | E_2) ; id | ... : d unions on the way to the hole, each beside a member
    that never finishes, with an open span between them."""
    q = inner; prog = dict(prog)
    for j in range(d):
        pj, e = gen_j(j); prog.update(pj)
        q = union(q, e)
        if j + 1 < d: q = chain(q, I)
    return prog, q

def nest_fan(m):
    return lambda d: nest(d, call('h'), fan(m)[0]) + (canon((A, B)),)
def nest_tgt(d):
    return nest(d, span(A, B), {}) + (canon((A, B)),)

BUILT = ('as built (turns of 4)', dict(T.LEAN, race='own', turn=4, race_cap=True))
def credit(name, **kw):
    return (name, dict(kw, cover=False, fair_units=True, check_apart=True, race='own', _credit=True))
PLAIN = credit('credit, equal shares')
WEIGHT = credit('credit, by weight', weights=True)

def table(title, mk, ks, variants, cols=('first', 'req', 'goals'), limit=3_000_000):
    print('\n' + title)
    print('  k | ' + ' | '.join('%-30s' % name for name, _ in variants))
    print('    | ' + ' | '.join('%-30s' % ' '.join('%9s' % c for c in cols) for _ in variants))
    for k in ks:
        row = []
        for _, opts in variants:
            prog, q, want = mk(k); opts = dict(opts)
            M = CMachine(prog, q, **opts) if opts.pop('_credit', False) else Machine(prog, q, **opts)
            first, req, halt, goals = M.run(limit=limit, want=want)
            d = {'first': first, 'req': req, 'halt': halt, 'goals': goals}
            row.append('%-30s' % ' '.join('%9s' % ('-' if d[c] is None else d[c]) for c in cols))
        print('%3d | ' % k + ' | '.join(row))
    sys.stdout.flush()

if __name__ == '__main__':
    V3 = [BUILT, PLAIN, WEIGHT]
    which = sys.argv[1:] or ['fan', 'nest', 'old']
    if 'fan' in which:
        table('The fan alone, by m (ticks at the first answer covering (a, b))', fan, (1, 2, 4, 6, 8, 10), V3, limit=2_000_000)
    if 'nest' in which:
        table('The target written out under d unions', nest_tgt, (1, 2, 3, 4, 5, 6), V3, limit=2_000_000)
        table('The fan (m = 2) under d unions', nest_fan(2), (1, 2, 3, 4, 5, 6), V3, limit=2_000_000)
        table('The fan (m = 6) under d unions', nest_fan(6), (1, 2, 3, 4, 5, 6), V3, limit=2_000_000)
    if 'old' in which:
        for n, f, ks, c, lim in (
                ('counting down alone', countdown, (2, 4, 8, 12, 16), ('first', 'req', 'goals'), 3_000_000),
                ('counting down, to the halt', countdown, (2, 4, 8, 16), ('halt', 'req', 'goals'), 3_000_000),
                ('a line of k calls alone', line, (4, 8, 16, 32), ('first', 'req', 'goals'), 2_000_000),
                ('fair OR, three members that never finish', lambda k: fair(k, 3), (2, 4, 8, 12), ('first', 'req', 'goals'), 2_000_000),
                ('strings of k bits', strings, (2, 4, 6, 8, 10), ('first', 'req', 'goals'), 2_000_000),
                ('the line beside an endless member', beside_endless, (4, 8, 16, 32), ('first', 'req', 'goals'), 8_000_000),
                ('bit^k ; ($x -> t_k) ; unbit^k with pushes', mid, (2, 4, 6, 8), ('halt', 'req', 'goals'), 30_000_000),
                ('the ladder', ladder, (4, 6, 10, 12), ('halt', 'req', 'goals'), 30_000_000)):
            table(n, f, ks, V3, cols=c, limit=lim)
