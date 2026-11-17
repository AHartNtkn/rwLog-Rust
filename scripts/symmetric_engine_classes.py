"""Prototype: every tick charged to a class of union choices (design question for rung 2).

A small machine of its own, with the terms of scripts/symmetric_engine_tables.py. A table reads the
tables of its parts: a call its body, a union its members, a chain its last part and the chain of
the rest. There are no boundaries and no pushes, so it says nothing of halting.

The class of a unit of work is the union choices on the way to the answers it works on: the scope of
its table (the choices above the table) and then the paths of the answers. A request is one tick of
credit. It goes down the tree of classes: at a class, to the least charged among the work of exactly
that class and the classes one choice further that have work. The unit at the front of the class
chosen is done when the class has saved what it costs. So what is spent in a class is never more
than it was given, and the members of a union are given alike while they have work, whatever work is
done on their answers and wherever.

With scoped=True a table is seen only from its own class and the classes inside it, so no member of
a union gains from the work of another. With scoped=False tables are shared by all, as in rung 1.

This is a measurement aid, not part of any engine.
Run: python3 scripts/symmetric_engine_classes.py"""
import sys
from symmetric_engine_tables import span, call, chain, union, canon, S, ap, V, compose, cost

class Node:
    """A class: what it was given, what it has saved, the units of exactly this class, the classes
    one choice further, and how many units wait in it and below."""
    def __init__(n, up): n.up = up; n.given = 0; n.own = 0; n.saved = 0; n.items = []; n.kids = {}; n.waiting = 0

class Table:
    def __init__(t, scope, node): t.scope, t.node = scope, node; t.ans = []; t.seen = set(); t.readers = []; t.open = False

class Z:
    def __init__(M, prog, query, scoped=True):
        M.prog, M.scoped = prog, scoped; M.tables = {}; M.top = Node(None); M.ticks = 0; M.requests = 0
        M.uid = {}; M.root = M.table((), query)

    def cls(M, path):
        n = M.top
        for c in path:
            if c not in n.kids: n.kids[c] = Node(n)
            n = n.kids[c]
        return n

    def post(M, path, price, act):
        n = M.cls(path); n.items.append((price, act))
        while n is not None: n.waiting += 1; n = n.up

    def table(M, scope, node):
        if not M.scoped: scope = ()
        for k in range(len(scope), -1, -1):
            t = M.tables.get((scope[:k], node))
            if t is not None: return t
        t = M.tables[(scope, node)] = Table(scope, node)
        M.post(scope, 1, lambda: M.expand(t))
        return t

    def add(M, t, a, path):
        if a is None or a in t.seen: return
        t.seen.add(a); t.ans.append((a, path))
        for r in t.readers: r(a, path)

    def read(M, t, f):
        t.readers.append(f)
        for a, p in list(t.ans): f(a, p)

    def expand(M, t):
        n, sc = t.node, t.scope
        if n[0] == 'span': M.add(t, n[1], ())
        elif n[0] == 'call':
            M.read(M.table(sc, M.prog[n[1]]), lambda a, p: M.post(sc + p, 1, lambda: M.add(t, a, p)))
        elif n[0] == 'union':
            u = M.uid.setdefault(id(t), len(M.uid))
            for i, m in enumerate(n[1]):
                c = ((u, i),)
                M.read(M.table(sc + c, m), lambda a, p, c=c: M.post(sc + c + p, 1, lambda: M.add(t, a, c + p)))
        else:
            A, B = M.table(sc, chain(*n[1][:-1])), M.table(sc, n[1][-1])
            def pair(x, px, y, py): M.post(sc + px + py, cost(x, y), lambda: M.add(t, compose(x, y), px + py))
            def left(x, px):
                for y, py in list(B.ans): pair(x, px, y, py)
            def right(y, py):
                for x, px in list(A.ans): pair(x, px, y, py)
            M.read(A, left); B.readers.append(right)
            for y, py in list(B.ans):
                for x, px in list(A.ans[:0]): pair(x, px, y, py)

    def request(M):
        """One tick of credit, to the least charged class with work, at each choice on the way down."""
        M.requests += 1; M.ticks += 1
        n = M.top
        if not n.waiting: return False
        while True:
            n.given += 1
            best = None
            if n.items: best = (n.own, 0, None)
            for c, k in n.kids.items():
                if k.waiting and (best is None or (k.given, 1) < best[:2]): best = (k.given, 1, k)
            if best[2] is None: break
            n = best[2]
        n.own += 1; n.saved += 1
        price, act = n.items[0]
        if n.saved >= price:
            n.saved -= price; n.items.pop(0); M.ticks += price
            m = n
            while m is not None: m.waiting -= 1; m = m.up
            act()
        return True

    def run(M, want, limit=3_000_000):
        while M.ticks <= limit:
            if want in M.root.seen: return M.ticks
            if not M.request(): return None
        return None

# ---------------------------------------------------------------- families
I = span(V, V)
A, B = S('a'), S('b')
TGT = canon((A, B))

def fan(m):
    u = union(span(V, ap('s', V)), span(V, ap(ap('s', V), S('s'))))
    return {'h': chain(I, I, I, I, union(span(A, B), chain(*[u] * (m + 2))), call('c')),
            'c': union(I, chain(call('c'), I))}

def gen(j):
    """A member that never finishes, with names of its own: every number, then tagged."""
    return {'g%d' % j: union(span(V, S('z')), chain(call('g%d' % j), span(V, ap('s', V))))}, \
        chain(call('g%d' % j), span(V, ap('w%d' % j, V)))

def slow(j, t):
    """A relation whose only answer takes about `t` ticks to find: a line of `t` calls."""
    p = {'l%d_%d' % (j, i): chain(call('l%d_%d' % (j, i + 1)), I) for i in range(t)}
    p['l%d_%d' % (j, t)] = span(V, S('z'))
    return p, call('l%d_0' % j)

def nest(d, hole, prog, beside):
    """((hole | E_1) ; id | E_2) ; id | ... : d unions above the hole with an open span between them;
    `beside(j)` gives the definitions and the member beside the hole at the union j."""
    q = hole; prog = dict(prog)
    for j in range(d):
        pj, e = beside(j); prog.update(pj)
        q = chain(union(q, e), I)
    return prog, q

def sleepers(n, t):
    """Beside the hole: a slow relation, and after its answer `n` members that never finish."""
    def beside(j):
        prog, s = slow(j, t)
        ms = []
        for i in range(n):
            pi, e = gen(1000 * (j + 1) + i); prog.update(pi); ms.append(e)
        return prog, chain(s, union(*ms))
    return beside

def dag(k):
    """p_i := p_(i+1) | p_(i+1) ; ($x -> s $x): two members that call the same relation, k deep."""
    prog = {'p%d' % i: union(call('p%d' % (i + 1)), chain(call('p%d' % (i + 1)), span(V, ap('s', V))))
            for i in range(k)}
    prog['p%d' % k] = span(S('z'), S('z'))
    t = S('z')
    for _ in range(k): t = ap('s', t)
    return prog, call('p0'), canon((S('z'), t))

def row(label, cells): print('%-34s' % label + ' '.join('%10s' % ('-' if c is None else c) for c in cells)); sys.stdout.flush()

if __name__ == '__main__':
    which = sys.argv[1:] or ['fan', 'nest', 'sleepers', 'dag']
    if 'fan' in which:
        print('\nThe fan alone, by m: ticks at the first answer (a, b)')
        ms = (1, 2, 4, 6, 8)
        row('m', ms); row('scoped', [Z(fan(m), call('h')).run(TGT) for m in ms])
    if 'nest' in which:
        print('\nUnder d unions, each beside a member that never finishes: target written out, the fan (m = 4), ratio')
        for d in (1, 2, 3, 4, 5, 6, 8):
            t = Z(*nest(d, span(A, B), {}, gen)).run(TGT); f = Z(*nest(d, call('h'), fan(4), gen)).run(TGT)
            row('d = %d' % d, [t, f, None if not (t and f) else round(f / t, 1)])
    if 'sleepers' in which:
        print('\nUnder d unions, each beside a slow relation followed by n members that never finish (slow: 40 calls)')
        for n in (2, 8):
            for d in (1, 2, 3, 4):
                t = Z(*nest(d, span(A, B), {}, sleepers(n, 40))).run(TGT)
                f = Z(*nest(d, call('h'), fan(4), sleepers(n, 40))).run(TGT)
                row('n = %d, d = %d' % (n, d), [t, f, None if not (t and f) else round(f / t, 1)])
    if 'dag' in which:
        print('\nTwo members that call the same relation, k deep: ticks at the deepest answer; tables by class, tables shared')
        for k in (2, 4, 6, 8, 10, 12):
            p, q, w = dag(k)
            row('k = %d' % k, [Z(p, q).run(w), Z(p, q, scoped=False).run(w)])
