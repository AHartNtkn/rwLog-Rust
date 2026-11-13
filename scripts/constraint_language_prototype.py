#!/usr/bin/env python3
"""Prototype of the constraint rule language of lean/CONSTRAINT_LANGUAGE.md.

It is a model of the design, not an engine: every search is brute force.

  * `Theory`       reads a `theory { ... }` block and classifies every rule as a
                   definition `K \\ r <=> eqs, B` or a restriction `K ==> eqs`.
  * `check`        the well-formedness check: rule shape, the order condition,
                   created variables, liveness, joinable critical pairs.
  * `nf`           the normal form of a store (with the bindings its equations force).
  * `canon`        the canonical representative of a span: normal form, core,
                   canonical labelling, orientation bit.

Run it with no argument. It checks every example theory of the repository as
written and as expressed in the language, and the claims of the design note.
"""
import itertools
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ---------------------------------------------------------------- terms
# A variable is a string starting with '$'. A symbol is any other string.
# A compound term is a tuple (head, arg1, ..., argn).


def is_var(t):
    return isinstance(t, str) and t.startswith('$')


def vars_of(t, acc=None):
    acc = [] if acc is None else acc
    if is_var(t):
        acc.append(t)
    elif isinstance(t, tuple):
        for a in t[1:]:
            vars_of(a, acc)
    return acc


def size(t):
    return 1 + sum(size(a) for a in t[1:]) if isinstance(t, tuple) else 1


def subst(t, s):
    if is_var(t):
        return subst(s[t], s) if t in s else t
    if isinstance(t, tuple):
        return (t[0],) + tuple(subst(a, s) for a in t[1:])
    return t


def occurs(v, t, s):
    t = subst(t, s)
    return v in vars_of(t)


def unify(a, b, s):
    """Most general unifier extending `s`, or None."""
    a, b = subst(a, s), subst(b, s)
    if a == b:
        return s
    if is_var(a):
        if occurs(a, b, s):
            return None
        return {**s, a: b}
    if is_var(b):
        return unify(b, a, s)
    if isinstance(a, tuple) and isinstance(b, tuple) and a[0] == b[0] and len(a) == len(b):
        for x, y in zip(a[1:], b[1:]):
            s = unify(x, y, s)
            if s is None:
                return None
        return s
    return None


def match(p, t, s):
    """One-way matching: bind variables of `p` only. Variables of `t` are rigid."""
    if is_var(p):
        if p in s:
            return s if s[p] == t else None
        return {**s, p: t}
    if isinstance(p, tuple):
        if not (isinstance(t, tuple) and p[0] == t[0] and len(p) == len(t)):
            return None
        for x, y in zip(p[1:], t[1:]):
            s = match(x, y, s)
            if s is None:
                return None
        return s
    return s if p == t else None


def apply_match(t, s):
    """Apply a matching substitution (not idempotent-closed, one pass)."""
    if is_var(t):
        return s.get(t, t)
    if isinstance(t, tuple):
        return (t[0],) + tuple(apply_match(a, s) for a in t[1:])
    return t


def show(t):
    if isinstance(t, tuple):
        return '(' + ' '.join([t[0]] + [show(a) for a in t[1:]]) + ')'
    return t


def show_store(c):
    return '{' + ', '.join(sorted(show(a) for a in c)) + '}'


def pred(atom):
    return (atom[0], len(atom) - 1) if isinstance(atom, tuple) else (atom, 0)


# ---------------------------------------------------------------- parsing

TOKEN = re.compile(r'\(|\)|<=>|==>|,|\||=|\\|\.(?![\w$])|[^\s(),|=\\]+?(?=[\s(),|=\\]|\.(?![\w$])|$)')


def tokens(src):
    src = re.sub(r'#[^\n]*', '', src)
    return TOKEN.findall(src)


class ParseError(Exception):
    pass


def parse_term(ts, i):
    if i >= len(ts):
        raise ParseError('unexpected end of rule')
    if ts[i] == '(':
        i += 1
        items = []
        while i < len(ts) and ts[i] != ')':
            if ts[i] in ('<=>', '==>', '.', ',', '|', '=', '\\'):
                raise ParseError("unbalanced parenthesis before '%s'" % ts[i])
            t, i = parse_term(ts, i)
            items.append(t)
        if i >= len(ts):
            raise ParseError('unbalanced parenthesis')
        if not items or not isinstance(items[0], str) or is_var(items[0]):
            raise ParseError('a compound term needs a symbol first')
        return tuple(items), i + 1
    if ts[i] in (')', '<=>', '==>', '.', ',', '|', '=', '\\'):
        raise ParseError("unexpected '%s'" % ts[i])
    return ts[i], i + 1


class Rule:
    """A rule after classification.

    kind 'def':      kept \\ removed <=> eqs, body      (one removed atom)
    kind 'restrict': kept ==> eqs                        (fails when `fails`)
    """

    def __init__(self, text):
        self.text = text
        self.kind = None
        self.kept, self.removed, self.eqs, self.body, self.fails = [], None, [], [], False

    def heads(self):
        return self.kept + ([self.removed] if self.removed is not None else [])

    def rename(self, tag):
        r = Rule(self.text)
        ren = lambda t: (t + tag if is_var(t) else
                         (t[0],) + tuple(ren(a) for a in t[1:]) if isinstance(t, tuple) else t)
        r.kind, r.fails = self.kind, self.fails
        r.kept = [ren(a) for a in self.kept]
        r.removed = None if self.removed is None else ren(self.removed)
        r.eqs = [(ren(a), ren(b)) for a, b in self.eqs]
        r.body = [ren(a) for a in self.body]
        return r


class Rejected(Exception):
    pass


def parse_rule(ts, text):
    """Surface forms:  H1, ..., Hn <=> body.      K1, ... \\ H <=> body.
    A body is `fail`, `.`/`true`, or a list of atoms and equations `s = t`;
    `G | body` is sugar for writing the atoms of G on both sides."""
    i, side, heads, kept_explicit = 0, [], None, None
    lhs = []
    while ts[i] not in ('<=>', '==>'):
        if ts[i] == ',':
            i += 1
        elif ts[i] == '\\':
            kept_explicit, lhs = lhs, []
            i += 1
        else:
            t, i = parse_term(ts, i)
            lhs.append(t)
        if i >= len(ts):
            raise ParseError("expected '<=>'")
    arrow = ts[i]
    i += 1
    items, guard, fails = [], [], False
    while i < len(ts):
        if ts[i] == ',':
            i += 1
        elif ts[i] == '|':
            guard, items = [x for x in items], []
            i += 1
        elif ts[i] == 'fail':
            fails = True
            i += 1
        elif ts[i] == 'true':
            i += 1
        else:
            t, i = parse_term(ts, i)
            if i < len(ts) and ts[i] == '=':
                u, i = parse_term(ts, i + 1)
                items.append(('=', t, u))
            else:
                items.append(t)
    if any(isinstance(g, tuple) and g[0] == '=' for g in guard):
        raise ParseError('a guard is a list of atoms')
    heads = (kept_explicit or []) + lhs + guard
    eqs = [(x[1], x[2]) for x in items if x[0] == '=']
    atoms = [x for x in items if x[0] != '='] + (kept_explicit or []) + guard
    if arrow == '==>':
        atoms = atoms + lhs
    return classify(heads, eqs, atoms, fails, text)


def classify(heads, eqs, atoms, fails, text):
    r = Rule(text)
    hs = list(dict.fromkeys(heads))
    head_vars = set(v for h in hs for v in vars_of(h))
    for a, b in eqs:
        if not set(vars_of(a) + vars_of(b)) <= head_vars:
            raise Rejected('an equation mentions a variable that no head binds')
    mu = {}
    for a, b in eqs:
        mu = unify(a, b, mu) if mu is not None else None
    if fails or mu is None:
        r.kind, r.kept, r.fails = 'restrict', hs, True
        return r
    hmu = [subst(h, mu) for h in hs]
    bmu = set(subst(b, mu) for b in atoms)
    kept = [h for h, m in zip(hs, hmu) if m in bmu]
    removed = [h for h, m in zip(hs, hmu) if m not in bmu]
    added = [b for b in dict.fromkeys(atoms) if subst(b, mu) not in hmu]
    r.eqs = eqs
    if not removed:
        if added:
            raise Rejected('it removes no head and adds atoms (a propagation); '
                           'the language has none')
        if all(subst(a, {}) == subst(b, {}) for a, b in eqs):
            raise Rejected('it says nothing: on a set of atoms the heads are the body')
        r.kind, r.kept = 'restrict', hs
        return r
    if len(removed) > 1:
        raise Rejected('it removes %d heads; a rule defines one atom '
                       '(write the body as the defined atom instead)' % len(removed))
    r.kind, r.kept, r.removed, r.body = 'def', kept, removed[0], added
    return r


class Theory:
    def __init__(self, src, name='?'):
        self.name, self.rules, self.errors, self.preds, self.closed = name, [], [], {}, set()
        body = src
        m = re.search(r'theory\s+(\w+)\s*\{(.*)\}', src, re.S)
        if m:
            self.name, body = m.group(1), m.group(2)
        body = re.sub(r'#[^\n]*', '', body)
        for line in body.split('\n'):
            m = re.match(r'\s*constraint\s*(\S*)\s*(closed)?\s*$', line)
            if m:
                d = re.match(r'(\w+)/(\d+)$', m.group(1))
                if not d:
                    self.errors.append(("constraint " + m.group(1), 'not a declaration name/arity'))
                else:
                    self.preds[(d.group(1), int(d.group(2)))] = True
                    if m.group(2):
                        self.closed.add((d.group(1), int(d.group(2))))
        body = '\n'.join(l for l in body.split('\n') if not re.match(r'\s*constraint\b', l))
        ts = tokens(body)
        cur = []
        for t in ts:
            if t == '.':
                # `<=> .` is the empty body; the same dot ends the rule
                if cur:
                    self._add(cur)
                cur = []
            else:
                cur.append(t)
        if cur:
            self.errors.append((' '.join(cur), "no '.' at the end"))

    def _add(self, ts):
        text = ' '.join(ts).replace('( ', '(').replace(' )', ')') + '.'
        try:
            self.rules.append(parse_rule(ts, text))
        except ParseError as e:
            self.errors.append((text, 'syntax: ' + str(e)))
        except Rejected as e:
            self.errors.append((text, str(e)))


# ---------------------------------------------------------------- rewriting

FAIL = 'fail'
_fresh = itertools.count()


def instances(rule, store):
    """Every matching of the heads of `rule` (renamed apart) into `store`."""
    hs = rule.heads()

    def go(k, s):
        if k == len(hs):
            yield s
            return
        for atom in store:
            s2 = match(hs[k], atom, s)
            if s2 is not None:
                yield from go(k + 1, s2)
    yield from go(0, {})


def fire(rule, sigma, state):
    """Apply one instance. Returns the new state, FAIL, or None when it changes nothing."""
    iface, store = state
    if rule.fails:
        return FAIL
    theta = {}
    for a, b in rule.eqs:
        theta = unify(apply_match(a, sigma), apply_match(b, sigma), theta)
        if theta is None:
            return FAIL
    new = set(store)
    if rule.kind == 'def':
        created = {}
        for b in rule.body:
            for v in vars_of(b):
                if v not in sigma and v not in created:
                    created[v] = '$_%d' % next(_fresh)
        new.discard(apply_match(rule.removed, sigma))
        for b in rule.body:
            new.add(apply_match(apply_match(b, created), sigma))
    new = frozenset(subst(a, theta) for a in new)
    iface2 = tuple(subst(t, theta) for t in iface)
    if new == store and iface2 == iface:
        return None
    return (iface2, new)


def closed_refuted(T, atom):
    """An atom of a closed predicate that unifies with no defining head is false."""
    if pred(atom) not in T.closed:
        return False
    for k, r in enumerate(T.rules):
        if r.kind == 'def' and pred(r.removed) == pred(atom):
            if unify(r.rename('~c').removed, atom, {}) is not None:
                return False
    return True


def steps(T, state, skip=None):
    """All single steps from a state."""
    iface, store = state
    for atom in store:
        if closed_refuted(T, atom):
            yield FAIL
    for k, rule in enumerate(T.rules):
        if k == skip:
            continue
        r = rule.rename('~%d' % k)
        for sigma in instances(r, store):
            out = fire(r, sigma, state)
            if out is not None:
                yield out


def nf(T, state, skip=None, limit=2000):
    """Normal form: FAIL or (iface, store). The theory is assumed checked, so
    the first step found is as good as any."""
    for _ in range(limit):
        if state == FAIL:
            return FAIL
        nxt = next(steps(T, state, skip), None)
        if nxt is None:
            return state
        state = nxt
    raise RuntimeError('no normal form within %d steps' % limit)


def nf_random(T, state, rng, limit=2000):
    """A normal form reached by choosing every step at random."""
    for _ in range(limit):
        if state == FAIL:
            return FAIL
        nxt = list(steps(T, state))
        if not nxt:
            return state
        state = rng.choice(nxt)
    raise RuntimeError('no normal form within %d steps' % limit)


def stress(T, rounds, seed=0):
    """Random stores built from instances of the theory's heads: every order of
    steps gives one normal form, and nf (nf A ∪ B) = nf (A ∪ B). Returns the
    number of stores tried, or a counterexample."""
    import random
    rng = random.Random(seed)
    heads = [h for r in T.rules for h in r.heads()]
    syms = sorted(set(x for h in heads for x in _constructors(h)), key=repr)
    vs = ['$a', '$b', '$c']

    def term(d):
        k = rng.random()
        if d == 0 or k < 0.35:
            return rng.choice(vs + [f for f, n in syms if n == 0])
        f, n = rng.choice([x for x in syms if x[1] > 0] or [('f', 1)])
        return (f,) + tuple(term(d - 1) for _ in range(n))

    def atom():
        h = rng.choice(heads)
        return apply_match(h, {v: term(2) for v in set(vars_of(h))})

    for k in range(rounds):
        A = [atom() for _ in range(rng.randint(1, 3))]
        B = [atom() for _ in range(rng.randint(0, 2))]
        iface = tuple(vs)
        want = label_state(nf(T, (iface, frozenset(A + B))))
        for _ in range(3):
            got = label_state(nf_random(T, (iface, frozenset(A + B)), rng))
            if got != want:
                return 'two normal forms of %s' % show_store(A + B)
        first = nf(T, (iface, frozenset(A)))
        if first == FAIL:
            got = FAIL
        else:
            # the bindings of the first part are equations on the interface
            th = {}
            for v, t in zip(iface, first[0]):
                th = unify(v, t, th)
            got = label_state(nf(T, (first[0], first[1] | frozenset(subst(b, th) for b in B))))
        if got != want:
            return 'nf (nf A ∪ B) differs from nf (A ∪ B) for A = %s, B = %s' % (
                show_store(A), show_store(B))
    return rounds


def _constructors(t, top=True):
    """Function symbols with their arities, below the predicate symbol."""
    if isinstance(t, tuple):
        if not top:
            yield (t[0], len(t) - 1)
        for a in t[1:]:
            yield from _constructors(a, False)
    elif not is_var(t) and not top:
        yield (t, 0)


def nf_store(T, atoms):
    vs = tuple(dict.fromkeys(v for a in atoms for v in vars_of(a)))
    return nf(T, (vs, frozenset(atoms)))


# ---------------------------------------------------------------- canonical form

def struct_key(t):
    if isinstance(t, tuple):
        return (2, t[0], len(t), tuple(struct_key(a) for a in t[1:]))
    return (0, t) if is_var(t) else (1, t)


def label_state(state):
    """Rename a state canonically: interface variables by first occurrence in the
    interface, the remaining (store-only) variables by the labelling that makes the
    sorted store least. Brute force."""
    if state == FAIL:
        return FAIL
    iface, store = state
    ren = {}
    for v in (v for t in iface for v in vars_of(t)):
        ren.setdefault(v, '$%d' % len(ren))
    rest = sorted(set(v for a in store for v in vars_of(a)) - set(ren))
    if len(rest) > 8:
        raise RuntimeError('prototype: too many store-only variables')
    best = None
    n = len(ren)
    for perm in itertools.permutations(range(len(rest))):
        r2 = dict(ren)
        for v, k in zip(rest, perm):
            r2[v] = '$e%d' % k
        cand = tuple(sorted((apply_match(a, r2) for a in store), key=struct_key))
        if best is None or [struct_key(a) for a in cand] < [struct_key(a) for a in best[1]]:
            best = (r2, cand)
    r2, cand = best if best else (ren, ())
    return (tuple(apply_match(t, r2) for t in iface), cand)


def core(iface, store):
    """The core of a store: drop atoms as long as a substitution of store-only
    variables maps the store into what is left."""
    fixed = set(v for t in iface for v in vars_of(t))
    store = set(store)
    changed = True
    while changed:
        changed = False
        for a in sorted(store, key=struct_key):
            rest = store - {a}
            if hom(sorted(store, key=struct_key), rest, fixed) is not None:
                store, changed = rest, True
                break
    return frozenset(store)


def hom(src, dst, fixed):
    """A substitution of the non-fixed variables of `src` sending every atom into `dst`."""
    def go(k, s):
        if k == len(src):
            return s
        for d in dst:
            s2 = match(src[k], d, s)
            if s2 is not None:
                out = go(k + 1, s2)
                if out is not None:
                    return out
        return None
    return go(0, {v: v for v in fixed})


class Span:
    def __init__(self, l, r, c=()):
        self.l, self.r, self.c = l, r, frozenset(c)

    def swap(self):
        return Span(self.r, self.l, self.c)

    def __repr__(self):
        c = ' ' + show_store(self.c) if self.c else ''
        return '%s%s -> %s' % (show(self.l), c, show(self.r))


def simplify(T, s):
    out = nf(T, ((s.l, s.r), s.c))
    if out == FAIL:
        return None
    (l, r), c = out
    return Span(l, r, c)


def label_span(s, take_core=True):
    c = core((s.l, s.r), s.c) if take_core else s.c
    (l, r), cs = label_state(((s.l, s.r), c))
    return (l, r, cs)


def canon(T, s, take_core=True):
    """The canonical representative: (bit, labelled span). The labelled span is
    the smaller of the labellings of the span and of its converse; the bit says
    which one was taken, and is 0 for a span that is its own converse."""
    s = simplify(T, s)
    if s is None:
        return None
    a, b = label_span(s, take_core), label_span(s.swap(), take_core)
    ka = (struct_key(a[0]), struct_key(a[1]), [struct_key(x) for x in a[2]])
    kb = (struct_key(b[0]), struct_key(b[1]), [struct_key(x) for x in b[2]])
    if ka <= kb:
        return (0, a)
    return (1, b)


def canon_swap(c):
    """The converse on canonical representatives: flip the bit."""
    bit, (l, r, cs) = c
    selfconv = label_span(Span(r, l, cs)) == (l, r, cs)
    return (bit, (l, r, cs)) if selfconv else (1 - bit, (l, r, cs))


def rename_span(s, tag):
    ren = lambda t: (t + tag if is_var(t) else
                     (t[0],) + tuple(ren(a) for a in t[1:]) if isinstance(t, tuple) else t)
    return Span(ren(s.l), ren(s.r), [ren(a) for a in s.c])


def compose(T, a, b):
    a, b = rename_span(a, 'a%d' % next(_fresh)), rename_span(b, 'b%d' % next(_fresh))
    th = unify(a.r, b.l, {})
    if th is None:
        return None
    return simplify(T, Span(subst(a.l, th), subst(b.r, th),
                            [subst(x, th) for x in a.c | b.c]))


def covers(a, s):
    """Syntactic coverage: an instance of `a` has the sides of `s` and a store inside its store."""
    th = match(a.l, s.l, {})
    th = match(a.r, s.r, th) if th is not None else None
    if th is None:
        return False
    src = sorted(a.c, key=struct_key)

    def go(k, m):
        if k == len(src):
            return True
        return any(go(k + 1, m2) for d in s.c for m2 in [match(src[k], d, m)] if m2 is not None)
    return go(0, th)


def subterms(t, acc):
    acc.add(t)
    if isinstance(t, tuple):
        for a in t[1:]:
            subterms(a, acc)
    return acc


def covers_t(T, a, s):
    """The coverage test of the design note, on simplified spans: an instance of
    `a` has the sides of `s`, its store-only variables go to subterms of `s`, and
    the store of `s` entails its store."""
    th = match(a.l, s.l, {})
    th = match(a.r, s.r, th) if th is not None else None
    if th is None:
        return False
    free = sorted(set(v for x in a.c for v in vars_of(x)) - set(th))
    cands = set()
    for t in [s.l, s.r] + [x for at in s.c for x in at[1:]]:
        subterms(t, cands)
    iface = tuple(dict.fromkeys(vars_of(s.l) + vars_of(s.r) + [v for x in s.c for v in vars_of(x)]))
    for choice in itertools.product(sorted(cands, key=struct_key), repeat=len(free)):
        rho = {**th, **dict(zip(free, choice))}
        out = nf(T, (iface, s.c | frozenset(apply_match(x, rho) for x in a.c)))
        if out != FAIL and out == (iface, s.c):
            return True
    return False


# ---------------------------------------------------------------- the check

def smaller(u, t):
    """`u` is smaller than `t` under every substitution."""
    vu, vt = vars_of(u), vars_of(t)
    return size(u) < size(t) and all(vu.count(v) <= vt.count(v) for v in set(vu))


def levels(T):
    """Strongly connected components of 'the definition of p mentions q', numbered
    so that a predicate's level is above the level of everything it mentions."""
    dep = {}
    for r in T.rules:
        if r.kind == 'def':
            dep.setdefault(pred(r.removed), set()).update(pred(a) for a in r.kept + r.body)
    nodes = set(dep) | set(q for qs in dep.values() for q in qs)
    reach = {p: set(dep.get(p, ())) for p in nodes}
    changed = True
    while changed:
        changed = False
        for p in nodes:
            new = set().union(*[reach[q] for q in reach[p]]) - reach[p] if reach[p] else set()
            if new:
                reach[p] |= new
                changed = True
    same = lambda p, q: p == q or (q in reach[p] and p in reach[q])
    return reach, same


def check(T):
    """Returns the list of reasons the theory is not well formed (empty: accepted).
    W1 to W3 and W6 come first: the normal forms that W4 and W5 compute exist
    only for theories that pass them."""
    errs = ['%s\n      %s' % (t, why) for t, why in T.errors]
    reach, same = levels(T)
    # W2: the defined atom is above its guards and its body
    for r in T.rules:
        if r.kind != 'def':
            continue
        mu = {}
        for a, b in r.eqs:
            mu = unify(a, b, mu)
        rm = subst(r.removed, mu)
        for x in r.kept + r.body:
            xm = subst(x, mu)
            if same(pred(x), pred(r.removed)) and not smaller(xm, rm):
                errs.append('%s\n      %s is not below the defined atom %s' %
                            (r.text, show(xm), show(rm)))
    # W3: a variable the body creates is never bound
    eq_heads = set(pred(h) for r in T.rules if r.eqs for h in r.heads())
    for r in T.rules:
        if r.kind != 'def':
            continue
        hv = set(v for h in r.heads() for v in vars_of(h))
        for b in r.body:
            if set(vars_of(b)) - hv:
                if same(pred(b), pred(r.removed)):
                    errs.append('%s\n      the created variable is in an atom of the '
                                'defined predicate\'s own level' % r.text)
                below = {pred(b)} | reach.get(pred(b), set())
                if below & eq_heads:
                    errs.append('%s\n      a created variable can reach a rule with an '
                                'equation, which could bind it' % r.text)
    # closed predicates: unguarded definitions over closed predicates
    for r in T.rules:
        if r.kind == 'def' and pred(r.removed) in T.closed:
            if r.kept or any(pred(b) not in T.closed for b in r.body):
                errs.append('%s\n      a closed predicate is defined without guards, '
                            'from closed predicates' % r.text)
    if errs:
        return errs
    # W5: every rule that does not fail can fire on a store that can hold
    for k, r in enumerate(T.rules):
        if r.fails:
            continue
        if nf(T, ((), frozenset(r.rename('!').heads())), skip=k) == FAIL:
            errs.append('%s\n      its heads are refuted by the other rules, so it never '
                        'fires on a store that can hold' % r.text)
    # W4: critical pairs
    for i, r1 in enumerate(T.rules):
        if r1.kind != 'def':
            continue
        a = r1.rename('~a')
        for j, r2 in enumerate(T.rules):
            b = r2.rename('~b')
            for h in b.heads():
                if h is b.removed and j < i:
                    continue          # the same overlap, seen from the other rule
                nu = unify(a.removed, h, {})
                if nu is None:
                    continue
                O = frozenset(subst(x, nu) for x in a.heads() + b.heads())
                iface = tuple(dict.fromkeys(v for x in O for v in vars_of(x)))
                st = (iface, O)
                sa = {v: subst(v, nu) for x in a.heads() for v in vars_of(x)}
                sb = {v: subst(v, nu) for x in b.heads() for v in vars_of(x)}
                one, two = fire(a, sa, st), fire(b, sb, st)
                one = st if one is None else one
                two = st if two is None else two
                n1, n2 = label_state(nf(T, one)), label_state(nf(T, two))
                if n1 != n2:
                    errs.append('critical pair on %s\n      %s\n        gives %s\n      %s\n        gives %s'
                                % (show_store(O), r1.text, show_nf(n1), r2.text, show_nf(n2)))
    return errs


def show_nf(n):
    if n == FAIL:
        return 'fail'
    iface, store = n
    return show_store(store) + ('' if all(is_var(t) for t in iface) else
                                '  with ' + ' '.join(show(t) for t in iface))


# ---------------------------------------------------------------- the examples

def theories_in(path):
    """The source of every theory block of a file or notebook."""
    full = os.path.join(ROOT, path)
    if path.endswith('.ipynb'):
        nb = json.load(open(full))
        src = '\n'.join(''.join(c['source']) for c in nb['cells'] if c['cell_type'] == 'code')
    else:
        src = open(full).read()
    out = []
    for m in re.finditer(r'theory\s+\w+\s*\{', src):
        depth, k = 1, m.end()
        while depth:
            depth += {'{': 1, '}': -1}.get(src[k], 0)
            k += 1
        out.append(src[m.start():k])
    return out


EXAMPLES = ['examples/equality_constraints.txt', 'examples/range_sets.txt', 'examples/SK.ipynb',
            'examples/program_synth.ipynb', 'examples/ProofSynth.ipynb', 'examples/Lambda.ipynb',
            'examples/polysimp.ipynb', 'examples/SimpleLam.ipynb', 'examples/SubstConstr.ipynb',
            'examples/Untitled.ipynb']

# The example theories in the language. Where a theory is accepted as written it
# is not listed. Every difference from the file is in the design note.
IN_LANGUAGE = {
    'eq_neq': '''
        constraint eq/2
        constraint neq/2
        constraint nonzero/1
        (eq $x $x) <=> .
        (eq z (s $x)) <=> fail.
        (eq (s $x) z) <=> fail.
        (eq (s $x) (s $y)) <=> (eq $x $y).
        (neq $x $x) <=> fail.
        (neq z (s $x)) <=> .
        (neq (s $x) z) <=> .
        (neq (s $x) (s $y)) <=> (neq $x $y).
        (eq $x $y), (neq $x $y) <=> fail.
        (nonzero z) <=> fail.
        (nonzero (s $x)) <=> .
        (nonzero $x) <=> (eq $x z) | fail.
        (nonzero $x) <=> (neq $x z) | true.
    ''',
    'lamvar_constraints': '''
        constraint neq/2
        (neq $x $x) <=> fail.
    ''',
    'fresh_constraints': '''
        constraint fresh/2
        (fresh $x (var $x)) <=> fail.
        (fresh $x (a $y $z)) <=> (fresh $x $y), (fresh $x $z).
        (fresh $x (lam $y $z)) <=> (fresh $x (var $y)), (fresh $x $z).
    ''',
}


def P(src):
    ts = tokens(src)
    t, i = parse_term(ts, 0)
    assert i == len(ts), src
    return t


def S(src):
    """Parse a span `l {atoms} -> r`."""
    m = re.match(r'\s*(.*?)\s*(?:\{(.*)\})?\s*->\s*(.*)$', src)
    atoms = []
    if m.group(2):
        ts = [t for t in tokens(m.group(2)) if t != ',']
        i = 0
        while i < len(ts):
            t, i = parse_term(ts, i)
            atoms.append(t)
    return Span(P(m.group(1)), P(m.group(3)), atoms)


def expect(what, got, want):
    ok = got == want
    print('  %s %s' % ('ok  ' if ok else 'FAIL', what))
    if not ok:
        print('       got  %s\n       want %s' % (got, want))
    return ok


def run():
    good = True
    print('== Example theories as written ==')
    seen = {}
    for path in EXAMPLES:
        for src in theories_in(path):
            T = Theory(src)
            key = (T.name, re.sub(r'\s+', ' ', src))
            errs = check(T)
            tag = 'accepted' if not errs else 'not accepted'
            print('%-28s %-20s %s' % (path, T.name, tag))
            for e in errs:
                print('    - ' + e)
            seen.setdefault(T.name, []).append((path, not errs))
    print()
    print('== Example theories in the language ==')
    for name, src in IN_LANGUAGE.items():
        errs = check(Theory(src, name))
        good &= expect('%s is accepted' % name, errs, [])
    for name, results in seen.items():
        if name not in IN_LANGUAGE:
            good &= expect('%s is accepted as written (%s)' %
                           (name, ', '.join(p for p, _ in results)), all(ok for _, ok in results), True)

    eqneq = Theory(IN_LANGUAGE['eq_neq'], 'eq_neq')
    print()
    print('== Conformance cases 2 and 4 (stores) ==')
    st = lambda T, s: (lambda o: FAIL if o == FAIL else show_store(o[1]))(nf_store(T, [P(x) for x in s]))
    good &= expect('{(nonzero z)} is refuted', st(eqneq, ['(nonzero z)']), FAIL)
    good &= expect('{(nonzero (s z))} holds', st(eqneq, ['(nonzero (s z))']), '{}')
    good &= expect('{(nonzero $x)} stays', st(eqneq, ['(nonzero $x)']), '{(nonzero $x)}')
    good &= expect('{(nonzero $x), (neq $x z)} keeps the guard only',
                   st(eqneq, ['(nonzero $x)', '(neq $x z)']), '{(neq $x z)}')
    good &= expect('{(nonzero $x), (eq $x z)} is refuted', st(eqneq, ['(nonzero $x)', '(eq $x z)']), FAIL)
    good &= expect('{(neq $x $x)} is refuted', st(eqneq, ['(neq $x $x)']), FAIL)
    good &= expect('{(eq $x $y), (neq $x $y)} is refuted', st(eqneq, ['(eq $x $y)', '(neq $x $y)']), FAIL)
    good &= expect('{(neq (s $x) z)} holds', st(eqneq, ['(neq (s $x) z)']), '{}')
    good &= expect('{(eq (s (s $x)) (s (s $y)))} is {(eq $x $y)}',
                   st(eqneq, ['(eq (s (s $x)) (s (s $y)))']), '{(eq $x $y)}')
    pin = Theory('constraint pin/1\n (pin $x) <=> $x = z.', 'pin')
    good &= expect('pin is accepted', check(pin), [])
    good &= expect('(pair $x $y) {(pin $x)} -> $y is (pair z $y) -> $y',
                   repr(simplify(pin, S('(pair $x $y) {(pin $x)} -> $y'))), '(pair z $y) -> $y')
    pin2 = Theory('constraint pin/1\n (pin $x) <=> $x = z, (pin z).', 'pin, written back')
    good &= expect('the written-back pin is accepted', check(pin2), [])
    good &= expect('written-back pin keeps (pin z)',
                   repr(simplify(pin2, S('(pair $x $y) {(pin $x)} -> $y'))), '(pair z $y) {(pin z)} -> $y')

    print()
    print('== Lambda: guarded definitions ==')
    lam = Theory(theories_in('examples/Lambda.ipynb')[0])
    good &= expect('{(norm (app $x $z)), (var $x)} is {(norm $z), (var $x)}',
                   st(lam, ['(norm (app $x $z))', '(var $x)']), '{(norm $z), (var $x)}')
    good &= expect('{(norm (app $x (app (lam $a $b) $c))), (var $x)} is refuted',
                   st(lam, ['(norm (app $x (app (lam $a $b) $c)))', '(var $x)']), FAIL)
    good &= expect('{(norm (lam $x (app $x $y))), (var $x)} is {(norm $y), (var $x)}',
                   st(lam, ['(norm (lam $x (app $x $y)))', '(var $x)']), '{(norm $y), (var $x)}')

    print()
    print('== Theories the check must reject ==')
    bad = {
        'redesign notes, counterexample 1 (merge)':
            '(p (f $x)) <=> (q $x).\n (q $x), (r (g $x)) <=> (t $x).\n (q $x), (t $x) <=> fail.',
        'redesign notes, counterexample 2 (pin and bad)':
            '(pin $x) <=> $x = z.\n (pin z), bad <=> fail.',
        'a guard that a definition decides':
            '(p z) <=> .\n (p (f $x)) <=> fail.\n (p $x), (q $x) <=> (q $x).',
        'L10, first counterexample (link and bad)':
            '(link $x $y) <=> .\n (link $x $y), bad <=> fail.',
        'L10, second counterexample (link and k)':
            '(link $x $y) <=> .\n (link (f $x) $y) <=> (k $x $y).',
        'symmetry as a simplification':
            '(neq $x $y), (neq $y $x) <=> (neq $x $y).',
        'a rule that says nothing':
            '(neq $x $y), (neq $x $y) <=> (neq $x $y).',
        'a propagation':
            '(lt $x $y) ==> (leq $x $y).',
        'a body that is not below its head':
            '(r $x) <=> (t $x).\n (t $x) <=> (r $x).',
        'guards as written in equality_constraints.txt':
            '(eq $x $x) <=> .\n (neq (s $x) z) <=> .\n (nonzero $x) <=> (eq $x z) | fail.\n'
            ' (nonzero $x) <=> (neq $x z) | true.',
        'a created variable that an equation can bind':
            '(a (f $x)) <=> (a $x), (b $x).\n (b $x) <=> (c $y $x).\n (c $y $x) <=> $x = (f $y), (d $y).',
        'a created variable in an equation':
            '(isf $x) <=> $x = (f $y).',
    }
    for what, src in bad.items():
        errs = check(Theory(src))
        good &= expect('rejected: ' + what, bool(errs), True)
        for e in errs[:2]:
            print('       ' + e.replace('\n', '\n       '))
    ok_theories = {
        'L10 first counterexample, completed with `bad <=> fail.`':
            '(link $x $y) <=> .\n (link $x $y), bad <=> fail.\n bad <=> fail.',
        'a body below its head by level':
            '(r $x) <=> (t $x).',
        'a created variable that nothing can bind':
            '(even $x) <=> (double $h $x).\n (double z z) <=> .\n (double (s $h) (s (s $x))) <=> (double $h $x).',
        'a functional dependency':
            '(val $k $v), (val $k $w) <=> $v = $w, (val $k $v).',
    }
    for what, src in ok_theories.items():
        good &= expect('accepted: ' + what, check(Theory(src)), [])

    print()
    print('== Stores along a recursion ==')
    link = Theory('(link $x $y) <=> .')
    r = S('$x {(link $x $y)} -> $y')
    rr = compose(link, r, r)
    good &= expect('with (link $x $y) <=> . the chain r ; r is $x -> $y',
                   canon(link, rr), canon(link, S('$x -> $y')))
    noc = Theory(theories_in('examples/SK.ipynb')[0])
    piled = S('(a $p $q) {(no_c $u), (no_c $v), (no_c $w), (no_c $p)} -> $q')
    good &= expect('the core drops three dangling atoms beside one on the span',
                   canon(noc, piled), canon(noc, S('(a $p $q) {(no_c $p)} -> $q')))

    print()
    print('== Canonical representatives and the converse ==')
    samples = ['(f $v $w) -> (f $w $v)', '(f $v $w) -> (g $w)', '$x {(no_c $x), (no_c $y)} -> (a $x k)',
               '(a $p $q) {(no_c (a $p $q))} -> $q', '(g $w) -> (f $v $w)', '$x -> $x']
    for src in samples:
        s = S(src)
        good &= expect('canon (swap s) = swap (canon s) for %s' % src,
                       canon(noc, s.swap()), canon_swap(canon(noc, s)))
    a, b = S('(f $v $w) -> (f $w $v)'), S('(f $w $v) -> (f $v $w)')
    good &= expect('(f $v $w) -> (f $w $v) is its own converse up to renaming',
                   label_span(a), label_span(b))

    print()
    print('== Composition, simplification and the core ==')
    x, y, z = S('$u {(no_c $u)} -> (a $u $t)'), S('(a $u $t) {(no_c $t)} -> $t'), S('(a k $m) -> $m')
    lhs = compose(noc, compose(noc, x, y), z)
    rhs = compose(noc, x, compose(noc, y, z))
    good &= expect('(x ; y) ; z = x ; (y ; z) with no core taken in between',
                   canon(noc, lhs, False), canon(noc, rhs, False))
    s1 = S('$l {(no_c $y), (no_c $w)} -> $w')
    s2 = S('$l {(no_c $w)} -> $w')
    good &= expect('s1 and its core s2 have one canonical representative', canon(noc, s1), canon(noc, s2))
    k = S('k -> k')
    c1, c2 = compose(noc, s1, k), compose(noc, s2, k)
    print('       s1 ; @k = %s      s2 ; @k = %s' % (c1, c2))
    good &= expect('but s1 ; @k and s2 ; @k are not equivalent as written',
                   covers(c1, c2) and covers(c2, c1), False)
    good &= expect('s2 ; @k covers s1 ; @k', covers(c2, c1), True)
    good &= expect('without the core, canonical representatives compose exactly',
                   canon(noc, s1, False) == canon(noc, s2, False), False)

    cx3 = Theory('(p z) <=> .\n (p (f $x)) <=> fail.')
    good &= expect('redesign notes, counterexample 3 is a well-formed theory', check(cx3), [])
    t1, t2 = S('$w {(p z)} -> $w'), S('$w {(p z), (p $y)} -> $w')
    good &= expect('its two spans are equivalent as written', covers(t1, t2) and covers(t2, t1), True)
    u1, u2 = simplify(cx3, t1), simplify(cx3, t2)
    print('       they simplify to %s and %s' % (u1, u2))
    good &= expect('and their simplifications are not', covers(u1, u2) and covers(u2, u1), False)

    print()
    print('== Coverage ==')
    good &= expect('($w {(no_c $w)} -> $w) covers (k -> k) by the test',
                   covers_t(noc, S('$w {(no_c $w)} -> $w'), S('k -> k')), True)
    good &= expect('and not as written', covers(S('$w {(no_c $w)} -> $w'), S('k -> k')), False)
    wit = Theory('(A (g k)) <=> .')
    c1, c2, c3 = S('$u {(A $y)} -> $u'), S('$u {(A (g $u))} -> $u'), S('k -> k')
    good &= expect('the test is not transitive: first covers second', covers_t(wit, c1, c2), True)
    good &= expect('second covers third', covers_t(wit, c2, c3), True)
    good &= expect('first does not pass against third', covers_t(wit, c1, c3), False)
    good &= expect('although (A (g k)) holds', nf_store(wit, [P('(A (g k))')])[1], frozenset())

    print()
    print('== A created variable that an equation binds ==')
    loop = Theory('(a (f $x)) <=> (a $x), (b $x).\n (b $x) <=> (c $y $x).\n'
                  ' (c $y $x) <=> $x = (f $y), (d $y).')
    good &= expect('W3 is the only condition it fails',
                   [e for e in check(loop) if 'created variable' not in e], [])
    try:
        nf(loop, (('$v',), frozenset([P('(a $v)'), P('(b $v)')])), limit=150)
        ran = 'halted'
    except RuntimeError:
        ran = 'no normal form in 150 steps'
    good &= expect('{(a $v), (b $v)} keeps firing', ran, 'no normal form in 150 steps')

    print()
    print('== The correspondence problem as a theory ==')
    pcp = Theory("""
        (top e e) <=> .
        (bot e e) <=> .
        (top (t1 $y) (a $w)) <=> (top $y $w).
        (bot (t1 $y) (a (b $w))) <=> (bot $y $w).
        (top (t2 $y) (b (b $w))) <=> (top $y $w).
        (bot (t2 $y) (b $w)) <=> (bot $y $w).
        (ne (t1 $y)) <=> .
        (ne (t2 $y)) <=> .
    """, 'pcp')
    good &= expect('it is well formed', check(pcp), [])
    sol, word = '(t1 (t2 e))', '(a (b (b e)))'
    good &= expect('a solution makes the store hold',
                   st(pcp, ['(top %s %s)' % (sol, word), '(bot %s %s)' % (sol, word), '(ne %s)' % sol]), '{}')
    good &= expect('and without it the store waits',
                   st(pcp, ['(top $y $w)', '(bot $y $w)', '(ne $y)']), '{(bot $y $w), (ne $y), (top $y $w)}')

    print()
    print('== Extending a theory ==')
    small = Theory(theories_in('examples/range_sets.txt')[0])
    big = Theory(theories_in('examples/range_sets.txt')[0].rstrip().rstrip('}') +
                 '(lt $x $x) <=> fail.\n (lt $x $y), (lt $y $x) <=> fail.\n}')
    good &= expect('ranges with the two refutation rules for lt is accepted', check(big), [])
    for src in ['(between (s $x) (range (open $x) (closed $y)))', '(lt (s $a) (s $b))',
                '(leq (s $a) (s (s $a)))', '(between $x (range (open $y) (open $x)))']:
        c = [P(src), P('(lt $b $a)')]
        one = nf_store(small, c)
        one = FAIL if one == FAIL else nf(big, one)
        good &= expect('nf_big (nf_small c) = nf_big c for c = %s' % show_store(c),
                       label_state(one), label_state(nf_store(big, c)))

    print()
    print('== Every order of steps gives one normal form (random stores) ==')
    accepted = [Theory(IN_LANGUAGE[n], n) for n in IN_LANGUAGE] + [small, big, noc, lam, pin, pin2,
        Theory(theories_in('examples/ProofSynth.ipynb')[0]),
        Theory(theories_in('examples/program_synth.ipynb')[0])]
    for T in accepted:
        good &= expect('%s: 400 stores' % T.name, stress(T, 400), 400)

    print()
    print('== Closed predicates ==')
    nat = Theory('constraint nat/1 closed\n (nat z) <=> .\n (nat (s $x)) <=> (nat $x).')
    good &= expect('a closed nat is accepted', check(nat), [])
    good &= expect('{(nat (s (s z)))} holds', st(nat, ['(nat (s (s z)))']), '{}')
    good &= expect('{(nat (s (pair a b)))} is refuted', st(nat, ['(nat (s (pair a b)))']), FAIL)
    good &= expect('{(nat (s $x))} waits as {(nat $x)}', st(nat, ['(nat (s $x))']), '{(nat $x)}')

    print()
    print('ALL CHECKS PASS' if good else 'SOME CHECKS FAILED')
    return 0 if good else 1


if __name__ == '__main__':
    sys.exit(run())
