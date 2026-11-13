#!/usr/bin/env python3
"""Prototype of the constraint rule language of lean/CONSTRAINT_LANGUAGE.md.

It is a model of the design, not an engine: every search is brute force.

  * `Theory`       reads a `theory { ... }` block and classifies every rule: a
                   definition `K \\ r <=> eqs, B`, a restriction `K ==> eqs`, an
                   inert rule, a propagation, or a rule that removes several heads.
                   No rule is rejected.
  * `detect`       classifies a theory as detected confluent or not, with the
                   reasons. It rejects nothing.
  * `nf`           the exact path: the normal form of a store under a detected
                   theory (guards hold by entailment).
  * `fallback`     the path of every other theory: refutation and forced
                   equations on the closure, the store kept as written.
  * `canon`        the canonical representative of a span: simplification by
                   the path of its theory, core, canonical labelling, orientation bit.

Run it with no argument. It classifies every example theory of the repository
as written, and checks the claims of the design note.
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
    kind 'inert':    on a set of atoms the heads are the body; it says nothing
    kind 'prop':     no head removed, atoms added (a propagation)
    kind 'multi':    two or more heads removed

    `all_heads`, `eqs`, `atoms` and `fails` are the rule as written; the closure
    of the fallback path reads them forwards for every kind.
    """

    def __init__(self, text):
        self.text = text
        self.kind = None
        self.kept, self.removed, self.eqs, self.body, self.fails = [], None, [], [], False
        self.all_heads, self.atoms, self.loose_eq = [], [], False

    def heads(self):
        return self.kept + ([self.removed] if self.removed is not None else [])

    def rename(self, tag):
        r = Rule(self.text)
        ren = lambda t: (t + tag if is_var(t) else
                         (t[0],) + tuple(ren(a) for a in t[1:]) if isinstance(t, tuple) else t)
        r.kind, r.fails, r.loose_eq = self.kind, self.fails, self.loose_eq
        r.all_heads = [ren(a) for a in self.all_heads]
        r.atoms = [ren(a) for a in self.atoms]
        r.kept = [ren(a) for a in self.kept]
        r.removed = None if self.removed is None else ren(self.removed)
        r.eqs = [(ren(a), ren(b)) for a, b in self.eqs]
        r.body = [ren(a) for a in self.body]
        return r


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
    return classify(heads, (kept_explicit or []) + guard, eqs, atoms, fails, text)


def classify(heads, guards, eqs, atoms, fails, text):
    """Section 3.3. Every rule gets a kind; none is rejected."""
    r = Rule(text)
    hs = list(dict.fromkeys(heads))
    r.all_heads, r.eqs, r.atoms, r.fails = hs, eqs, list(dict.fromkeys(atoms)), fails
    head_vars = set(v for h in hs for v in vars_of(h))
    r.loose_eq = any(not set(vars_of(a) + vars_of(b)) <= head_vars for a, b in eqs)
    mu = {}
    for a, b in eqs:
        mu = unify(a, b, mu) if mu is not None else None
    if fails or mu is None:
        r.fails = True
        written = [h for h in hs if h not in guards]
        if guards and len(written) == 1:
            # `H <=> G | fail`: under the guards G, the atom H is false
            r.kind, r.kept, r.removed = 'def', [g for g in hs if g in guards], written[0]
        else:
            r.kind, r.kept = 'restrict', hs
        return r
    hmu = [subst(h, mu) for h in hs]
    bmu = set(subst(b, mu) for b in atoms)
    kept = [h for h, m in zip(hs, hmu) if m in bmu]
    removed = [h for h, m in zip(hs, hmu) if m not in bmu]
    added = [b for b in dict.fromkeys(atoms) if subst(b, mu) not in hmu]
    if not removed:
        r.kept = hs
        if added:
            r.kind, r.body = 'prop', added
        elif all(subst(a, {}) == subst(b, {}) for a, b in eqs):
            r.kind = 'inert'
        else:
            r.kind = 'restrict'
        return r
    if len(removed) > 1:
        r.kind, r.kept, r.body = 'multi', kept, added
        return r
    r.kind, r.kept, r.removed, r.body = 'def', kept, removed[0], added
    return r


class Theory:
    def __init__(self, src, name='?'):
        self.name, self.rules, self.errors, self.preds, self.closed = name, [], [], {}, set()
        self._levels, self._entails, self._detected = None, {}, None
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

    def below(self, a, r):
        """The atom `a` is below the atom `r`: its predicate is strictly below, or
        it is at the same level and smaller under every substitution."""
        if self._levels is None:
            self._levels = levels(self)
        reach, same = self._levels
        pa, pr = pred(a), pred(r)
        if pa not in reach or pr not in reach:
            return False
        if same(pa, pr):
            return smaller(a, r)
        return pa in reach[pr]

    def detected(self):
        if self._detected is None:
            self._detected = not detect(self).reasons
        return self._detected


# ---------------------------------------------------------------- rewriting

FAIL = 'fail'
_fresh = itertools.count()


def instances(T, rule, store):
    """Every way the heads of `rule` (renamed apart) apply to `store`.

    A restriction needs all its heads in the store. A definition needs its
    removed atom in the store. When that atom binds every variable of the
    guards, a guard holds when the part of the store below the removed atom
    entails it. Otherwise the guards are matched against atoms of the store,
    like the heads of a restriction."""
    by_entailment = rule.kind == 'def' and \
        set(v for g in rule.kept for v in vars_of(g)) <= set(vars_of(rule.removed))
    if not by_entailment:
        hs = ([rule.removed] if rule.kind == 'def' else []) + rule.kept

        def go(k, s):
            if k == len(hs):
                yield s
                return
            for atom in store:
                s2 = match(hs[k], atom, s)
                if s2 is not None:
                    yield from go(k + 1, s2)
        yield from go(0, {})
        return
    for atom in store:
        s = match(rule.removed, atom, {})
        if s is not None and all(entails(T, store, atom, apply_match(g, s)) for g in rule.kept):
            yield s


def entails(T, store, r, g):
    """The part of `store` below the atom `r` entails the atom `g`: adding `g`
    to it changes neither its normal form nor any variable."""
    if g in store:
        return True
    lower = frozenset(a for a in store if T.below(a, r))
    key = (lower, g)
    if key not in T._entails:
        iface = tuple(sorted(set(v for a in lower | {g} for v in vars_of(a))))
        n0 = nf(T, (iface, lower))
        n1 = nf(T, (iface, lower | {g}))
        T._entails[key] = n0 != FAIL and label_state(n1) == label_state(n0)
    return T._entails[key]


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
        if k == skip or rule.kind not in ('def', 'restrict'):
            continue
        r = rule.rename('~%d' % k)
        for sigma in instances(T, r, store):
            out = fire(r, sigma, state)
            if out is not None:
                yield out


def nf(T, state, skip=None, limit=2000):
    """Normal form on the exact path: FAIL or (iface, store). For a detected
    theory the first step found is as good as any."""
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


def random_atoms(T, rng):
    """A generator of atoms: instances of the theory's heads over a few variables."""
    heads = [h for r in T.rules for h in r.all_heads]
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
    return tuple(vs), atom


def stress(T, rounds, seed=0):
    """The exact path on random stores: every order of steps gives one normal
    form, and nf (nf A ∪ B) = nf (A ∪ B). Returns the number of stores tried,
    or a counterexample."""
    import random
    rng = random.Random(seed)
    iface, atom = random_atoms(T, rng)
    for k in range(rounds):
        A = [atom() for _ in range(rng.randint(1, 3))]
        B = [atom() for _ in range(rng.randint(0, 2))]
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


def stress_fallback(T, rounds, seed=0, exact=False):
    """The fallback path on random stores: its result is the same up to a
    renaming of the variables, simplifying twice is simplifying once, and (when
    `exact`, for a detected theory, where the normal form decides) it refutes
    only what has no instance and keeps every instance of what it keeps."""
    import random
    rng = random.Random(seed)
    iface, atom = random_atoms(T, rng)
    ren = {'$a': '$c', '$b': '$a', '$c': '$b'}
    for k in range(rounds):
        A = frozenset(atom() for _ in range(rng.randint(1, 4)))
        one = fallback(T, (iface, A))
        two = fallback(T, (tuple(ren[v] for v in iface), frozenset(apply_match(x, ren) for x in A)))
        if label_state(one) != label_state(two):
            return 'renaming changes the result on %s' % show_store(A)
        if one != FAIL and fallback(T, one) != one:
            return 'not idempotent on %s' % show_store(A)
        if exact:
            want = nf(T, (iface, A))
            if one == FAIL and want != FAIL:
                return 'refutes %s, which has an instance' % show_store(A)
            if one != FAIL and label_state(nf(T, one)) != label_state(want):
                return 'changes the meaning of %s' % show_store(A)
    return rounds


def fuzz_guarded(count, seed=0):
    """Random theories of guarded definitions over three levels of predicates.
    For every one that is detected confluent, random stores must have one
    normal form. Returns (theories detected, counterexamples)."""
    import random
    rng = random.Random(seed)
    pats = ['$x', 'z', '(s $x)', '(f $x)', '(s (s $x))', '(s z)']

    def rule():
        lv = rng.randint(0, 2)
        hp = rng.choice(pats)
        hasx = '$x' in hp
        lower = lambda: '(p%d %s)' % (rng.randint(0, lv - 1) if lv else 0,
                                      rng.choice(['$x', '(s $x)', 'z'] if hasx else ['z', '(s z)']))
        guards = [lower() for _ in range(rng.choice([0, 0, 1, 1, 2]))] if lv else []
        k = rng.random()
        body = 'fail' if k < 0.3 else 'true'
        if k >= 0.55:
            bs = []
            for _ in range(rng.randint(1, 2)):
                if lv and rng.random() < 0.6:
                    bs.append(lower())
                elif hasx and hp != '$x':
                    bs.append('(p%d $x)' % lv)
                elif lv:
                    bs.append(lower())
            if bs:
                body = ', '.join(bs)
        return '(p%d %s) <=> %s%s.' % (lv, hp, ', '.join(guards) + ' | ' if guards else '', body)

    found, wrong = 0, []
    for i in range(count):
        src = '\n'.join(rule() for _ in range(rng.randint(2, 6)))
        T = Theory(src)
        if detect(T).reasons:
            continue
        found += 1
        if stress(T, 40, seed=i) != 40:
            wrong.append(src)
    return found, wrong


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
    """By the path of the theory: the normal form when it is detected confluent,
    the fallback otherwise."""
    out = (nf if T.detected() else fallback)(T, ((s.l, s.r), s.c))
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


def not_larger(u, t):
    """`u` is at most the size of `t` under every substitution."""
    vu, vt = vars_of(u), vars_of(t)
    return size(u) <= size(t) and all(vu.count(v) <= vt.count(v) for v in set(vu))


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


class Detection:
    """What reading a theory reports. `reasons` empty: detected confluent."""

    def __init__(self):
        self.reasons, self.notes = [], []


def detect(T, created=True):
    """Classify a theory. Nothing is rejected: a theory with reasons runs on
    the fallback path. D1 to D3 and D5 come first, because the normal forms
    that D4 compares exist only for theories that pass them. With
    `created=False` a body variable that no head binds is itself a reason
    (the state of the Lean before the lemma of section 6 is proved)."""
    d = Detection()
    errs = d.reasons
    for r in T.rules:
        if r.kind == 'inert':
            d.notes.append('%s\n      says nothing on a set of atoms; it is never fired' % r.text)
        if not bounded(r):
            d.notes.append('%s\n      is not used by the fallback path: its body is larger '
                           'than its heads' % r.text)
    # D1: every rule that says something defines one atom or restricts
    for r in T.rules:
        if r.kind == 'prop':
            errs.append('%s\n      removes no head and adds atoms (a propagation)' % r.text)
        if r.kind == 'multi':
            errs.append('%s\n      removes more than one head' % r.text)
        if r.loose_eq:
            errs.append('%s\n      an equation mentions a variable that no head binds' % r.text)
    reach, same = levels(T)
    # D2: the defined atom is above its guards and its body
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
    # D3: a variable the body creates is never bound
    eq_heads = set(pred(h) for r in T.rules if r.eqs for h in r.heads())
    for r in T.rules:
        if r.kind != 'def':
            continue
        hv = set(v for h in r.heads() for v in vars_of(h))
        for b in r.body:
            if set(vars_of(b)) - hv:
                if not created:
                    errs.append('%s\n      the body has a variable that no head binds' % r.text)
                if same(pred(b), pred(r.removed)):
                    errs.append('%s\n      the created variable is in an atom of the '
                                'defined predicate\'s own level' % r.text)
                below = {pred(b)} | reach.get(pred(b), set())
                if below & eq_heads:
                    errs.append('%s\n      a created variable can reach a rule with an '
                                'equation, which could bind it' % r.text)
    # D5: closed predicates are unguarded definitions over closed predicates
    for r in T.rules:
        if r.kind == 'def' and pred(r.removed) in T.closed:
            if r.kept or any(pred(b) not in T.closed for b in r.body):
                errs.append('%s\n      a closed predicate is defined without guards, '
                            'from closed predicates' % r.text)
    if errs:
        return d
    # D4: critical pairs
    for i, r1 in enumerate(T.rules):
        if r1.kind != 'def':
            continue
        a = r1.rename('~a')
        for j, r2 in enumerate(T.rules):
            if r2.kind not in ('def', 'restrict'):
                continue
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
                    errs.append('two results on %s\n      %s\n        gives %s\n      %s\n        gives %s'
                                % (show_store(O), r1.text, show_nf(n1), r2.text, show_nf(n2)))
    if errs:
        return d
    # a note, not a reason: a rule whose heads the other rules refute
    for k, r in enumerate(T.rules):
        if r.fails or r.kind == 'inert':
            continue
        if nf(T, ((), frozenset(r.rename('!').heads())), skip=k) == FAIL:
            d.notes.append('%s\n      its heads are refuted by the other rules, so it never '
                           'fires on a store that can hold' % r.text)
    return d


# ---------------------------------------------------------------- the fallback path

def bounded(rule):
    """Once its equations hold, no body atom is larger than every head: each is
    at most the size of some head under every substitution. The closure fires
    only such rules, so it stays inside the atoms of the store's own size."""
    if rule.loose_eq:
        return False
    mu = {}
    for a, b in rule.eqs:
        mu = unify(a, b, mu) if mu is not None else None
    if rule.fails or mu is None:
        return True
    hm = [subst(h, mu) for h in rule.all_heads]
    return all(any(not_larger(subst(b, mu), h) for h in hm) for b in rule.atoms)


def closure(T, store):
    """The closure of a store under the bounded rules read forwards (heads imply
    body). Nothing is removed, so the result does not depend on any order.
    Returns FAIL, or the closure with the bindings its equations force."""
    cl, binds = set(store), {}
    while True:
        new = set()
        for atom in cl:
            if closed_refuted(T, atom):
                return FAIL
        for k, rule in enumerate(T.rules):
            if not bounded(rule):
                continue
            r = rule.rename('~%d' % k)

            def go(i, s):
                if i == len(r.all_heads):
                    yield s
                    return
                for atom in cl:
                    s2 = match(r.all_heads[i], atom, s)
                    if s2 is not None:
                        yield from go(i + 1, s2)
            for sigma in go(0, {}):
                if r.fails:
                    return FAIL
                th = {}
                for a, b in r.eqs:
                    th = unify(apply_match(a, sigma), apply_match(b, sigma), th)
                    if th is None:
                        return FAIL
                if th:
                    for v, t in th.items():
                        binds = unify(v, t, binds)
                        if binds is None:
                            return FAIL
                    continue
                for b in r.atoms:
                    x = apply_match(b, sigma)
                    if x not in cl:
                        new.add(x)
        if not new:
            return cl, binds
        cl |= new


def fallback(T, state):
    """Simplification on the fallback path: refute on the closure, instantiate
    by every equation the closure forces, keep the store as written."""
    while True:
        if state == FAIL:
            return FAIL
        iface, store = state
        out = closure(T, store)
        if out == FAIL:
            return FAIL
        _, binds = out
        if not binds:
            return state
        state = (tuple(subst(t, binds) for t in iface), frozenset(subst(a, binds) for a in store))


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

# What reading each example theory as written must report.
DETECTED = {'eq_neq': True, 'ranges': True, 'treecalc_constraints': True, 'depth_constraints': True,
            'bound_vars': True, 'fresh_constraints': True, 'lamvar_constraints': False}


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
    print('== Example theories as written: nothing is rejected ==')
    seen = {}
    for path in EXAMPLES:
        for src in theories_in(path):
            T = Theory(src)
            d = detect(T)
            print('%-34s %-22s %s' % (path, T.name, 'detected confluent' if not d.reasons
                                      else 'not detected (fallback path)'))
            for text, why in T.errors:
                print('    does not parse: %s   (%s)' % (text.strip(), why))
            for e in d.reasons:
                print('    because ' + e)
            for e in d.notes:
                print('    note    ' + e)
            seen.setdefault(T.name, []).append((path, not d.reasons))
    for name, results in seen.items():
        good &= expect('%s is %s (%s)' % (name, 'detected confluent' if DETECTED[name] else 'not detected',
                                          ', '.join(p for p, _ in results)),
                       [ok for _, ok in results], [DETECTED[name]] * len(results))

    eqneq = Theory(theories_in('examples/equality_constraints.txt')[0])
    print()
    print('== Conformance cases 2 and 4 (stores), on equality_constraints.txt as written ==')
    st = lambda T, s: (lambda o: FAIL if o == FAIL else show_store(o[1]))(nf_store(T, [P(x) for x in s]))
    good &= expect('{(nonzero z)} is refuted', st(eqneq, ['(nonzero z)']), FAIL)
    good &= expect('{(nonzero (s z))} holds', st(eqneq, ['(nonzero (s z))']), '{}')
    good &= expect('{(nonzero (s $x))} holds', st(eqneq, ['(nonzero (s $x))']), '{}')
    good &= expect('{(nonzero $x)} stays', st(eqneq, ['(nonzero $x)']), '{(nonzero $x)}')
    good &= expect('{(nonzero $x), (neq $x z)} keeps the guard only',
                   st(eqneq, ['(nonzero $x)', '(neq $x z)']), '{(neq $x z)}')
    good &= expect('{(nonzero $x), (neq (s $x) (s z))}: the guard holds by entailment',
                   st(eqneq, ['(nonzero $x)', '(neq (s $x) (s z))']), '{(neq $x z)}')
    good &= expect('{(nonzero $x), (eq $x z)} is refuted', st(eqneq, ['(nonzero $x)', '(eq $x z)']), FAIL)
    good &= expect('{(neq $x $x)} is refuted', st(eqneq, ['(neq $x $x)']), FAIL)
    good &= expect('{(eq $x $y), (neq $x $y)} is refuted', st(eqneq, ['(eq $x $y)', '(neq $x $y)']), FAIL)
    good &= expect('{(neq (s $x) z)} holds', st(eqneq, ['(neq (s $x) z)']), '{}')
    good &= expect('{(eq (s (s $x)) (s (s $y)))} is {(eq $x $y)}',
                   st(eqneq, ['(eq (s (s $x)) (s (s $y)))']), '{(eq $x $y)}')
    pin = Theory('constraint pin/1\n (pin $x) <=> $x = z.', 'pin')
    good &= expect('pin is detected confluent', detect(pin).reasons, [])
    good &= expect('(pair $x $y) {(pin $x)} -> $y is (pair z $y) -> $y',
                   repr(simplify(pin, S('(pair $x $y) {(pin $x)} -> $y'))), '(pair z $y) -> $y')
    pin2 = Theory('constraint pin/1\n (pin $x) <=> $x = z, (pin z).', 'pin, written back')
    good &= expect('the written-back pin is detected confluent', detect(pin2).reasons, [])
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
    print('== Theories that are not detected confluent, with the reason shown ==')
    undetected = {
        'redesign notes, counterexample 1 (merge)':
            '(p (f $x)) <=> (q $x).\n (q $x), (r (g $x)) <=> (t $x).\n (q $x), (t $x) <=> fail.',
        'redesign notes, counterexample 2 (pin and bad)':
            '(pin $x) <=> $x = z.\n (pin z), bad <=> fail.',
        'two definitions that disagree under a guard':
            '(p z) <=> .\n (p (f $x)) <=> fail.\n (p $x), (q $x) <=> (q $x).',
        'L10, first counterexample (link and bad)':
            '(link $x $y) <=> .\n (link $x $y), bad <=> fail.',
        'L10, second counterexample (link and k)':
            '(link $x $y) <=> .\n (link (f $x) $y) <=> (k $x $y).',
        'symmetry as a simplification':
            '(neq $x $x) <=> fail.\n (neq $x $y), (neq $y $x) <=> (neq $x $y).',
        'a propagation':
            '(lt $x $y) ==> (leq $x $y).\n (leq $x $y), (lt $y $x) <=> fail.',
        'a body that is not below its head':
            '(r $x) <=> (t $x).\n (t $x) <=> (r $x).',
        'a created variable that an equation can bind':
            '(a (f $x)) <=> (a $x), (b $x).\n (b $x) <=> (c $y $x).\n (c $y $x) <=> $x = (f $y), (d $y).',
        'a created variable in an equation':
            '(isf $x) <=> $x = (f $y).',
    }
    for what, src in undetected.items():
        d = detect(Theory(src))
        good &= expect('not detected: ' + what, bool(d.reasons), True)
        for e in d.reasons[:2]:
            print('       ' + e.replace('\n', '\n       '))
    detected = {
        'L10 first counterexample, completed with `bad <=> fail.`':
            '(link $x $y) <=> .\n (link $x $y), bad <=> fail.\n bad <=> fail.',
        'a body below its head by level':
            '(r $x) <=> (t $x).',
        'a created variable that nothing can bind':
            '(even $x) <=> (double $h $x).\n (double z z) <=> .\n (double (s $h) (s (s $x))) <=> (double $h $x).',
        'a functional dependency':
            '(val $k $v), (val $k $w) <=> $v = $w, (val $k $v).',
        'a rule that says nothing, beside one that does':
            '(neq $x $x) <=> fail.\n (neq $x $y), (neq $x $y) <=> (neq $x $y).',
        'a guard whose support is rewritten by a guarded rule':
            '(g (s $x)) <=> (h $x).\n (r $x) <=> (g (s $x)) | (t $x).\n (h $x) <=> w | m.',
    }
    for what, src in detected.items():
        good &= expect('detected: ' + what, detect(Theory(src)).reasons, [])
    even = Theory(detected['a created variable that nothing can bind'])
    good &= expect('until the lemma of section 6 is proved, a created variable is a reason',
                   bool(detect(even, created=False).reasons), True)
    sup = Theory(detected['a guard whose support is rewritten by a guarded rule'])
    good &= expect('{(r a), (h a), w} has one normal form',
                   st(sup, ['(r a)', '(h a)', 'w']), '{(t a), m, w}')
    good &= expect('a guard whose support is rewritten: 400 stores', stress(sup, 400), 400)

    print()
    print('== The fallback path ==')
    lamvar = Theory(theories_in('examples/SimpleLam.ipynb')[0])
    fb = lambda T, s: (lambda o: FAIL if o == FAIL else show_store(o[1]))(
        fallback(T, (tuple(dict.fromkeys(v for x in s for v in vars_of(P(x)))), frozenset(P(x) for x in s))))
    good &= expect('lamvar_constraints: {(neq $x $x)} is refuted', fb(lamvar, ['(neq $x $x)']), FAIL)
    good &= expect('lamvar_constraints: {(neq a b), (neq b a)} is kept as written',
                   fb(lamvar, ['(neq a b)', '(neq b a)']), '{(neq a b), (neq b a)}')
    linkbad = Theory(undetected['L10, first counterexample (link and bad)'])
    good &= expect('link and bad: {(link a b), bad} is refuted', fb(linkbad, ['(link a b)', 'bad']), FAIL)
    good &= expect('link and bad: {(link a b)} is kept, so link chains pile up',
                   fb(linkbad, ['(link a b)']), '{(link a b)}')
    prop = Theory(undetected['a propagation'])
    good &= expect('a propagation: {(lt a b), (lt b a)} is refuted through the closure',
                   fb(prop, ['(lt a b)', '(lt b a)']), FAIL)
    good &= expect('a propagation: {(lt a b)} is kept as written', fb(prop, ['(lt a b)']), '{(lt a b)}')
    pinbad = Theory(undetected['redesign notes, counterexample 2 (pin and bad)'])
    good &= expect('pin and bad: {(pin $x), bad} is refuted (the equation is forced, then the rule fires)',
                   fb(pinbad, ['(pin $x)', 'bad']), FAIL)
    good &= expect('pin and bad: (pair $x $y) {(pin $x)} -> $y keeps (pin z)',
                   repr(simplify(pinbad, S('(pair $x $y) {(pin $x)} -> $y'))), '(pair z $y) {(pin z)} -> $y')
    for T, n in ((linkbad, 'link and bad'), (prop, 'a propagation'), (pinbad, 'pin and bad')):
        T.name = n
    fallback_theories = [lamvar, linkbad, prop, pinbad] + [
        Theory(undetected[k], k) for k in ('redesign notes, counterexample 1 (merge)',
                                           'symmetry as a simplification',
                                           'two definitions that disagree under a guard')]
    for T in fallback_theories:
        good &= expect('%s: deterministic up to renaming and idempotent, 300 stores' % T.name,
                       stress_fallback(T, 300), 300)
    for T in fallback_theories[:4]:
        for src in ['(f $v $w) {(neq $v $w)} -> (f $w $v)', '$x {(link $x $y), (pin $x)} -> (g $y)',
                    '(g $w) {(lt $v $w), (neq $u $w)} -> (f $v $w)']:
            s = S(src)
            c = canon(T, s)
            good &= expect('%s: canon (swap s) = swap (canon s) for %s' % (T.name, src),
                           canon(T, s.swap()), canon_swap(c))
            if c is not None:
                good &= expect('%s: the representative of a representative is itself' % T.name,
                               canon(T, Span(c[1][0], c[1][1], c[1][2])), (0, c[1]))
    noc = Theory(theories_in('examples/SK.ipynb')[0])
    small = Theory(theories_in('examples/range_sets.txt')[0])
    for T in [eqneq, small, noc, lam, pin, pin2]:
        good &= expect('%s: against the exact path the fallback refutes only what is dead and '
                       'loses nothing, 300 stores' % T.name, stress_fallback(T, 300, exact=True), 300)

    print()
    print('== Stores along a recursion ==')
    link = Theory('(link $x $y) <=> .')
    r = S('$x {(link $x $y)} -> $y')
    rr = compose(link, r, r)
    good &= expect('with (link $x $y) <=> . the chain r ; r is $x -> $y',
                   canon(link, rr), canon(link, S('$x -> $y')))
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
    good &= expect('redesign notes, counterexample 3 is detected confluent', detect(cx3).reasons, [])
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
    good &= expect('D3 is the only condition it fails',
                   [e for e in detect(loop).reasons if 'created variable' not in e], [])
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
    good &= expect('it is detected confluent', detect(pcp).reasons, [])
    sol, word = '(t1 (t2 e))', '(a (b (b e)))'
    good &= expect('a solution makes the store hold',
                   st(pcp, ['(top %s %s)' % (sol, word), '(bot %s %s)' % (sol, word), '(ne %s)' % sol]), '{}')
    good &= expect('and without it the store waits',
                   st(pcp, ['(top $y $w)', '(bot $y $w)', '(ne $y)']), '{(bot $y $w), (ne $y), (top $y $w)}')

    print()
    print('== Extending a theory ==')
    big = Theory(theories_in('examples/range_sets.txt')[0].rstrip().rstrip('}') +
                 '(lt $x $x) <=> fail.\n (lt $x $y), (lt $y $x) <=> fail.\n}')
    good &= expect('ranges with the two refutation rules for lt is detected confluent', detect(big).reasons, [])
    for src in ['(between (s $x) (range (open $x) (closed $y)))', '(lt (s $a) (s $b))',
                '(leq (s $a) (s (s $a)))', '(between $x (range (open $y) (open $x)))']:
        c = [P(src), P('(lt $b $a)')]
        one = nf_store(small, c)
        one = FAIL if one == FAIL else nf(big, one)
        good &= expect('nf_big (nf_small c) = nf_big c for c = %s' % show_store(c),
                       label_state(one), label_state(nf_store(big, c)))

    print()
    print('== Every order of steps gives one normal form (random stores) ==')
    accepted = [eqneq, small, big, noc, lam, pin, pin2,
                Theory(theories_in('examples/ProofSynth.ipynb')[0]),
                Theory(theories_in('examples/program_synth.ipynb')[0]),
                Theory(theories_in('examples/polysimp.ipynb')[0]),
                Theory(theories_in('examples/Untitled.ipynb')[0])]
    for T in accepted:
        good &= expect('%s: 400 stores' % T.name, stress(T, 400), 400)

    found, wrong = fuzz_guarded(300)
    print('       %d of 300 random guarded theories are detected confluent' % found)
    good &= expect('none of them has a store with two normal forms', wrong, [])

    print()
    print('== Closed predicates ==')
    nat = Theory('constraint nat/1 closed\n (nat z) <=> .\n (nat (s $x)) <=> (nat $x).')
    good &= expect('a closed nat is detected confluent', detect(nat).reasons, [])
    good &= expect('{(nat (s (s z)))} holds', st(nat, ['(nat (s (s z)))']), '{}')
    good &= expect('{(nat (s (pair a b)))} is refuted', st(nat, ['(nat (s (pair a b)))']), FAIL)
    good &= expect('{(nat (s $x))} waits as {(nat $x)}', st(nat, ['(nat (s $x))']), '{(nat $x)}')

    print()
    print('ALL CHECKS PASS' if good else 'SOME CHECKS FAILED')
    return 0 if good else 1


if __name__ == '__main__':
    sys.exit(run())
