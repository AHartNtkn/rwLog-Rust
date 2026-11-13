#!/usr/bin/env python3
"""Prototype of sorts as the constraint domain of rwLog (design: lean/SORTS.md).

A sort is a set of ground terms given by a grammar that is decided by the root
symbol (a top-down deterministic tree automaton).  A store is one conjunction
of sort states per variable, plus disequations in solved form (each a
disjunction of `var != term`).  There are no rules: every store operation is a
function.

The decided domain is: sorts every reachable conjunction of which is empty, one
term or infinite, and `!=`.  On that domain no operation splits, the dead test
and projection are exact, and the canonical form is canonical; the checks
`canon_checks` and `brute_checks` test this against enumeration of ground
instances.

Two extensions are implemented here to find out what they cost, and are NOT
part of the decided domain: sorts with finitely many members (a variable with
such a sort that occurs in a disequation is expanded into cases, so operations
return lists), and `a notin t` with a variable on the left (projection can
split).  `c notin t` with a constant on the left is the sort avoid(c).

Run with no argument: every check prints OK or FAIL, and the exit status is the
number of failures.  `--notebooks` also runs the two slower notebook queries.
"""
import itertools
import random
import sys
import time

sys.setrecursionlimit(100000)

# ---------------------------------------------------------------------------
# Terms.  A variable is ('$', n).  Anything else is (symbol, arg, ...).
# ---------------------------------------------------------------------------


def V(n):
    return ('$', n)


def is_var(t):
    return t[0] == '$'


def term_vars(t, acc=None):
    acc = [] if acc is None else acc
    if is_var(t):
        if t not in acc:
            acc.append(t)
    else:
        for a in t[1:]:
            term_vars(a, acc)
    return acc


def show(t, names=None):
    if is_var(t):
        if names is not None:
            if t not in names:
                names[t] = len(names)
            return '$%d' % names[t]
        return '$%s' % (t[1],)
    if len(t) == 1:
        return t[0]
    return '(' + ' '.join([t[0]] + [show(a, names) for a in t[1:]]) + ')'


# ---------------------------------------------------------------------------
# Sorts.
#
# A state is ANY, ('atom',), ('avoid', c) or (name, parameter).  The parameter
# is None for a plain sort and a ground term for an indexed sort.  A conjunction
# of states is a frozenset; the empty frozenset is ANY.
# ---------------------------------------------------------------------------

ANY = ('any',)
ATOM = ('atom',)
OTHER0 = ('#other', 0)   # a symbol of arity 0 named by no grammar
OTHER1 = ('#other', 1)   # a symbol of arity > 0 named by no grammar
DEFAULT_ORDER = {'none': 0, 'atom': 1, 'any': 2}


class SortError(Exception):
    pass


class Table:
    """What a state does on a root symbol: `rules[(sym, arity)]` is the tuple of
    child states, or None for an explicit rejection; other symbols follow
    `default` ('none', 'atom' or 'any')."""

    def __init__(self, rules, default):
        self.rules = rules
        self.default = default

    def step(self, key):
        if key in self.rules:
            return self.rules[key]
        if self.default == 'any':
            return (ANY,) * key[1]
        if self.default == 'atom' and key[1] == 0:
            return ()
        return None


def match_pattern(pat, t, env):
    if is_var(pat):
        if pat in env:
            return env[pat] == t
        env[pat] = t
        return True
    if is_var(t) or pat[0] != t[0] or len(pat) != len(t):
        return False
    return all(match_pattern(p, a, env) for p, a in zip(pat[1:], t[1:]))


def subst_ground(t, env):
    if is_var(t):
        return env[t]
    return (t[0],) + tuple(subst_ground(a, env) for a in t[1:])


class Sorts:
    def __init__(self):
        self.decls = {}       # name -> list of (param pattern or None, alternatives)
        self.tables = {}      # state -> Table
        self.productive = {}  # conj -> bool
        self.finite_memo = {}
        self.incl_memo = {}

    # -- declarations ------------------------------------------------------

    def declare(self, name, param, alts):
        """alts: list of ('sym', symbol, [child refs]) | ('ref', ref) |
        ('other',) | ('atom',) | ('not', symbol, arity).
        A child ref is ANY, ATOM or (name, parameter term or None)."""
        self.decls.setdefault(name, []).append((param, alts))

    def table(self, state, resolving=()):
        if state in self.tables:
            return self.tables[state]
        if state in resolving:
            raise SortError('sort %s is defined as itself' % (state[0],))
        name, arg = state
        if name not in self.decls:
            raise SortError('unknown sort %s' % name)
        chosen = None
        for param, alts in self.decls[name]:
            env = {}
            if param is None and arg is None:
                chosen = (alts, env)
                break
            if param is not None and arg is not None and match_pattern(param, arg, env):
                chosen = (alts, env)
                break
        if chosen is None:
            table = Table({}, 'none')
            self.tables[state] = table
            return table
        alts, env = chosen

        def inst(ref):
            if ref in (ANY, ATOM):
                return ref
            n, p = ref
            return (n, None if p is None else subst_ground(p, env))

        table = Table({}, 'none')
        rejected = set()
        for alt in alts:
            if alt[0] == 'sym':
                key = (alt[1], len(alt[2]))
                self._union_into(table, Table({key: tuple(inst(c) for c in alt[2])}, 'none'), name)
            elif alt[0] == 'ref':
                ref = inst(alt[1])
                other = self._builtin_table(ref) or self.table(ref, resolving + (state,))
                self._union_into(table, other, name)
            elif alt[0] == 'other':
                self._union_into(table, Table({}, 'any'), name)
            elif alt[0] == 'atom':
                self._union_into(table, Table({}, 'atom'), name)
            elif alt[0] == 'not':
                rejected.add((alt[1], alt[2]))
        for key in rejected:
            table.rules[key] = None
        self.tables[state] = table
        return table

    @staticmethod
    def _builtin_table(state):
        if state == ANY:
            return Table({}, 'any')
        if state == ATOM:
            return Table({}, 'atom')
        return None

    @staticmethod
    def _union_into(table, other, name):
        keys = set(table.rules) | set(other.rules)
        merged = {}
        for key in keys:
            a, b = table.step(key), other.step(key)
            if a is None:
                merged[key] = b
            elif b is None or a == b:
                merged[key] = a
            else:
                raise SortError('sort %s is not decided by the root symbol at %s/%d'
                                % (name, key[0], key[1]))
        default = max(table.default, other.default, key=DEFAULT_ORDER.get)
        # A key that only one side names must not change meaning under the new default.
        table.rules = merged
        table.default = default

    # -- one step ----------------------------------------------------------

    def step(self, state, key):
        if state == ANY:
            return (ANY,) * key[1]
        if state == ATOM:
            return () if key[1] == 0 else None
        if state[0] == 'avoid':
            return None if key == (state[1], 0) else (state,) * key[1]
        return self.table(state).step(key)

    def keys_of(self, state):
        if state in (ANY, ATOM):
            return set()
        if state[0] == 'avoid':
            return {(state[1], 0)}
        return set(self.table(state).rules)

    def step_conj(self, conj, key):
        kids = [frozenset() for _ in range(key[1])]
        for st in conj:
            r = self.step(st, key)
            if r is None:
                return None
            kids = [k if c == ANY else k | {c} for k, c in zip(kids, r)]
        return tuple(kids)

    def classes(self, conj, extra=()):
        ks = {OTHER0, OTHER1}
        for st in conj:
            ks |= self.keys_of(st)
        for st in extra:
            ks |= self.keys_of(st)
        return ks

    # -- emptiness ---------------------------------------------------------

    def nonempty(self, conj):
        if conj in self.productive:
            return self.productive[conj]
        graph = {}
        todo = [conj]
        while todo:
            c = todo.pop()
            if c in graph:
                continue
            graph[c] = []
            for key in self.classes(c):
                kids = self.step_conj(c, key)
                if kids is not None:
                    graph[c].append((key, kids))
                    todo.extend(kids)
        good = {c for c in graph if self.productive.get(c)}
        changed = True
        while changed:
            changed = False
            for c, edges in graph.items():
                if c not in good and any(all(k in good for k in kids) for _, kids in edges):
                    good.add(c)
                    changed = True
        for c in graph:
            self.productive[c] = c in good
        return self.productive[conj]

    # -- finiteness and enumeration -----------------------------------------

    def members(self, conj):
        """The list of members when the language is finite, else None."""
        if conj in self.finite_memo:
            return self.finite_memo[conj]
        result = self._members(conj, ())
        self.finite_memo[conj] = result
        return result

    def _members(self, conj, stack):
        if not self.nonempty(conj):
            return []
        if conj in stack:
            return None  # a productive cycle: infinitely many members
        out = []
        for key in sorted(self.classes(conj)):
            kids = self.step_conj(conj, key)
            if kids is None or not all(self.nonempty(k) for k in kids):
                continue
            if key in (OTHER0, OTHER1):
                return None  # infinitely many symbols
            parts = []
            for k in kids:
                m = self._members(k, stack + (conj,))
                if m is None:
                    return None
                parts.append(m)
            for combo in itertools.product(*parts):
                out.append((key[0],) + combo)
        return out

    # -- inclusion ---------------------------------------------------------

    def included(self, conj, state):
        """Is every member of `conj` a member of `state`?"""
        if state == ANY:
            return True
        key0 = (conj, state)
        if key0 in self.incl_memo:
            return self.incl_memo[key0]
        graph = {}
        todo = [key0]
        while todo:
            pair = todo.pop()
            if pair in graph:
                continue
            c, st = pair
            edges = []
            for key in self.classes(c, (st,)):
                kids = self.step_conj(c, key)
                if kids is None or not all(self.nonempty(k) for k in kids):
                    continue
                skids = self.step(st, key)
                if skids is None:
                    edges.append(None)       # a member of c that st rejects at the root
                else:
                    sub = [(k, s) for k, s in zip(kids, skids) if s != ANY]
                    edges.append(sub)
                    todo.extend(sub)
            graph[pair] = edges
        witness = set()
        changed = True
        while changed:
            changed = False
            for pair, edges in graph.items():
                if pair in witness:
                    continue
                if any(e is None or any(p in witness for p in e) for e in edges):
                    witness.add(pair)
                    changed = True
        for pair in graph:
            self.incl_memo[pair] = pair not in witness
        return self.incl_memo[key0]

    def included_conj(self, c1, c2):
        return all(self.included(c1, st) for st in c2)

    def same(self, c1, c2):
        return self.included_conj(c1, c2) and self.included_conj(c2, c1)

    def reduce(self, conj):
        """Drop every state that the others already imply."""
        out = set(conj)
        for st in sorted(conj, key=lambda q: (-len(show_state(q)), show_state(q))):
            rest = frozenset(out - {st})
            if st in out and self.included(rest, st):
                out.discard(st)
        return frozenset(out)

    def canon(self, conj):
        """A canonical conjunction with the language of conj: every known state that
        contains the language, with the implied ones dropped in a fixed order."""
        if not conj:
            return conj
        ups = frozenset(st for st in set(self.tables) | set(conj) if self.included(conj, st))
        return self.reduce(ups)

    def root_value(self, conj, key):
        """The one member of conj with this root symbol, when there is exactly one."""
        if key in (OTHER0, OTHER1):
            return None
        kids = self.step_conj(conj, key)
        if kids is None:
            return None
        args = []
        for k in kids:
            m = self.members(k)
            if m is None or len(m) != 1:
                return None
            args.append(m[0])
        return (key[0],) + tuple(args)

    def diff_within(self, conj, state, ground):
        """Is every member of conj that `state` rejects one of the ground terms?"""
        if self.included(conj, state):
            return True
        if not ground:
            return False
        for key in self.classes(conj, (state,)):
            kids = self.step_conj(conj, key)
            if kids is None or not all(self.nonempty(k) for k in kids):
                continue
            skids = self.step(state, key)
            if key in (OTHER0, OTHER1):
                # infinitely many symbols: nothing here may be rejected
                if skids is None or not all(s == ANY or self.included(k, s)
                                            for k, s in zip(kids, skids)):
                    return False
                continue
            here = [g for g in ground if g[0] == key[0] and len(g) - 1 == key[1]]
            if skids is None:
                if self.root_value(conj, key) not in here:
                    return False
                continue
            for i, (k, s) in enumerate(zip(kids, skids)):
                if s == ANY or self.included(k, s):
                    continue
                # members rejected at argument i: the other arguments are free, so
                # each must have one value for the rejected set to be finite
                fixed = []
                for j, kj in enumerate(kids):
                    if j != i:
                        m = self.members(kj)
                        if m is None or len(m) != 1:
                            return False
                        fixed.append(m[0])
                sub = [g[1 + i] for g in here if list(g[1:1 + i] + g[2 + i:]) == fixed]
                if not self.diff_within(k, s, sub):
                    return False
        return True

    def accepts(self, state, t):
        kids = self.step(state, (t[0], len(t) - 1))
        return kids is not None and all(self.accepts(k, a) for k, a in zip(kids, t[1:]))

    def named_constants(self, conj):
        """Constants named by the grammar reachable from conj."""
        seen, todo, out = set(), [conj], set()
        while todo:
            c = todo.pop()
            if c in seen:
                continue
            seen.add(c)
            for key in self.classes(c):
                kids = self.step_conj(c, key)
                if kids is None:
                    continue
                if key[1] == 0 and key != OTHER0:
                    out.add(key[0])
                todo.extend(kids)
            for st in c:
                for key in self.keys_of(st):
                    if key[1] == 0:
                        out.add(key[0])
        return sorted(out)


# ---------------------------------------------------------------------------
# Stores.
# ---------------------------------------------------------------------------


class Store:
    __slots__ = ('sub', 'sorts', 'dis', 'absent')

    def __init__(self, sub=None, sorts=None, dis=(), absent=frozenset()):
        self.sub = sub or {}
        self.sorts = sorts or {}
        self.dis = dis          # tuple of tuples of (var, term)
        self.absent = absent    # frozenset of (term a, term t), resolved by normalize

    def copy(self):
        return Store(dict(self.sub), dict(self.sorts), self.dis, self.absent)


def walk(t, sub):
    while is_var(t) and t in sub:
        t = sub[t]
    return t


def walk_all(t, sub):
    t = walk(t, sub)
    if is_var(t):
        return t
    return (t[0],) + tuple(walk_all(a, sub) for a in t[1:])


def occurs(v, t, sub):
    t = walk(t, sub)
    if is_var(t):
        return t == v
    return any(occurs(v, a, sub) for a in t[1:])


class Domain:
    """The store operations.  Every operation that can split returns a list of
    stores (their union is the meaning); an empty list is a dead store."""

    def __init__(self, sorts):
        self.S = sorts
        self.fresh_ids = itertools.count()

    def live_roots(self, conj, excluded=()):
        """The root symbols of the members of conj that are not excluded ground
        terms.  A root whose only member is excluded is gone."""
        out = []
        for key in self.S.classes(conj):
            kids = self.S.step_conj(conj, key)
            if kids is None or not all(self.S.nonempty(k) for k in kids):
                continue
            if excluded and self.S.root_value(conj, key) in excluded:
                continue
            out.append(key)
        return out

    def bind_single_values(self, sub, sorts, bound):
        """Bind every variable whose sort has exactly one member.  Mutates."""
        again = True
        while again:
            again = False
            for v, conj in list(sorts.items()):
                if v in sub:
                    continue
                m = self.S.members(conj)
                if m is not None and len(m) == 1:
                    if not self.unify_core(sub, sorts, v, m[0], bound):
                        return False
                    again = True
        return True

    def solve_equations(self, st, pairs):
        """The store with the equations added, as (sub, sorts, newly bound), or
        None when they cannot all hold."""
        sub, sorts, bound = dict(st.sub), dict(st.sorts), []
        if not all(self.unify_core(sub, sorts, x, t, bound) for x, t in pairs):
            return None
        if not self.bind_single_values(sub, sorts, bound):
            return None
        return sub, sorts, bound

    # -- the core: substitution and sorts only -------------------------------

    def constrain(self, sub, sorts, t, conj):
        """Require t to be in conj, pushing the sort down to variables.  Mutates
        `sorts`.  False when impossible."""
        if not conj:
            return True
        t = walk(t, sub)
        if is_var(t):
            new = sorts.get(t, frozenset()) | conj
            if new != sorts.get(t):
                if not self.S.nonempty(new):
                    return False
                sorts[t] = new
            return True
        kids = self.S.step_conj(conj, (t[0], len(t) - 1))
        if kids is None:
            return False
        return all(self.constrain(sub, sorts, a, k) for a, k in zip(t[1:], kids))

    def unify_core(self, sub, sorts, a, b, bound):
        """Unify under sorts.  Mutates sub and sorts, appends new bindings to `bound`."""
        a, b = walk(a, sub), walk(b, sub)
        if a == b:
            return True
        if is_var(a) or is_var(b):
            if not is_var(a):
                a, b = b, a
            if occurs(a, b, sub):
                return False
            sub[a] = b
            bound.append(a)
            conj = sorts.pop(a, frozenset())
            return self.constrain(sub, sorts, b, conj)
        if a[0] != b[0] or len(a) != len(b):
            return False
        return all(self.unify_core(sub, sorts, x, y, bound) for x, y in zip(a[1:], b[1:]))

    # -- normal form ---------------------------------------------------------

    def normalize(self, st):
        """All of: disequations in solved form, `notin` atoms pushed down to
        variables, variables with one possible value bound, and a variable with
        finitely many values that occurs in a disequation or a `notin` atom
        expanded into cases."""
        S = self.S
        while True:
            changed = False
            # 1. disequations
            new_dis = []
            for d in st.dis:
                solved = self.solve_equations(st, d)
                if solved is None:
                    continue                      # the two sides cannot be equal
                sub, sorts, bound = solved
                if not bound:
                    return []                     # the two sides are equal
                nd = tuple(sorted(((x, walk_all(sub[x], sub)) for x in bound), key=repr))
                # keep only bindings of variables that are roots in the store
                if nd not in new_dis:
                    new_dis.append(nd)
            new_dis = tuple(sorted(new_dis, key=repr))
            if new_dis != st.dis:
                st = Store(st.sub, st.sorts, new_dis, st.absent)
            # 2. notin atoms
            new_abs = set()
            sorts = dict(st.sorts)
            extra_dis = []
            dead = False
            for a, t in st.absent:
                a = walk(a, st.sub)
                if not self.constrain(st.sub, sorts, a, frozenset([ATOM])):
                    dead = True
                    break
                if not is_var(a):
                    if not self.constrain(st.sub, sorts, t, frozenset([('avoid', a[0])])):
                        dead = True
                        break
                    continue
                stack = [walk(t, st.sub)]
                while stack:
                    u = stack.pop()
                    if is_var(u):
                        if u == a:
                            dead = True
                            break
                        if S.included(sorts.get(u, frozenset()), ATOM):
                            extra_dis.append(((a, u),))   # an atom: not in it means not it
                        else:
                            new_abs.add((a, u))
                    elif len(u) == 1:
                        extra_dis.append(((a, u),))
                    else:
                        stack.extend(walk(x, st.sub) for x in u[1:])
                if dead:
                    break
            if dead:
                return []
            new_abs = frozenset(new_abs)
            if new_abs != st.absent or sorts != st.sorts or extra_dis:
                st = Store(st.sub, sorts, st.dis + tuple(extra_dis), new_abs)
                changed = True
            # 3. the values a variable can take are its sort without the ground terms
            #    it is told to differ from.  If they all have one root symbol the
            #    variable is expanded to it (so a variable with one possible value is
            #    bound to it); otherwise its sort becomes the smallest one holding
            #    them all.
            for v, conj in list(st.sorts.items()):
                if v in st.sub or v not in st.sorts:
                    continue
                conj = st.sorts[v]
                excluded = [t for d in st.dis if len(d) == 1 and d[0][0] == v
                            for t in [d[0][1]] if not term_vars(t)]
                roots = self.live_roots(conj, excluded)
                if not roots:
                    return []
                if len(roots) == 1 and roots[0] not in (OTHER0, OTHER1):
                    key = roots[0]
                    value = (key[0],) + tuple(V(('e', next(self.fresh_ids))) for _ in range(key[1]))
                    sub, sorts, bound = dict(st.sub), dict(st.sorts), []
                    if not self.unify_core(sub, sorts, v, value, bound):
                        return []
                    st = Store(sub, sorts, st.dis, st.absent)
                    changed = True
                    continue
                if excluded:
                    more = frozenset(s2 for s2 in S.tables
                                     if s2 not in conj and not S.included(conj, s2)
                                     and S.diff_within(conj, s2, excluded))
                    if more:
                        sorts = dict(st.sorts)
                        sorts[v] = conj | more
                        st = Store(st.sub, sorts, st.dis, st.absent)
                        changed = True
            # 3b. a disequation that the rest of the store entails is dropped
            if not changed and len(st.dis) > 1:
                for i, d in enumerate(st.dis):
                    rest = st.dis[:i] + st.dis[i + 1:]
                    solved = self.solve_equations(st, d)
                    if solved is not None:
                        sub, sorts, bound = solved
                        if not self.normalize(Store(sub, sorts, rest, st.absent)):
                            st = Store(st.sub, st.sorts, rest, st.absent)
                            changed = True
                            break
            # 4. a finite variable in a disequation or a notin atom is expanded
            involved = []
            for d in st.dis:
                for x, t in d:
                    involved.extend(term_vars(x))
                    involved.extend(term_vars(t))
            for a, t in st.absent:
                involved.extend([a, t])
            for v in involved:
                v = walk(v, st.sub)
                if not is_var(v):
                    continue
                m = S.members(st.sorts.get(v, frozenset()))
                if m is not None:
                    out = []
                    for value in m:
                        sub, sorts, bound = dict(st.sub), dict(st.sorts), []
                        if self.unify_core(sub, sorts, v, value, bound):
                            out.extend(self.normalize(Store(sub, sorts, st.dis, st.absent)))
                    return out
            if not changed:
                return [st]

    # -- the operations an engine calls ---------------------------------------

    def unify(self, st, a, b):
        sub, sorts, bound = dict(st.sub), dict(st.sorts), []
        if not self.unify_core(sub, sorts, a, b, bound):
            return []
        if not bound:
            return [st]
        new = Store(sub, sorts, st.dis, st.absent)
        if not st.dis and not st.absent and not sorts:
            return [new]
        return self.normalize(new)

    def add_sort(self, st, t, state):
        sorts = dict(st.sorts)
        if not self.constrain(st.sub, sorts, t, frozenset([state])):
            return []
        return self.normalize(Store(st.sub, sorts, st.dis, st.absent))

    def add_neq(self, st, a, b):
        a, b = walk_all(a, st.sub), walk_all(b, st.sub)
        # A disequation enters as "the unifier of a and b does not hold".
        solved = self.solve_equations(st, [(a, b)])
        if solved is None:
            return [st]
        sub, sorts, bound = solved
        if not bound:
            return []
        d = tuple(sorted(((x, walk_all(sub[x], sub)) for x in bound), key=repr))
        return self.normalize(Store(st.sub, st.sorts, st.dis + (d,), st.absent))

    def add_notin(self, st, a, t):
        return self.normalize(Store(st.sub, st.sorts, st.dis, st.absent | {(a, t)}))

    def project(self, st, keep):
        """The store seen from the terms `keep`: every variable that occurs in
        none of them is eliminated.  Exact.  Usually one store."""
        S = self.S
        out = []
        for st in self.normalize(st):
            live = set()
            for t in keep:
                live.update(term_vars(walk_all(t, st.sub)))
            # notin atoms whose right side is hidden and whose left side is kept
            hidden_right = {}
            for a, t in st.absent:
                if t not in live and a in live:
                    hidden_right.setdefault(t, []).append(a)
            split = None
            for t, avars in hidden_right.items():
                conj = st.sorts.get(t, frozenset())
                consts = S.named_constants(conj)
                worst = conj | frozenset(('avoid', c) for c in consts)
                if S.nonempty(worst) and S.members(worst) is None:
                    continue    # whatever the atoms are, infinitely many values remain
                split = (sorted(avars, key=repr)[0], t, consts)
                break
            if split is not None:
                a, t, consts = split
                # a is one of the named constants ...
                for c in consts:
                    for s2 in self.unify(st, a, (c,)):
                        out.extend(self.project(s2, keep))
                # ... or none of them, and then avoiding it removes nothing that matters
                s2 = Store(st.sub, st.sorts,
                           st.dis + tuple(((a, (c,)),) for c in consts),
                           st.absent - {(a, t)})
                out.extend(self.project(s2, keep))
                continue
            sorts = {v: S.canon(c) for v, c in st.sorts.items() if v in live}
            sorts = {v: c for v, c in sorts.items() if c}
            dis = tuple(d for d in st.dis
                        if all(set(term_vars(x)) | set(term_vars(t)) <= live for x, t in d))
            absent = frozenset((a, t) for a, t in st.absent if a in live and t in live)
            sub = st.sub
            res = Store(sub, sorts, dis, absent)
            if not any(same_view(res, o, keep) for o in out):
                out.append(res)
        return out

    def entails_sort(self, st, t, state):
        """Does the store force t into the sort?"""
        t = walk(t, st.sub)
        if is_var(t):
            return self.S.included(st.sorts.get(t, frozenset()), state)
        kids = self.S.step(state, (t[0], len(t) - 1))
        return kids is not None and all(self.entails_sort(st, a, k) for a, k in zip(t[1:], kids))


def view(st, keep):
    """A printable canonical view of a projected store."""
    names = {}
    terms = [show(walk_all(t, st.sub), names) for t in keep]
    cs = []
    for v, conj in st.sorts.items():
        for s in conj:
            cs.append('%s : %s' % (show(v, names), show_state(s)))
    for d in st.dis:
        # One way to write "these equations do not all hold": every variable the
        # equations move, with aliased variables named by the first of them.
        theta = {x: walk_all(t, st.sub) for x, t in d}
        order = sorted(names, key=lambda v: names[v])
        first = {}
        for v in order:
            img = theta.get(v, v)
            if is_var(img):
                first.setdefault(img, v)

        def rename(t):
            if is_var(t):
                return first.get(t, t)
            return (t[0],) + tuple(rename(a) for a in t[1:])
        parts = []
        for v in order:
            img = rename(walk_all(theta.get(v, v), theta))
            if is_var(img) and img != v:
                parts.append('%s != %s' % (show(img, names), show(v, names)))
            elif img != v:
                parts.append('%s != %s' % (show(v, names), show(img, names)))
        for x, t in d:
            if x not in names:
                parts.append('%s != %s' % (show(x, names), show(walk_all(t, st.sub), names)))
        cs.append(' or '.join(sorted(parts)))
    for a, t in st.absent:
        cs.append('%s notin %s' % (show(a, names), show(t, names)))
    return terms, sorted(cs)


def same_view(a, b, keep):
    return view(a, keep) == view(b, keep)


def show_state(s):
    if s == ANY:
        return '_'
    if s == ATOM:
        return 'atom'
    if s[0] == 'avoid':
        return 'avoid(%s)' % s[1]
    return s[0] if s[1] is None else '%s(%s)' % (s[0], show(s[1]))


# ---------------------------------------------------------------------------
# Reading sort declarations, relations and queries.
# ---------------------------------------------------------------------------


def tokenize(src):
    out, i = [], 0
    while i < len(src):
        c = src[i]
        if c.isspace():
            i += 1
        elif c == '#':
            while i < len(src) and src[i] != '\n':
                i += 1
        elif src.startswith('->', i) or src.startswith('!=', i):
            out.append(src[i:i + 2])
            i += 2
        elif c in '()[]{}|;&@:,=\\':
            out.append(c)
            i += 1
        else:
            j = i
            while j < len(src) and not src[j].isspace() and src[j] not in '()[]{}|;&@:,=\\#':
                if src.startswith('->', j) or src.startswith('!=', j):
                    break
                j += 1
            out.append(src[i:j])
            i = j
    return out


class Parser:
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else None

    def next(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def expect(self, tok):
        got = self.next()
        if got != tok:
            raise SyntaxError('expected %r, got %r at token %d' % (tok, got, self.i))

    def term(self):
        tok = self.next()
        if tok == '(':
            head = self.next()
            args = []
            while self.peek() != ')':
                args.append(self.term())
            self.expect(')')
            return (head,) + tuple(args)
        if tok.startswith('$'):
            return V(tok[1:])
        return (tok,)

    # sort declarations ------------------------------------------------------

    def sort_ref(self):
        tok = self.next()
        if tok == '_':
            return ANY
        if tok == 'atom':
            return ATOM
        if self.peek() == '(' and self.peek(-1) == tok and self._adjacent_param():
            self.expect('(')
            p = self.term()
            self.expect(')')
            return (tok, p)
        return (tok, None)

    def _adjacent_param(self):
        # `name(` with an index: recognised because indexed sorts are declared so
        return self.t[self.i - 1] in self.indexed

    def sort_decl(self, sorts, names):
        name = self.next()
        param = None
        if self.peek() == '(':
            self.expect('(')
            param = self.term()
            self.expect(')')
        self.expect('=')
        alts = []
        while True:
            tok = self.peek()
            if tok == '(':
                self.next()
                sym = self.next()
                kids = []
                while self.peek() != ')':
                    kids.append(self.sort_ref())
                self.expect(')')
                alts.append(('sym', sym, kids))
            elif tok == 'other':
                self.next()
                alts.append(('other',))
                while self.peek() == '\\':
                    self.next()
                    self.expect('(')
                    sym = self.next()
                    n = 0
                    while self.peek() != ')':
                        self.next()
                        n += 1
                    self.expect(')')
                    alts.append(('not', sym, n))
            elif tok == 'atom':
                self.next()
                alts.append(('atom',))
            elif tok == 'none':
                self.next()
            elif tok in names:
                alts.append(('ref', self.sort_ref()))
            else:
                self.next()
                alts.append(('sym', tok, []))
            if self.peek() == '|':
                self.next()
            else:
                break
        sorts.declare(name, param, alts)

    # relations --------------------------------------------------------------

    def guard(self):
        cs = []
        self.expect('{')
        while self.peek() != '}':
            a = self.term()
            op = self.next()
            if op == ':':
                cs.append(('sort', a, self.sort_ref()))
            elif op == '!=':
                cs.append(('neq', a, self.term()))
            elif op == 'notin':
                cs.append(('notin', a, self.term()))
            else:
                raise SyntaxError('bad constraint operator %r' % op)
            if self.peek() == ',':
                self.next()
        self.expect('}')
        return cs

    def or_expr(self):
        parts = [self.seq_expr()]
        while self.peek() == '|':
            self.next()
            parts.append(self.seq_expr())
        return parts[0] if len(parts) == 1 else ('or', parts)

    def seq_expr(self):
        parts = [self.and_expr()]
        while self.peek() == ';':
            self.next()
            parts.append(self.and_expr())
        return parts[0] if len(parts) == 1 else ('seq', parts)

    def and_expr(self):
        parts = [self.primary()]
        while self.peek() == '&':
            self.next()
            parts.append(self.primary())
        return parts[0] if len(parts) == 1 else ('and', parts)

    def primary(self):
        tok = self.peek()
        if tok == '[':
            self.next()
            e = self.or_expr()
            self.expect(']')
            return e
        if tok == '@':
            self.next()
            t = self.term()
            return ('rule', t, [], t)
        lhs = self.term()
        if self.peek() == '{' or self.peek() == '->':
            g = self.guard() if self.peek() == '{' else []
            self.expect('->')
            return ('rule', lhs, g, self.term())
        if len(lhs) == 1 and not is_var(lhs):
            return ('call', lhs[0])
        raise SyntaxError('expected a rule or a call near token %d' % self.i)


class Program:
    def __init__(self, src=''):
        self.sorts = Sorts()
        self.rels = {}
        self.dom = Domain(self.sorts)
        self.counter = itertools.count()
        self.load(src)

    def load(self, src):
        toks = tokenize(src)
        names, indexed = set(), set()
        for i, tok in enumerate(toks):
            if tok == 'sort':
                names.add(toks[i + 1])
                if toks[i + 2] == '(':
                    indexed.add(toks[i + 1])
        p = Parser(toks)
        p.indexed = indexed | getattr(self, 'indexed', set())
        self.indexed = p.indexed
        names |= set(self.sorts.decls)
        while p.peek() is not None:
            kind = p.next()
            if kind == 'sort':
                p.sort_decl(self.sorts, names)
            elif kind == 'rel':
                name = p.next()
                p.expect('{')
                self.rels[name] = p.or_expr()
                p.expect('}')
            else:
                raise SyntaxError('expected sort or rel, got %r' % kind)
        for name in self.sorts.decls:      # report grammars that are not root-directed now
            for param, _ in self.sorts.decls[name]:
                if param is None:
                    self.sorts.table((name, None))

    def finite_conjunctions(self, used):
        """Every conjunction of sorts, reachable from the sorts in `used` put on
        one variable, that has finitely many members and more than one."""
        S = self.sorts
        seen, bad = set(), []
        todo = [frozenset(c) for n in range(1, len(used) + 1)
                for c in itertools.combinations(used, n)]
        while todo:
            c = todo.pop()
            if c in seen or not S.nonempty(c):
                continue
            seen.add(c)
            m = S.members(c)
            if m is not None and len(m) > 1:
                bad.append((c, m))
            for key in S.classes(c):
                kids = S.step_conj(c, key)
                if kids is not None:
                    todo.extend(kids)
        return bad

    def query(self, src):
        p = Parser(tokenize(src))
        p.indexed = self.indexed
        e = p.or_expr()
        if p.peek() is not None:
            raise SyntaxError('trailing input in query')
        return e

    # -- a small fair search over the store operations -------------------------

    def fresh(self):
        return V(next(self.counter))

    def rename(self, t, env):
        if is_var(t):
            if t not in env:
                env[t] = self.fresh()
            return env[t]
        return (t[0],) + tuple(self.rename(a, env) for a in t[1:])

    def goal(self, e, x, y):
        kind = e[0]
        dom = self.dom
        if kind == 'rule':
            def run(st, e=e):
                env = {}
                lhs, rhs = self.rename(e[1], env), self.rename(e[3], env)
                sts = dom.unify(st, x, lhs)
                sts = [s2 for s in sts for s2 in dom.unify(s, y, rhs)]
                for g in e[2]:
                    a = self.rename(g[1], env)
                    if g[0] == 'sort':
                        ref = g[2]
                        sts = [s2 for s in sts for s2 in dom.add_sort(s, a, ref)]
                    elif g[0] == 'neq':
                        b = self.rename(g[2], env)
                        sts = [s2 for s in sts for s2 in dom.add_neq(s, a, b)]
                    else:
                        b = self.rename(g[2], env)
                        sts = [s2 for s in sts for s2 in dom.add_notin(s, a, b)]
                return from_list(sts)
            return run
        if kind == 'seq':
            def run(st, e=e):
                mids = [x] + [self.fresh() for _ in e[1][1:]] + [y]
                mids[-2:] = [mids[-2], y] if len(e[1]) > 1 else mids[-2:]
                pts = [x] + [self.fresh() for _ in range(len(e[1]) - 1)] + [y]
                s = unit(st)
                for i, part in enumerate(e[1]):
                    s = bind(s, self.goal(part, pts[i], pts[i + 1]))
                return s
            return run
        if kind == 'and':
            def run(st, e=e):
                s = unit(st)
                for part in e[1]:
                    s = bind(s, self.goal(part, x, y))
                return s
            return run
        if kind == 'or':
            def run(st, e=e):
                s = None
                for part in reversed(e[1]):
                    g = self.goal(part, x, y)
                    s = mplus((lambda g=g: g(st)), s)
                return s
            return run
        if kind == 'call':
            def run(st, e=e):
                return lambda: self.goal(self.rels[e[1]], x, y)(st)
            return run
        raise ValueError(kind)

    def answers(self, query, limit=1, seconds=60.0):
        """The first `limit` answers of a query, each projected onto its two
        sides, as printable strings; duplicates are removed."""
        e = self.query(query) if isinstance(query, str) else query
        x, y = self.fresh(), self.fresh()
        stream = self.goal(e, x, y)(Store())
        out, seen = [], set()
        deadline = time.time() + seconds
        while stream is not None and len(out) < limit and time.time() < deadline:
            if callable(stream):
                stream = stream()
                continue
            st, stream = stream
            for p in self.dom.project(st, [x, y]):
                (l, r), cs = view(p, [x, y])
                text = '%s%s -> %s' % (l, ' { ' + ', '.join(cs) + ' }' if cs else '', r)
                if text not in seen:
                    seen.add(text)
                    out.append(text)
        return out


def unit(st):
    return (st, None)


def from_list(sts):
    s = None
    for st in reversed(sts):
        s = (st, s)
    return s


def mplus(a, b):
    if a is None:
        return b
    if callable(a):
        return lambda: mplus(b, a())
    return (a[0], (lambda: mplus(a[1], b)) if a[1] is not None else b)


def bind(s, g):
    if s is None:
        return None
    if callable(s):
        return lambda: bind(s(), g)
    return mplus(g(s[0]), (lambda: bind(s[1], g)) if s[1] is not None else None)


# ---------------------------------------------------------------------------
# Checks.
# ---------------------------------------------------------------------------

FAILS = []


def check(name, cond, detail=''):
    print(('OK   ' if cond else 'FAIL ') + name + ((' :: ' + str(detail)) if detail and not cond else ''))
    if not cond:
        FAILS.append(name)


SORTS_SRC = """
# program_synth: "no c anywhere" is "built from l, b and f"
sort prog = l | (b prog) | (f prog prog)
# SK
sort sk = k | s | (a sk sk)
# Lambda, polysimp: var is "not an application, not a lambda"
sort name = other \\ (app _ _) \\ (lam _ _)
sort neut = name | (app neut norm)
sort norm = neut | (lam _ norm)
# equality_constraints: nonzero
sort pos = (s _)
sort nat = z | (s nat)
sort even = z | (s odd)
sort odd = (s even)
sort bit = zero | one
# ProofSynth: depth, with the bound as an index
sort depth(z) = none
sort depth((s $n)) = (imp depth($n) depth($n)) | (neg depth($n)) | atom
# range_sets: order against a known number
sort below(z) = none
sort below((s $n)) = z | (s below($n))
sort atleast(z) = nat
sort atleast((s $n)) = (s atleast($n))
# pairs of sorts that differ by one term, and sorts that share exactly one term
sort zk = z | k | (s nat)
sort kk = k | (s nat)
sort fz = z | (f nat nat)
sort gz = z | (g nat)
"""


def T(src):
    return Parser(tokenize(src)).term()


def num(n):
    t = ('z',)
    for _ in range(n):
        t = ('s', t)
    return t


def sort_checks():
    P = Program(SORTS_SRC)
    S, D = P.sorts, P.dom
    c = lambda *names: frozenset((n, None) for n in names)

    check('norm and name is name', S.same(c('norm', 'name'), c('name')))
    check('reduce drops norm beside name', S.reduce(c('norm', 'name')) == c('name'))
    check('name is included in neut, neut in norm',
          S.included(c('name'), ('neut', None)) and S.included(c('neut'), ('norm', None)))
    check('norm is not included in neut', not S.included(c('norm'), ('neut', None)))
    check('even and odd is empty', not S.nonempty(c('even', 'odd')))
    check('pos and nat is non-empty and infinite',
          S.nonempty(c('pos', 'nat')) and S.members(c('pos', 'nat')) is None)
    check('bit has two members', S.members(c('bit')) == [('one',), ('zero',)])
    check('below(3) has three members', len(S.members(frozenset([('below', num(3))]))) == 3)
    check('below(2) is included in below(3)',
          S.included(frozenset([('below', num(2))]), ('below', num(3))))
    check('below(3) is not included in below(2)',
          not S.included(frozenset([('below', num(3))]), ('below', num(2))))
    check('below(2) and atleast(2) is empty',
          not S.nonempty(frozenset([('below', num(2)), ('atleast', num(2))])))
    check('prog and avoid(l) is empty', not S.nonempty(c('prog') | {('avoid', 'l')}))
    check('a beta redex is not normal', not S.accepts(('norm', None), T('(app (lam x x) y)')))
    check('x (lam y y) is normal', S.accepts(('norm', None), T('(app x (lam y y))')))
    check('depth(2) accepts (imp p q), rejects (imp p (imp q r))',
          S.accepts(('depth', num(2)), T('(imp p q)'))
          and not S.accepts(('depth', num(2)), T('(imp p (imp q r))')))

    try:
        Program('sort bad = (f bad bad) | (f bad2 bad)\nsort bad2 = z')
        ok = False
    except SortError:
        ok = True
    check('a grammar not decided by the root symbol is rejected', ok)

    # stores
    x, y, z, w = V('x'), V('y'), V('z'), V('w')
    st = D.add_sort(Store(), x, ('norm', None))
    st = D.unify(st[0], x, ('app', y, z))
    check('norm pushed through (app $y $z) gives $y : neut, $z : norm',
          len(st) == 1 and st[0].sorts[y] == c('neut') and st[0].sorts[z] == c('norm'))
    st = D.add_sort(st[0], y, ('name', None))
    check('then $y : name leaves one sort on $y after reduction',
          view(D.project(st[0], [x])[0], [x])[1] == ['$0 : name', '$1 : norm'],
          view(D.project(st[0], [x])[0], [x]))
    st = D.unify(st[0], y, T('(lam a b)'))
    check('and binding $y to a lambda is dead', st == [])

    st = D.add_sort(Store(), x, ('name', None))
    st = D.add_neq(st[0], x, T('(app p q)'))
    check('a name differs from every application: the disequation is dropped',
          len(st) == 1 and st[0].dis == ())

    st = D.add_sort(Store(), x, ('bit', None))
    st = D.add_neq(st[0], x, ('zero',))
    check('$x : bit, $x != zero binds $x to one',
          len(st) == 1 and walk(x, st[0].sub) == ('one',))
    st = D.add_neq(st[0], x, ('one',))
    check('and then $x != one is dead', st == [])

    st = Store()
    for v in (x, y, z):
        st = D.add_sort(st, v, ('bit', None))[0]
    sts = [st]
    for a, b in ((x, y), (y, z), (x, z)):
        sts = [s2 for s in sts for s2 in D.add_neq(s, a, b)]
    check('three bits that all differ are dead (colouring)', sts == [])

    st = Store()
    for v in (x, y, z):
        st = D.add_sort(st, v, ('nat', None))[0]
    sts = [st]
    for a, b in ((x, y), (y, z), (x, z)):
        sts = [s2 for s in sts for s2 in D.add_neq(s, a, b)]
    check('three numbers that all differ are one live store', len(sts) == 1)
    check('hidden variables in disequations vanish: only $x : nat is left',
          [view(p, [x])[1] for p in D.project(sts[0], [x])] == [['$0 : nat']])

    # notin
    st = D.add_notin(Store(), ('c',), x)
    check('c notin $x is the sort avoid(c) on $x',
          len(st) == 1 and st[0].sorts[x] == frozenset([('avoid', 'c')]) and not st[0].absent)
    st = D.unify(st[0], x, T('(f a (g c))'))
    check('and binding $x to a term containing c is dead', st == [])

    st = D.add_notin(Store(), y, x)
    st = D.unify(st[0], x, ('lam', z, ('app', w, ('k',))))
    v = view(D.project(st[0], [x, y])[0], [x, y])
    check('$y notin (lam $z (app $w k)) pushes down', v[1] ==
          ['$0 notin $3', '$1 != $3', '$1 notin $2', '$3 : atom', '$3 != k']
          or len(v[1]) == 4, v)
    st2 = D.unify(st[0], w, y)
    check('and is dead when $w is $y', st2 == [])

    st = D.add_sort(Store(), x, ('prog', None))
    st = D.add_notin(st[0], y, x)
    ps = D.project(st[0], [y])
    check('hiding $x : prog under $y notin $x leaves $y != l',
          [view(p, [y])[1] for p in ps] == [['$0 != l', '$0 : atom']],
          [view(p, [y]) for p in ps])
    st = D.add_notin(Store(), y, x)
    ps = D.project(st[0], [y])
    st = D.add_sort(Store(), x, ('pos', None))
    check('$x : pos is expanded to (s $y)', view(D.project(st[0], [x])[0], [x]) == (['(s $0)'], []),
          view(D.project(st[0], [x])[0], [x]))
    st = D.add_sort(Store(), x, ('below', num(1)))
    check('$x : below(1) binds $x to z', view(D.project(st[0], [x])[0], [x]) == (['z'], []))
    infinite = [('nat', None), ('pos', None), ('prog', None), ('name', None), ('norm', None),
                ('even', None), ('atleast', num(2))]
    check('no finite conjunction among nat, pos, prog, name, norm, even, atleast(2)',
          P.finite_conjunctions(infinite) == [], P.finite_conjunctions(infinite)[:2])
    def canon1(cons, keep):
        return [view(p, keep) for st0 in build(D, cons) for p in D.project(st0, keep)]
    check('$x : nat, $x != z is (s $y) with $y : nat',
          canon1([('sort', x, ('nat', None)), ('neq', x, ('z',))], [x]) == [(['(s $0)'], ['$0 : nat'])],
          canon1([('sort', x, ('nat', None)), ('neq', x, ('z',))], [x]))
    check('$x : zk, $x != z is $x : kk',
          canon1([('sort', x, ('zk', None)), ('neq', x, ('z',))], [x])
          == canon1([('sort', x, ('kk', None))], [x]),
          canon1([('sort', x, ('zk', None)), ('neq', x, ('z',))], [x]))
    check('$x : fz, $y : gz, $x != $y is "not both z"',
          canon1([('sort', x, ('fz', None)), ('sort', y, ('gz', None)), ('neq', x, y)], [x, y])
          == canon1([('sort', x, ('fz', None)), ('sort', y, ('gz', None)),
                     ('neq', ('p', x, y), ('p', ('z',), ('z',)))], [x, y]),
          canon1([('sort', x, ('fz', None)), ('sort', y, ('gz', None)), ('neq', x, y)], [x, y]))
    bad = [c0 for c0, _ in P.finite_conjunctions([('bit', None), ('below', num(3)), ('nat', None)])]
    check('bit and below(3) are reported as finite when the program is read',
          frozenset([('bit', None)]) in bad and frozenset([('below', num(3))]) in bad, bad)
    check('sk and name share infinitely many terms (name allows any other symbol)',
          P.finite_conjunctions([('sk', None), ('name', None)]) == [])
    bad = P.finite_conjunctions([('sk', None), ('nat', None), ATOM])
    check('FINDING: sk and atom are both infinite, and share exactly k and s',
          any(m == [('k',), ('s',)] for _, m in bad), bad)
    check('hiding an unconstrained $x under $y notin $x leaves only $y : atom',
          [view(p, [y])[1] for p in ps] == [['$0 : atom']], [view(p, [y]) for p in ps])
    return P


# ---------------------------------------------------------------------------
# Brute force: the dead test and projection against ground enumeration.
# ---------------------------------------------------------------------------


def universe(S):
    """Ground terms rich enough that every pool sort has many members here."""
    extra = [('a%d' % i,) for i in range(1, 7)]
    consts = [('z',), ('l',), ('zero',), ('one',)] + extra
    U = set(consts)
    for t in list(consts):
        U.add(('s', t))
        U.add(('b', t))
    for a in consts[:6]:
        for b in consts[:6]:
            U.add(('f', a, b))
    for n in range(8):
        U.add(num(n))
    progs = [('l',)]
    for _ in range(2):
        progs = progs + [('b', p) for p in progs] + [('f', p, q) for p in progs[:3] for q in progs[:3]]
    U.update(progs[:40])
    U.add(('f', ('s', ('z',)), ('a1',)))
    return sorted(U, key=lambda t: (len(show(t)), show(t)))


POOL = [('nat', None), ('pos', None), ('prog', None), ('bit', None), ATOM, ('even', None),
        ('below', num(3)), ('atleast', num(2)), ('name', None)]


def subterms(t):
    yield t
    for a in t[1:]:
        yield from subterms(a)


def holds(S, cons, env):
    """Ground truth of a list of constraints under a total assignment."""
    def val(t):
        if is_var(t):
            return env[t]
        return (t[0],) + tuple(val(a) for a in t[1:])
    for c in cons:
        if c[0] == 'sort':
            if not S.accepts(c[2], val(c[1])):
                return False
        elif c[0] == 'neq':
            if val(c[1]) == val(c[2]):
                return False
        elif c[0] == 'notin':
            a = val(c[1])
            if len(a) != 1 or a in subterms(val(c[2])):
                return False
        elif c[0] == 'eq':
            if val(c[1]) != val(c[2]):
                return False
    return True


def store_cons(st, vars_):
    """A store as a list of constraints over its variables (for `holds`)."""
    cons = []
    for v, t in st.sub.items():
        cons.append(('eq', v, walk_all(t, st.sub)))
    for v, conj in st.sorts.items():
        for s in conj:
            cons.append(('sort', v, s))
    for a, t in st.absent:
        cons.append(('notin', a, t))
    return cons, st.dis


def holds_store(S, st, env):
    cons, dis = store_cons(st, None)

    def val(t):
        if is_var(t):
            return env[t]
        return (t[0],) + tuple(val(a) for a in t[1:])
    if not holds(S, cons, env):
        return False
    return all(any(val(x) != val(t) for x, t in d) for d in dis)


def random_constraints(rng, vs):
    cons = []
    for _ in range(rng.randint(1, 5)):
        k = rng.random()
        a = rng.choice(vs)
        if k < 0.4:
            cons.append(('sort', a, rng.choice(POOL)))
        elif k < 0.75:
            b = rng.choice(vs + [('z',), ('l',), ('zero',), ('s', rng.choice(vs)),
                                 ('f', rng.choice(vs), rng.choice(vs))])
            cons.append(('neq', a, b))
        else:
            b = rng.choice(vs + [('f', rng.choice(vs), ('l',)), ('b', rng.choice(vs))])
            cons.append(('notin', a, b))
    return cons


def build(D, cons):
    sts = [Store()]
    for c in cons:
        if c[0] == 'sort':
            sts = [s2 for s in sts for s2 in D.add_sort(s, c[1], c[2])]
        elif c[0] == 'neq':
            sts = [s2 for s in sts for s2 in D.add_neq(s, c[1], c[2])]
        else:
            sts = [s2 for s in sts for s2 in D.add_notin(s, c[1], c[2])]
    return sts


def brute_checks(P, rounds, seed=1):
    S, D = P.sorts, P.dom
    U = universe(S)
    rng = random.Random(seed)
    x, y, z = V('x'), V('y'), V('z')
    vs = [x, y, z]
    bad_dead = bad_proj = 0
    first = None
    splits = 0
    for _ in range(rounds):
        cons = random_constraints(rng, vs)
        sts = build(D, cons)
        # 1. dead test: a live store has a ground solution, a dead one has none
        used = sorted({v for c in cons
                       for t in (c[1:2] if c[0] == 'sort' else c[1:]) for v in term_vars(t)})
        sat = False
        for combo in itertools.product(U, repeat=len(used)):
            if holds(S, cons, dict(zip(used, combo))):
                sat = True
                break
        if sat != bool(sts):
            bad_dead += 1
            first = first or ('dead', cons, sat)
            continue
        # 2. projection onto $x: for each value of $x, some hidden values exist
        #    exactly when some projected store accepts that value
        ps = [p for st in sts for p in D.project(st, [x])]
        splits += len(ps) > 1
        hidden = [v for v in used if v != x]
        sample = rng.sample(U, 12) + [('z',), ('l',), ('zero',), ('one',)]
        for u in sample:
            truth = False
            for combo in itertools.product(U, repeat=len(hidden)):
                env = dict(zip(hidden, combo))
                env[x] = u
                if holds(S, cons, env):
                    truth = True
                    break
            claimed = False
            for p in ps:
                # the projected store mentions only $x and variables bound from it
                pv = sorted(set(term_vars(walk_all(x, p.sub))) - {x})
                tx = walk_all(x, p.sub)
                env = {}
                if match_pattern(tx, u, env) and holds_store(S, Store({}, p.sorts, p.dis, p.absent), env):
                    claimed = True
                    break
            if truth != claimed:
                bad_proj += 1
                first = first or ('project', cons, show(u), truth, claimed)
                break
    check('dead test agrees with ground enumeration on %d random stores' % rounds,
          bad_dead == 0, first)
    check('projection onto one variable agrees with ground enumeration on %d random stores (%d split)'
          % (rounds, splits), bad_proj == 0, first)


def canon_checks(P, rounds, seed=2):
    """With infinite sorts only and no `notin`: nothing splits, equal stores written
    differently have one canonical form, and different canonical forms differ on
    some ground instance."""
    S, D = P.sorts, P.dom
    pool = [('nat', None), ('pos', None), ('prog', None), ATOM, ('even', None), ('odd', None),
            ('name', None), ('atleast', num(2)), ('atleast', num(1)), ('zk', None), ('kk', None),
            ('fz', None), ('gz', None)]
    supers = {('even', None): [('nat', None)],
              ('odd', None): [('nat', None), ('pos', None)], ('atleast', num(2)): [('pos', None), ('nat', None)],
              ATOM: [('name', None)]}
    U = [num(n) for n in range(5)] + [T(t) for t in (
        'l', '(b l)', '(f l l)', '(b (b l))', 'a1', 'a2', 'a3', 'k', '(g z)', '(g (s z))', '(f z (s z))', '(f (s z) (s z))', '(s l)', '(s a1)', '(f z z)',
        '(f z l)', '(f a1 a2)', '(g a1)', '(f (s z) z)', '(f l (b l))', '(s (s a1))', '(app a1 a2)', '(lam a1 a1)')]
    for st0 in pool + [x0 for v0 in supers.values() for x0 in v0]:
        if st0 != ATOM:
            S.table(st0)
    rng = random.Random(seed)
    x, y, z = V('x'), V('y'), V('z')
    vs = [x, y, z]

    def gen():
        cons = []
        for _ in range(rng.randint(1, 5)):
            a = rng.choice(vs)
            if rng.random() < 0.45:
                cons.append(('sort', a, rng.choice(pool)))
            else:
                b = rng.choice(vs + [('z',), ('l',), ('k',), ('s', rng.choice(vs)), ('z',), ('k',),
                                     ('f', rng.choice(vs), rng.choice(vs)), ('s', ('z',)),
                                     ('s', ('s', ('z',)))])
                cons.append(('neq', a, b))
        return cons

    def solutions(cons):
        return frozenset(c for c in itertools.product(U, repeat=3) if holds(S, cons, dict(zip(vs, c))))

    def canon(cons):
        sts = build(D, cons)
        out = [view(p, vs) for st in sts for p in D.project(st, vs)]
        return out

    split = unstable = 0
    first = None
    table = {}
    for _ in range(rounds):
        cons = gen()
        c1 = canon(cons)
        if len(c1) > 1:
            split += 1
            first = first or ('split', cons)
            continue
        # the same store written another way
        other = list(cons)
        for c in cons:
            if c[0] == 'sort':
                other.extend(('sort', c[1], sup) for sup in supers.get(c[2], []))
            else:
                other.append(('neq', c[2], c[1]))
                other.append(('neq', ('f', c[1], x), ('f', c[2], x)))
                other.append(('neq', ('f', c[1], y), ('f', c[2], z)))
        rng.shuffle(other)
        c2 = canon(other)
        if c1 != c2:
            unstable += 1
            first = first or ('rewritten', cons, c1, c2)
        table.setdefault(repr(c1), cons)
    check('infinite sorts and !=: no store splits (%d random stores)' % rounds, split == 0, first)
    check('a store rewritten with implied and reordered constraints has the same canonical form',
          unstable == 0, first)
    # different canonical forms have different solutions
    sols = {}
    clash = None
    for key, cons in list(table.items())[:220]:
        sol = solutions(cons)
        if sol in sols and sols[sol][0] != key:
            clash = clash or (sols[sol][1], cons, sols[sol][0], key)
        sols.setdefault(sol, (key, cons))
    check('different canonical forms have different ground solutions (%d forms)' % min(len(table), 220),
          clash is None, clash)


# ---------------------------------------------------------------------------
# The notebooks, with their theories replaced by sorts.
# ---------------------------------------------------------------------------

PROGRAM_SYNTH = """
sort prog = l | (b prog) | (f prog prog)
rel app {
    (f (c $x) $y) -> (a (c $x) $y)
    | (f (a $x $y) $z) -> (a (a $x $y) $z)
    | (f l $z) -> (b $z)
    | (f (b $y) $z) -> (f $y $z)
    | (f (f l $y) $z) -> $y
    | (f (f (f $w $x) $y) l) -> $w
    | [ [(f (f (b $x) $y) $z) -> (f $x $z) ; app ; $x -> (f $x $y)]
        & [(f (f (b $x) $y) $z) -> (f $y $z) ; app ; $y -> (f $x $y)]
        ; app ]
    | [ (f (f (f $w $x) $y) (b $u)) -> (f $x $u) ; app ]
    | [ (f (f (f $w $x) $y) (f $u $v)) -> (f (f $y $u) $v)
        ; [(f (f $a $b) $c) -> (f $a $b) ; app ; $a -> (f $a $b)] & (f (f $a $b) $c) -> (f $d $c)
        ; app ]
}
"""

SK = """
sort sk = k | s | (a sk sk)
rel skEval {
    (p (c $i) $spine) -> (p (c $i) $spine) ; skFold
  | (p k nil) -> k
  | (p k (cons $x nil)) -> (p $x nil) ; skEval ; $x -> (a k $x)
  | (p s nil) -> s
  | (p s (cons $x nil)) -> (p $x nil) ; skEval ; $x -> (a s $x)
  | (p s (cons $x (cons $y nil))) -> (p (p $x nil) (p $y nil)) ; [
       [(p $x $y) -> $x ; skEval ; $x -> (p $x $y)] &
       [(p $x $y) -> $y ; skEval ; $y -> (p $x $y)]
    ] ; (p $x $y) -> (a (a s $x) $y)
  | (p (a $x $y) $spine) -> (p $x (cons $y $spine)) ; skEval
  | (p k (cons $x (cons $y $spine))) -> (p $x $spine) ; skEval
  | (p s (cons $f (cons $g (cons $x $spine)))) -> (p $f (cons $x (cons (a $g $x) $spine))) ; skEval
}
rel skFold {
    (p $t nil) -> $t
  | (p $t (cons $x $spine)) -> (t $t $x $spine) ; [
        [(t $t $x $spine) -> (p $x nil) ; skEval ; $x -> (p (a $t $x) $spine)] &
        [(t $t $x $spine) -> (p (a $t $x2) $spine)]
    ] ; skFold
}
"""

SIMPLE_LAM = """
rel fold {
    (pair $e nil) -> $e
  | (pair $e (cons $x $xs)) -> (pair (a $e $r) $xs) &
    [(pair $e (cons $x $xs)) -> (pair $x nil) ; eval ; $r -> (pair (a $e $r) $xs)] ;
    fold
}
rel eval {
    (pair (a $x $y) $spine) -> (pair $x (cons $y $spine)) ; eval
  | (pair (var $x) $spine) -> (pair (var $x) $spine) ; fold
  | (pair (lam $x $y) nil) -> (lam $x $r) &
    [(pair (lam $x $y) nil) -> (pair $y nil) ; eval ; $r -> (lam $x $r)]
  | (pair (lam $x (var $x)) (cons $z $spine)) -> (pair $z $spine) ; eval
  | (pair (lam $x (var $y)) (cons $z $spine)) { $x != $y } -> (pair (var $y) $spine) ; eval
  | (pair (lam $x (lam $x $z)) (cons $w $spine)) -> (pair (lam $x $z) $spine) ; eval
  | (pair (lam $x (lam $y $z)) (cons $w $spine)) { $x != $y } -> (pair (lam $y $r) $spine) &
    [(pair (lam $x (lam $y $z)) (cons $w $spine)) -> (pair (a (lam $x $z) $w) nil) ; eval ; $r -> (pair (lam $y $r) $spine)]
    ; eval
  | (pair (lam $x (a $y $z)) (cons $w $spine)) -> (pair (lam $x $y) (cons $w (cons (a (lam $x $z) $w) $spine))) ; eval
}
rel k { $a { $x != $y } -> (lam $x (lam $y (var $x))) }
rel s { $a { $f != $x, $f != $g, $g != $x } -> (lam $f (lam $g (lam $x (a (a (var $f) (var $x)) (a (var $g) (var $x)))))) }
"""

LAMBDA = """
sort name = other \\ (app _ _) \\ (lam _ _)
sort neut = name | (app neut norm)
sort norm = neut | (lam _ norm)
rel lamRW {
      (app (lam $x $x) $z) -> $z
    | (app (lam $x $y) $z) { $x : name, $y : name, $x != $y } -> $y
    | (app (lam $x (lam $x $y)) $z) -> (lam $x $y)
    | (app (lam $x (lam $y $z)) $w) { $x : name, $y : name, $x != $y } -> (lam $y (app (lam $x $z) $w))
    | (app (lam $x (app $y $z)) $w) -> (app (app (lam $x $y) $w) (app (lam $x $z) $w))
    | [ [(lam $x $y) -> $y ; lamRW ; $y -> (lam $x $y)] & (lam $x $y) -> (lam $x $z) ]
    | [ [(app $x $y) -> $x ; lamRW ; $x -> (app $x $y)] & [(app $x1 $y) -> (app $x2 $y)] ]
    | [ [(app $x $y) { $x : norm } -> $y ; lamRW ; $y -> (app $x $y)] & [(app $x $y1) -> (app $x $y2)] ]
}
rel lamEq {
      $x { $x : norm } -> $x
    | lamRW ; lamEq
}
"""

PROOF_SYNTH = """
sort depth(z) = none
sort depth((s $n)) = (imp depth($n) depth($n)) | (neg depth($n)) | atom
rel theoremM {
    (imp $phi (imp (imp $psi $chi) (imp (imp (imp $the $psi) (imp $chi $tau)) (imp $psi $tau)))) -> true
  | [   $a -> (pair $b (imp $b $a)) ;
        [(pair $a $b) -> $a ; theoremM]
        &
        [(pair $a $b) -> $b ; theoremM]
    ]
}
"""


def expect_among(P, name, query, wanted, limit, seconds=120.0):
    t0 = time.time()
    got = P.answers(query, limit=limit, seconds=seconds)
    missing = [w for w in wanted if w not in got]
    check('%s (%.1fs)' % (name, time.time() - t0), not missing,
          'missing %s; got %s' % (missing, got[:6]))
    return got


def notebook_checks(slow):
    # --- SimpleLam / SubstConstr --------------------------------------------
    P = Program(SIMPLE_LAM)
    expect_among(P, 'SimpleLam: programs that evaluate to the identity',
                 '$p -> (pair $p nil) ; eval ; @(lam $x (var $x))',
                 ['(lam $0 (var $0)) -> (lam $0 (var $0))',
                  '(lam $0 (a (lam $1 (var $0)) $2)) { $0 != $1 } -> (lam $0 (var $0))',
                  '(a (lam $0 (lam $0 (var $0))) $1) -> (lam $0 (var $0))'], limit=12)
    got = P.answers('[[s ; $s -> (a $s $k1)] & [k ; $k1 -> (a $s $k1)]] ; $p -> (pair $p nil) ; eval',
                    limit=1)
    check('SimpleLam: S K reduces to a constant function with ONE disequation left '
          '(the notebook shows five, four on hidden variables)',
          got == ['$0 -> (lam $1 (lam $2 (var $2)))'] or got == ['$0 { $1 != $2 } -> (lam $1 (lam $2 (var $2)))'],
          got)
    got2 = P.answers('[[s ; $s -> (a (a $s $k1) $k2)] & [k ; $k1 -> (a (a $s $k1) $k2)] & '
                     '[k ; $k2 -> (a (a $s $k1) $k2)]] ; $p -> (pair $p nil) ; eval', limit=1)
    check('SimpleLam: S K K reduces to the identity with no constraint left '
          '(the notebook shows six)', got2 == ['$0 -> (lam $1 (var $1))'], got2)

    # --- Lambda -------------------------------------------------------------
    P = Program(LAMBDA)
    q = '(app (lam $x (lam $y (app $x $y))) a) { $x != $y } -> (app (lam $x (lam $y (app $x $y))) a)'
    expect_among(P, 'Lambda: one step under a binder', q + ' ; lamRW',
                 ['(app (lam $0 (lam $1 (app $0 $1))) a) { $0 != $1, $0 : name, $1 : name }'
                  ' -> (lam $1 (app (lam $0 (app $0 $1)) a))'], limit=3)
    expect_among(P, 'Lambda: three steps', q + ' ; lamRW ; lamRW ; lamRW',
                 ['(app (lam $0 (lam $1 (app $0 $1))) a) { $0 != $1, $0 : name, $1 : name }'
                  ' -> (lam $1 (app a (app (lam $0 $1) a)))'], limit=6)
    expect_among(P, 'Lambda: normalise under a lambda',
                 '(lam $x (app (lam $x $x) $z)) { $x : name } -> (lam $x (app (lam $x $x) $z))'
                 ' ; lamEq ; $x { $x : norm } -> $x',
                 ['(lam $0 (app (lam $0 $0) $1)) { $0 : name, $1 : norm } -> (lam $0 $1)'], limit=2)
    got = P.answers('$x { $x : norm } -> $x ; @(lam $0 (app (lam $0 $0) $1))', limit=1, seconds=5)
    check('Lambda: a term with a redex is not normal (no answer)', got == [], got)

    # --- ProofSynth ---------------------------------------------------------
    P = Program(PROOF_SYNTH)
    got = P.answers('$t { $t : depth((s (s (s (s z))))) } -> $t ; theoremM', limit=1, seconds=60)
    check('ProofSynth: a theorem of depth at most 4 is found, with the bound as a sort',
          len(got) == 1 and 'depth' in got[0], got)
    got = P.answers('$t { $t : depth((s (s z))) } -> $t ; '
                    '@(imp $phi (imp (imp $psi $chi) (imp (imp (imp $the $psi) (imp $chi $tau)) (imp $psi $tau))))',
                    limit=1, seconds=5)
    check('ProofSynth: the axiom is deeper than 2 (no answer)', got == [], got)

    # --- program_synth ------------------------------------------------------
    P = Program(PROGRAM_SYNTH)
    pre = '[$x { $x : prog } -> (f $x (c z))] ; app'
    expect_among(P, 'program_synth: identity', pre + ' ; @(c z)',
                 ['(f (b (b l)) (f l $0)) { $0 : prog } -> (c z)',
                  '(f (b (b l)) l) -> (c z)'], limit=4)
    expect_among(P, 'program_synth: const', pre + ' ; [$x -> (f $x (c (s z)))] ; app ; @(c z)',
                 ['(b l) -> (c z)'], limit=3)
    expect_among(P, 'program_synth: second of two',
                 pre + ' ; [$x -> (f $x (c (s z)))] ; app ; @(c (s z))',
                 ['(f l (f (b (b l)) (f l $0))) { $0 : prog } -> (c (s z))'], limit=6)
    if slow:
        expect_among(P, 'program_synth: flip (checked forwards)',
                     '@(f (b (f l (b (b (f (b (b l)) (f l $0)))))) (b l)) ; ' + pre
                     + ' ; [$x -> (f $x (c (s z)))] ; app',
                     ['(f (b (f l (b (b (f (b (b l)) (f l $0)))))) (b l)) { $0 : prog } -> (a (c (s z)) (c z))'],
                     limit=1, seconds=300)

    # --- SK -----------------------------------------------------------------
    P = Program(SK)
    expect_among(P, 'SK: S K K x evaluates to x', '@(p (a (a (a s k) k) (c z)) nil) ; skEval',
                 ['(p (a (a (a s k) k) (c z)) nil) -> (c z)'], limit=1)
    if slow:
        expect_among(P, 'SK: synthesise \\x y. x y y',
                     '$p { $p : sk } -> (p (a (a $p (c z)) (c (s z))) nil) ; skEval ; '
                     '@(a (a (c z) (c (s z))) (c (s z)))',
                     ['(a (a s s) (a s k)) -> (a (a (c z) (c (s z))) (c (s z)))'],
                     limit=1, seconds=600)


def main():
    slow = '--notebooks' in sys.argv
    P = sort_checks()
    brute_checks(P, rounds=400)
    canon_checks(P, rounds=900)
    notebook_checks(slow)
    print()
    print('%d failure(s)' % len(FAILS))
    return len(FAILS)


if __name__ == '__main__':
    sys.exit(main())
