"""Random small programs on R005 and on the prototype of the symmetric engine: where does each halt?

For Lemma U of lean/SYMMETRIC_ENGINE_SIMULATION.md (the interface check finishes what R005's
unfolding race finishes) and for `TerminatesWhere`. R005 is scripts/r005_interpreter.py, the engine is
scripts/symmetric_engine_tables.py under the split balance with the interface check on sides that
contain a call. A program is reported when R005 halts within its budget and the engine does not
within its own, and counted when it is the other way round.

Run: python3 scripts/symmetric_engine_halting.py [programs] [seed]
This is a measurement aid, not part of any engine."""
import sys, random
sys.setrecursionlimit(1_000_000)
import r005_interpreter as R
import symmetric_engine_tables as E

SPANS = [('u', c) for c in 'ab'] + [('w', c) for c in 'ab'] + [('r', 'a', 'b'), ('r', 'b', 'a'), ('z',), ('k',), ('at', 'a')]
def gen_item(rnd, names, p_call):
    return ('call', rnd.choice(names)) if rnd.random() < p_call else ('span', rnd.choice(SPANS))
def gen_chain(rnd, names, p_call, lo=1, hi=3):
    return [gen_item(rnd, names, p_call) for _ in range(rnd.randint(lo, hi))]
def gen(rnd):
    names = ['p%d' % i for i in range(rnd.randint(1, 3))]
    defs = [(n, [gen_chain(rnd, names, 0.35) for _ in range(rnd.randint(1, 3))]) for n in names]
    return defs, gen_chain(rnd, names, 0.6, 2, 3)

def span_terms(mk_var, mk_sym, mk_app, s):
    x = mk_var(0); c = lambda f, t: mk_app(mk_sym(f), t)
    if s[0] == 'u': return c(s[1], x), x                 # (c $x) -> $x
    if s[0] == 'w': return x, c(s[1], x)                 # $x -> (c $x)
    if s[0] == 'r': return c(s[1], x), c(s[2], x)        # (c $x) -> (d $x)
    if s[0] == 'z': return mk_sym('z'), mk_sym('z')      # z -> z
    if s[0] == 'k': return x, mk_sym('z')                # $x -> z
    return c(s[1], x), c(s[1], x)                        # @(c $x)

def to_r005(defs, q):
    def item(i): return R.call(i[1]) if i[0] == 'call' else R.rw(*span_terms(R.var, R.sym, R.app, i[1]))
    def chain(c):
        out = item(c[-1])
        for i in c[-2::-1]: out = R.seq(item(i), out)
        return out
    def body(alts):
        out = chain(alts[-1])
        for a in alts[-2::-1]: out = R.r_or(chain(a), out)
        return out
    return R.Program([(n, body(b)) for n, b in defs]), chain(q)
def to_engine(defs, q):
    mk = (lambda n: ('v', n)), (lambda f: ('s', f)), (lambda f, x: ('a', f, x))
    def item(i): return E.call(i[1]) if i[0] == 'call' else E.span(*span_terms(*mk, i[1]))
    def chain(c): return E.chain(*[item(i) for i in c])
    return {n: E.union(*[chain(a) for a in b]) for n, b in defs}, chain(q)

def r005_halts(defs, q, rounds=8, ticks=1_000_000):
    # the tables of results kept by the interpreter are per program
    for d in (R._compose, R._meet, R._covers, R._spans): d.clear()
    P, e = to_r005(defs, q)
    R.M.t = 0; R.M.limit = ticks
    try:
        s = R.R005.init(P, e)
        for i in range(rounds):
            r = R.R005.step(s)
            if r[0] == 'done': return i, R.M.t
            s = r[2]
    except R.Exceeded:
        pass
    finally:
        R.M.limit = float('inf')
    return None
def engine_halts(defs, q, opts, ticks=150_000):
    prog, e = to_engine(defs, q)
    m = E.Machine(prog, e, **opts)
    r = m.run(limit=ticks)
    return r[2]

def show(defs, q):
    def sp(s):
        return {'u': '(%s $x) -> $x', 'w': '$x -> (%s $x)', 'r': '(%s $x) -> (%s $x)', 'z': 'z -> z', 'k': '$x -> z', 'at': '@(%s $x)'}[s[0]] % tuple(s[1:])
    def chain(c): return ' ; '.join(i[1] if i[0] == 'call' else '[' + sp(i[1]) + ']' for i in c)
    return '; '.join('%s = %s' % (n, ' | '.join(chain(a) for a in b)) for n, b in defs) + '   query: ' + chain(q)

RULES = {
    'split balance, check on sides with a call': dict(rule='level', units='alone', cover=True, check_apart=True, check_calls=True),
    'split balance, no check': dict(rule='level', units='alone'),
    'whole rounds, check on every side': dict(rule='flat', units='all', cover=True),
}
def verdicts(defs, q):
    """What R005 and each rule of the engine do on one program, computed in a process of its own
    with bounded memory and time, so that one program cannot take the run down. None if it could not."""
    import os, pickle, resource, signal
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r)
        resource.setrlimit(resource.RLIMIT_AS, (3 << 30, 3 << 30))
        signal.alarm(60)
        try:
            out = (r005_halts(defs, q), {name: engine_halts(defs, q, opts) for name, opts in RULES.items()})
            os.write(w, pickle.dumps(out))
        finally:
            os._exit(0)
    os.close(w)
    data = b''
    while True:
        chunk = os.read(r, 65536)
        if not chunk: break
        data += chunk
    os.close(r); os.waitpid(pid, 0)
    return pickle.loads(data) if data else None

def main(n, seed):
    rnd = random.Random(seed)
    both = {k: 0 for k in RULES}; only_r = {k: [] for k in RULES}; only_e = {k: 0 for k in RULES}
    r_halts = 0; failed = 0
    for _ in range(n):
        defs, q = gen(rnd)
        v = verdicts(defs, q)
        if v is None: failed += 1; continue
        a, bs = v
        r_halts += a is not None
        for name in RULES:
            b = bs[name]
            if a is not None and b is not None: both[name] += 1
            elif a is not None: only_r[name].append((a, show(defs, q)))
            elif b is not None: only_e[name] += 1
    print('%d programs, seed %d. R005 halts within 8 rounds and 1,000,000 ticks on %d; the engine is given 150,000 ticks.'
          % (n, seed, r_halts))
    print('%d programs gave no verdict within 60 seconds and 3 GB.' % failed)
    for name in RULES:
        print('\n%s: both halt %d, only the engine %d, only R005 %d' % (name, both[name], only_e[name], len(only_r[name])))
        for a, text in sorted(only_r[name], key=lambda x: len(x[1]))[:6]:
            print('    R005 halts in round %d at %d ticks: %s' % (a[0], a[1], text))

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    main(n, seed)
