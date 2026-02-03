#!/usr/bin/env python3
"""
Port of treecalc test to the LAZY prototype (df_engine_proto_lazy.py).
"""

import time
import sys
from df_engine_proto_lazy import (
    Term, Var, Con, NF, V, C,
    AtomRel, CallRel, OrRel, AndRel, SeqRel,
    build_engine, pp_nf, pp_term,
    Goal, Engine, Node, JoinNode
)

# Tree calculus constructors
def L() -> Term:
    return C("l")

def B(x: Term) -> Term:
    return C("b", x)

def F(x: Term, y: Term) -> Term:
    return C("f", x, y)

def Cv(x: Term) -> Term:  # C is taken by the prototype
    return C("c", x)

def A(x: Term, y: Term) -> Term:
    return C("a", x, y)

def Z() -> Term:
    return C("z")

def S(x: Term) -> Term:
    return C("s", x)


def build_app_relation():
    """Build the app relation."""
    v = [V(i) for i in range(10)]

    # Rule 1: (f (c $x) $y) -> (a (c $x) $y)
    rule1 = AtomRel(NF(
        match=(F(Cv(v[0]), v[1]),),
        build=(A(Cv(v[0]), v[1]),)
    ))

    # Rule 2: (f (a $x $y) $z) -> (a (a $x $y) $z)
    rule2 = AtomRel(NF(
        match=(F(A(v[0], v[1]), v[2]),),
        build=(A(A(v[0], v[1]), v[2]),)
    ))

    # Rule 3: (f l $z) -> (b $z)
    rule3 = AtomRel(NF(
        match=(F(L(), v[0]),),
        build=(B(v[0]),)
    ))

    # Rule 4: (f (b $y) $z) -> (f $y $z)
    rule4 = AtomRel(NF(
        match=(F(B(v[0]), v[1]),),
        build=(F(v[0], v[1]),)
    ))

    # Rule 5: (f (f l $y) $z) -> $y
    rule5 = AtomRel(NF(
        match=(F(F(L(), v[0]), v[1]),),
        build=(v[0],)
    ))

    # Rule 6: (f (f (f $w $x) $y) l) -> $w
    rule6 = AtomRel(NF(
        match=(F(F(F(v[0], v[1]), v[2]), L()),),
        build=(v[0],)
    ))

    # Rule 7: Complex with And and recursive calls
    rule7_left_pre = AtomRel(NF(
        match=(F(F(B(v[0]), v[1]), v[2]),),
        build=(F(v[0], v[2]),)
    ))
    rule7_left_post = AtomRel(NF(
        match=(v[0],),
        build=(F(v[0], v[1]),)
    ))
    rule7_left = SeqRel((rule7_left_pre, CallRel("app"), rule7_left_post))

    rule7_right_pre = AtomRel(NF(
        match=(F(F(B(v[0]), v[1]), v[2]),),
        build=(F(v[1], v[2]),)
    ))
    rule7_right_post = AtomRel(NF(
        match=(v[1],),
        build=(F(v[0], v[1]),)
    ))
    rule7_right = SeqRel((rule7_right_pre, CallRel("app"), rule7_right_post))

    rule7 = SeqRel((AndRel(rule7_left, rule7_right), CallRel("app")))

    # Rule 8: [(f (f (f $w $x) $y) (b $u)) -> (f $x $u) ; app]
    rule8_pre = AtomRel(NF(
        match=(F(F(F(v[0], v[1]), v[2]), B(v[3])),),
        build=(F(v[1], v[3]),)
    ))
    rule8 = SeqRel((rule8_pre, CallRel("app")))

    # Rule 9: Complex
    rule9_pre = AtomRel(NF(
        match=(F(F(F(v[0], v[1]), v[2]), F(v[3], v[4])),),
        build=(F(F(v[2], v[3]), v[4]),)
    ))

    rule9_and_left_pre = AtomRel(NF(
        match=(F(F(v[0], v[1]), v[2]),),
        build=(F(v[0], v[1]),)
    ))
    rule9_and_left_post = AtomRel(NF(
        match=(v[0],),
        build=(F(v[0], v[1]),)
    ))
    rule9_and_left = SeqRel((rule9_and_left_pre, CallRel("app"), rule9_and_left_post))

    rule9_and_right = AtomRel(NF(
        match=(F(F(v[0], v[1]), v[2]),),
        build=(F(v[3], v[2]),)
    ))

    rule9 = SeqRel((rule9_pre, AndRel(rule9_and_left, rule9_and_right), CallRel("app")))

    # Combine all rules with Or
    app_body = OrRel(
        rule1,
        OrRel(rule2,
        OrRel(rule3,
        OrRel(rule4,
        OrRel(rule5,
        OrRel(rule6,
        OrRel(rule7,
        OrRel(rule8, rule9)))))))
    )

    return app_body


def build_query_term():
    """The input term: (f (b (f l (b (b (f (b (b l)) (f l l)))))) (b l))"""
    return F(
        B(F(L(), B(B(F(B(B(L())), F(L(), L())))))),
        B(L())
    )


def run_test():
    print("=" * 60, flush=True)
    print("TREECALC LAZY PROTOTYPE TEST", flush=True)
    print("=" * 60, flush=True)

    print("Building app relation...", flush=True)
    app_body = build_app_relation()
    defs = {"app": app_body}
    print("Done.", flush=True)

    input_term = build_query_term()
    print(f"\nInput term: {pp_term(input_term)}", flush=True)

    v0 = V(0)

    # @input - ground term as atom
    atom_input = AtomRel(NF(match=(input_term,), build=(input_term,)))

    # [$x -> (f $x (c z))]
    wrap1 = AtomRel(NF(match=(v0,), build=(F(v0, Cv(Z())),)))

    # [$x -> (f $x (c (s z)))]
    wrap2 = AtomRel(NF(match=(v0,), build=(F(v0, Cv(S(Z()))),)))

    # Full query: input ; wrap1 ; app ; wrap2 ; app
    query = SeqRel((atom_input, wrap1, CallRel("app"), wrap2, CallRel("app")))

    print("\nQuery: input ; [$x -> (f $x (c z))] ; app ; [$x -> (f $x (c (s z)))] ; app", flush=True)
    print("\nBuilding engine...", flush=True)

    eng = build_engine(defs, query)

    print(f"\nRunning query with fuel=100000...", flush=True)
    start = time.time()

    # Progress tracking
    steps = [0]
    last_report = [0]
    original_step = eng.step
    def tracked_step():
        original_step()
        steps[0] += 1
        if steps[0] - last_report[0] >= 500:
            last_report[0] = steps[0]
            elapsed = time.time() - start
            root_out = len(eng.nodes[eng.root].out_vec)
            print(f"  Step {steps[0]}: {elapsed:.2f}s, goals={eng.stats.goal_inserts}, root_out={root_out}", flush=True)
        if steps[0] >= 50000:
            raise StopIteration("Step limit reached")
    eng.step = tracked_step

    try:
        result = eng.next_with_fuel(100000)
        elapsed = time.time() - start

        print(f"\nResult: {pp_nf(result) if result else None}", flush=True)
        print(f"Time: {elapsed:.3f}s", flush=True)
        print(f"Steps: {steps[0]}", flush=True)
        print(f"Goal inserts: {eng.stats.goal_inserts}", flush=True)
        print(f"Output inserts: {eng.stats.output_inserts}", flush=True)

    except StopIteration as e:
        elapsed = time.time() - start
        print(f"\n{e}", flush=True)
        print(f"Time: {elapsed:.3f}s", flush=True)
        print(f"Steps: {steps[0]}", flush=True)
        print(f"Goal inserts: {eng.stats.goal_inserts}", flush=True)
        print(f"Root outputs: {len(eng.nodes[eng.root].out_vec)}", flush=True)

    except Exception as e:
        elapsed = time.time() - start
        print(f"\nException after {elapsed:.3f}s: {e}", flush=True)
        print(f"Steps: {steps[0]}", flush=True)
        print(f"Goal inserts: {eng.stats.goal_inserts}", flush=True)
        print(f"Root outputs: {len(eng.nodes[eng.root].out_vec)}", flush=True)

    # Node statistics
    print("\n" + "=" * 60, flush=True)
    print("NODE STATISTICS", flush=True)
    print("=" * 60, flush=True)

    from df_engine_proto_lazy import AtomNode, OrNode, JoinNode, TableNode, CallNode

    total_goals = 0
    total_outputs = 0
    for node in eng.nodes:
        total_goals += len(node.goals_set)
        total_outputs += len(node.out_vec)

    print(f"Nodes: {len(eng.nodes)} total", flush=True)
    print(f"Total goals across all nodes: {total_goals}", flush=True)
    print(f"Total outputs across all nodes: {total_outputs}", flush=True)

    # Sample goals from app table
    print("\n" + "=" * 60, flush=True)
    print("SAMPLE GOALS FROM APP TABLE", flush=True)
    print("=" * 60, flush=True)

    from df_engine_proto_lazy import pp_boundary
    for node in eng.nodes:
        if isinstance(node, TableNode) and node.name == "app":
            print(f"Table 'app' has {len(node.goals_set)} goals:", flush=True)
            for i, g in enumerate(list(node.goals_set)[:10]):
                m_str = pp_boundary(g.gmatch) if g.gmatch else "None"
                b_str = pp_boundary(g.gbuild) if g.gbuild else "None"
                print(f"  {i}: match={m_str} build={b_str}", flush=True)
            if len(node.goals_set) > 10:
                print(f"  ... and {len(node.goals_set) - 10} more", flush=True)
            break


if __name__ == "__main__":
    run_test()
