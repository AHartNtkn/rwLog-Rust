#!/usr/bin/env python3
"""
Port of treecalc_forward_execution_is_fast test to Python prototype.

Tests the same query against the df_engine_proto.py implementation.
"""

import time
import sys
from df_engine_proto import (
    Term, Var, Con, NF, Boundary,
    AtomRel, CallRel, OrRel, AndRel, SeqRel,
    build_engine, pp_nf, pp_term,
    Goal, Engine, Node, JoinNode
)

# Tree calculus constructors
def L() -> Term:
    return Con("l", ())

def B(x: Term) -> Term:
    return Con("b", (x,))

def F(x: Term, y: Term) -> Term:
    return Con("f", (x, y))

def C(x: Term) -> Term:
    return Con("c", (x,))

def A(x: Term, y: Term) -> Term:
    return Con("a", (x, y))

def Z() -> Term:
    return Con("z", ())

def S(x: Term) -> Term:
    return Con("s", (x,))


def build_app_relation():
    """
    Build the app relation from the test:

    rel app {
        (f (c $x) $y) -> (a (c $x) $y)                                    -- rule 1
        | (f (a $x $y) $z) -> (a (a $x $y) $z)                            -- rule 2
        | (f l $z) -> (b $z)                                               -- rule 3
        | (f (b $y) $z) -> (f $y $z)                                       -- rule 4
        | (f (f l $y) $z) -> $y                                            -- rule 5
        | (f (f (f $w $x) $y) l) -> $w                                     -- rule 6
        | [                                                                -- rule 7
            [(f (f (b $x) $y) $z) -> (f $x $z) ; app ; $x -> (f $x $y)]
            & [(f (f (b $x) $y) $z) -> (f $y $z) ; app ; $y -> (f $x $y)]
            ; app
          ]
        | [(f (f (f $w $x) $y) (b $u)) -> (f $x $u) ; app]                -- rule 8
        | [                                                                -- rule 9
            (f (f (f $w $x) $y) (f $u $v)) -> (f (f $y $u) $v)
            ; [(f (f $a $b) $c) -> (f $a $b) ; app ; $a -> (f $a $b)]
              & (f (f $a $b) $c) -> (f $d $c)
            ; app
          ]
    }
    """
    v = [Var(i) for i in range(10)]

    # Rule 1: (f (c $x) $y) -> (a (c $x) $y)
    rule1 = AtomRel(NF(
        match=(F(C(v[0]), v[1]),),
        build=(A(C(v[0]), v[1]),)
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
    # [(f (f (b $x) $y) $z) -> (f $x $z) ; app ; $x -> (f $x $y)]
    # & [(f (f (b $x) $y) $z) -> (f $y $z) ; app ; $y -> (f $x $y)]
    # ; app
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
    # (f (f (f $w $x) $y) (f $u $v)) -> (f (f $y $u) $v)
    # ; [(f (f $a $b) $c) -> (f $a $b) ; app ; $a -> (f $a $b)]
    #   & (f (f $a $b) $c) -> (f $d $c)
    # ; app
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
    """
    The input term: (f (b (f l (b (b (f (b (b l)) (f l l)))))) (b l))
    """
    return F(
        B(F(L(), B(B(F(B(B(L())), F(L(), L())))))),
        B(L())
    )


def run_test():
    """Run the treecalc test and observe behavior."""
    print("=" * 60, flush=True)
    print("TREECALC PYTHON PROTOTYPE TEST", flush=True)
    print("=" * 60, flush=True)

    # Build the app relation
    print("Building app relation...", flush=True)
    app_body = build_app_relation()
    defs = {"app": app_body}
    print("Done.", flush=True)

    # Build the input term
    input_term = build_query_term()
    print(f"\nInput term: {pp_term(input_term)}", flush=True)

    # The full query in the Rust test is:
    # @input ; [$x { (no_c $x) } -> (f $x (c z))] ; app ; [$x -> (f $x (c (s z)))] ; app
    #
    # Since Python doesn't have CHR constraints, we skip the guard and just do:
    # @input ; [$x -> (f $x (c z))] ; app ; [$x -> (f $x (c (s z)))] ; app

    v0 = Var(0)

    # @input - ground term as atom
    atom_input = AtomRel(NF(match=(input_term,), build=(input_term,)))

    # [$x -> (f $x (c z))]
    wrap1 = AtomRel(NF(match=(v0,), build=(F(v0, C(Z())),)))

    # [$x -> (f $x (c (s z)))]
    wrap2 = AtomRel(NF(match=(v0,), build=(F(v0, C(S(Z()))),)))

    # Full query: input ; wrap1 ; app ; wrap2 ; app
    query = SeqRel((atom_input, wrap1, CallRel("app"), wrap2, CallRel("app")))

    print("\nQuery: input ; [$x -> (f $x (c z))] ; app ; [$x -> (f $x (c (s z)))] ; app")
    print("\nBuilding engine...")

    eng = build_engine(defs, query)

    # Instrument to track goals
    total_goals_added = [0]
    original_add_goal = Node.add_goal
    def tracked_add_goal(self, eng, goal):
        total_goals_added[0] += 1
        return original_add_goal(self, eng, goal)
    Node.add_goal = tracked_add_goal

    print("\nRunning query with fuel=100000...", flush=True)
    start = time.time()

    # Instrument step to print progress
    steps = [0]
    original_step_with_fuel = eng.step_with_fuel
    def tracked_step(fuel, stop_when):
        while fuel > 0:
            if stop_when():
                break
            if not eng.worklist:
                break
            nid = eng.worklist.popleft()
            eng.scheduled.discard(nid)
            eng.nodes[nid].step(eng)
            fuel -= 1
            steps[0] += 1
            if steps[0] % 500 == 0:
                elapsed = time.time() - start
                print(f"  Step {steps[0]}: {elapsed:.2f}s, worklist={len(eng.worklist)}, goals={total_goals_added[0]}, root_out={len(eng.nodes[eng.root_id].out_vec)}", flush=True)
            if steps[0] >= 1600:
                print(f"  Stopping at {steps[0]} steps", flush=True)
                return 0  # Force stop
        return fuel
    eng.step_with_fuel = tracked_step

    try:
        result = eng.next_with_fuel(100000)
        elapsed = time.time() - start

        print(f"\nResult: {pp_nf(result) if result else None}")
        print(f"Time: {elapsed:.3f}s")
        print(f"Total goals added: {total_goals_added[0]}")
        print(f"Worklist empty: {len(eng.worklist) == 0}")
        print(f"Root outputs: {len(eng.nodes[eng.root_id].out_vec)}")

    except Exception as e:
        elapsed = time.time() - start
        print(f"\nException after {elapsed:.3f}s: {e}")
        print(f"Total goals added: {total_goals_added[0]}")
        print(f"Worklist size: {len(eng.worklist)}")
        print(f"Root outputs: {len(eng.nodes[eng.root_id].out_vec)}")

    # Print goal statistics per node type
    print("\n" + "=" * 60)
    print("NODE STATISTICS")
    print("=" * 60)

    atom_count = 0
    or_count = 0
    join_count = 0
    table_count = 0
    call_count = 0

    total_node_goals = 0
    total_node_outputs = 0

    for node in eng.nodes:
        total_node_goals += len(node.goals)
        total_node_outputs += len(node.out_vec)

        from df_engine_proto import AtomNode, OrNode, JoinNode, TableNode, CallNode
        if isinstance(node, AtomNode):
            atom_count += 1
        elif isinstance(node, OrNode):
            or_count += 1
        elif isinstance(node, JoinNode):
            join_count += 1
        elif isinstance(node, TableNode):
            table_count += 1
        elif isinstance(node, CallNode):
            call_count += 1

    print(f"Nodes: {len(eng.nodes)} total")
    print(f"  Atom: {atom_count}")
    print(f"  Or: {or_count}")
    print(f"  Join: {join_count}")
    print(f"  Table: {table_count}")
    print(f"  Call: {call_count}")
    print(f"\nTotal goals across all nodes: {total_node_goals}")
    print(f"Total outputs across all nodes: {total_node_outputs}")

    # Sample some goals from the table
    print("\n" + "=" * 60)
    print("SAMPLE GOALS FROM APP TABLE")
    print("=" * 60)

    from df_engine_proto import TableNode
    for node in eng.nodes:
        if isinstance(node, TableNode) and node.name == "app":
            print(f"Table 'app' has {len(node.goals)} goals:")
            for i, g in enumerate(list(node.goals)[:10]):
                m_str = "[" + " ".join(pp_term(t) for t in g.match) + "]" if g.match else "None"
                b_str = "[" + " ".join(pp_term(t) for t in g.build) + "]" if g.build else "None"
                print(f"  {i}: match={m_str} build={b_str}")
            if len(node.goals) > 10:
                print(f"  ... and {len(node.goals) - 10} more")
            break


if __name__ == "__main__":
    run_test()
