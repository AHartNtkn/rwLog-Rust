#!/usr/bin/env python3
"""
Trace version to understand why exhaustion isn't detected.
"""

from test_exhaustion import *

def test_listlen_exhaustion_trace():
    v0 = Var(0)
    v1 = Var(1)

    nf_base = NF(match=(Nil(),), build=(Z(),))
    nf_step1 = NF(match=(Cons(v0, v1),), build=(v1,))
    nf_step2 = NF(match=(v0,), build=(S(v0),))

    listlen_body = OrRel(
        AtomRel(nf_base),
        SeqRel((AtomRel(nf_step1), CallRel("listlen"), AtomRel(nf_step2)))
    )

    defs = {"listlen": listlen_body}

    nf_query = NF(match=(Nil(),), build=(Nil(),))
    query = SeqRel((AtomRel(nf_query), CallRel("listlen")))

    eng = build_engine(defs, query)

    print("First answer:")
    ans1 = eng.next_with_fuel(100)
    print(f"  {pp_nf(ans1) if ans1 else 'None'}")

    print("\nNow tracing what happens on second call...")
    print("=" * 60)

    # Manually step with tracing
    root = eng.nodes[eng.root_id]
    eng.activate(eng.root_id)

    step = 0
    while step < 50:
        if not eng.worklist:
            print(f"\nWorklist empty! Exhaustion detected.")
            break

        nid = eng.worklist.popleft()
        eng.scheduled.discard(nid)
        node = eng.nodes[nid]

        node_type = type(node).__name__
        out_before = len(node.out_vec)

        node.step(eng)

        out_after = len(node.out_vec)
        new_outputs = out_after - out_before

        # Only print if something interesting happened
        if new_outputs > 0 or step < 10:
            print(f"Step {step}: Node {nid} ({node_type})")
            if new_outputs > 0:
                for i in range(out_before, out_after):
                    print(f"  NEW OUTPUT: {pp_nf(node.out_vec[i])}")

            # If it's the table, show what goals it has
            if isinstance(node, TableNode):
                print(f"  Table goals: {[str(g) for g in node.goals]}")

            # If it's a Call, show its goals
            if isinstance(node, CallNode):
                print(f"  Call goals: {[str(g) for g in node.demand_goals]}")

        step += 1

    print(f"\nTotal steps: {step}")
    print(f"Root outputs: {len(root.out_vec)}")
    for i, nf in enumerate(root.out_vec):
        print(f"  [{i}] {pp_nf(nf)}")

    # Check if there's a second answer
    if eng.root_read_idx < len(root.out_vec):
        ans2 = root.out_vec[eng.root_read_idx]
        print(f"\nSecond answer available: {pp_nf(ans2)}")
    else:
        print(f"\nNo second answer (root_read_idx={eng.root_read_idx}, out_vec len={len(root.out_vec)})")

if __name__ == "__main__":
    test_listlen_exhaustion_trace()
