"""q = inf | ($s x -> x ; q) | (z -> z) asked at s^k z, inf distinct per level and never finishing.
Level j has a table with two live members: inf_j (always has one tick of work) and the
recursive member, which needs W ticks of its own (compose with the span) and then the
answers of level j-1. Level 0's base case answers after one tick.
share: a request goes to the member that has spent least (the design note's balance).
mixed: requests alternate between the share rule and one flat round over every opened live goal."""
def run(k, mixed, W=1):
    spent_inf = [0]*(k+1); spent_rec = [0]*(k+1); own = [0]*(k+1)
    opened = [False]*(k+1); opened[k] = True
    answered = [False]*(k+1); total = 0
    def work_rec(j):   # one tick inside the recursive member of level j, not below it
        nonlocal total
        if own[j] < W: own[j] += 1; spent_rec[j] += 1; total += 1; opened[j-1] = True; return True
        return False
    def give(j):
        nonlocal total
        if j == 0:
            answered[0] = True; total += 1; return 1
        if answered[j-1] and own[j] >= W:
            answered[j] = True; total += 1; return 1
        if spent_inf[j] < spent_rec[j]:
            spent_inf[j] += 1; total += 1; return 1
        if work_rec(j): return 1
        c = give(j-1); spent_rec[j] += c; return c
    def flat():
        nonlocal total
        for j in range(k, -1, -1):
            if not opened[j] or answered[j]: continue
            if j == 0: answered[0] = True; total += 1; continue
            spent_inf[j] += 1; total += 1
            if not work_rec(j) and answered[j-1]: answered[j] = True; total += 1
    turn = 0
    while not answered[k]:
        if mixed and turn % 2: flat()
        else: give(k)
        turn += 1
        if total > 10**7: return None
    return total
print(" k   share-only   share+flat-round")
for k in (1,2,4,6,8,10,12,14,16,18,20): print(f"{k:>2} {str(run(k,False)):>12} {str(run(k,True)):>12}")
