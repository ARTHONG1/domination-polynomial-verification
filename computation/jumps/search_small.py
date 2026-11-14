import sys, itertools
sys.path.insert(0, 'research/q72_jump')
from family_low import low, jump
# sanity: U = T(2,2,3) + one pendant P2 -> 2, 75, 2837 ; T(2,2,3) -> 1, 37, 1352
print('U', low((2,2,3), 1)[1:4], 'T223', low((2,2,3), 0)[1:4], 'T233', low((2,3,3), 0)[1:4])
best = None
res = []
for r in (2, 3, 4, 5):
    for ks in itertools.combinations_with_replacement(range(3, 14), r):
        lo, hi = 1, 60000
        # scan M geometrically then refine for the smallest M that violates
        found = None
        M = 50
        while M <= 60000:
            n, g, v, bad = jump(ks, M)
            if bad: found = M; break
            M = int(M * 1.25) + 1
        if found is None: continue
        a, b = int(found / 1.25) - 2, found
        while b - a > 1:
            m = (a + b) // 2
            if m < 1: a = m; continue
            if jump(ks, m)[3]: b = m
            else: a = m
        n, g, v, bad = jump(ks, b)
        res.append((n, ks, b, v))
res.sort()
for x in res[:12]: print(x)

