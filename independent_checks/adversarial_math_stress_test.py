import json, math, random
from fractions import Fraction
from pathlib import Path

def exact_graph_analysis(n, edges):
    nb = [1 << v for v in range(n)]
    adj = [set() for _ in range(n)]
    for u, v in edges:
        if u == v:
            continue
        adj[u].add(v)
        adj[v].add(u)
        nb[u] |= 1 << v
        nb[v] |= 1 << u
    full = (1 << n) - 1
    dom_sets_by_k = [[] for _ in range(n + 1)]
    crit_count = {}
    is_dom = bytearray(1 << n)
    dm = [0] * (1 << n)
    for s in range(0, 1 << n):
        if s > 0:
            low = (s & -s).bit_length() - 1
            dm[s] = dm[s & (s - 1)] | nb[low]
        if dm[s] == full:
            is_dom[s] = 1
            dom_sets_by_k[s.bit_count()].append(s)

    gamma = next(k for k in range(n + 1) if dom_sets_by_k[k])
    Gamma = 0
    for k in range(gamma, n + 1):
        for s in dom_sets_by_k[k]:
            a = 0
            x = s
            while x:
                lb = x & -x
                x ^= lb
                if not is_dom[s ^ lb]:
                    a += 1
            crit_count[s] = a
            if a == k and k > Gamma:
                Gamma = k

    # Independence number exact
    alpha = 0
    edge_mask = [0] * n
    for u in range(n):
        m = 0
        for v in adj[u]:
            m |= 1 << v
        edge_mask[u] = m
    for s in range(0, 1 << n):
        k = s.bit_count()
        if k <= alpha:
            continue
        ok = True
        x = s
        while x:
            lb = x & -x
            v = lb.bit_length() - 1
            x ^= lb
            if edge_mask[v] & s:
                ok = False
                break
        if ok:
            alpha = k

    d = [len(dom_sets_by_k[k]) for k in range(n + 1)]
    c = {}
    v = {}
    for k in range(gamma, n + 1):
        assert d[k] > 0, f"Support failure at k={k}"
        ck = Fraction(sum(crit_count[s] for s in dom_sets_by_k[k]), d[k])
        vk = Fraction(sum((Fraction(crit_count[s]) - ck) ** 2 for s in dom_sets_by_k[k]), d[k])
        c[k] = ck
        v[k] = vk

    return {
        "n": n, "adj": adj, "d": d, "gamma": gamma, "Gamma": Gamma, "alpha": alpha,
        "dom_sets_by_k": dom_sets_by_k, "crit_count": crit_count, "c": c, "v": v,
        "isolates": [u for u in range(n) if len(adj[u]) == 0],
    }

def is_unimodal(d):
    n = len(d) - 1
    i = 0
    while i < n and d[i] <= d[i + 1]:
        i += 1
    while i < n and d[i] >= d[i + 1]:
        i += 1
    return i == n

def is_logconcave(d):
    return all(d[j] * d[j] >= d[j - 1] * d[j + 1] for j in range(1, len(d) - 1))

rng = random.Random(20261113)
stats = {
    "disconnected_forests_checked": 0,
    "forests_with_isolates_checked": 0,
    "cyclic_bipartite_checked": 0,
    "c4_lower_bound_counterexample_confirmed": False,
    "cauchy_binet_pairs_checked": 0,
    "violations": [],
}

# 1. Check C_4 explicitly (paper p.5: |S|=3 has a(S)=0 while 2*gamma(C_4)-|S|=1, whereas |S|+a(S)<=2*alpha(C_4)=4 holds)
c4 = exact_graph_analysis(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
assert c4["gamma"] == 2 and c4["Gamma"] == 2 and c4["alpha"] == 2
s3_a = [c4["crit_count"][s] for s in c4["dom_sets_by_k"][3]]
assert all(a == 0 for a in s3_a) and 2 * c4["gamma"] - 3 == 1
stats["c4_lower_bound_counterexample_confirmed"] = True

# 2. Disconnected forests (including isolated vertices r = 0..4 and multiple tree components)
for trial in range(220):
    n = rng.randint(2, 13)
    comps = rng.randint(2, min(n, 5))
    # Partition vertices into 'comps' components; build random tree on each component
    verts = list(range(n))
    rng.shuffle(verts)
    cuts = sorted(rng.sample(range(1, n), comps - 1))
    parts = []
    prev = 0
    for cut in cuts + [n]:
        parts.append(verts[prev:cut])
        prev = cut
    edges = []
    for comp in parts:
        for idx in range(1, len(comp)):
            p = comp[rng.randrange(idx)]
            edges.append((comp[idx], p))
    res = exact_graph_analysis(n, edges)
    stats["disconnected_forests_checked"] += 1
    d, gamma, Gamma, alpha, c, v = res["d"], res["gamma"], res["Gamma"], res["alpha"], res["c"], res["v"]
    h = Gamma - gamma
    K_h = (h + 1) ** 2 // 4 if ((h + 1) ** 2) % 4 == 0 else ((h + 1) ** 2) // 4 + 1

    # Check alpha == Gamma (bipartite eq (4))
    if alpha != Gamma:
        stats["violations"].append(("alpha!=Gamma", trial))
    # Check Lemma 2.1(iii) & eq (5), Lemma 4.2 covariance, Lemma 4.3 jump, Prop 7.2(i)
    for j in range(1, n + 1):
        lhs = (n - j + 1) * d[j - 1]
        rhs = sum(j - res["crit_count"][s] for s in res["dom_sets_by_k"][j])
        if lhs != rhs:
            stats["violations"].append(("lemma2.1_iii", trial, j))
    for k in range(gamma, n + 1):
        for s in res["dom_sets_by_k"][k]:
            a = res["crit_count"][s]
            if k + a < 2 * gamma or k + a > 2 * Gamma:
                stats["violations"].append(("cor3.3_twosided", trial, k, a, gamma, Gamma))
    for j in range(gamma + 1, n + 1):
        if (j - c[j]) * (c[j] - c[j - 1]) > v[j]:
            stats["violations"].append(("lemma4.2_cov", trial, j))
        if j >= gamma + K_h and c[j] - c[j - 1] > 2:
            stats["violations"].append(("lemma4.3_jump", trial, j))
        if j < n and c[j + 1] - c[j] >= 2 * (j - gamma) + 1:
            stats["violations"].append(("prop7.2_i", trial, j))

    # Check Lemma 2.3 (delete isolated vertices)
    r = len(res["isolates"])
    if r > 0 and r < n:
        stats["forests_with_isolates_checked"] += 1
        keep = [u for u in range(n) if u not in res["isolates"]]
        remap = {u: idx for idx, u in enumerate(keep)}
        edges0 = [(remap[u], remap[w]) for (u, w) in edges if u in remap and w in remap]
        res0 = exact_graph_analysis(len(keep), edges0)
        if res["gamma"] != res0["gamma"] + r or res["Gamma"] != res0["Gamma"] + r:
            stats["violations"].append(("lemma2.3_params", trial))
        if res["d"] != [0] * r + res0["d"]:
            stats["violations"].append(("lemma2.3_poly", trial))
        if is_unimodal(res["d"]) != is_unimodal(res0["d"]):
            stats["violations"].append(("lemma2.3_unimodal", trial))
    if r == 0:
        # Lemma 2.2 (Ore)
        if n < gamma + Gamma:
            stats["violations"].append(("lemma2.2_ore", trial))
    # Theorem 1.1 & Theorem 1.2 & Corollary 6.3
    if h <= 4 and not is_unimodal(d):
        stats["violations"].append(("thm1.1", trial))
    if n - gamma >= 3 * K_h - 7 and not is_unimodal(d):
        stats["violations"].append(("thm1.2_i", trial))
    if not is_logconcave(d):
        stats["violations"].append(("cor6.3_small_forest_lc", trial))

# 3. Cyclic bipartite graphs (test Lemma 3.2, eq (4) alpha=Gamma, Corollary 3.4(ii), Lemma 4.2)
for trial in range(150):
    n1 = rng.randint(2, 6)
    n2 = rng.randint(2, 7)
    n = n1 + n2
    p_edge = rng.uniform(0.25, 0.75)
    edges = [(u, n1 + w) for u in range(n1) for w in range(n2) if rng.random() < p_edge]
    if len(edges) < n:  # force cycles frequently
        for _ in range(n):
            edges.append((rng.randrange(n1), n1 + rng.randrange(n2)))
    res = exact_graph_analysis(n, edges)
    stats["cyclic_bipartite_checked"] += 1
    d, gamma, Gamma, alpha, c, v = res["d"], res["gamma"], res["Gamma"], res["alpha"], res["c"], res["v"]
    if alpha != Gamma:
        stats["violations"].append(("bip_alpha!=Gamma", trial))
    for k in range(gamma, n + 1):
        for s in res["dom_sets_by_k"][k]:
            a = res["crit_count"][s]
            if k + a > 2 * alpha:
                stats["violations"].append(("lemma3.2_upper", trial, k, a, alpha))
    for j in range(1, n + 1):
        if 3 * j >= n + 2 * alpha + 1 and d[j - 1] < d[j]:
            stats["violations"].append(("cor3.4_ii_decr", trial, j))
    total_dom = sum(d)
    avd = Fraction(sum(k * d[k] for k in range(n + 1)), total_dom)
    if avd > Fraction(n + 2 * alpha, 3):
        stats["violations"].append(("cor3.4_ii_avd", trial))

# 4. Lemma 6.2 Cauchy-Binet identity exact check on 200 pairs of log-concave no-internal-zero sequences
for trial in range(200):
    la, lb = rng.randint(2, 10), rng.randint(2, 10)
    # Build log-concave sequences without internal zeros by convolving Bernoulli/binomial factors
    a = [1]
    for _ in range(la):
        w = rng.randint(1, 7)
        a = [ (a[i] if i < len(a) else 0) + w * (a[i-1] if i > 0 else 0) for i in range(len(a) + 1) ]
    b = [1]
    for _ in range(lb):
        w = rng.randint(1, 7)
        b = [ (b[i] if i < len(b) else 0) + w * (b[i-1] if i > 0 else 0) for i in range(len(b) + 1) ]
    shift_a, shift_b = rng.randint(0, 3), rng.randint(0, 3)
    a = [0] * shift_a + a
    b = [0] * shift_b + b
    A = lambda idx: a[idx] if 0 <= idx < len(a) else 0
    B = lambda idx: b[idx] if 0 <= idx < len(b) else 0
    deg_c = len(a) + len(b) - 2
    c = [sum(A(i) * B(k - i) for i in range(k + 1)) for k in range(deg_c + 1)]
    C = lambda idx: c[idx] if 0 <= idx < len(c) else 0
    M = deg_c + 3
    for k in range(0, deg_c + 1):
        lhs = C(k) ** 2 - C(k - 1) * C(k + 1)
        rhs = 0
        for i in range(-2, M):
            for j in range(i + 1, M + 1):
                f1 = A(i) * A(j - 1) - A(i - 1) * A(j)
                f2 = B(k - j + 1) * B(k - i) - B(k - j) * B(k - i + 1)
                if f1 < 0 or f2 < 0:
                    stats["violations"].append(("tp2_minor_negative", trial, k, i, j))
                rhs += f1 * f2
        if lhs != rhs:
            stats["violations"].append(("cauchy_binet_mismatch", trial, k, lhs, rhs))
    if not is_logconcave(c):
        stats["violations"].append(("product_not_lc", trial))
    stats["cauchy_binet_pairs_checked"] += 1

print(json.dumps(stats, indent=2))
assert len(stats["violations"]) == 0, stats["violations"]

