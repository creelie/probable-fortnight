"""Independent checks of Section 7 (clique blow-ups of longer odd cycles).

  * formula (7.1), chi(C_{2k+1}[w]) = max(s(w), ceil(n/k)), against an exact dynamic programme for
    k = 1, ..., 5 and all weight vectors with small entries (zero entries allowed);
  * the colouring of the proof of Theorem 7.1 (bag i gets the colours a_i, ..., a_i + w_i - 1 read
    modulo m) is proper with m = max(s(w), ceil(n/k)) colours on the same vectors;
  * the arithmetic of Corollary 7.2 for k = 3 and k = 4.

The dynamic programme does not use the formula. Fix the colour set T_0 of bag 0. Colour
permutations fixing T_0 act transitively on the sets T with given |T & T_0| and |T - T_0|, and the
constraints only link consecutive bags and bags 2k and 0, so a colouring with c colours exists iff
some sequence of pairs (|T_i & T_0|, |T_i - T_0|), i = 1, ..., 2k, is compatible step by step and
ends with T_{2k} & T_0 empty.

Run: python3 verification/python/odd_cycles.py
"""
import itertools
import sys


def s_of(w):
    L = len(w)
    if L == 3:
        return sum(w)  # C_3[w] is complete
    return max(w[i] + w[(i + 1) % L] for i in range(L))


def formula(w):
    k = (len(w) - 1) // 2
    return max(s_of(w), -(-sum(w) // k))


def colourable(w, c):
    """exact: does C_{2k+1}[w] have a proper colouring with c colours?"""
    w0 = w[0]
    if w0 > c:
        return False
    # state (a, b): a colours inside T_0, b outside
    states = {(w0, 0)}
    for wi in w[1:]:
        new = set()
        for a, b in states:
            for a2 in range(0, min(wi, w0 - a) + 1):
                b2 = wi - a2
                if b2 <= c - w0 - b:
                    new.add((a2, b2))
        states = new
        if not states:
            return False
    return any(a == 0 for a, _ in states)


def chi_dp(w):
    c = 0
    while not colourable(w, c):
        c += 1
    return c


def arc_colouring(w):
    L = len(w)
    k = (L - 1) // 2
    m = formula(w)
    g = k * m - sum(w)
    S = C = 0
    arcs = []
    for i in range(L):
        a = S + min(g, C)
        arcs.append([(a + j) % m for j in range(w[i])])
        S += w[i]
        if i < L - 1:
            C += m - w[i] - w[i + 1]
    return m, arcs


def arc_ok(w):
    L = len(w)
    m, arcs = arc_colouring(w)
    for i in range(L):
        if len(set(arcs[i])) != w[i] or any(x >= m for x in arcs[i]):
            return False
        nbrs = range(L) if L == 3 else [(i + 1) % L]
        for t in nbrs:
            if t != i and set(arcs[i]) & set(arcs[t]):
                return False
    return True


def main():
    ok = True

    def check(cond, msg):
        nonlocal ok
        print(("ok:   " if cond else "FAIL: ") + msg)
        ok &= bool(cond)

    for k, top in [(1, 8), (2, 7), (3, 4), (4, 3), (5, 2)]:
        L = 2 * k + 1
        count = 0
        good_dp = good_arc = True
        for w in itertools.product(range(top + 1), repeat=L):
            count += 1
            good_dp &= chi_dp(w) == formula(w)
            good_arc &= arc_ok(w)
        check(good_dp, f"k = {k}: chi = max(s(w), ceil(n/k)) by exact DP on all {count} vectors in {{0..{top}}}^{L}")
        check(good_arc, f"k = {k}: the arc colouring is proper with max(s(w), ceil(n/k)) colours on the same vectors")

    # Corollary 7.2, k = 3: s(w) <= 8 and at most 4n - 8 edges between bags force n <= 27
    bad = []
    for w in itertools.product(range(9), repeat=7):
        if s_of(w) <= 8 and sum(w) >= 28:
            cross = sum(w[i] * w[(i + 1) % 7] for i in range(7))
            if cross <= 4 * sum(w) - 8:
                bad.append(w)
    check(not bad, "k = 3: no w with s(w) <= 8 and n >= 28 has at most 4n - 8 edges between bags")
    # k = 4: s(w) <= 8 gives n <= 36 <= 9k
    check(all(-(-(4 * (2 * k + 1)) // k) <= 9 for k in range(4, 200)), "k >= 4: ceil((8k+4)/k) <= 9")

    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
