"""Independent checks of the finite parts of the paper.

  * the 26 vectors with n(w) = 17 and the 36 with n(w) = 16 (s(w) <= 8), up to the dihedral action
    (Lemma 2.2), against verification/data/cands17.txt and wits16.txt;
  * Lemma 2.1 by enumeration: every positive w with s(w) <= 8 lies above a 17-vertex vector when
    n(w) >= 17 and below a 16-vertex vector when n(w) <= 16;
  * Proposition 2.3: for each of the 36 graphs, the two layers cover all edges and each layer is a
    plane straight-line drawing (exact integer tests), and each layer is planar by networkx's own test;
  * the 8-colourings of the 36 graphs;
  * Trivedi's chromatic number formula on all 62 graphs, by exhaustive search.

Run: python3 verification/python/verify_c5.py   (needs networkx)
"""
import itertools
import json
import os
import sys

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data")


def symmetries(w):
    out = []
    for r in range(5):
        x = list(w[r:]) + list(w[:r])
        out.append(tuple(x))
        out.append(tuple(reversed(x)))
    return out


def canon(w):
    return min(symmetries(w))


def s_of(w):
    return max(w[i] + w[(i + 1) % 5] for i in range(5))


def bags(w):
    return [i for i, x in enumerate(w) for _ in range(x)]


def edges(w):
    b = bags(w)
    n = len(b)
    return [(u, v) for u in range(n) for v in range(u + 1, n) if (b[u] - b[v]) % 5 in (0, 1, 4)]


def read_vectors(name):
    vs = []
    for line in open(os.path.join(DATA, name)):
        line = line.strip()
        if line and not line.startswith("#"):
            vs.append(tuple(int(t) for t in line.split()))
    return vs


def orient(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def on_seg(a, b, p):
    return (orient(a, b, p) == 0 and min(a[0], b[0]) <= p[0] <= max(a[0], b[0])
            and min(a[1], b[1]) <= p[1] <= max(a[1], b[1]))


def segs_meet(a, b, c, d):
    d1, d2, d3, d4 = orient(c, d, a), orient(c, d, b), orient(a, b, c), orient(a, b, d)
    if ((d1 > 0 > d2) or (d1 < 0 < d2)) and ((d3 > 0 > d4) or (d3 < 0 < d4)):
        return True
    return on_seg(c, d, a) or on_seg(c, d, b) or on_seg(a, b, c) or on_seg(a, b, d)


def is_plane_drawing(n, E, P):
    if len(P) != n or len(set(map(tuple, P))) != n:
        return False
    for u, v in E:
        for x in range(n):
            if x not in (u, v) and on_seg(P[u], P[v], P[x]):
                return False
    for (u, v), (s, t) in itertools.combinations(E, 2):
        if len({u, v, s, t}) == 4 and segs_meet(P[u], P[v], P[s], P[t]):
            return False
    return True


def chromatic_number(w):
    G = nx.Graph()
    G.add_nodes_from(range(sum(w)))
    G.add_edges_from(edges(w))
    order = sorted(G.nodes, key=lambda v: -G.degree(v))

    def colourable(k):
        col = {}

        def rec(i):
            if i == len(order):
                return True
            v = order[i]
            used = {col[u] for u in G[v] if u in col}
            for c in range(min(k, max(col.values(), default=-1) + 2)):
                if c not in used:
                    col[v] = c
                    if rec(i + 1):
                        return True
                    del col[v]
            return False

        return rec(0)

    k = 1
    while not colourable(k):
        k += 1
    return k


def main():
    ok = True

    def check(cond, msg):
        nonlocal ok
        print(("ok   " if cond else "FAIL ") + msg)
        ok = ok and cond

    cands17 = read_vectors("cands17.txt")
    wits16 = read_vectors("wits16.txt")
    allw = [w for w in itertools.product(range(1, 8), repeat=5) if s_of(w) <= 8]
    c17 = sorted({canon(w) for w in allw if sum(w) == 17})
    c16 = sorted({canon(w) for w in allw if sum(w) == 16})
    check(len(c17) == 26 and sorted(map(canon, cands17)) == c17, "26 classes with n=17, s<=8 match cands17.txt")
    check(len(c16) == 36 and sorted(map(canon, wits16)) == c16, "36 classes with n=16, s<=8 match wits16.txt")
    big = [w for w in itertools.product(range(1, 10), repeat=5) if s_of(w) <= 8]
    check(all(max(w) <= 7 for w in big), "positive w with s(w)<=8 have all entries at most 7")

    le = lambda a, b: all(x <= y for x, y in zip(a, b))
    up = all(any(le(c, g) for c in cands17 for g in symmetries(w)) for w in allw if sum(w) >= 17)
    down = all(any(le(g, c) for c in wits16 for g in symmetries(w)) for w in allw if sum(w) <= 16)
    check(up, "every w with n(w)>=17, s(w)<=8 lies above a member of cands17 (Lemma 2.1a)")
    check(down, "every w with n(w)<=16, s(w)<=8 lies below a member of wits16 (Lemma 2.1b)")

    W = json.load(open(os.path.join(DATA, "witnesses16.json")))
    check(len(W) == 36 and sorted(canon(tuple(d["w"])) for d in W.values()) == c16, "witness file covers the 36 vectors")
    good_draw = good_nx = good_cov = good_col = True
    for tag, d in W.items():
        w = tuple(d["w"])
        n = sum(w)
        E = set(edges(w))
        L1 = [tuple(e) for e in d["layer1"]]
        L2 = [tuple(e) for e in d["layer2"]]
        good_cov &= E <= set(L1) | set(L2) and set(L1) | set(L2) <= E
        for L, P in ((L1, d["pos1"]), (L2, d["pos2"])):
            good_draw &= is_plane_drawing(n, L, P)
            G = nx.Graph()
            G.add_nodes_from(range(n))
            G.add_edges_from(L)
            good_nx &= nx.check_planarity(G)[0]
        col = d["colouring"]
        good_col &= len(col) == n and all(0 <= c < 8 for c in col) and all(col[u] != col[v] for u, v in E)
    check(good_cov, "the two layers of each witness are exactly the edge set of C5[w]")
    check(good_draw, "every layer is a plane straight-line drawing (exact integer tests)")
    check(good_nx, "every layer is planar by networkx.check_planarity")
    check(good_col, "every witness colouring is a proper 8-colouring")

    formula = True
    for w in cands17 + wits16:
        chi = chromatic_number(w)
        formula &= chi == max(s_of(w), -(-sum(w) // 2))
    check(formula, "chi(C5[w]) = max(s(w), ceil(n/2)) for the 62 vectors (exhaustive colouring)")

    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
