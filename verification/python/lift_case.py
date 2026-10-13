# lift_case.py W base.cnf out.cnf MODE
#
# Adds to the formula Phi(W) written by biplanar-dump the consequences of Lemma (winding lift):
# map each vertex to its bag in Z_5. A layer either lifts (every cycle of the layer has winding 0,
# so there are sheets s(v) in 0..4 with s(u) = s(v) on same-bag edges and on edges between bags j and
# j+1 < 5, and s(v) = s(u) + 1 on edges from bag 4 to bag 0), or it has at most 3n - 10 edges and its
# inter-bag part has at most 2n - 5 edges. MODE fixes which layers lift: LL, LN (layer 0 lifts,
# layer 1 does not; NL is the same case with the layers exchanged) or NN.
# Also added: the planar counting bounds on every union of bags (3s - 6 edges, 2s - 4 inter-bag
# edges) and, from the edge totals, the matching lower bounds on each layer.
import sys, itertools
from pysat.card import CardEnc, EncType

w = [int(t) for t in sys.argv[1].split(',')]; K = len(w); mode = sys.argv[4]
assert K == 5 and mode in ('LL', 'LN', 'NN')
bag = [i for i, k in enumerate(w) for _ in range(k)]; n = len(bag)

def lay(l, a, b):
    if a > b: a, b = b, a
    return 6 * n * n + (l * n + a) * n + b + 1

E = [(a, b) for a, b in itertools.combinations(range(n), 2) if (bag[a] - bag[b]) % K in (0, 1, K - 1)]
EH = [(a, b) for a, b in E if bag[a] != bag[b]]
hdr = None; cls = []
with open(sys.argv[2]) as f:
    for line in f:
        if line.startswith('p'): hdr = line.split(); continue
        if line.startswith('c'): continue
        cls.append(line)
top = int(hdr[2]); out = []

def new():
    global top; top += 1; return top

def atmost(lits, k, guard=None):
    global top
    if len(lits) <= k: return
    enc = CardEnc.atmost(lits=lits, bound=k, top_id=top, encoding=EncType.totalizer)
    top = max(top, enc.nv)
    out.extend(([guard] + c) if guard else c for c in enc.clauses)

def atleast(lits, k):
    global top
    if k <= 0: return
    enc = CardEnc.atleast(lits=lits, bound=k, top_id=top, encoding=EncType.totalizer)
    top = max(top, enc.nv); out.extend(enc.clauses)

# planar counting bounds on unions of bags
for mask in range(1, 32):
    Sset = {v for v in range(n) if mask >> bag[v] & 1}
    if len(Sset) < 3: continue
    for l in (0, 1):
        atmost([lay(l, a, b) for a, b in E if a in Sset and b in Sset], 3 * len(Sset) - 6)
        atmost([lay(l, a, b) for a, b in EH if a in Sset and b in Sset], 2 * len(Sset) - 4)

NS = 5
lifts = {0: mode[0] == 'L', 1: mode[1] == 'L'}
for l in (0, 1):
    if lifts[l]:
        S = [[new() for k in range(NS)] for v in range(n)]
        for v in range(n):
            out.append(S[v])
            for a, b in itertools.combinations(range(NS), 2): out.append([-S[v][a], -S[v][b]])
        for a, b in E:
            x = lay(l, a, b)
            ba, bb = bag[a], bag[b]
            if ba == K - 1 and bb == 0: u, v, sh = a, b, 1
            elif bb == K - 1 and ba == 0: u, v, sh = b, a, 1
            else: u, v, sh = a, b, 0
            for k in range(NS):
                out.append([-x, -S[u][k], S[v][k + sh]] if k + sh < NS else [-x, -S[u][k]])
                out.append([-x, -S[v][k], S[u][k - sh]] if k - sh >= 0 else [-x, -S[v][k]])
    else:
        atmost([lay(l, a, b) for a, b in E], 3 * n - 10)
        atmost([lay(l, a, b) for a, b in EH], 2 * n - 5)

# lower bounds: every edge lies in a layer, so each layer carries what the other cannot
capG = {l: (3 * n - 6 if lifts[l] else 3 * n - 10) for l in (0, 1)}
capH = {l: (2 * n - 4 if lifts[l] else 2 * n - 5) for l in (0, 1)}
for l in (0, 1):
    atleast([lay(l, a, b) for a, b in E], len(E) - capG[1 - l])
    atleast([lay(l, a, b) for a, b in EH], len(EH) - capH[1 - l])

with open(sys.argv[3], 'w') as f:
    f.write('p cnf %d %d\n' % (top, len(cls) + len(out))); f.writelines(cls)
    for c in out: f.write(' '.join(map(str, c)) + ' 0\n')
print(sys.argv[1], mode, 'n', n, 'edges', len(E), 'inter', len(EH), 'vars', top, 'added', len(out))
