"""tree.py: complete a march_cu cube list to the leaves of a decision tree, and join leaf proofs.

  python3 tree.py leaves ICNF OUT        write every leaf (march cubes plus refuted branches) to OUT
  python3 tree.py join LEAVES FINALS NEXT   print LRAT lines deriving the empty clause from the clauses
                                           "not leaf" whose ids are listed in FINALS (one per leaf, in order)
"""
import sys


def build(cubes, d, out):
    # all cubes share the prefix cubes[0][:d]
    if len(cubes) == 1 and len(cubes[0]) == d:
        out.append(cubes[0])
        return
    if any(len(c) == d for c in cubes):
        raise SystemExit("a cube is a prefix of another")
    v = abs(cubes[0][d])
    if any(abs(c[d]) != v for c in cubes):
        raise SystemExit("cubes do not form a tree at depth %d" % d)
    pre = cubes[0][:d]
    for lit in (v, -v):
        part = [c for c in cubes if c[d] == lit]
        if part:
            build(part, d + 1, out)
        else:
            out.append(pre + [lit])


def leaves(icnf, outp):
    cubes = []
    for line in open(icnf):
        t = line.split()
        if t and t[0] == 'a':
            cubes.append([int(x) for x in t[1:-1]])
    out = []
    build(cubes, 0, out)
    with open(outp, 'w') as f:
        for c in out:
            f.write(' '.join(map(str, c)) + ' 0\n')
    print(len(cubes), 'cubes,', len(out) - len(cubes), 'refuted branches added,', len(out), 'leaves')


def join(leavesf, finalsf, nxt):
    L = [tuple(int(x) for x in line.split()[:-1]) for line in open(leavesf)]
    F = [int(line.split()[0]) for line in open(finalsf)]
    assert len(L) == len(F)
    ids = dict(zip(L, F))
    nxt = int(nxt)
    out = sys.stdout

    def node(pre):
        nonlocal nxt
        if pre in ids:
            return ids[pre]
        kids = [k for k in ids if len(k) > len(pre) and k[:len(pre)] == pre]
        lit = kids[0][len(pre)]
        a = node(pre + (abs(lit),))
        b = node(pre + (-abs(lit),))
        cid = nxt
        nxt += 1
        out.write('%d %s0 %d %d 0\n' % (cid, ''.join('%d ' % -x for x in pre), a, b))
        out.write('%d d %d %d 0\n' % (cid, a, b))
        ids[pre] = cid
        return cid

    sys.setrecursionlimit(100000)
    node(())


if __name__ == '__main__':
    if sys.argv[1] == 'leaves':
        leaves(sys.argv[2], sys.argv[3])
    else:
        join(sys.argv[2], sys.argv[3], sys.argv[4])
