"""Independent geometric oracle for row-pair compatibility (p=17 or 7).
Two rows r,s are compatible iff the partial structure formed by the fixed points/lines and the point classes G_r,G_s
(lines restricted to these points; lines built as in plane.py, validated on the p=7 planes) satisfies
 (A) no two points lie on two common lines (partial linear space), and
 (B) every pair (G_r,X),(G_s,Y) lies on exactly one common line.
Compares with the C++ decisions dumped by `fast4 ... pairdump` (flags: legacy compat, new compatFull2).
usage: python -I oracle_pairs.py dumpfile [p]
"""
import sys, itertools, collections

def lines_of(p, th, rows):
    s = [[0]*p, list(range(p)), list(th)]
    lines = {}
    for k in range(3):
        lines[('L', k)] = set([('S', k, z) for z in range(p)] + [('P', c) for c in range(3) if c != k])
    for k in range(3):
        for w in range(p):
            L = {('P', k), ('S', k, w)}
            for i, (g, u1, u2) in enumerate(rows):
                u = (0, u1, u2)[k]
                L.add(('G', i, (w-u) % p))
            lines[('V', k, w)] = L
    for j in range(p):
        for y in range(p):
            L = set()
            for k in range(3):
                L.add(('S', k, (y-s[k][j]) % p))
            for i, (g, u1, u2) in enumerate(rows):
                for x in range(1, p):
                    if g[x-1] == j:
                        L.add(('G', i, (y-x) % p))
            lines[('H', j, y)] = L
    return lines

def oracle(p, th, r, s):
    lines = lines_of(p, th, [r, s])
    cnt = collections.Counter()
    for L in lines.values():
        for a, b in itertools.combinations(sorted(L), 2):
            cnt[(a, b)] += 1
    if any(v > 1 for v in cnt.values()):
        return False
    for X in range(p):
        for Y in range(p):
            if cnt[(('G', 0, X), ('G', 1, Y))] != 1:
                return False
    return True

def main():
    fn = sys.argv[1]; p = int(sys.argv[2]) if len(sys.argv) > 2 else 17
    th = None; stats = collections.Counter(); bad = []
    for line in open(fn):
        t = line.split()
        if not t: continue
        if t[0] == 'NET':
            th = list(map(int, t[1:1+p]))
        elif t[0] == 'PAIR':
            stg, c1, c2 = int(t[1]), int(t[2]), int(t[3])
            v = list(map(int, t[4:]))
            n = p-1
            r = (v[:n], v[n], v[n+1]); s = (v[n+2:2*n+2], v[2*n+2], v[2*n+3])
            o = oracle(p, th, r, s)
            stats[(stg, c1, c2, int(o))] += 1
            if not (c1 == c2 == int(o)):
                bad.append((stg, c1, c2, int(o)))
    print(fn, 'net', th)
    for k in sorted(stats): print('  stage %d legacy %d new %d oracle %d : %d pairs' % (k + (stats[k],)))
    print('  DISAGREEMENTS:', len(bad), bad[:5])

main()
