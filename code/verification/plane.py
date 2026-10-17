import itertools
def build(p,th,rows):
    """rows: list of (g,u1,u2), g[x-1]=column(alpha). returns point list and line list as incidence sets."""
    n=len(rows)
    # points: ('P',c),('S',k,z),('G',i,X); lines: ('L',k),('V',k,w),('H',j,y)
    s=[[0]*p,[a for a in range(p)],[th[a] for a in range(p)]]  # s[k][column j=alpha]
    lines={}
    for k in range(3): lines[('L',k)]=set([('S',k,z) for z in range(p)]+[('P',c) for c in range(3) if c!=k])
    for k in range(3):
        for w in range(p):
            L={('P',k),('S',k,w)}
            for i,(g,u1,u2) in enumerate(rows):
                u=(0,u1,u2)[k]
                L.add(('G',i,(w-u)%p))
            lines[('V',k,w)]=L
    for j in range(p):
        for y in range(p):
            L=set()
            for k in range(3): L.add(('S',k,(y-s[k][j])%p))
            for i,(g,u1,u2) in enumerate(rows):
                for x in range(1,p):
                    if g[x-1]==j: L.add(('G',i,(y-x)%p))
            lines[('H',j,y)]=L
    return lines
def check(p,lines):
    pts=set(); 
    for L in lines.values(): pts|=L
    n=p+1
    if len(pts)!=n*n+n+1 or len(lines)!=n*n+n+1: return 'count',len(pts),len(lines)
    if any(len(L)!=n+1 for L in lines.values()): return 'linesize',sorted({len(L) for L in lines.values()})
    cnt={}
    for L in lines.values():
        for a,b in itertools.combinations(sorted(L),2): cnt[(a,b)]=cnt.get((a,b),0)+1
    if len(cnt)!=len(pts)*(len(pts)-1)//2 or set(cnt.values())!={1}: return 'pairs',len(cnt),set(cnt.values())
    return 'PLANE'
