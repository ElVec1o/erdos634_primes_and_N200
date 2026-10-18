#!/usr/bin/env python3
"""fastverify.py FILE.exact a b c X1 Y1 X2 Y2 X3 Y3  -- same four exact checks as code/analysis/verify_tiling_exact.py (frame (X,Y*sqrt3)),
with disjointness tested only for bounding-box-overlapping pairs (grid hash); all arithmetic exact (integers after common denominator)."""
import sys
from fractions import Fraction as F
from math import gcd
def main():
    path=sys.argv[1]; a,b,c=(int(x) for x in sys.argv[2:5]); T=[F(x) for x in sys.argv[5:11]]; Dn=3
    tgt=[(T[0],T[1]),(T[2],T[3]),(T[4],T[5])]
    rows=[]
    for ln in open(path):
        if ln.startswith('#') or not ln.strip(): continue
        w=[F(x) for x in ln.split()]; rows.append([(w[0],w[1]),(w[2],w[3]),(w[4],w[5])])
    L=1
    for t in rows+[tgt]:
        for p in t:
            for v in p: L=L*v.denominator//gcd(L,v.denominator)
    def I(p): return (int(p[0]*L),int(p[1]*L))
    tiles=[[I(p) for p in t] for t in rows]; tg=[I(p) for p in tgt]
    def cr(p,q,r): return (q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0])
    def d2(p,q): return (p[0]-q[0])**2+Dn*(p[1]-q[1])**2
    if cr(*tg)<0: tg[1],tg[2]=tg[2],tg[1]
    for t in tiles:
        assert cr(*t)!=0
        if cr(*t)<0: t[1],t[2]=t[2],t[1]
    want=sorted([a*a*L*L,b*b*L*L,c*c*L*L])
    ok1=all(sorted([d2(t[0],t[1]),d2(t[1],t[2]),d2(t[0],t[2])])==want for t in tiles)
    ok2=all(cr(tg[i],tg[(i+1)%3],p)>=0 for t in tiles for p in t for i in range(3))
    def disj(A,B):
        for (P,Q) in ((A,B),(B,A)):
            for i in range(3):
                if all(cr(P[i],P[(i+1)%3],q)<=0 for q in Q): return True
        return False
    n=len(tiles)
    # bounding boxes in (x, y) integer frame coordinates; hash into cells of size ~ longest side
    import math
    cs=max(1,int(c*L))   # cell size in x; y in frame is scaled by sqrt3 in length -> use same number (bboxes overlap test is on raw coords, valid)
    cell={}
    bbs=[]
    for i,t in enumerate(tiles):
        x0=min(p[0] for p in t); x1=max(p[0] for p in t); y0=min(p[1] for p in t); y1=max(p[1] for p in t)
        bbs.append((x0,x1,y0,y1))
        for gx in range(x0//cs,x1//cs+1):
            for gy in range(y0//cs,y1//cs+1): cell.setdefault((gx,gy),[]).append(i)
    seen=set(); bad=0
    for lst in cell.values():
        for ii in range(len(lst)):
            i=lst[ii]
            for jj in range(ii+1,len(lst)):
                j=lst[jj]
                key=(i,j) if i<j else (j,i)
                if key in seen: continue
                seen.add(key)
                A,B=bbs[i],bbs[j]
                if A[1]<=B[0] or B[1]<=A[0] or A[3]<=B[2] or B[3]<=A[2]: continue
                if not disj(tiles[i],tiles[j]): bad+=1
    area2=sum(cr(*t) for t in tiles)
    ok4=area2==cr(*tg) and len({cr(*t) for t in tiles})==1
    print(f"tiles={n} congruent={ok1} inside={ok2} disjoint={bad==0} (bad pairs: {bad}; pairs tested: {len(seen)}) area={ok4}")
    sys.exit(0 if (ok1 and ok2 and bad==0 and ok4) else 1)
main()
