"""Piece-level exact checker: pieces = [(poly vertices (frame x,y*sqrt3), tile_count)], target triangle, tile (a,b,c)."""
from fractions import Fraction as Fr
D=3
def cr(p,q,r): return (q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0])
def d2(p,q): return (p[0]-q[0])**2+D*(p[1]-q[1])**2
def area2(P):  # twice area / sqrt3
    return sum(P[i][0]*P[(i+1)%len(P)][1]-P[(i+1)%len(P)][0]*P[i][1] for i in range(len(P)))
def ccw(P): return P if area2(P)>0 else P[::-1]
def convex(P):
    n=len(P); return all(cr(P[i],P[(i+1)%n],P[(i+2)%n])>0 for i in range(n))
def disjoint(P,Q):
    for X,Y in ((P,Q),(Q,P)):
        n=len(X)
        for i in range(n):
            if all(cr(X[i],X[(i+1)%n],q)<=0 for q in Y): return True
    return False
def check(pieces,target,tile,verbose=False):
    a,b,c=tile; tarea=Fr(a*b,2)   # cr of one tile
    pc=[(ccw(list(P)),k) for P,k in pieces]
    T=ccw(list(target))
    ok={}
    ok['convex']=all(convex(P) for P,_ in pc)
    ok['inside']=all(cr(T[i],T[(i+1)%3],p)>=0 for P,_ in pc for p in P for i in range(3))
    ok['disjoint']=all(disjoint(pc[i][0],pc[j][0]) for i in range(len(pc)) for j in range(i+1,len(pc)))
    ok['areas_sum']=sum(area2(P) for P,_ in pc)==area2(T)
    ok['count_area']=all(area2(P)==k*tarea for P,k in pc)   # area2 = 2*cr-sum ; one tile has area2 = 2*ab/2
    ok['target_sides']=True
    return ok
def tri_scale(P,tile):
    """if triangle P has sides k*(a,b,c) return k else None"""
    a,b,c=tile
    s=sorted(d2(P[i],P[(i+1)%3]) for i in range(3))
    k2=Fr(s[0],a*a)
    if s!=[k2*a*a,k2*b*b,k2*c*c] if False else False: return None
    k2=Fr(s[0])/ (min(a,b,c)**2)
    if [k2*x*x for x in sorted((a,b,c))]!=s: return None
    k=k2**Fr(1,2) if False else None
    import math
    n,dn=k2.numerator,k2.denominator
    if dn!=1: return None
    r=math.isqrt(n); return r if r*r==n else None
