import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import sys,json
from rows import *
def target_ok(T,sides,tile):
    a,b,c=tile; s=sorted([norm(sub(T[0],T[1])),norm(sub(T[1],T[2])),norm(sub(T[0],T[2]))])
    return s==sorted(x*x for x in sides)
def build(row,a,b,c):
    if row=='F4a<b': L,T,_=F4_small(a,b,c); sides=(a*c,b*(2*a+b),c*(a+b)); N=(2*a+b)*(a+b)
    elif row=='F4rev': r=F4_rev(a,b,c); L,T=r; sides=(a*c,b*(2*a+b),c*(a+b)); N=(2*a+b)*(a+b)
    elif row=='F2': r=F2_(a,b,c); L,T,_=r; sides=(a*(a+2*b),b*(2*a+b),c*c); N=(a+2*b)*(2*a+b)
    elif row=='F3ord':
        if a<b: L,T=F3_small(a,b,c)
        elif a<=2*b: L,T=F3_gamma(a,b,c)
        else: raise SystemExit('a>2b mixed corner not implemented')
        sides=(c*c,c*(a+2*b),3*b*(a+b)); N=3*(a+b)*(a+2*b)
    return L,T,sides,N
if __name__=='__main__':
    row=sys.argv[1]; a,b,c=map(int,sys.argv[2:5]); out=sys.argv[5] if len(sys.argv)>5 else None
    L,T,sides,N=build(row,a,b,c)
    print(row,(a,b,c),'N=',N,'sides ok',target_ok(T,sides,(a,b,c)),'prims',len(L))
    print(check(L,T,(a,b,c),N))
    if out:
        tl=tiles_all(L); assert len(tl)==N
        write_exact(out,tl,"%s (%d,%d,%d) N=%d Paliy layout, decoded here"%(row,a,b,c,N))
        t=[frame(p) for p in T]
        print("python3 -I code/r8/fastverify.py %s %d %d %d %s"%(out,a,b,c,' '.join("%s %s"%q for q in t)))
