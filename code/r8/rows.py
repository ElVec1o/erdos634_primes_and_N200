import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
"""Layouts of D. Paliy's announced rows (research/group2-f4, group2-trapezoids/BALANCED_F4.md, group2-nested-corners, best-move-oct7/hexagon/F3_SMALL_A.md,
group2-gamma-corners), decoded from the prose proofs and implemented here in the Eisenstein framework eis.py.  All m = 1."""
from eis import *
from fractions import Fraction as Fr
def Z(a,b): return (Fr(a),Fr(b))
def F4_small(a,b,c):
    """F4, a<b.  returns layout, target (O,D,C)"""
    assert c*c==a*a+a*b+b*b and a<b
    u=Z(b,a); O=P(0); A=P(b*c); B=sc(c,u); D=P((a+b)*c); C=sc(Fr(b*(2*a+b),c),u); E=add(A,sc(Fr(a*b,c),u)); F=add(A,sc(b*c,RHO))
    L=[tri(O,A,B,c),tri(A,D,E,a),tri(D,C,E,a),grid(F,sc(Fr(1,b),sub(A,F)),sc(Fr(1,b),sub(E,F)),[(b-a,0),(b,0),(0,b),(0,b-a)])]
    return L,(O,D,C),dict(O=O,A=A,B=B,D=D,C=C,E=E,F=F)
def in_semigroup(r,gens):
    a,b,c=gens
    for s in range(r//c+1):
        rr=r-s*c
        for A in range(rr//a+1):
            if (rr-A*a)%b==0: return A,(rr-A*a)//b,s
    return None
def Qcorner(a,b,c):
    """nested-corner quadrilateral Q=[na, c^2, ac z, nc z], m=k=1; needs bc-a^2 in <a,b,c>.  returns layout, (O,A0,B0,C) or None"""
    assert c*c==a*a+a*b+b*b and a>b
    r0=b*c-a*a
    if r0<0: return None
    sol=in_semigroup(r0,(a,b,c))
    if sol is None: return None
    A,B,s=sol; n=a-b; k=1; q=n+s; r=A*a+B*b
    z=(Fr(a,c),Fr(b,c))
    F=P(0); A0=P(c*c); B0=sc(a*c,z); E=P(a*k*c); C=sc(q*c,z); D=add(E,C); U=add(C,sc(a*a*k,z)); V=add(E,sc(a*(c-a*k),z))
    L=[grid(F,P(a),Z(a,b),[(n,0),(k*c,0),(k*c,q),(0,q),(0,n)]),tri(C,D,U,a*k),tri(E,A0,V,c-a*k)]
    if r>0:
        w0=sub(P(c),sc(a,z))   # length b
        assert norm(w0)==b*b
        if A>0: L.append(par(U,sc(a,z),w0,A,a*k,(a,b,c)))
        if B>0: L.append(par(add(U,sc(a*A,z)),sc(b,z),sc(Fr(a,b),w0),B,b*k,(a,b,c)))
    O=sc(n*a,P(1)) if False else P(n*a)
    return L,(O,A0,B0,sc(n*c,z)),dict(A=A,B=B,s=s,q=q,r=r)
def F4_rev(a,b,c):
    """reversed F4 (a>b): N=(2a+b)(a+b). returns layout, target"""
    Qr=Qcorner(a,b,c)
    if Qr is None: return None
    LQ,(O,A0,B0,C),info=Qr
    u=Z(b,a); al=sc(Fr(-1,c),u); be=sc(c,u)
    L=tfl(LQ,al,be)
    # macro points of F4 notation
    O0=P(0); A0_=P(b*c); Fo=add(A0_,sc(b*c,RHO)); C0=sc(Fr(b*(2*a+b),c),u); D0=P((a+b)*c); E0=add(A0_,sc(Fr(a*b,c),u))
    f=lambda w:add(mul(al,w),be)
    assert (f(O),f(A0),f(B0),f(C))==(C0,O0,A0_,Fo),(f(O),f(A0),f(B0),f(C),C0,O0,A0_,Fo)
    L+= [tri(A0_,D0,E0,a),tri(D0,C0,E0,a),tri(Fo,A0_,E0,b)]
    return L,(O0,D0,C0)
def F2_(a,b,c):
    """F2 N=(a+2b)(2a+b), a>b. returns layout, target XYT, extras for F3"""
    Qr=Qcorner(a,b,c)
    if Qr is None: return None
    LQ,(O,A0,B0,C),info=Qr
    S=c*c; h=a+2*b; Zz=Z(a,b)
    X=P(0); Y=P(S); I=sc(a,Zz); J=mul(Zz,Zz); T=sc(Fr(a*h,S),J)
    v=(Fr(-(a+b)),Fr(a)); v2=sc(Fr(1,S),mul(v,v))
    Rf=lambda w:add(P(S),mul(v2,conj(sub(w,P(S)))))
    assert (Rf(A0),Rf(B0),Rf(C),Rf(O))==(Y,I,J,T),(Rf(A0),Rf(B0),Rf(C),Rf(O),Y,I,J,T)
    L=[tri(X,Y,I,c),tri(X,I,J,c)]
    for g in LQ:
        L.append(dict(o=Rf(g['o']),u=mul(v2,conj(g['u'])),v=mul(v2,conj(g['v'])),poly=g['poly']))
    return L,(X,Y,T),dict(T=T,Zz=Zz,S=S,h=h)
def F3_nested(a,b,c):
    r=F2_(a,b,c)
    if r is None: return None
    L,(X,Y,T),d=r
    Zz=d['Zz']; S=d['S']; h=d['h']
    K=sc(Fr(h,S),mul(Zz,mul(Zz,Zz)))
    L=L+[tri(X,T,K,h)]
    return L,(X,Y,K)
def F3_gamma(a,b,c):
    """F3 ordered, b<a<=2b: N=3(a+b)(a+2b)"""
    assert c*c==a*a+a*b+b*b and b<a<=2*b
    S=c*c; h=a+2*b; d=a-b; Zz=Z(a,b)
    X=P(0); Y=P(S); I=sc(a,Zz); J=mul(Zz,Zz); T=sc(Fr(a*h,S),J); K=sc(Fr(h,S),mul(Zz,mul(Zz,Zz))); Jp=sc(a,mul(add(P(1),RHO),Zz))
    L=[tri(X,Y,I,c),tri(Y,I,Jp,c),tri(X,I,J,c)]
    u=sc(Fr(1,h),sub(X,T)); v=sc(Fr(1,h),sub(K,T))
    L.append(grid(T,u,v,[(b,0),(h,0),(b,h-b)]))
    L.append(grid(T,u,v,[(0,a),(b,a),(b,h-b),(0,h)]))
    u2=sc(Fr(b,a),u); v2=sc(Fr(a,b),v)
    L.append(grid(T,u2,v2,[(d,0),(a,0),(a,b),(0,b),(0,d)]))
    return L,(X,Y,K)
def trapezoid(a,b,c,d_extra=None):
    """ideal trapezoid T(K-b d, ab) of the 6-region construction (tile (a,b,c) as in the proof, a,b not nec ordered). Returns layout in coordinates
    translated by (-bd,0): vertices (0,0),(c^2-bd,0),(K-bd,ab),(0,ab)."""
    d=a+b-c; K=a*a+b*b; Lg=a*b
    Fp=P(0); Ap=P(c*c); Bp=P(b*b,a*b); Cp=P(b*d,a*d); Ep=P(b*c); Dp=P(b*(c+d),a*d); z=(Fr(b,c),Fr(a,c))
    Qp=add(Cp,sc(b*b,z)); Rp=add(Ep,sc(b*(c-b),z)); Hp=P(b*d,a*b); Jp=P(K,a*b)
    U_=P(b); V_=P(b,a)
    L=[grid(Fp,U_,V_,[(d,0),(c,0),(c,d),(0,d)]),tri(Cp,Dp,Qp,b),tri(Ep,Ap,Rp,c-b)]
    # parallelogram Q B R D: from Q, side Q->B (length a d, direction z) in cells of a*z, Q->D (length ab) in cells of b*w
    assert norm(sub(Bp,Qp))==(a*d)**2 and norm(sub(Dp,Qp))==(a*b)**2
    p=sc(Fr(a,1),z); w=sc(Fr(1,a),sub(Dp,Qp))      # w: unit step of length b along Q->D? |D-Q|=ab so (D-Q)/a has length b
    assert norm(p)==a*a and norm(w)==b*b
    L.append(par(Qp,p,w,d,a,(a,b,c)))
    L+=[tri(Cp,Bp,Hp,b-d),tri(Bp,Ap,Jp,a)]
    sh=P(-b*d)
    L=[dict(o=add(g['o'],sh),u=g['u'],v=g['v'],poly=g['poly']) for g in L]
    return L,dict(x=K-b*d,Lg=Lg)
def F3_small(a,b,c):
    """F3 ordered, a<b: N=3(a+b)(a+2b)"""
    assert c*c==a*a+a*b+b*b and a<b
    A=a*b; B=b*b
    X=P(-a*a); Y=P(2*A,-2*A-B); K=P(2*A,A+2*B)
    Pp=P(A,-A); E=P(2*A,-2*A); Lp=P(A,A+B); R=P(2*A,A+B)
    LF4,(O,Dd,C),_=F4_small(a,b,c)
    zz=(Fr(a,c),Fr(b,c)); al=sc(-1,zz); be=Lp
    f=lambda w:add(mul(al,w),be)
    assert (f(O),f(Dd),f(C))==(Lp,X,Pp),(f(O),f(Dd),f(C),Lp,X,Pp)
    L=[tri(X,Y,Pp,c),tri(Y,Pp,E,b),tri(Lp,R,K,b)]+tfl(LF4,al,be)
    # trapezoid T(2ab+b^2, ab): base seed with roles swapped (a_=b,b_=a): T(K-a d, ab); then parallelogram of width a(3b-c)
    d=a+b-c
    LT,info=trapezoid(b,a,c)
    x=info['x']; assert x==a*a+b*b-a*d
    M=3*b-c
    assert x+a*M==2*A+B and M>0
    ext=par(P(x+A),P(a),sc(b,(Fr(-1),Fr(1))),M,a,(a,b,c))
    LT=LT+[ext]
    rho=RHO
    L+=tfl(LT,rho,E)
    return L,(X,Y,K)
