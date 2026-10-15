# tricert.py Ta Tb Tc a b c -> certgenm arguments for the target with |P0P1| = Ta, |P1P2| = Tb, |P0P2| = Tc
# (the mrv2 orientation `o=[Ta Tb Tc]`), P0 = (0,0), P1 = (Ta,0); tile sides a b c.
import sys
from fractions import Fraction as F
from math import isqrt
Ta,Tb,Tc,a,b,c=map(int,sys.argv[1:7])
def sqfree(n):
    d=1;p=2
    while p*p<=n:
        k=0
        while n%p==0: n//=p;k+=1
        if k%2: d*=p
        p+=1
    return d*n
x=F(Ta*Ta+Tc*Tc-Tb*Tb,2*Ta); y2=F(Tc*Tc)-x*x
Dn=sqfree(y2.numerator*y2.denominator)
def rt(q):
    q=q/Dn; n,d=q.numerator,q.denominator
    assert isqrt(n)**2==n and isqrt(d)**2==d,(q,Dn); return F(isqrt(n),isqrt(d))
y=rt(y2)
x3=F(a*a+c*c-b*b,2*a); rt(F(c*c)-x3*x3)   # the tile lives in the same field
print(Dn, f'"0,0; {Ta},0; {x},{y}"', f'"{a} {b} {c}"')
