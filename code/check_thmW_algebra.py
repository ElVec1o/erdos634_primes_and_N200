#!/usr/bin/env python3
"""Computer-algebra check of the algebra of Theorem W (Paper W, Appendices A-B).

Verifies, with sympy and exact arithmetic:
  (1) the three identities eps^3 eta^2 = -1, a + b*omega = c*conj(eta), f*omega + e*eps = f*conj(eta);
  (2) P lies on AB and OP = OB; the shape identities of the six pieces;
  (3) the doubled signed area of piece i equals (e*b/2) * (number of tiles of piece i), and the
      six tile counts sum to M^2 (2 f^2 - e^2) identically;
  (4) every cross product used for containment and separation, factored into named positive factors;
  (5) with the canonical parameters (t,r,q) of Lemma C: the polynomial identities LB = s*Psi - kappa*(rho+e),
      d*M = f*s - rho, and (by exhaustive integer check, coprime pairs f <= FMAX, M < 5f) that the
      canonical parameters satisfy every sign condition exactly when M >= M*(e,f).
Usage: python3 check_thmW_algebra.py [FMAX] [--tex FILE]   (FMAX default 60; --tex writes the tables of Appendix B)
"""
import sys
from math import gcd
import sympy as sp

e, f, M, t, r, q = sp.symbols('e f M t r q', positive=True)
b = f**2 - e**2; c = f**2; a = e*f; kap = 2*f**2 - e**2
W2 = 4*f**2 - e**2          # w^2 ; the complex number x + i w y is written [x, y]

def mul(u, v): return (sp.expand(u[0]*v[0] - W2*u[1]*v[1]), sp.expand(u[0]*v[1] + u[1]*v[0]))
def add(*vs): return (sp.expand(sum(v[0] for v in vs)), sp.expand(sum(v[1] for v in vs)))
def sc(s, u): return (sp.expand(s*u[0]), sp.expand(s*u[1]))
def conj(u): return (u[0], -u[1])
def neg(u): return sc(-1, u)
def sub(u, v): return add(u, neg(v))
def cross(u, v): return sp.expand(u[0]*v[1] - u[1]*v[0])      # = (1/w) Im(conj(u) v)
def S(z): return tuple(sp.simplify(x) for x in z)

D = 2*f**2
eps = (kap/D, e/D)
eta = (e*(3*f**2 - e**2)/(2*f**3), b/(2*f**3))
om = S(conj(mul(eps, eta)))
etab = conj(eta)

ok = True
def check(name, cond):
    global ok
    print(('PASS  ' if cond else 'FAIL  ') + name)
    ok = ok and bool(cond)

check('|eps|=|eta|=1', sp.simplify(eps[0]**2 + W2*eps[1]**2) == 1 and sp.simplify(eta[0]**2 + W2*eta[1]**2) == 1)
check('eps^3 eta^2 = -1', S(mul(mul(mul(eps, eps), eps), mul(eta, eta))) == (-1, 0))
check('a + b omega = c conj(eta)', S(add((a, 0), sc(b, om))) == S(sc(c, etab)))
check('f omega + e eps = f conj(eta)', S(add(sc(f, om), sc(e, eps))) == S(sc(f, etab)))

O = (0, 0); B = (f*b*M, 0); A = sc(f**3*M, mul(eps, eps)); P = sc(f*b*M, eps)
P2 = sc(b*(f*M - e*t), eps); P3 = add(P, sc(-e*a*t, om)); Q = add(P, sc(f*b*t, om)); R = add(P, sc(f*b*r, om))
v = f*M - e*r; s1 = f*(r - t); s2 = f*r - e*M; x = f*t - e*q; u1 = f*q - e*t; u2 = f*q - e*r
Cp = sc(b*v, eps); Bp = (c*v, 0)
V2 = add(P, sc(f**3*t, etab), (-e*f**2*r, 0))
X4 = add(P, sc(-f*b*q, eps))
U1 = add(P, (-e*f**2*t, 0), sc(e*f**2*q, etab)); U2 = add(P, (-e*f**2*r, 0), sc(e*f**2*q, etab))
names = {'O': O, 'B': B, 'A': A, 'P': P, 'P2': P2, 'P3': P3, 'Q': Q, 'R': R, "B'": Bp, "C'": Cp, 'V2': V2, 'X4': X4, 'U1': U1, 'U2': U2}
def nm(z):
    for k, w in names.items():
        if w == z: return k

check('|OB|=|OP|=f b M, P on AB (A-P = -a f M omega, B-P = e b M omega)',
      S(sub(A, P)) == S(sc(-a*f*M, om)) and S(sub(B, P)) == S(sc(e*b*M, om))
      and sp.simplify((P[0]**2 + W2*P[1]**2) - (f*b*M)**2) == 0)
pcs = {0: [A, O, P2, P3], 1: [O, Bp, Cp], 2: [P3, P2, Q], 3: [B, Q, V2, Bp], 4: [Q, U1, U2, V2], 5: [U1, P2, Cp, U2]}
cnt = {0: f**2*M**2 - e**2*t**2, 1: v**2, 2: f**2*t**2, 3: s1**2 - s2**2, 4: 2*s1*x, 5: u1**2 - u2**2}
def area2(pl): return sp.expand(sum(cross(pl[j], pl[(j+1) % len(pl)]) for j in range(len(pl))))
for i in range(6):
    check('piece %d: doubled signed area = (e b / 2) * tiles' % i, sp.simplify(area2(pcs[i]) - e*b*cnt[i]/2) == 0)
check('tile counts sum to M^2 (2f^2-e^2)', sp.expand(sum(cnt.values()) - M**2*(2*f**2 - e**2)) == 0)
check('triangle OAB has doubled area (e b/2) M^2 (2f^2-e^2)', sp.simplify(area2([O, B, A]) - e*b*M**2*(2*f**2 - e**2)/2) == 0)
# shapes (Lemma A) as vector identities
check('A: P3-P = -e a t omega ; Q-P = f b t omega (so |P3Q| = c f t)', S(sub(P3, P)) == S(sc(-e*a*t, om)))
check('A: Q - V2 = a s1 (real)', S(sub(Q, V2)) == S((a*s1, 0)))
check('A: U1 - Q = -f^2 x conj(eta) = U2 - V2', S(sub(U1, Q)) == S(sc(-f**2*x, etab)) and S(sub(U2, V2)) == S(sc(-f**2*x, etab)))
check('A: P2 - X4 = b u1 eps ; |U1-X4|=c u1 ; |U1-P2| = a u1',
      S(sub(P2, X4)) == S(sc(b*u1, eps)))

# ---------------- cross-product tables -----------------
# named positive factors; (polynomial, label)
d = f - e
fac = [(r - t, 'C2'), (e*M - f*t, 'C3'), (f*r - e*M, 'C4'), (f*M - e*t, 'C3b'), (f*M - e*r, 'C5'), (f*q - e*r, 'C6'), (f*q - e*t, 'C6b'),
       (f*t - e*q, 'C7'), (f**2*t - e**2*r, 'C8'), (f*r - e*q, 'C9'), (M - q, 'C10'),
       (b*f*M - e*kap*t + f**3*q, 'LA'), (b*f*M - e*kap*r + f**3*q, 'LB'), (e*f*b*M - e**2*kap*r + f**4*t, 'LC'),
       (b*M + e*f*t, 'E1'), (e*f*M + b*t, 'E2'), (b*r + e**2*t, 'E3'),
       (e, 'e'), (f, 'f'), (M, 'M'), (t, 't'), (r, 'r'), (e + f, 'f+e'), (f - e, 'd'), (b, 'b'), (kap, '\\kappa')]
def label(g):
    for h, nme in fac:
        if sp.expand(g - h) == 0: return nme, 1
        if sp.expand(g + h) == 0: return nme, -1
    return None, 0

def decompose(expr):
    """expr = polynomial/rational; returns (sign, dict label->power, rational const) ; sign=0 if expr == 0"""
    expr = sp.together(expr)
    if sp.simplify(expr) == 0: return 0, {}, 1
    num, den = sp.fraction(expr)
    cst, fl = sp.factor_list(num)
    sign = 1 if cst > 0 else -1
    const = abs(cst)
    labs = {}
    for g, k in fl + [(h, -kk) for h, kk in sp.factor_list(den)[1]]:
        nme, sg = label(g)
        if nme is None:
            # try b and kappa products expressed as e^2-f^2 etc.
            if sp.expand(g - (e**2 - f**2)) == 0: nme, sg = 'b', -1
            elif sp.expand(g - (e**2 - 2*f**2)) == 0: nme, sg = '\\kappa', -1
            else: raise SystemExit('unnamed factor %s' % g)
        sign *= sg**k
        labs[nme] = labs.get(nme, 0) + k
    cden = sp.factor_list(den)[0]
    const = sp.Rational(const) / abs(cden)
    sign *= (1 if cden > 0 else -1)
    return sign, labs, const

def tex_name(k):
    import re
    m = re.fullmatch(r'([CLE])(\d*)(b?)', k)
    if k == 'f+e': return '(f{+}e)'
    if k in ('LA', 'LB', 'LC'): return '\\mathrm{L}_{%s}' % k[1]
    if m and m.group(2): return '%s_{%s}%s' % (m.group(1), m.group(2), "'" if m.group(3) else '')
    return k
def tv(z):
    return z.replace('P2', 'P_2').replace('P3', 'P_3').replace('U1', 'U_1').replace('U2', 'U_2').replace('V2', 'V_2')
def fmt(sign, labs, const):
    if sign == 0: return '0'
    s = '' if const == 1 else ('\\tfrac{%d}{%d}' % (const.p, const.q) if const.q != 1 else '%d' % const.p)
    for k in sorted(labs):
        p = labs[k]
        if p == 0: continue
        s += ('\\,' if s else '') + tex_name(k) + ('^{%d}' % p if p != 1 else '')
    return s or '1'

import random
vals = dict(e=2, f=5, M=3, t=1, r=2, q=1)
def edge_idx(i, a_, b_):
    pl = pcs[i]
    for k in range(len(pl)):
        if nm(pl[k]) == a_ and nm(pl[(k+1) % len(pl)]) == b_: return k
chosen = [(0, 1, 'O', 'P2'), (0, 2, 'P2', 'P3'), (0, 3, 'O', 'P2'), (0, 4, 'O', 'P2'), (0, 5, 'O', 'P2'), (1, 2, "B'", "C'"), (1, 3, "B'", "C'"),
          (1, 4, "B'", "C'"), (1, 5, "B'", "C'"), (2, 3, 'P2', 'Q'), (2, 4, 'P2', 'Q'), (2, 5, 'P2', 'Q'), (3, 4, 'Q', 'V2'), (3, 5, 'Q', 'V2'), (4, 5, 'U1', 'U2')]
sep_rows = []
used = set()
for (i, j, s_, e_) in chosen:
    k = edge_idx(i, s_, e_); pl = pcs[i]
    for z in pcs[j]:
        c_ = cross(sub(pl[(k+1) % len(pl)], pl[k]), sub(z, pl[k]))
        sg, labs, cst = decompose(-c_)          # separation needs -cross >= 0 (z on the right of the directed edge)
        assert sg >= 0, ('separation sign', i, j, nm(z), sg)
        sep_rows.append((i, j, s_, e_, nm(z), sg, labs, cst))
        used |= set(labs)
cont_rows = []
for i, pl in pcs.items():
    for z in pl:
        for (s_, e_) in [(O, B), (B, A), (A, O)]:
            c_ = cross(sub(e_, s_), sub(z, s_))     # inside CCW triangle: cross >= 0
            sg, labs, cst = decompose(c_)
            assert sg >= 0, ('containment sign', nm(z), nm(s_), nm(e_), sg)
            cont_rows.append((i, nm(z), nm(s_), nm(e_), sg, labs, cst))
            used |= set(labs)
# convexity / orientation: consecutive cross products of each piece
conv_rows = []
for i, pl in pcs.items():
    n = len(pl)
    for j in range(n):
        c_ = cross(sub(pl[(j+1) % n], pl[j]), sub(pl[(j+2) % n], pl[(j+1) % n]))
        sg, labs, cst = decompose(c_)
        assert sg > 0
        conv_rows.append((i, nm(pl[j]), sg, labs, cst))
        used |= set(labs)
where = {}
for (i, j, s_, e_, vz, sg, labs, cst) in sep_rows:
    for k in labs: where.setdefault(k, set()).add('sep %d|%d' % (i, j))
for (i, vz, s_, e_, sg, labs, cst) in cont_rows:
    for k in labs: where.setdefault(k, set()).add('cont %s' % vz)
for (i, vz, sg, labs, cst) in conv_rows:
    for k in labs: where.setdefault(k, set()).add('conv pi%d' % i)
if '--where' in sys.argv:
    for k in sorted(where): print('WHERE', k, sorted(where[k]))
print('PASS  every separation/containment/convexity cross product is (positive constant) x (named factors) with the right sign (up to the sign of the named factors)')
print('named non-trivial factors that occur:', sorted(u for u in used if u.startswith(('C', 'L', 'E'))))

# ---------------- canonical parameters -----------------
Psi = f**3 + 2*e*f**2 - e**2*f - e**3
LB = b*f*M - e*kap*r + f**3*q
FMAX = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 60
bad = 0; total = 0
for ff in range(4, FMAX + 1):
    for ee in range(2, ff - 1):
        if gcd(ee, ff) != 1: continue
        dd = ff - ee; bb = ff*ff - ee*ee; kk = 2*ff*ff - ee*ee; PP = ff**3 + 2*ee*ff*ff - ee*ee*ff - ee**3
        Mstar = max(-(-ff // ee), -(-ff // dd) + 1)
        for MM in range(1, 5*ff):
            n = (ee*MM)//ff; rho = ee*MM - ff*n; s = MM - n; dl = 1 if rho == 0 else 0
            tt = n - dl; rr = n + 1; qq = n
            conds = [rr - tt > 0, tt > 0, ee*MM - ff*tt > 0, ff*rr - ee*MM > 0, ff*MM - ee*rr > 0, ff*qq - ee*rr > 0, ff*qq - ee*tt > 0,
                     ff*tt - ee*qq > 0, ff**2*tt - ee*ee*rr > 0, ff*rr - ee*qq > 0, MM - qq > 0,
                     bb*ff*MM - ee*kk*tt + ff**3*qq > 0, bb*ff*MM - ee*kk*rr + ff**3*qq > 0, ee*ff*bb*MM - ee*ee*kk*rr + ff**4*tt > 0]
            assert bb*ff*MM - ee*kk*rr + ff**3*qq == s*PP - kk*(rho + ee) and dd*MM == ff*s - rho
            total += 1
            if all(conds) != (MM >= Mstar): bad += 1; print('MISMATCH', ee, ff, MM)
check('canonical parameters satisfy all %s sign conditions iff M >= M*(e,f) [%d triples, f<=%d]' % ('14', total, FMAX), bad == 0)

if '--tex' in sys.argv:
    path = sys.argv[sys.argv.index('--tex') + 1]
    with open(path, 'w') as fh:
        fh.write('%% generated by check_thmW_algebra.py; do not edit\n')
        fh.write('\\begin{longtable}{@{}llcp{6.4cm}@{}}\n\\toprule\n pair & edge line & vertex & $-$cross $=$ positive constant $\\times$\\\\\\midrule\\endhead\n')
        for (i, j, s_, e_, vz, sg, labs, cst) in sep_rows:
            if sg == 0: continue
            fh.write('$\\pi_%d|\\pi_%d$ & $%s%s$ & $%s$ & $%s$\\\\\n' % (i, j, tv(s_), tv(e_), tv(vz), fmt(sg, labs, cst)))
        fh.write('\\bottomrule\n\\end{longtable}\n')
    print('wrote', path)
    with open(path.replace('.tex', '_cont.tex'), 'w') as fh:
        fh.write('%% generated by check_thmW_algebra.py; do not edit\n')
        fh.write('\\begin{longtable}{@{}lcp{7cm}@{}}\n\\toprule\n vertex & side line of $OAB$ & cross product $=$ positive constant $\\times$\\\\\\midrule\\endhead\n')
        done = set()
        for (i, vz, s_, e_, sg, labs, cst) in cont_rows:
            if (vz, s_, e_) in done or sg == 0: continue
            done.add((vz, s_, e_))
            fh.write('$%s$ & $%s%s$ & $%s$\\\\\n' % (tv(vz), s_, e_, fmt(sg, labs, cst)))
        fh.write('\\bottomrule\n\\end{longtable}\n')
    with open(path.replace('.tex', '_conv.tex'), 'w') as fh:
        fh.write('%% generated by check_thmW_algebra.py; do not edit\n')
        fh.write('\\begin{longtable}{@{}lcp{7cm}@{}}\n\\toprule\n piece & vertex $X_j$ & turn $\\langle X_{j+1}-X_j,X_{j+2}-X_{j+1}\\rangle=$ positive constant $\\times$\\\\\\midrule\\endhead\n')
        for (i, vz, sg, labs, cst) in conv_rows:
            fh.write('$\\pi_%d$ & $%s$ & $%s$\\\\\n' % (i, tv(vz), fmt(sg, labs, cst)))
        fh.write('\\bottomrule\n\\end{longtable}\n')
sys.exit(0 if ok else 1)
