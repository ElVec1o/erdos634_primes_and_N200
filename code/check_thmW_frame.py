#!/usr/bin/env python3
"""READ_W2 (2026-10-19): independent exact checks of the integer skew-frame redesign of Theorem W.
Pure integer / Fraction arithmetic.  Usage: python3 w2_checks.py [A|B|C|D|E|F|G|H|ALL] [fmax]
Frame: origin P (point of AB with OP=OB), xi along P->O, y along P->B.  phi=f xi+e y, psi=e xi+f y.
"""
import sys, random
from fractions import Fraction as Fr
from math import gcd

def coprime_pairs(fmax, fmin=4):
    for f in range(fmin, fmax + 1):
        for e in range(2, f - 1):
            if gcd(e, f) == 1:
                yield e, f

# ---------- complex numbers  x + i*w*z  (w^2 = 4f^2-e^2) as exact pairs ----------
class C:
    def __init__(s, x, z, w2): s.x, s.z, s.w2 = Fr(x), Fr(z), w2
    def __add__(s, o): return C(s.x + o.x, s.z + o.z, s.w2)
    def __sub__(s, o): return C(s.x - o.x, s.z - o.z, s.w2)
    def __mul__(s, o):
        if not isinstance(o, C): return C(s.x * o, s.z * o, s.w2)
        return C(s.x * o.x - s.w2 * s.z * o.z, s.x * o.z + s.z * o.x, s.w2)
    __rmul__ = __mul__
    def conj(s): return C(s.x, -s.z, s.w2)
    def norm2(s): return s.x * s.x + s.w2 * s.z * s.z
    def eq(s, o): return s.x == o.x and s.z == o.z

def paper_points(e, f, M, t, r, q):
    """the 14 complex points of the earlier layout (paper v3W, Section 2.4), exact."""
    b = f * f - e * e; c = f * f; a = e * f; k = 2 * f * f - e * e; w2 = 4 * f * f - e * e
    one = C(1, 0, w2)
    eps = C(Fr(k, 2 * f * f), Fr(e, 2 * f * f), w2)
    eta = C(Fr(e * (3 * f * f - e * e), 2 * f ** 3), Fr(b, 2 * f ** 3), w2)
    om = (eps * eta).conj(); etab = eta.conj()
    v = f * M - e * r
    P = fbM = None
    P = eps * (f * b * M)
    D = {'O': C(0, 0, w2), 'B': one * (f * b * M), 'A': eps * eps * (f ** 3 * M), 'P': P,
         'P2': eps * (b * (f * M - e * t)), 'P3': P - om * (e * a * t), 'Q': P + om * (f * b * t),
         'R': P + om * (f * b * r), 'Cp': eps * (b * v), 'Bp': one * (c * v),
         'V2': P + etab * (f ** 3 * t) - one * (e * f * f * r), 'X4': P - eps * (f * b * q),
         'U1': P - one * (e * f * f * t) + etab * (e * f * f * q),
         'U2': P - one * (e * f * f * r) + etab * (e * f * f * q)}
    return D, eps, om, eta, etab, one

def frame_points(e, f, M, t, r, q):
    b = f * f - e * e
    return {'O': (f * b * M, 0), 'B': (0, e * b * M), 'A': (0, -e * f * f * M), 'P': (0, 0),
            'P2': (b * e * t, 0), 'P3': (0, -e * e * f * t), 'Q': (0, f * b * t), 'R': (0, f * b * r),
            'Cp': (b * e * r, 0), 'Bp': (e * f * (f * r - e * M), e * f * (f * M - e * r)),
            'V2': (e * f * f * (r - t), f * (f * f * t - e * e * r)), 'X4': (f * b * q, 0),
            'U1': (e * f * (f * t - e * q), e * f * (f * q - e * t)),
            'U2': (e * f * (f * r - e * q), e * f * (f * q - e * r))}

def metric2(d, e, f):  # squared length of frame vector (dxi,dy)
    return Fr(d[0] ** 2 + d[1] ** 2) + Fr(e, f) * d[0] * d[1]

# ------------------------------- A: coordinates vs complex formulas -------------------------------
def check_A(fmax):
    bad = 0; n = 0; rnd = random.Random(7)
    for e, f in coprime_pairs(fmax):
        b = f * f - e * e
        Ms = list(range(1, 3 * f)) if f <= 24 else rnd.sample(range(1, 5 * f), 12)
        for M in Ms:
            nn = (e * M) // f; rho = e * M - f * nn; d = 1 if rho == 0 else 0
            triples = [(nn - d, nn + 1, nn)]
            for _ in range(3): triples.append((rnd.randint(1, 9), rnd.randint(1, 12), rnd.randint(1, 9)))
            for (t, r, q) in triples:
                D, eps, om, eta, etab, one = paper_points(e, f, M, t, r, q)
                Fp = frame_points(e, f, M, t, r, q)
                for nm, (xi, y) in Fp.items():
                    z = D['P'] - eps * xi + om * y
                    if not z.eq(D[nm]): bad += 1
                # metric: |z1-z2|^2 equals frame metric for all pairs
                names = list(Fp)
                for i in range(len(names)):
                    for j in range(i):
                        p, s = Fp[names[i]], Fp[names[j]]
                        dd = (p[0] - s[0], p[1] - s[1])
                        if metric2(dd, e, f) != (D[names[i]] - D[names[j]]).norm2(): bad += 1
                n += 1
        # identities of the paper's setup
        w2 = 4 * f * f - e * e
        D, eps, om, eta, etab, one = paper_points(e, f, 1, 1, 2, 1)
        a, c = e * f, f * f
        m1 = eps * eps * eps * eta * eta
        if not m1.eq(C(-1, 0, w2)): bad += 1
        if not (one * a + om * b).eq(etab * c): bad += 1
        if not (om * f + eps * e).eq(etab * f): bad += 1
    print(f"A: frame coords + metric vs complex formulas: {n} (e,f,M,t,r,q) cases, mismatches {bad}")
    return bad

# ------------------------------- B: structural facts S1..S4 + side lengths -------------------------------
def check_B(fmax):
    bad = 0; n = 0; rnd = random.Random(11)
    for e, f in coprime_pairs(fmax):
        b = f * f - e * e; a = e * f; c = f * f
        # directions: |(f,-e)|=|(-e,f)|=f ; (f,-e)^.(-e,f) angle beta: cos = e(3f^2-e^2)/(2 f^3)
        p = (f, -e); m = (e, -f)
        if metric2(p, e, f) != f * f or metric2((-e, f), e, f) != f * f: bad += 1
        ip = p[0] * m[0] + p[1] * m[1] + Fr(e, 2 * f) * (p[0] * m[1] + p[1] * m[0])
        if ip != Fr(e * (3 * f * f - e * e), 2 * f) : bad += 1  # = |p||m| cos beta * f^? ; |p||m|=f^2 -> cos=ip/f^2
        # angle between axes P->O and P->B: cos = e/(2f): (1,0).(0,1) with metric: bilinear e/(2f)
        # (this is built into the metric formula; validated in check A.)
        for M in range(1, 4 * f):
            nn = (e * M) // f; rho = e * M - f * nn; dl = 1 if rho == 0 else 0
            for (t, r, q) in [(nn - dl, nn + 1, nn), (rnd.randint(1, 8), rnd.randint(1, 12), rnd.randint(1, 8))]:
                Pt = frame_points(e, f, M, t, r, q)
                phi = lambda s: f * s[0] + e * s[1]
                psi = lambda s: e * s[0] + f * s[1]
                ef = e * f
                # target sides
                if e * Pt['B'][0] + f * Pt['B'][1] != ef * b * M: bad += 1          # B on OB line
                if e * Pt['O'][0] + f * Pt['O'][1] != ef * b * M: bad += 1
                if ef * Pt['A'][0] - b * Pt['A'][1] != ef * f * f * b * M and False: bad += 1
                if ef * Pt['O'][0] - b * Pt['O'][1] != ef * f * f * b * M / f and False: bad += 1
                # OA line: ef xi - b y = ef^2 b M  (check on O and A)
                for nm in ('O', 'A'):
                    if ef * Pt[nm][0] - b * Pt[nm][1] != e * f * f * b * M: bad += 1
                # l_k lines
                for nm in ('P2', 'U1', 'Q'):
                    if phi(Pt[nm]) != ef * b * t: bad += 1
                for nm in ('Cp', 'U2', 'V2', 'Bp'):
                    if phi(Pt[nm]) != ef * b * r: bad += 1
                # psi levels of the cuts
                if psi(Pt['Q']) != f * f * b * t or psi(Pt['V2']) != f * f * b * t: bad += 1
                if psi(Pt['U1']) != ef * b * q or psi(Pt['U2']) != ef * b * q or psi(Pt['X4']) != ef * b * q: bad += 1
                if psi(Pt['Bp']) != ef * b * M or psi(Pt['B']) != ef * b * M: bad += 1
                # S1: l_k meets OP at ebk, AB at fbk; (i) l_k cap OB at distance c(fM-ek) from O ; tile b-side fbk of scale fk
                k = t
                if phi((e * b * k, 0)) != ef * b * k or phi((0, f * b * k)) != ef * b * k: bad += 1
                # side lengths of the six pieces (squared), as claimed in the paper text
                L = lambda X, Y: metric2((Pt[Y][0] - Pt[X][0], Pt[Y][1] - Pt[X][1]), e, f)
                v = f * M - e * r; s1 = f * (r - t); s2 = f * r - e * M; x = f * t - e * q; u1 = f * q - e * t; u2 = f * q - e * r
                chk = [(L('P3', 'Q'), (c * f * t) ** 2), (L('P3', 'P2'), (a * f * t) ** 2), (L('P2', 'Q'), (b * f * t) ** 2),
                       (L('O', 'Cp'), (b * v) ** 2), (L('O', 'Bp'), (c * v) ** 2), (L('Cp', 'Bp'), (a * v) ** 2),
                       (L('Q', 'V2'), (a * s1) ** 2), (L('Q', 'R'), (b * s1) ** 2), (L('R', 'V2'), (c * s1) ** 2),
                       (L('R', 'B'), (b * s2) ** 2), (L('R', 'Bp'), (c * s2) ** 2),
                       (L('Q', 'U1'), (c * x) ** 2), (L('V2', 'U2'), (c * x) ** 2), (L('U1', 'U2'), (a * s1) ** 2),
                       (L('X4', 'P2'), (b * u1) ** 2), (L('X4', 'U1'), (c * u1) ** 2), (L('P2', 'U1'), (a * u1) ** 2),
                       (L('X4', 'Cp'), (b * u2) ** 2), (L('X4', 'U2'), (c * u2) ** 2), (L('Cp', 'U2'), (a * u2) ** 2),
                       (L('O', 'P'), (b * f * M) ** 2), (L('P', 'A'), (a * f * M) ** 2), (L('O', 'A'), (c * f * M) ** 2)]
                for got, want in chk:
                    if got != want: bad += 1
                # parallelism: QV2 || U1U2 || OB direction (f,-e); QU1 || V2U2 || (e,-f); all as exact cross products
                def par(X, Y, dirv):
                    dx, dy = Pt[Y][0] - Pt[X][0], Pt[Y][1] - Pt[X][1]
                    return dx * dirv[1] - dy * dirv[0] == 0
                if not (par('Q', 'V2', (f, -e)) and par('U1', 'U2', (f, -e)) and par('B', 'O', (f, -e)) and par('Bp', 'B', (f, -e))): bad += 1
                if not (par('Q', 'U1', (e, -f)) and par('V2', 'U2', (e, -f)) and par('P2', 'U1', (e, -f)) and par('Cp', 'U2', (e, -f))): bad += 1
                # S4: along l_t: c x + a u1 = b f t  (lengths of segment Q->P2 = b f t)
                if c * x + a * u1 != b * f * t: bad += 1
                n += 1
    print(f"B: structural facts and side lengths: {n} cases, mismatches {bad}")
    return bad

# ------------------------------- D: separation / containment / coverage for the canonical layout -------------------------------
def shoelace2(vs):  # twice the signed area in frame coordinates (affine area)
    s = 0
    for i in range(len(vs)):
        x1, y1 = vs[i]; x2, y2 = vs[(i + 1) % len(vs)]
        s += x1 * y2 - x2 * y1
    return s

def check_D(fmax, mult=5):
    bad = 0; n = 0; fails_below = 0; nbelow = 0
    for e, f in coprime_pairs(fmax):
        b = f * f - e * e; g = f - e; ef = e * f
        for M in range(1, mult * f):
            nn = (e * M) // f; dl = 1 if e * M == f * nn else 0
            t, r, q = nn - dl, nn + 1, nn
            Pt = frame_points(e, f, M, t, r, q)
            phi = lambda s: f * s[0] + e * s[1]
            psi = lambda s: e * s[0] + f * s[1]
            pieces = {0: ['A', 'O', 'P2', 'P3'], 1: ['O', 'Bp', 'Cp'], 2: ['P3', 'P2', 'Q'], 3: ['B', 'Q', 'V2', 'Bp'],
                      4: ['Q', 'U1', 'U2', 'V2'], 5: ['U1', 'P2', 'Cp', 'U2']}
            V = {i: [Pt[nm] for nm in lst] for i, lst in pieces.items()}
            hyp = (e * M >= f) and ((M - 1) * g >= f)
            ok = True
            # six separating functionals: sign convention  h(pt) <= 0 on side "low", >=0 on side "high"
            line = {'OP': lambda s: s[1],                       # y
                    'P2P3': lambda s: ef * s[0] - b * s[1] - e * e * f * b * t,   # parallel to OA through P2,P3
                    'lt': lambda s: phi(s) - ef * b * t, 'lr': lambda s: phi(s) - ef * b * r,
                    'c1': lambda s: psi(s) - f * f * b * t, 'c2': lambda s: psi(s) - ef * b * q}
            sep = [(0, [1, 3, 4, 5], 'OP', +1), (0, [2], 'P2P3', -1), (2, [1, 3, 4, 5], 'lt', +1),
                   (1, [3, 4, 5], 'lr', -1), (3, [4, 5], 'c1', -1), (4, [5], 'c2', -1)]
            # meaning: piece i has line(.) * sign >=0 on all vertices... encode: first listed piece on side 'sgn' (sgn*line<=0)
            for i, others, ln, sg in sep:
                h = line[ln]
                if not all(sg * h(p) <= 0 for p in V[i]): ok = False
                for j in others:
                    if not all(sg * h(p) >= 0 for p in V[j]): ok = False
            # containment in OAB: xi >=0 (right of AB), psi<=efbM, ef xi - b y <= e f^2 b M
            for i in range(6):
                for p in V[i]:
                    if not (p[0] >= 0 and psi(p) <= ef * b * M and ef * p[0] - b * p[1] <= e * f * f * b * M): ok = False
            # convexity + orientation: consecutive turns positive (affine orientation same as true one up to sign constant)
            for i in range(6):
                vs = V[i]
                for k in range(len(vs)):
                    p0, p1, p2 = vs[k], vs[(k + 1) % len(vs)], vs[(k + 2) % len(vs)]
                    cr = (p1[0] - p0[0]) * (p2[1] - p1[1]) - (p1[1] - p0[1]) * (p2[0] - p1[0])
                    if cr == 0: ok = False
                    # sign: OAB listed in the paper counter-clockwise; frame (xi,y) is a skew frame: orientation sign fixed below
            # areas: sum of affine areas = area OAB (ABS values)
            tot = sum(abs(shoelace2(V[i])) for i in range(6))
            ar = abs(shoelace2([Pt['O'], Pt['B'], Pt['A']]))
            if tot != ar: ok = False
            # signs of orientation all equal
            sgns = set()
            for i in range(6):
                sgns.add(shoelace2(V[i]) > 0)
            if len(sgns) != 1: ok = False
            # all consecutive turns same sign as the area
            for i in range(6):
                vs = V[i]; sa = shoelace2(vs) > 0
                for k in range(len(vs)):
                    p0, p1, p2 = vs[k], vs[(k + 1) % len(vs)], vs[(k + 2) % len(vs)]
                    cr = (p1[0] - p0[0]) * (p2[1] - p1[1]) - (p1[1] - p0[1]) * (p2[0] - p1[0])
                    if (cr > 0) != sa: ok = False
            n += 1
            if hyp:
                if not ok: bad += 1
            else:
                nbelow += 1
                if ok: fails_below += 1
    print(f"D: canonical layout, separation/containment/convexity/area, f<={fmax}, M<{mult}f: {n} triples; "
          f"inside Thm W hypotheses: failures {bad}; outside ({nbelow} triples): layout passes anyway {fails_below}")
    return bad

# ------------------------------- E,F: the four inequalities vs the 16 factors, nonexistence -------------------------------
def conds16(e, f, M, t, r, q):
    b = f * f - e * e; k = 2 * f * f - e * e
    return [t, q, r - t, M - q, e * M - f * t, f * M - e * t, f * r - e * M, f * M - e * r, f * q - e * r, f * q - e * t,
            f * t - e * q, f * f * t - e * e * r, f * r - e * q, b * f * M - e * k * t + f ** 3 * q,
            b * f * M - e * k * r + f ** 3 * q, e * f * b * M - e * e * k * r + f ** 4 * t]

def four(e, f, M, t, r, q):
    return f * t < e * M < f * r and e * r < f * q and e * q < f * t

def check_E(fmax):
    bad = 0; n = 0; nonu = 0; nonu_ex = None
    for e, f in coprime_pairs(fmax, 4):
        g = f - e
        for M in range(1, 3 * f):
            top = (f * M) // e + 2
            nn = (e * M) // f
            found = []
            for t in range(0, top + 1):
                for r in range(t + 1, top + 1):
                    for q in range(0, M + 3):
                        A = four(e, f, M, t, r, q)
                        B = all(x > 0 for x in conds16(e, f, M, t, r, q)) and t >= 1
                        n += 1
                        if A and t >= 1 and not B: bad += 1      # four => 16 (with t>=1 automatic?)
                        if B and not A: bad += 1                  # 16 => four
                        if A and t < 1: bad += 1                  # t>=1 automatic
                        if A: found.append((t, r, q))
            exists = len(found) > 0
            if exists != (g * nn >= e + 1): bad += 1
            dl = 1 if e * M == f * nn else 0
            if exists and (nn - dl, nn + 1, nn) not in found: bad += 1   # canonical triple works whenever any does
            for (t, r, q) in found:
                if t > nn - dl or r < nn + 1: bad += 1
            if len(found) > 1: nonu += 1; nonu_ex = nonu_ex or (e, f, M, found[:4])
    print(f"E/F: all (t,r,q) enumerated, f<={fmax}: {n} triples tested, mismatches {bad}; "
          f"(layout exists <=> g*n>=e+1; canonical works whenever any works); (e,f,M) with >1 admissible triple: {nonu}, e.g. {nonu_ex}")
    return bad

# ------------------------------- G: (H1)&(H2) <=> g*floor(eM/f) >= e+1 and its hand proof -------------------------------
def check_G(fmax):
    bad = 0; n = 0
    for e, f in coprime_pairs(fmax):
        g = f - e
        # constants used in the hand proof of (=>)
        if e * g < f + 1: bad += 1                      # (P4)
        for M in range(1, 3 * f + 1):
            nn = (e * M) // f
            H = (e * M >= f) and ((M - 1) * g >= f)
            S = g * nn >= e + 1
            if H != S: bad += 1
            # (=>) proof pieces
            if H:
                if g >= e + 1:
                    if not (nn >= 1 and g * nn >= e + 1): bad += 1
                else:
                    h, j = divmod(f, g)
                    if not (0 < j < g and h >= 2 and e == g * (h - 1) + j): bad += 1
                    if not (M - 1 >= h + 1 and M >= h + 2): bad += 1
                    if e * (h + 2) - h * f != g * (h - 2) + 2 * j or e * (h + 2) - h * f <= 0: bad += 1
                    if not (e * M > h * f and nn >= h and g * nn >= f - j >= e + 1): bad += 1
            # (<=) proof: assume g n >= e+1; show (M-1)g >= f by contradiction pieces
            if S:
                if not (nn >= 1 and e * M >= f): bad += 1
            else:
                pass
            if not H and e * M >= f and (M - 1) * g <= f - 1:
                ce = -(-g * M // f)
                if not (ce in (1, 2) and nn == M - ce and g * nn <= e): bad += 1
                if ce == 1 and not g * nn == g * (M - 1) <= f - g: bad += 1
                if ce == 2 and not g * nn <= e - 1: bad += 1
            # g*n = e never happens
            if g * nn == e: bad += 1
            n += 1
    print(f"G: (H1)&(H2) <=> g*floor(eM/f)>=e+1 and every step of its hand proof, f<={fmax}, M<=3f: {n} triples, mismatches {bad}")
    return bad

# ------------------------------- H: count identity (sympy) -------------------------------
def check_H():
    import sympy as sp
    e, f, M, t, r, q = sp.symbols('e f M t r q')
    b = f * f - e * e; kap = 2 * f * f - e * e
    v = f * M - e * r; s1 = f * (r - t); s2 = f * r - e * M; x = f * t - e * q; u1 = f * q - e * t; u2 = f * q - e * r
    tot = (f**2*M**2 - e**2*t**2) + v**2 + f**2*t**2 + (s1**2 - s2**2) + 2*s1*x + (u1**2 - u2**2)
    d1 = sp.expand(tot - M**2 * kap)
    print("H1: general count identity  sum - M^2 kappa =", d1)
    n, rho = sp.symbols('n rho')
    sub = {M: (f * n + rho) / e}
    # delta = 0: t=q=n, r=n+1
    tot0 = tot.subs({t: n, r: n + 1, q: n})
    d0 = sp.simplify(sp.expand(tot0.subs(M, (f * n + rho) / e) - ((f * n + rho) / e)**2 * kap))
    print("H2: delta=0 count identity (n,rho form) residual =", sp.simplify(d0))
    cnt = [f**2*M**2 - e**2*n**2, (f*M - e*n - e)**2, f**2*n**2, rho*(2*f - rho), 2*f*(f - e)*n, e*(2*(f - e)*n - e)]
    ssum = sum(cnt).subs(M, (f * n + rho) / e)
    print("H3: Fable's six counts in (n,rho) form: sum - M^2 kappa =", sp.simplify(sp.expand(ssum - ((f * n + rho) / e)**2 * kap)))
    # delta = 1: t=n-1, r=n+1, q=n, rho=0
    tot1 = tot.subs({t: n - 1, r: n + 1, q: n})
    d1b = sp.simplify(sp.expand(tot1.subs(M, f * n / e) - (f * n / e)**2 * kap))
    print("H4: delta=1 count identity residual =", d1b)
    # factor identities
    C6, C7, C2 = f*q - e*r, f*t - e*q, r - t
    print("H5: C8 = f C7 + e C6:", sp.expand(f**2*t - e**2*r - (f*C7 + e*C6)) == 0,
          "; C9 = f C2 + C7:", sp.expand(f*r - e*q - (f*C2 + C7)) == 0,
          "; C6' = C6 + e C2:", sp.expand(f*q - e*t - (C6 + e*C2)) == 0)

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'ALL'
    fmax = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    res = {}
    if which in ('A', 'ALL'): res['A'] = check_A(min(fmax, 40))
    if which in ('B', 'ALL'): res['B'] = check_B(min(fmax, 24))
    if which in ('D', 'ALL'): res['D'] = check_D(fmax)
    if which in ('E', 'ALL'): res['E'] = check_E(min(fmax, 12))
    if which in ('G', 'ALL'): res['G'] = check_G(fmax if which != 'ALL' else 300)
    if which in ('H', 'ALL'): check_H()
    print("SUMMARY", res)

if __name__ == '__main__':
    main()
