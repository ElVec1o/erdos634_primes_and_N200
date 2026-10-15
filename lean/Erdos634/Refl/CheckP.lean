import Erdos634.Refl.CheckR

/-! Refl/CheckP.lean -- reflective checker for 4-vertex (parallelogram) targets.
    Extends Check.lean; target-polygon pieces use Quad (4 vertices) and range 4 / e%4.
    Dn-dependent helpers are redefined with Dn : Int explicit (same formulas as Check.lean). -/

namespace Erdos634.Refl.CheckP

-- ── 4-vertex target ────────────────────────────────────────────────────────

structure Quad where
  a : Pt
  b : Pt
  c : Pt
  d : Pt

def Quad.vert (q : Quad) : Nat → Pt
  | 0 => q.a
  | 1 => q.b
  | 2 => q.c
  | _ => q.d

def Quad.ok (q : Quad) : Bool :=
  decide (0 < q.a.w) && decide (0 < q.b.w) && decide (0 < q.c.w) && decide (0 < q.d.w) &&
  decide (0 < det3 q.a q.b q.c) && decide (0 < det3 q.b q.c q.d) &&
  decide (0 < det3 q.c q.d q.a) && decide (0 < det3 q.d q.a q.b)

def Quad.edge (q : Quad) (i : Nat) : Lin := linOf (q.vert (i % 4)) (q.vert ((i + 1) % 4))

-- ── InstP ──────────────────────────────────────────────────────────────────

structure InstP where
  Dn    : Int
  tgt   : Quad
  sides : Int × Int × Int
  pl    : List Place

-- ── Dn-parameterized helpers (same formulas as Check.lean) ─────────────────

def placeOkP (Dn : Int) (l1 l2 l3 : Int) (p : Place) : Bool :=
  decide (0 < p.l1) && decide (0 < p.pd) && decide (0 < p.qd) && decide (0 < p.qn) &&
  (p.l1 == l1) &&
  (2 * l1 * p.pn == (l1 * l1 + l2 * l2 - l3 * l3) * p.pd) &&
  (Dn * p.qn * p.qn * p.pd * p.pd == (l2 * l2 * p.pd * p.pd - p.pn * p.pn) * (p.qd * p.qd))

def placeTriP (Dn : Int) (v d : Pt) (p : Place) : Tri :=
  let P : Pt := ⟨v.x * d.w + p.l1 * d.x * v.w, v.y * d.w + p.l1 * d.y * v.w, v.w * d.w⟩
  let Q : Pt := ⟨v.x * d.w * p.pd * p.qd + p.pn * d.x * v.w * p.qd - Dn * p.qn * d.y * v.w * p.pd,
                 v.y * d.w * p.pd * p.qd + p.pn * d.y * v.w * p.qd + p.qn * d.x * v.w * p.pd,
                 v.w * d.w * p.pd * p.qd⟩
  ⟨v, P, Q⟩

def quadP (Dn : Int) (v d : Pt) (l : Lin) : Int × Int × Int :=
  ((l.α * v.x + l.β * v.y + l.γ * v.w) * d.w,
   (l.α * d.x + l.β * d.y) * v.w,
   (-(l.α * Dn * d.y) + l.β * d.x) * v.w)

def blockedOkP (Dn : Int) (cfg : List Tri) (v d : Pt) (b : Blocked) : Bool :=
  if b.base then (v.y == 0 && d.y == 0 && decide (0 < d.x) && d.x == d.w)
  else
    match cfg[b.m]? with
    | none => false
    | some T =>
      let W := b.W
      let e1 := vsub W.b W.a
      let e2 := vsub W.c W.a
      let dd : Int × Int := (d.x, d.y)
      let nn : Int × Int := (-(Dn * d.y), d.x)
      eqvPt W.a v && decide (0 < det3 W.a W.b W.c) && W.ok &&
      inClosed T W.a && inClosed T W.b && inClosed T W.c &&
      (decide (0 < vcross dd e2) || (vcross dd e2 == 0 && decide (vcross nn e2 < 0))) &&
      (decide (0 < vcross e1 dd) || (vcross e1 dd == 0 && decide (vcross e1 nn < 0)))

-- ── InstP.ok ───────────────────────────────────────────────────────────────

def InstP.ok (I : InstP) : Bool :=
  let (a, b, c) := I.sides
  I.pl.length == 6 && I.tgt.ok && decide (0 < I.Dn) &&
  (match I.pl with
   | [p1, p2, p3, p4, p5, p6] =>
     placeOkP I.Dn a c b p1 && placeOkP I.Dn c a b p2 &&
     placeOkP I.Dn a b c p3 && placeOkP I.Dn b a c p4 &&
     placeOkP I.Dn c b a p5 && placeOkP I.Dn b c a p6
   | _ => false)

-- ── Core checker (4-edge target) ──────────────────────────────────────────

/-- killOk variant for 4-edge target: e % 4 instead of e % 3. -/
def killOkP (I : InstP) (cfg : List Tri) (tri : Tri) (rec : List Tri → Bool) : Kill → Bool
  | .esc q e =>
    let pt := if q then tri.c else tri.b
    decide (det3 (I.tgt.vert (e % 4)) (I.tgt.vert ((e + 1) % 4)) pt < 0)
  | .ovl m w =>
    match cfg[m]? with
    | none => false
    | some U => decide (0 < w.w) && inOpen tri w && inOpen U w
  | .child => rec (cfg ++ [tri])

def killsCheckP (I : InstP) (cfg : List Tri) (v d : Pt) :
    List Kill → List Place → List Node → (Node → List Tri → Bool) → Bool
  | [], [], [], _ => true
  | k :: ks, p :: ps, ch, rec =>
    let tri := placeTriP I.Dn v d p
    match k with
    | .child =>
      match ch with
      | [] => false
      | c :: cs =>
        killOkP I cfg tri (fun cfg' => rec c cfg') .child &&
        killsCheckP I (cfg ++ [tri]) v d ks ps cs rec
    | _ =>
      killOkP I cfg tri (fun _ => false) k &&
      killsCheckP I cfg v d ks ps ch rec
  | _, _, _, _ => false

def nodeLocalOkP (I : InstP) (cfg : List Tri) (n : Node) : Bool :=
  let v := n.v
  let d := n.d
  let tgtLins := (List.range 4).map (fun i => I.tgt.edge i)
  let ylt  : Lin := ⟨0, -v.w, v.y⟩
  let ygeL : Lin := ⟨0, v.w, -v.y⟩
  let xltL : Lin := ⟨-v.w, 0, v.x⟩
  let r1 := n.t1.check cfg [] [] false (tgtLins.map (fun l => (l, false)) ++ [(ylt, true)]) []
  let r2 := n.t2.check cfg (tgtLins ++ [ygeL]) [(ylt, false), (xltL, true)] true
      (tgtLins.map (fun l => (l, false)) ++ [(ygeL, false), (xltL, true)]) []
  let tgtQ  := tgtLins.all (fun l => okPos (quadP I.Dn v d l) n.tauN n.tauD)
  let tileQ := (cfg.zip n.fedges).all
      (fun (T, e) => okNeg (quadP I.Dn v d (T.edge e)) n.tauN n.tauD)
  decide (0 < v.w) && decide (0 < d.w) &&
  (d.x * d.x + I.Dn * d.y * d.y == d.w * d.w) &&
  decide (0 < n.tauN) && decide (0 < n.tauD) && (n.fedges.length == cfg.length) &&
  r1 && r2 && tgtQ && tileQ && blockedOkP I.Dn cfg v d n.hb

def checkNodeP (I : InstP) : Nat → List Tri → Node → Bool
  | 0, _, _ => false
  | fuel + 1, cfg, n =>
    nodeLocalOkP I cfg n &&
    killsCheckP I cfg n.v n.d n.kills I.pl n.children
      (fun c cfg' => checkNodeP I fuel cfg' c)

def InstP.checkAll (I : InstP) (fuel : Nat) (n : Node) : Bool :=
  I.ok && checkNodeP I fuel [] n

-- ── Chunked checker (mirrors Refl.checkNodeR for 4-vertex targets) ─────────

/-- Chunked variant: a stub node (tauN = 0) is accepted iff the current
    configuration matches one of the `known` configurations. -/
def checkNodeRP (I : InstP) (known : List (List Tri)) : Nat → List Tri → Node → Bool
  | 0, _, _ => false
  | fuel + 1, cfg, n =>
    if n.tauN == 0 then known.any (fun c => Refl.cfgEq c cfg)
    else nodeLocalOkP I cfg n && killsCheckP I cfg n.v n.d n.kills I.pl (n.children)
      (fun c cfg' => checkNodeRP I known fuel cfg' c)

def InstP.checkAllR (I : InstP) (known : List (List Tri)) (fuel : Nat) (n : Node) : Bool :=
  I.ok && checkNodeRP I known fuel [] n

end Erdos634.Refl.CheckP
