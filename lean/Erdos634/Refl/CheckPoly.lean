import Erdos634.Refl.CheckN

/-! Refl/CheckPoly.lean -- the free-branch-point checker for a convex polygon target: the triangle `I.tgt` cut by the extra
closed half-planes `ext`.  Core Lean only (light imports for generated certificate data).  Soundness: `RegionP.lean`. -/

namespace Refl

def tgtLinsP (I : Inst) (ext : List Lin) : List Lin := tgtLinsM I ++ ext

def consP1 (I : Inst) (ext : List Lin) (n : NodeM) : List (Lin × Bool) :=
  (tgtLinsP I ext ++ boxL n.v n.eN n.eD).map (fun l => (l, false)) ++ [((rayL n.v n.d).neg, true)]

def consP2 (I : Inst) (ext : List Lin) (n : NodeM) : List (Lin × Bool) :=
  (tgtLinsP I ext ++ boxL n.v n.eN n.eD).map (fun l => (l, false)) ++
    [(rayL n.v n.d, false), (rayL n.v n.g, true)]

def nodeLocalOkP (I : Inst) (ext : List Lin) (cfg : List Tri) (n : NodeM) : Bool :=
  let v := n.v
  let d := n.d
  let r1 := n.t1.check cfg [] [] false (consP1 I ext n) []
  let r2 := n.t2.check cfg [] [] false (consP2 I ext n) []
  let tgtQ := (tgtLinsP I ext).all (fun l => okPos (quad I v d l) n.tauN n.tauD)
  let tileQ := (cfg.zip n.fedges).all (fun (T, e) => okNeg (quad I v d (T.edge e)) n.tauN n.tauD)
  decide (0 < v.w) && decide (0 < d.w) && (d.x * d.x + I.Dn * d.y * d.y == d.w * d.w) &&
  decide (0 < n.tauN) && decide (0 < n.tauD) && (n.fedges.length == cfg.length) &&
  decide (0 < n.g.w) && decide (0 < n.eN) && decide (0 < n.eD) &&
  decide (0 < d.x * n.g.y - d.y * n.g.x) &&
  r1 && r2 && tgtQ && tileQ

/-- the homogeneous value of a line at a point (`w > 0`): its sign is the sign of `evalL l X Y` -/
def escX (l : Lin) (q : Pt) : Int := l.α * q.x + l.β * q.y + l.γ * q.w

/-- `killOk` with escapes across the extra lines: `Kill.esc b e`, `e ≥ 3`, tests `ext[e-3]` -/
def killOkP (I : Inst) (ext : List Lin) (cfg : List Tri) (tri : Tri) (k : Kill) : Bool :=
  match k with
  | .esc q e =>
    if e < 3 then killOk I cfg tri (fun _ => false) (.esc q e)
    else match ext[e - 3]? with
      | none => false
      | some l => decide (escX l (if q then tri.c else tri.b) < 0)
  | k => killOk I cfg tri (fun _ => false) k

def killsCheckP (I : Inst) (ext : List Lin) (cfg : List Tri) (v d : Pt) :
    List Kill → List Place → List NodeM → (NodeM → List Tri → Bool) → Bool
  | [], [], [], _ => true
  | k :: ks, p :: ps, ch, rec =>
    let tri := placeTri I v d p
    match k with
    | .child =>
      match ch with
      | [] => false
      | c :: cs => rec c (cfg ++ [tri]) && killsCheckP I ext cfg v d ks ps cs rec
    | _ => killOkP I ext cfg tri k && killsCheckP I ext cfg v d ks ps ch rec
  | _, _, _, _ => false

def checkNodeP (I : Inst) (ext : List Lin) (known : List (List Tri)) : Nat → List Tri → NodeM → Bool
  | 0, _, _ => false
  | fuel + 1, cfg, n =>
    if n.tauN == 0 then known.any (fun c => cfgSubV c cfg)
    else nodeLocalOkP I ext cfg n &&
      killsCheckP I ext cfg n.v n.d n.kills I.pl (n.children) (fun c cfg' => checkNodeP I ext known fuel cfg' c)

end Refl
