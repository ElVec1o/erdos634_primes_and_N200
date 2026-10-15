/- Discriminating control for
`lem:cornerstep`: the N = 44 tiling has no b-edges (`b = 24`), so every chain edge in `D44` is
`a` or `c`.  The N = 99 tiling (`D99`, `b = 48`) has genuine b-edges and is a stronger test.
All hypotheses proved WITHOUT sorry.  `D99_corner_step_corner0` is axiom-free.

`cornerAngle_eq_of_cos` signature (ApexWitness44): ha = dist p q, hb = dist r q, hd = dist p r,
conclusion = cornerAngle p q r = θ, cos formula: (a²+b²-d²)/(2ab).
-/
import Erdos634.Draft.CornerStepFormal
import Erdos634.Draft.FluxCWitness99
import Erdos634.Draft.ApexWitness44

open scoped Classical

namespace Erdos634.CornerPara.Witness99

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Z15Real Erdos634.CertCoord
  Erdos634.Tiling99Bridge Erdos634.Draft.FluxCWitness99 Erdos634.BaseBetaTargetCoord
  Erdos634.CornerPara

local notation "α44" => modelAlpha 1 ((2 : ℕ) : ℝ)
local notation "β44" => modelBeta 1 ((2 : ℕ) : ℝ)
local notation "γ44" => 2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)
local notation "T99" => Fin Tiling99.tiles.length

/-- The 99-tiling with τ-relabeled model: vertex 0 = α, vertex 1 = β, vertex 2 = γ. -/
noncomputable def D99 : CongruentDissection Tiling99.tiles.length :=
  dissection.relabelModel τ

/-! ## 1. Angle data for the relabeled model -/

-- `cornerAngle_eq_of_cos p q r θ`: ha = dist p q, hb = dist r q, hd = dist p r → cornerAngle p q r = θ
-- After `rw [τ0, τ1, τ2]` with τ0=2, τ1=0, τ2=1:
--   D99_hα goal: cornerAngle (M99.pts 0) (M99.pts 2) (M99.pts 1) = α44
--     p=pts0, q=pts2, r=pts1; ha=dist(pts0,pts2)=64, hb=dist(pts1,pts2)=48, hd=dist(pts0,pts1)=32
--   D99_hβ goal: cornerAngle (M99.pts 1) (M99.pts 0) (M99.pts 2) = β44
--     p=pts1, q=pts0, r=pts2; ha=dist(pts1,pts0)=32, hb=dist(pts2,pts0)=64, hd=dist(pts1,pts2)=48

private theorem D99_hα : cornerAngle (D99.model.pts 1) (D99.model.pts 0) (D99.model.pts 2) = α44 := by
  show cornerAngle (M99.pts (τ 1)) (M99.pts (τ 0)) (M99.pts (τ 2)) = _
  rw [τ0, τ1, τ2]
  -- goal: cornerAngle (M99.pts 0) (M99.pts 2) (M99.pts 1) = α44
  -- ha: dist(pts0, pts2)=64; hb: dist(pts1, pts2)=48; hd: dist(pts0, pts1)=32; cos=7/8
  exact Erdos634.Draft.ApexWitness44.cornerAngle_eq_of_cos (a := 64) (b := 48) (d := 32)
    (by rw [dist_comm]; exact m99_d20) m99_d12 m99_d01 (by norm_num) (by norm_num)
    Erdos634.Draft.ApexWitness44.alpha_bounds.1 Erdos634.Draft.ApexWitness44.alpha_bounds.2
    (by rw [Erdos634.Draft.ApexWitness44.cos_alpha12]; norm_num)

private theorem D99_hβ : cornerAngle (D99.model.pts 2) (D99.model.pts 1) (D99.model.pts 0) = β44 := by
  show cornerAngle (M99.pts (τ 2)) (M99.pts (τ 1)) (M99.pts (τ 0)) = _
  rw [τ0, τ1, τ2]
  -- goal: cornerAngle (M99.pts 1) (M99.pts 0) (M99.pts 2) = β44
  -- ha: dist(pts1, pts0)=32; hb: dist(pts2, pts0)=64; hd: dist(pts1, pts2)=48; cos=11/16
  exact Erdos634.Draft.ApexWitness44.cornerAngle_eq_of_cos (a := 32) (b := 64) (d := 48)
    (by rw [dist_comm]; exact m99_d01) m99_d20 m99_d12 (by norm_num) (by norm_num)
    Erdos634.Draft.ApexWitness44.beta_bounds.1 Erdos634.Draft.ApexWitness44.beta_bounds.2
    (by rw [Erdos634.Draft.ApexWitness44.cos_beta12]; norm_num)

private theorem D99_hγ : cornerAngle (D99.model.pts 0) (D99.model.pts 2) (D99.model.pts 1) = γ44 := by
  have hsum := Erdos634.Geometry.cornerAngle_sum D99.model
  rw [D99_hα, D99_hβ] at hsum
  linarith [modelAngle_rel 1 ((2 : ℕ) : ℝ)]

/-! ## 2. Target distances (from `targetTri_sides` by nlinarith) -/

private theorem tgt99_d01 : dist (targetTri.pts 0) (targetTri.pts 1) = 528 := by
  have hsq := targetTri_sides.1
  have hnn : (0 : ℝ) ≤ dist (targetTri.pts 0) (targetTri.pts 1) := dist_nonneg
  have h2 : (dist (targetTri.pts 0) (targetTri.pts 1) - 528) *
            (dist (targetTri.pts 0) (targetTri.pts 1) + 528) = 0 := by nlinarith
  rcases mul_eq_zero.mp h2 with h | h <;> linarith

private theorem tgt99_d12 : dist (targetTri.pts 1) (targetTri.pts 2) = 384 := by
  have hsq := targetTri_sides.2.1
  have hnn : (0 : ℝ) ≤ dist (targetTri.pts 1) (targetTri.pts 2) := dist_nonneg
  have h2 : (dist (targetTri.pts 1) (targetTri.pts 2) - 384) *
            (dist (targetTri.pts 1) (targetTri.pts 2) + 384) = 0 := by nlinarith
  rcases mul_eq_zero.mp h2 with h | h <;> linarith

private theorem tgt99_d20 : dist (targetTri.pts 2) (targetTri.pts 0) = 384 := by
  have hsq := targetTri_sides.2.2
  have hnn : (0 : ℝ) ≤ dist (targetTri.pts 2) (targetTri.pts 0) := dist_nonneg
  have h2 : (dist (targetTri.pts 2) (targetTri.pts 0) - 384) *
            (dist (targetTri.pts 2) (targetTri.pts 0) + 384) = 0 := by nlinarith
  rcases mul_eq_zero.mp h2 with h | h <;> linarith

/-! ## 3. Target corner angles in terms of modelBeta 1 2 -/

-- tgt99_hb0: cornerAngle (pts1) (pts0) (pts2) = β44
--   p=pts1, q=pts0, r=pts2; ha=dist(pts1,pts0)=528, hb=dist(pts2,pts0)=384, hd=dist(pts1,pts2)=384
--   cos = (528²+384²-384²)/(2·528·384) = 528²/(2·528·384) = 11/16

private theorem tgt99_hb0 :
    cornerAngle (targetTri.pts 1) (targetTri.pts 0) (targetTri.pts 2) = β44 :=
  Erdos634.Draft.ApexWitness44.cornerAngle_eq_of_cos (a := 528) (b := 384) (d := 384)
    (by rw [dist_comm]; exact tgt99_d01) tgt99_d20 tgt99_d12 (by norm_num) (by norm_num)
    Erdos634.Draft.ApexWitness44.beta_bounds.1 Erdos634.Draft.ApexWitness44.beta_bounds.2
    (by rw [Erdos634.Draft.ApexWitness44.cos_beta12]; norm_num)

-- tgt99_hb1: cornerAngle (pts2) (pts1) (pts0) = β44
--   p=pts2, q=pts1, r=pts0; ha=dist(pts2,pts1)=384, hb=dist(pts0,pts1)=528, hd=dist(pts2,pts0)=384

private theorem tgt99_hb1 :
    cornerAngle (targetTri.pts 2) (targetTri.pts 1) (targetTri.pts 0) = β44 :=
  Erdos634.Draft.ApexWitness44.cornerAngle_eq_of_cos (a := 384) (b := 528) (d := 384)
    (by rw [dist_comm]; exact tgt99_d12) tgt99_d01 tgt99_d20 (by norm_num) (by norm_num)
    Erdos634.Draft.ApexWitness44.beta_bounds.1 Erdos634.Draft.ApexWitness44.beta_bounds.2
    (by rw [Erdos634.Draft.ApexWitness44.cos_beta12]; norm_num)

private theorem tgt99_h3α :
    cornerAngle (targetTri.pts 0) (targetTri.pts 2) (targetTri.pts 1) = 3 * α44 := by
  have hsum := Erdos634.Geometry.cornerAngle_sum targetTri
  rw [tgt99_hb0, tgt99_hb1] at hsum
  linarith [modelAngle_rel 1 ((2 : ℕ) : ℝ)]

/-! ## 4. The structural theorems -/

-- D99.model = M99.relabel τ definitionally; sideOpp D99.model j = dist(M99.pts(τ(j+1)), M99.pts(τ(j+2)))
-- hs0: j=0 → dist(M99.pts(τ1), M99.pts(τ2)) = dist(pts0, pts1) = m99_d01 = 32 = 16*(1*2)
-- hs1: j=1 → dist(M99.pts(τ2), M99.pts(τ0)) = dist(pts1, pts2) = m99_d12 = 48 = 16*(4-1)
-- hs2: j=2 → dist(M99.pts(τ0), M99.pts(τ1)) = dist(pts2, pts0) = m99_d20 = 64 = 16*4

theorem D99_model : BaseBetaModel D99 1 2 16 α44 β44 γ44 where
  hs := by norm_num
  hs0 := by
    have h : sideOpp D99.model 0 = dist (M99.pts (τ 1)) (M99.pts (τ 2)) := rfl
    rw [h, τ1, τ2, m99_d01]; norm_num
  hs1 := by
    have h : sideOpp D99.model 1 = dist (M99.pts (τ 2)) (M99.pts (τ 0)) := rfl
    rw [h, τ2, τ0, m99_d12]; norm_num
  hs2 := by
    have h : sideOpp D99.model 2 = dist (M99.pts (τ 0)) (M99.pts (τ 1)) := rfl
    rw [h, τ0, τ1, m99_d20]; norm_num
  hα' := D99_hα
  hβ' := D99_hβ
  hγ' := D99_hγ

theorem D99_shape : BaseBetaShape D99.target α44 β44 := by
  -- D99.target = targetTri definitionally (relabelModel keeps toDissection unchanged)
  have h0 : cornerAngle (D99.target.pts 1) (D99.target.pts 0) (D99.target.pts 2) = β44 := by
    change cornerAngle (targetTri.pts 1) (targetTri.pts 0) (targetTri.pts 2) = _; exact tgt99_hb0
  have h1 : cornerAngle (D99.target.pts 2) (D99.target.pts 1) (D99.target.pts 0) = β44 := by
    change cornerAngle (targetTri.pts 2) (targetTri.pts 1) (targetTri.pts 0) = _; exact tgt99_hb1
  have h2 : cornerAngle (D99.target.pts 0) (D99.target.pts 2) (D99.target.pts 1) = 3 * α44 := by
    change cornerAngle (targetTri.pts 0) (targetTri.pts 2) (targetTri.pts 1) = _; exact tgt99_h3α
  intro m; fin_cases m
  · right; exact h0
  · right; exact h1
  · left; exact h2

theorem D99_iso₁ :
    cornerAngle (D99.target.pts (2 + 1 + 1)) (D99.target.pts (2 + 1)) (D99.target.pts (2 + 1 + 2)) =
      β44 := by
  change cornerAngle (targetTri.pts 1) (targetTri.pts 0) (targetTri.pts 2) = _; exact tgt99_hb0

theorem D99_iso₂ :
    cornerAngle (D99.target.pts (2 + 2 + 1)) (D99.target.pts (2 + 2)) (D99.target.pts (2 + 2 + 2)) =
      β44 := by
  change cornerAngle (targetTri.pts 2) (targetTri.pts 1) (targetTri.pts 0) = _; exact tgt99_hb1

theorem D99_angleData : MarchSlots.AngleData α44 β44 γ44 :=
  Erdos634.E1NormalForm.angleData_model 2 le_rfl

/-! ## 5. Chain data -/

-- Tile-0 index using ⟨n, proof⟩ form (avoids OfNat synthesis on non-reducible Tiling99.tiles)
private def i99_0 : Fin Tiling99.tiles.length := ⟨0, by decide⟩

private theorem coord_t99_0_0 : (D99.tile i99_0).pts 0 = mkPt 0 0 := by
  show (pieceAt i99_0).pts 0 = _
  unfold pieceAt
  rw [pieceTri_pts Tiling99.tiles[i99_0.val] (List.getElem_mem i99_0.isLt) 0]
  have hx : zx (toZPt (vertexOf Tiling99.tiles[i99_0.val] 0)) = ((0:ℤ),(0:ℤ)) := by decide
  have hy : zy (toZPt (vertexOf Tiling99.tiles[i99_0.val] 0)) = ((0:ℤ),(0:ℤ)) := by decide
  rw [hx, hy]; simp [toR]

private theorem coord_t99_0_1 : (D99.tile i99_0).pts 1 = mkPt 32 0 := by
  show (pieceAt i99_0).pts 1 = _
  unfold pieceAt
  rw [pieceTri_pts Tiling99.tiles[i99_0.val] (List.getElem_mem i99_0.isLt) 1]
  have hx : zx (toZPt (vertexOf Tiling99.tiles[i99_0.val] 1)) = ((32:ℤ),(0:ℤ)) := by decide
  have hy : zy (toZPt (vertexOf Tiling99.tiles[i99_0.val] 1)) = ((0:ℤ),(0:ℤ)) := by decide
  rw [hx, hy]; simp [toR]

private theorem coord_t99_0_dist02 :
    dist ((D99.tile i99_0).pts 0) ((D99.tile i99_0).pts 2) = 64 := by
  apply Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
  show dist ((pieceAt i99_0).pts 0) ((pieceAt i99_0).pts 2) ^ 2 = 64 ^ 2
  unfold pieceAt
  rw [pieceTri_dist_sq Tiling99.tiles[i99_0.val] (List.getElem_mem i99_0.isLt) 0 2]
  have hd : Tiling99.dist2
      (vertexOf Tiling99.tiles[i99_0.val] 0)
      (vertexOf Tiling99.tiles[i99_0.val] 2) = (4096, 0) := by decide
  rw [hd]; simp [toR]; norm_num

theorem D99_corner0_hlay :
    ∃ (wl : GLI.Wall D99.toDissection) (E : ℕ → T99 × Fin 3) (n : ℕ),
      wl.a = D99.target.pts 0 ∧ wl.b = D99.target.pts 1 ∧ GLI.IsChain wl E n ∧
      EdgeWordConversion.len D99 (E 0) = sideOpp D99.model 0 := by
  -- Step 1: CornerChord at k = 0
  obtain ⟨iA, P, Q, hC⟩ :=
    corner_chord_data D99 (by decide) le_rfl (by norm_num) D99_model D99_angleData D99_shape 0
      (show cornerAngle (D99.target.pts 1) (D99.target.pts 0) (D99.target.pts 2) = β44 from by
        change cornerAngle (targetTri.pts 1) (targetTri.pts 0) (targetTri.pts 2) = _
        exact tgt99_hb0)
  -- Step 2: tile i99_0's vertex 0 is A = target.pts 0
  have h_t0_A : (D99.tile i99_0).pts 0 = D99.target.pts 0 := by
    rw [coord_t99_0_0]
    change mkPt 0 0 = targetTri.pts 0
    exact t99_pts0.symm
  have h0_mem : D99.target.pts 0 ∈ (D99.tile i99_0).carrier := by
    rw [← h_t0_A]; exact subset_convexHull ℝ _ ⟨0, rfl⟩
  -- Step 3: uniqueness → iA = i99_0
  have hiA : iA = i99_0 := (hC.unique i99_0 h0_mem).symm
  subst hiA
  -- Step 4: vertex index j = 0 of tile i99_0 is A
  obtain ⟨j, hjA, hvert⟩ := hC.vertex
  have hj : j = 0 := (D99.tile i99_0).indep.injective
    (hjA.symm.trans h_t0_A.symm)
  subst hj
  -- Step 5: P = tile i99_0 .pts 1 (lenAP = 32; if P = pts 2 then dist = 64 ≠ 32)
  have hPQ : P = (D99.tile i99_0).pts 1 := by
    rcases hvert with ⟨hP, _⟩ | ⟨hP, _⟩
    · exact hP
    · exfalso
      have h1 := hC.lenAP
      rw [hP, hjA] at h1
      have hfin : (0:Fin 3) + 2 = 2 := by decide
      rw [hfin, coord_t99_0_dist02, D99_model.hs0] at h1; norm_num at h1
  -- Step 6: partner tile i3
  obtain ⟨i3, ⟨hne3, k3, h3⟩, -⟩ :=
    corner_chord_partner D99_model (by decide) le_rfl (by norm_num) hC
  -- Step 7: corner_first_two_edges_sides → w-side has len(E 0) = sideOpp model 0
  obtain ⟨w, _, _, _, _, ⟨p, hp0, _, hPpos⟩, -, hPside, -⟩ :=
    corner_first_two_edges_sides D99_model D99_angleData D99_shape
      (by decide) le_rfl (by norm_num) hC hne3 h3
  -- Step 8: w = 1 (P.y = 0 since P = tile i99_0 .pts 1 = mkPt 32 0)
  have hw1 : w = 1 := by
    have hPy0 : P 1 = 0 := by
      rw [hPQ, coord_t99_0_1, mkPt_one]
    by_contra hw
    have hw2 : w = 2 := by fin_cases w <;> simp_all
    subst hw2
    have hPy_pos : P 1 > 0 := by
      rw [hPpos]
      have hA0y : D99.target.pts 0 1 = 0 := by
        change targetTri.pts 0 1 = 0; rw [t99_pts0, mkPt_one]
      have hV2y : D99.target.pts 2 1 = 72 * Real.sqrt 15 := by
        change targetTri.pts 2 1 = _; rw [t99_pts2, mkPt_one]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hA0y, hV2y, mul_zero, zero_add]
      exact mul_pos hp0 (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))
    linarith
  subst hw1
  -- Step 9: get a concrete wall from corner 0 to corner 1, apply w-universal
  obtain ⟨wl, hwa, hwb, E, n, hE⟩ := walls_exist D99 0 1 (by decide)
  exact ⟨wl, E, n, hwa, hwb, hE, (hPside wl hwa hwb E n hE).2.2.1⟩

/-! ## 6. The discriminating witness -/

/-- **`lem:cornerstep` at the real 99-tiling, base from corner 0.**  No sorry.
Demonstrates non-vacuity: D99 has `b = 48`-edges, but `corner_step_base` guarantees
the second base edge is `a = 32` or `c = 64` (never `b = 48`). -/
theorem D99_corner_step_corner0 :
    ∃ (wl : GLI.Wall D99.toDissection) (E : ℕ → T99 × Fin 3) (n : ℕ),
      wl.a = D99.target.pts 0 ∧ wl.b = D99.target.pts 1 ∧ GLI.IsChain wl E n ∧
      EdgeWordConversion.len D99 (E 0) = sideOpp D99.model 0 ∧
      (EdgeWordConversion.len D99 (E 1) = sideOpp D99.model 0 ∨
       EdgeWordConversion.len D99 (E 1) = sideOpp D99.model 2) := by
  obtain ⟨wl, E, n, hwa, hwb, hE, hlay⟩ := D99_corner0_hlay
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlen⟩ :=
    corner_step_base D99 (by decide) le_rfl (by norm_num) D99_model D99_angleData 2
      D99_iso₁ D99_iso₂ 0 (by decide) (by decide) (by decide) wl hwa hwb E n hE hlay
  exact ⟨wl, E, n, hwa, hwb, hE, hlay, hlen⟩

end Erdos634.CornerPara.Witness99
