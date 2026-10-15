-- Draft/FluxGRow3AngleWitnessDissection.lean: a real `CongruentDissection 2` witness for the right tile
-- and isosceles targets `(α, α, π − 2α)`, at the concrete angle `α456` (the angle of the `(4,5,6)`
-- triangle with `cos α456 = 3/4`, `Irrational (α456/π)` proved in `FluxGRow3AngleWitness.lean`).
--
-- The witness of `Draft/FluxGRow3Witness.lean` is a dissection of an isosceles target into two copies of
-- a right tile with legs `(2, 1)`, i.e. `tan α = 1/2` and `cos α = 2/√5 ≈ 0.894`, which is not `α456`
-- (`cos α456 = 3/4`). A different angle needs a different triangle.
--
-- The triangle: a right triangle with legs `3` and `√7` has `cos = 3/4` and `sin = √7/4` at the angle
-- opposite the `√7` leg (since `3² + 7 = 16 = 4²`), i.e. its acute angle at the leg-`3` vertex is exactly
-- `α456` (`cos_α456 : Real.cos α456 = 3/4` in `FluxRow4Witness.lean`). The construction is the same as in
-- `FluxGRow3Witness.lean`: right angle at the shared vertex `M`, base `B`/`C` mirrored across the leg
-- `MA`, target `(B, C, A)`, with legs `(3, √7)` in place of `(2, 1)`: `B = (−3,0)`, `M = (0,0)`,
-- `A = (0,√7)`, `C = (3,0)`. The hypotenuse `4` comes from `3² + (√7)² = 4²` and is unrelated to any
-- tile-parameter pair.
import Erdos634.CertBridge
import Erdos634.CertCoord
import Erdos634.Draft.FluxRow4Witness

namespace Erdos634.Draft.FluxGRow3AngleWitnessDissection

open Erdos634.Geometry Erdos634.CertCoord Erdos634.AreaDet

/-! ## §0 The angle-defining constant -/

/-- `√7`, the leg making the acute angle at the origin-adjacent vertex equal `α456`
(`cos = 3/4`, `sin = √7/4`, since `3² + (√7)² = 16 = 4²`). -/
noncomputable def sq7 : ℝ := Real.sqrt 7

theorem sq7_sq : sq7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)

theorem sq7_pos : 0 < sq7 := Real.sqrt_pos.mpr (by norm_num)

/-! ## §1 The three triangles, in coordinates -/

theorem hdet0 : det3 (-3) 0 0 0 0 sq7 ≠ 0 := by
  have := sq7_pos; unfold det3; nlinarith

theorem hdet1 : det3 3 0 0 0 0 sq7 ≠ 0 := by
  have := sq7_pos; unfold det3; nlinarith

theorem hDTpos : (0:ℝ) < det3 (-3) 0 3 0 0 sq7 := by
  have := sq7_pos; unfold det3; nlinarith

/-- `tile0 = (B, M, A) = ((-3,0), (0,0), (0,√7))`: legs `BM = 3`, `MA = √7`, hypotenuse `AB = 4`.
The angle at `B` is exactly `α456` (`cos = 3/4`, `sin = √7/4`). -/
noncomputable def tile0 : Tri := mkTri (-3) 0 0 0 0 sq7 hdet0

/-- `tile1 = (C, M, A) = ((3,0), (0,0), (0,√7))`, the mirror image of `tile0` across `x = 0`. -/
noncomputable def tile1 : Tri := mkTri 3 0 0 0 0 sq7 hdet1

/-- `target = (B, C, A) = ((-3,0), (3,0), (0,√7))`, the isosceles triangle `(α456, α456, π − 2α456)`. -/
noncomputable def target : Tri := mkTri (-3) 0 3 0 0 sq7 hDTpos.ne'

/-- The model tile: `tile0` itself (every tile is congruent to it, `tile1` by an explicit isometry
below). -/
noncomputable def model : Tri := tile0

/-- The two-tile family. -/
noncomputable def tileF : Fin 2 → Tri := ![tile0, tile1]

/-! ## §2 Congruence — the (C1) check -/

theorem tile0_pts : tile0.pts = ![mkPt (-3) 0, mkPt 0 0, mkPt 0 sq7] := mkTri_pts _ _ _ _ _ _ _
theorem tile1_pts : tile1.pts = ![mkPt 3 0, mkPt 0 0, mkPt 0 sq7] := mkTri_pts _ _ _ _ _ _ _

theorem hd01 : ∀ i, dist ((tileF i).pts 0) ((tileF i).pts 1) = dist (model.pts 0) (model.pts 1) := by
  intro i
  fin_cases i
  · rfl
  · show dist ((tile1).pts 0) ((tile1).pts 1) = dist ((tile0).pts 0) ((tile0).pts 1)
    rw [tile0_pts, tile1_pts]
    show dist (mkPt 3 0) (mkPt 0 0) = dist (mkPt (-3) 0) (mkPt 0 0)
    apply Erdos634.SssCongruent.dist_of_sq
    rw [dist_sq_mkPt, dist_sq_mkPt]; ring

theorem hd12 : ∀ i, dist ((tileF i).pts 1) ((tileF i).pts 2) = dist (model.pts 1) (model.pts 2) := by
  intro i
  fin_cases i
  · rfl
  · show dist ((tile1).pts 1) ((tile1).pts 2) = dist ((tile0).pts 1) ((tile0).pts 2)
    rw [tile0_pts, tile1_pts]
    simp

theorem hd20 : ∀ i, dist ((tileF i).pts 2) ((tileF i).pts 0) = dist (model.pts 2) (model.pts 0) := by
  intro i
  fin_cases i
  · rfl
  · show dist ((tile1).pts 2) ((tile1).pts 0) = dist ((tile0).pts 2) ((tile0).pts 0)
    rw [tile0_pts, tile1_pts]
    show dist (mkPt 0 sq7) (mkPt 3 0) = dist (mkPt 0 sq7) (mkPt (-3) 0)
    apply Erdos634.SssCongruent.dist_of_sq
    rw [dist_sq_mkPt, dist_sq_mkPt]; ring

/-! ## §3 Containment in the target — the (C2) check -/

theorem memB : mkPt (-3 : ℝ) 0 ∈ target.carrier := by
  have := sq7_pos
  exact Erdos634.CertCoord.mem_carrier_of_dets hDTpos (by unfold det3; nlinarith)
    (by unfold det3; nlinarith) (by unfold det3; nlinarith)

theorem memM : mkPt (0 : ℝ) 0 ∈ target.carrier := by
  have := sq7_pos
  exact Erdos634.CertCoord.mem_carrier_of_dets hDTpos (by unfold det3; nlinarith)
    (by unfold det3; nlinarith) (by unfold det3; nlinarith)

theorem memA : mkPt (0 : ℝ) sq7 ∈ target.carrier := by
  have := sq7_pos
  exact Erdos634.CertCoord.mem_carrier_of_dets hDTpos (by unfold det3; nlinarith)
    (by unfold det3; nlinarith) (by unfold det3; nlinarith)

theorem memC : mkPt (3 : ℝ) 0 ∈ target.carrier := by
  have := sq7_pos
  exact Erdos634.CertCoord.mem_carrier_of_dets hDTpos (by unfold det3; nlinarith)
    (by unfold det3; nlinarith) (by unfold det3; nlinarith)

theorem tile0_sub : tile0.carrier ⊆ target.carrier := by
  show Erdos634.Geometry.Tri.carrier tile0 ⊆ target.carrier
  unfold Erdos634.Geometry.Tri.carrier
  rw [tile0_pts]
  apply convexHull_min _ target.convex
  rintro p ⟨i, rfl⟩
  fin_cases i
  · exact memB
  · exact memM
  · exact memA

theorem tile1_sub : tile1.carrier ⊆ target.carrier := by
  show Erdos634.Geometry.Tri.carrier tile1 ⊆ target.carrier
  unfold Erdos634.Geometry.Tri.carrier
  rw [tile1_pts]
  apply convexHull_min _ target.convex
  rintro p ⟨i, rfl⟩
  fin_cases i
  · exact memC
  · exact memM
  · exact memA

theorem hsub : ∀ i, (tileF i).carrier ⊆ target.carrier := by
  intro i; fin_cases i
  · exact tile0_sub
  · exact tile1_sub

/-! ## §4 Disjoint interiors — the (C3) check

Identical argument to `FluxGRow3Witness.lean` (P74): `tile0` lies in the closed half-plane
`x ≤ 0`, `tile1` in `x ≥ 0`, and a boundary point of either tile's *interior* would force a whole
ball into the wrong half-plane. This part of the construction is fully generic (it never mentions
`sq7`), so it is reused verbatim, not reproved. -/

theorem hlin0 : IsLinearMap ℝ (fun y : Plane => y 0) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem convex_le0 : Convex ℝ {p : Plane | p 0 ≤ 0} := convex_halfSpace_le hlin0 0
theorem convex_ge0 : Convex ℝ {p : Plane | 0 ≤ p 0} := convex_halfSpace_ge hlin0 0

theorem tile0_le0 : tile0.carrier ⊆ {p : Plane | p 0 ≤ 0} := by
  show Erdos634.Geometry.Tri.carrier tile0 ⊆ _
  unfold Erdos634.Geometry.Tri.carrier
  rw [tile0_pts]
  apply convexHull_min _ convex_le0
  rintro p ⟨i, rfl⟩
  fin_cases i <;> simp [mkPt_zero]

theorem tile1_ge0 : tile1.carrier ⊆ {p : Plane | 0 ≤ p 0} := by
  show Erdos634.Geometry.Tri.carrier tile1 ⊆ _
  unfold Erdos634.Geometry.Tri.carrier
  rw [tile1_pts]
  apply convexHull_min _ convex_ge0
  rintro p ⟨i, rfl⟩
  fin_cases i <;> simp [mkPt_zero]

theorem dist_eq_of_sq {x y : Plane} {s : ℝ} (hs : 0 ≤ s) (h : dist x y ^ 2 = s ^ 2) :
    dist x y = s :=
  (pow_left_inj₀ dist_nonneg hs two_ne_zero).mp h

theorem interior_lt0_of_le0 (T : Tri) (h : T.carrier ⊆ {p : Plane | p 0 ≤ 0}) :
    interior T.carrier ⊆ {p : Plane | p 0 < 0} := by
  intro p hp
  have hp' : p ∈ T.carrier := interior_subset hp
  have hle : p 0 ≤ 0 := h hp'
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
    set v : Plane := mkPt (r / 2) 0 with hv
    set q : Plane := p + v with hq
    have hq0 : q 0 = p 0 + r / 2 := by
      show p 0 + v 0 = p 0 + r / 2
      rw [hv, mkPt_zero]
    have hq1 : q 1 = p 1 := by
      show p 1 + v 1 = p 1
      rw [hv, mkPt_one]; ring
    have hdistsq : dist p q ^ 2 = (r / 2) ^ 2 := by
      rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
        Real.dist_eq, hq0, hq1, sq_abs, sq_abs]
      ring
    have hdisteq : dist p q = r / 2 := dist_eq_of_sq (by linarith) hdistsq
    have hballmem : q ∈ Metric.ball p r := by
      rw [Metric.mem_ball, dist_comm, hdisteq]; linarith
    have hqT : q ∈ T.carrier := interior_subset (hball hballmem)
    have hqle : q 0 ≤ 0 := h hqT
    rw [hq0, ← heq] at hqle
    linarith

theorem interior_gt0_of_ge0 (T : Tri) (h : T.carrier ⊆ {p : Plane | 0 ≤ p 0}) :
    interior T.carrier ⊆ {p : Plane | 0 < p 0} := by
  intro p hp
  have hp' : p ∈ T.carrier := interior_subset hp
  have hge : 0 ≤ p 0 := h hp'
  rcases lt_or_eq_of_le hge with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
    set v : Plane := mkPt (-(r / 2)) 0 with hv
    set q : Plane := p + v with hq
    have hq0 : q 0 = p 0 - r / 2 := by
      show p 0 + v 0 = p 0 - r / 2
      rw [hv, mkPt_zero]; ring
    have hq1 : q 1 = p 1 := by
      show p 1 + v 1 = p 1
      rw [hv, mkPt_one]; ring
    have hdistsq : dist p q ^ 2 = (r / 2) ^ 2 := by
      rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
        Real.dist_eq, hq0, hq1, sq_abs, sq_abs]
      ring
    have hdisteq : dist p q = r / 2 := dist_eq_of_sq (by linarith) hdistsq
    have hballmem : q ∈ Metric.ball p r := by
      rw [Metric.mem_ball, dist_comm, hdisteq]; linarith
    have hqT : q ∈ T.carrier := interior_subset (hball hballmem)
    have hqge : 0 ≤ q 0 := h hqT
    rw [hq0, ← heq] at hqge
    linarith

theorem tiles01_disjoint : Disjoint (interior tile0.carrier) (interior tile1.carrier) := by
  rw [Set.disjoint_left]
  intro p hp0 hp1
  have h0 : p 0 < 0 := interior_lt0_of_le0 tile0 tile0_le0 hp0
  have h1 : 0 < p 0 := interior_gt0_of_ge0 tile1 tile1_ge0 hp1
  linarith

theorem hdisj :
    Pairwise fun i j => Disjoint (interior ((tileF i)).carrier) (interior ((tileF j)).carrier) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact tiles01_disjoint
    | exact tiles01_disjoint.symm

/-! ## §5 The area identity — the (C4) check -/

theorem hdet : ∑ i, |Erdos634.AreaDet.detTri (tileF i)| = |Erdos634.AreaDet.detTri target| := by
  have hs := sq7_pos
  have e0 : Erdos634.AreaDet.detTri tile0 = det3 (-3) 0 0 0 0 sq7 := detTri_mkTri _ _ _ _ _ _ hdet0
  have e1 : Erdos634.AreaDet.detTri tile1 = det3 3 0 0 0 0 sq7 := detTri_mkTri _ _ _ _ _ _ hdet1
  have eT : Erdos634.AreaDet.detTri target = det3 (-3) 0 3 0 0 sq7 :=
    detTri_mkTri _ _ _ _ _ _ hDTpos.ne'
  have hv0 : det3 (-3) 0 0 0 0 sq7 = 3 * sq7 := by unfold det3; ring
  have hv1 : det3 3 0 0 0 0 sq7 = -(3 * sq7) := by unfold det3; ring
  have hvT : det3 (-3) 0 3 0 0 sq7 = 6 * sq7 := by unfold det3; ring
  simp only [tileF, Fin.sum_univ_two]
  show |Erdos634.AreaDet.detTri tile0| + |Erdos634.AreaDet.detTri tile1| = _
  rw [e0, e1, eT, hv0, hv1, hvT]
  rw [abs_of_pos (by linarith : (0:ℝ) < 3 * sq7), abs_of_neg (by linarith : -(3 * sq7) < (0:ℝ)),
    abs_of_pos (by linarith : (0:ℝ) < 6 * sq7)]
  ring

/-! ## §6 The witness -/

/-- **The witness.** `CertBridge.ofCert` applied to the four checks above: a genuine
`CongruentDissection 2` of the isosceles right-tile target `(α456, α456, π − 2α456)`
(`cos α456 = 3/4`, `Irrational (α456/π)`), transcribing `FluxGRow3Witness.lean`'s (P74) own
method, re-parametrized at legs `(3, √7)` instead of `(2, 1)` to land exactly on `α456`. -/
noncomputable def dissection : CongruentDissection 2 :=
  Erdos634.CertBridge.ofCert target model tileF hd01 hd12 hd20 hsub hdisj hdet

theorem dissection_target : dissection.target = target := rfl
theorem dissection_model : dissection.model = model := rfl

/-! ## Connecting the target angle to `α456`

The base angle of `target` at `B = (-3,0)` equals `α456` exactly: both have `cos = 3/4` in a right triangle
with legs `3, √7` and hypotenuse `4`, with the angle taken at the leg-`3` vertex. This is stated through
the shared side-length data rather than by re-deriving `Tri.angleAt`: the side lengths of `tile0`
(`BM = 3`, `MA = sq7`, `AB = 4`) match the law-of-cosines data of `T456` (`cos_α456`'s `3/4`). -/

theorem tile0_dist_BM : dist (mkPt (-3:ℝ) 0) (mkPt 0 0) = 3 := by
  apply dist_eq_of_sq (by norm_num)
  rw [dist_sq_mkPt]; norm_num

theorem tile0_dist_MA : dist (mkPt (0:ℝ) 0) (mkPt 0 sq7) = sq7 := by
  apply dist_eq_of_sq sq7_pos.le
  rw [dist_sq_mkPt]; ring

theorem tile0_dist_AB : dist (mkPt (-3:ℝ) 0) (mkPt 0 sq7) = 4 := by
  have h7 := sq7_sq
  apply dist_eq_of_sq (by norm_num)
  rw [dist_sq_mkPt]; nlinarith

/-- **The three side lengths of `tile0` are exactly `3`, `√7`, `4`**: the `3-√7-4` right-triangle shape
whose leg-`3` angle has `cos = 3/4`, i.e. exactly `α456` (`cos_α456`, `FluxRow4Witness.lean`). These
lengths are propagated by `hd01/hd12/hd20` to every tile in `tileF` (each congruent to `model = tile0`),
so all tiles of the dissection carry this shape. The statement uses shared side lengths rather than
re-deriving `Tri.angleAt`, since a right triangle's side lengths determine its angles uniquely (the
law-of-cosines machinery `AngleThreshold.cos_of_sides` covers that step generically). -/
theorem tile0_shape_matches_α456 :
    dist (mkPt (-3:ℝ) 0) (mkPt 0 0) = 3 ∧
    dist (mkPt (0:ℝ) 0) (mkPt 0 sq7) = sq7 ∧
    dist (mkPt (-3:ℝ) 0) (mkPt 0 sq7) = 4 :=
  ⟨tile0_dist_BM, tile0_dist_MA, tile0_dist_AB⟩

end Erdos634.Draft.FluxGRow3AngleWitnessDissection

#print axioms Erdos634.Draft.FluxGRow3AngleWitnessDissection.dissection
#print axioms Erdos634.Draft.FluxGRow3AngleWitnessDissection.hdisj
#print axioms Erdos634.Draft.FluxGRow3AngleWitnessDissection.hdet
#print axioms Erdos634.Draft.FluxGRow3AngleWitnessDissection.tile0_shape_matches_α456
