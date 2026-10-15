-- Draft/CVGCevianCutGen.lean -- the geometric cevian cut of the atom for ARBITRARY m at (e,f)=(1,2).
-- Generalizes CVCCevianCut (m = 4k) to every m >= 1: Delta_m = m(8,8,11) = 2 T_{2m} u A_m, counts 4m^2 + 3m^2 + 4m^2 = 11 m^2.
-- Then: m = 1 is not in the atom spectrum, via FDBBaseBetaE1.thm_basebeta_e1.
-- Imported by `All`.  No sorry, no native_decide.
import Erdos634.Draft.FDCCevianAtom
import Erdos634.Draft.FDBBaseBetaE1
import Erdos634.Draft.CVCCevianCut
import Erdos634.UnionDissection
import Erdos634.SssCongruent
import Erdos634.Ladder
import Erdos634.DissectionMap
import Erdos634.CongruentArea
import Erdos634.CertCoord
import Erdos634.AreaDet
import Erdos634.Subdivision

namespace Erdos634.Draft.CVGCevianCutGen

open Erdos634.Geometry MeasureTheory
open Erdos634.Draft.FDBBaseBetaE1 (HasSides congruent_of_hasSides)
open Erdos634.Draft.FDCCevianAtom (hasSides_scaleN hasSides_congr atomTiles atomSpectrum12)
open Erdos634.Draft.CVCCevianCut


theorem assemble (m : ℕ) (hm : 0 < m) (DA : CongruentDissection (3 * m ^ 2))
    (ht : HasSides DA.model 2 3 4) (W U V : Plane)
    (hcar : DA.target.carrier = convexHull ℝ {W, U, V})
    (hUV : dist U V = 3 * m) (hVW : dist V W = 6 * m) (hWU : dist W U = 6 * m)
    (hD : cr W U V ≠ 0) :
    ∃ (Δ : Tri) (D : CongruentDissection ((2 * m) * (2 * m) * 1 + (3 * m ^ 2 + (2 * m) * (2 * m) * 1)))
      (D1 : CongruentDissection ((2 * m) * (2 * m) * 1)) (D2 : CongruentDissection ((2 * m) * (2 * m) * 1)),
      HasSides Δ (8 * m) (8 * m) (11 * m) ∧ D.target = Δ ∧ HasSides D.model 2 3 4 ∧
      D1.model = D.model ∧ DA.model = D.model ∧ D2.model = D.model ∧
      (∃ T1 : Tri, HasSides T1 (4 * m) (6 * m) (8 * m) ∧ D1.target.carrier = T1.carrier) ∧
      (∃ T2 : Tri, HasSides T2 (4 * m) (6 * m) (8 * m) ∧ D2.target.carrier = T2.carrier) ∧
      D1.target.carrier ∪ (DA.target.carrier ∪ D2.target.carrier) = Δ.carrier ∧
      Disjoint (interior D1.target.carrier) (interior (DA.target.carrier ∪ D2.target.carrier)) ∧
      Disjoint (interior DA.target.carrier) (interior D2.target.carrier) ∧
      (∀ i, D.tile (Fin.castAdd _ i) = D1.tile i) ∧
      (∀ i, D.tile (Fin.natAdd _ (Fin.castAdd _ i)) = DA.tile i) ∧
      (∀ i, D.tile (Fin.natAdd _ (Fin.natAdd _ i)) = D2.tile i) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hUV' := sqd_of_dist _ _ _ hUV
  have hVW' := sqd_of_dist _ _ _ hVW
  have hWU' := sqd_of_dist _ _ _ hWU
  obtain ⟨X, hX⟩ : ∃ X : Plane, X = U - (4 / 3 : ℝ) • (V - U) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Plane, Y = V + (4 / 3 : ℝ) • (V - U) := ⟨_, rfl⟩
  have hX0 : X 0 = U 0 - 4 / 3 * (V 0 - U 0) := by rw [hX]; simp
  have hX1 : X 1 = U 1 - 4 / 3 * (V 1 - U 1) := by rw [hX]; simp
  have hY0 : Y 0 = V 0 + 4 / 3 * (V 0 - U 0) := by rw [hY]; simp
  have hY1 : Y 1 = V 1 + 4 / 3 * (V 1 - U 1) := by rw [hY]; simp
  -- determinants
  have c1 : cr W X Y ≠ 0 := by
    have : cr W X Y = 11 / 3 * cr W U V := by unfold cr; rw [hX0, hX1, hY0, hY1]; ring
    rw [this]; exact mul_ne_zero (by norm_num) hD
  have c2 : cr W X U ≠ 0 := by
    have : cr W X U = 4 / 3 * cr W U V := by unfold cr; rw [hX0, hX1]; ring
    rw [this]; exact mul_ne_zero (by norm_num) hD
  have c3 : cr W Y V ≠ 0 := by
    have : cr W Y V = -(4 / 3) * cr W U V := by unfold cr; rw [hY0, hY1]; ring
    rw [this]; exact mul_ne_zero (by norm_num) hD
  have c4 : cr W U Y ≠ 0 := by
    have : cr W U Y = 7 / 3 * cr W U V := by unfold cr; rw [hY0, hY1]; ring
    rw [this]; exact mul_ne_zero (by norm_num) hD
  -- distances
  have dWX : dist W X = 8 * m := dist_of_sqd _ _ _ (by positivity) (by
    rw [hX0, hX1]; linear_combination (7 / 3) * hWU' + (-4 / 3) * hVW' + (28 / 9) * hUV')
  have dXU : dist X U = 4 * m := dist_of_sqd _ _ _ (by positivity) (by
    rw [hX0, hX1]; linear_combination (16 / 9) * hUV')
  have dWY : dist W Y = 8 * m := dist_of_sqd _ _ _ (by positivity) (by
    rw [hY0, hY1]; linear_combination (-4 / 3) * hWU' + (7 / 3) * hVW' + (28 / 9) * hUV')
  have dYV : dist Y V = 4 * m := dist_of_sqd _ _ _ (by positivity) (by
    rw [hY0, hY1]; linear_combination (16 / 9) * hUV')
  have dXY : dist X Y = 11 * m := dist_of_sqd _ _ _ (by positivity) (by
    rw [hX0, hX1, hY0, hY1]; linear_combination (121 / 9) * hUV')
  have dUW : dist U W = 6 * m := by rw [dist_comm]; exact hWU
  have dWV : dist W V = 6 * m := by rw [dist_comm]; exact hVW
  -- the four triangles
  let Δ : Tri := triOf W X Y c1
  let T1 : Tri := triOf W X U c2
  let M : Tri := triOf W U Y c4
  let T2 : Tri := triOf W Y V c3
  have hs1 : HasSides T1 (4 * m) (6 * m) (8 * m) :=
    ⟨Equiv.refl _, dXU, dUW, dWX⟩
  have hs2 : HasSides T2 (4 * m) (6 * m) (8 * m) :=
    ⟨Equiv.refl _, dYV, hVW, dWY⟩
  have hsK1 : HasSides T1 (((2 * m : ℕ) : ℝ) * 2) (((2 * m : ℕ) : ℝ) * 3) (((2 * m : ℕ) : ℝ) * 4) :=
    hasSides_congr hs1 (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
  have hsK2 : HasSides T2 (((2 * m : ℕ) : ℝ) * 2) (((2 * m : ℕ) : ℝ) * 3) (((2 * m : ℕ) : ℝ) * 4) :=
    hasSides_congr hs2 (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
  have hk8 : 0 < 2 * m := by omega
  obtain ⟨E1, hE1c, hE1m⟩ := tileK DA.model T1 (2 * m) hk8 ht hsK1
  obtain ⟨E2, hE2c, hE2m⟩ := tileK DA.model T2 (2 * m) hk8 ht hsK2
  have hsw : ({W, V, Y} : Set Plane) = {W, Y, V} := by rw [Set.pair_comm V Y]
  have hP1 : U = X + (4 / 11 : ℝ) • (Y - X) := by rw [hX, hY]; module
  have hP2 : V = U + (3 / 7 : ℝ) • (Y - U) := by rw [hY]; module
  have cov1 := fan_cover W X Y U (4 / 11) (by norm_num) (by norm_num) hP1
  have dis1 := fan_disjoint W X Y U (4 / 11) (by norm_num) (by norm_num) hP1 c1
  have cov2 := fan_cover W U Y V (3 / 7) (by norm_num) (by norm_num) hP2
  have dis2 := fan_disjoint W U Y V (3 / 7) (by norm_num) (by norm_num) hP2 c4
  have hT1c : T1.carrier = convexHull ℝ {W, X, U} := carrier_triOf _ _ _ c2
  have hT2c : T2.carrier = convexHull ℝ {W, Y, V} := carrier_triOf _ _ _ c3
  have hMc : M.carrier = convexHull ℝ {W, U, Y} := carrier_triOf _ _ _ c4
  have hΔc : Δ.carrier = convexHull ℝ {W, X, Y} := carrier_triOf _ _ _ c1
  have hcov2 : DA.target.carrier ∪ E2.target.carrier = M.carrier := by
    rw [hcar, hE2c, hT2c, hMc, ← hsw]; exact cov2.symm
  have hdisj2 : Disjoint (interior DA.target.carrier) (interior E2.target.carrier) := by
    rw [hcar, hE2c, hT2c, ← hsw]; exact dis2
  have hcov1 : E1.target.carrier ∪ M.carrier = Δ.carrier := by
    rw [hE1c, hT1c, hMc, hΔc]; exact cov1.symm
  have hdisj1 : Disjoint (interior E1.target.carrier) (interior M.carrier) := by
    rw [hE1c, hT1c, hMc]; exact dis1
  let inner : CongruentDissection (3 * m ^ 2 + (2 * m) * (2 * m) * 1) :=
    unionCongruentDissection M DA E2 hE2m.symm hcov2 hdisj2
  have hinT : inner.target = M := rfl
  have hinM : inner.model = DA.model := rfl
  let outer := unionCongruentDissection Δ E1 inner (by rw [hinM]; exact hE1m)
    (by rw [hinT]; exact hcov1) (by rw [hinT]; exact hdisj1)
  let τ : Equiv.Perm (Fin 3) := ⟨![1, 2, 0], ![2, 0, 1], fun x => by fin_cases x <;> rfl,
    fun x => by fin_cases x <;> rfl⟩
  have hΔs : HasSides Δ (8 * m) (8 * m) (11 * m) := by
    refine ⟨τ, ?_, ?_, ?_⟩
    · show dist Y W = 8 * m
      rw [dist_comm]; exact dWY
    · show dist W X = 8 * m
      exact dWX
    · show dist X Y = 11 * m
      exact dXY
  have houtM : outer.model = E1.model := rfl
  refine ⟨Δ, outer, E1, E2, hΔs, rfl, ?_, rfl, ?_, ?_, ⟨T1, hs1, hE1c⟩, ⟨T2, hs2, hE2c⟩, ?_, ?_,
    hdisj2, ?_, ?_, ?_⟩
  · rw [houtM, hE1m]; exact ht
  · rw [houtM, hE1m]
  · rw [houtM, hE2m, hE1m]
  · rw [hcov2]; exact hcov1
  · rw [hcov2]; exact hdisj1
  · intro i
    show Fin.append E1.tile inner.tile (Fin.castAdd _ i) = _
    rw [Fin.append_left]
  · intro i
    show Fin.append E1.tile inner.tile (Fin.natAdd _ (Fin.castAdd _ i)) = _
    rw [Fin.append_right]
    show Fin.append DA.tile E2.tile (Fin.castAdd _ i) = _
    rw [Fin.append_left]
  · intro i
    show Fin.append E1.tile inner.tile (Fin.natAdd _ (Fin.natAdd _ i)) = _
    rw [Fin.append_right]
    show Fin.append DA.tile E2.tile (Fin.natAdd _ i) = _
    rw [Fin.append_right]


/-- **The geometric cevian cut, general `m` at `(e,f)=(1,2)`**: any tiling `DA` of the
atom `A_m` (legs `6m`, base `3m`, `3m^2` tiles of `(2,3,4)`) yields a `CongruentDissection` of
`Delta_m = m(8,8,11)` with `(2m)^2 + (3m^2 + (2m)^2) = 11 m^2` tiles, the concatenation `T1 ++ DA ++ T2`. -/
theorem cevian_cut_gen (m : ℕ) (hm : 0 < m) (DA : CongruentDissection (3 * m ^ 2))
    (ht : HasSides DA.model 2 3 4)
    (hA : HasSides DA.target (3 * m) (6 * m) (6 * m)) :
    ∃ (Δ : Tri) (D : CongruentDissection ((2 * m) * (2 * m) * 1 + (3 * m ^ 2 + (2 * m) * (2 * m) * 1)))
      (D1 : CongruentDissection ((2 * m) * (2 * m) * 1)) (D2 : CongruentDissection ((2 * m) * (2 * m) * 1)),
      HasSides Δ (8 * m) (8 * m) (11 * m) ∧ D.target = Δ ∧ HasSides D.model 2 3 4 ∧
      D1.model = D.model ∧ DA.model = D.model ∧ D2.model = D.model ∧
      (∃ T1 : Tri, HasSides T1 (4 * m) (6 * m) (8 * m) ∧ D1.target.carrier = T1.carrier) ∧
      (∃ T2 : Tri, HasSides T2 (4 * m) (6 * m) (8 * m) ∧ D2.target.carrier = T2.carrier) ∧
      D1.target.carrier ∪ (DA.target.carrier ∪ D2.target.carrier) = Δ.carrier ∧
      Disjoint (interior D1.target.carrier) (interior (DA.target.carrier ∪ D2.target.carrier)) ∧
      Disjoint (interior DA.target.carrier) (interior D2.target.carrier) ∧
      (∀ i, D.tile (Fin.castAdd _ i) = D1.tile i) ∧
      (∀ i, D.tile (Fin.natAdd _ (Fin.castAdd _ i)) = DA.tile i) ∧
      (∀ i, D.tile (Fin.natAdd _ (Fin.natAdd _ i)) = D2.tile i) := by
  obtain ⟨τ, h12, h20, h01⟩ := hA
  refine assemble m hm DA ht (DA.target.pts (τ 0)) (DA.target.pts (τ 1)) (DA.target.pts (τ 2)) ?_
    h12 h20 h01 (cr_pts_ne_zero (DA.target.relabel τ))
  unfold Tri.carrier
  rw [range_perm DA.target τ]

/-- `A_m` tiles implies `Delta_m = m(8,8,11)` has an `11 m^2`-tile `CongruentDissection` by `(2,3,4)`. -/
theorem atomTiles_imp_delta (m : ℕ) (hm : 0 < m) (h : atomTiles m) :
    ∃ (Δ : Tri) (D : CongruentDissection (11 * m ^ 2)),
      HasSides Δ (8 * m) (8 * m) (11 * m) ∧ D.target = Δ ∧ HasSides D.model 2 3 4 := by
  obtain ⟨DA, hAs, hAm⟩ := h
  obtain ⟨Δ, D, D1, D2, hΔ, hDt, hDm, -⟩ := cevian_cut_gen m hm DA hAm hAs
  obtain ⟨E, hEt, hEm⟩ := exists_reindex (M := 11 * m ^ 2) (by ring) D
  exact ⟨Δ, E, hΔ, by rw [hEt, hDt], by rw [hEm]; exact hDm⟩

/-- **`prop:cevianatom`, clause "the atom spectrum excludes `m = 1`"** (at `(1,2)`): `A_1` admits no tiling.
Derived from the cut and `thm_basebeta_e1` (all `N` quantified; the cut gives `N = 11`). -/
theorem atomTiles_one_false : ¬ atomTiles 1 := by
  intro h
  obtain ⟨Δ, D, hΔ, hDt, hDm⟩ := atomTiles_imp_delta 1 one_pos h
  rw [← hDt] at hΔ
  exact Erdos634.Draft.FDBBaseBetaE1.thm_basebeta_e1 D
    (by simpa using hΔ) hDm

theorem one_not_mem_atomSpectrum12 : 1 ∉ atomSpectrum12 := fun h => atomTiles_one_false h.2

/-- Non-vacuity of the cut hypotheses at general `m`: `A_{4k}` has a tiling (so `atomTiles_imp_delta` is
applied to a real hypothesis; instance `m = 4`, giving `Delta_4` with 176 tiles). -/
theorem atomTiles_imp_delta_witness :
    ∃ (Δ : Tri) (D : CongruentDissection (11 * 4 ^ 2)),
      HasSides Δ (8 * (4:ℕ)) (8 * (4:ℕ)) (11 * (4:ℕ)) ∧ D.target = Δ ∧ HasSides D.model 2 3 4 :=
  atomTiles_imp_delta 4 (by norm_num) Erdos634.Draft.FDCCevianAtom.atomTiles_four

end Erdos634.Draft.CVGCevianCutGen

#print axioms Erdos634.Draft.CVGCevianCutGen.assemble
#print axioms Erdos634.Draft.CVGCevianCutGen.cevian_cut_gen
#print axioms Erdos634.Draft.CVGCevianCutGen.atomTiles_imp_delta
#print axioms Erdos634.Draft.CVGCevianCutGen.atomTiles_one_false
#print axioms Erdos634.Draft.CVGCevianCutGen.one_not_mem_atomSpectrum12
#print axioms Erdos634.Draft.CVGCevianCutGen.atomTiles_imp_delta_witness
