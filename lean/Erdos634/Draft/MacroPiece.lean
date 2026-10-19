-- Draft/MacroPiece.lean — macro pieces: a triangle similar (integer ratio k) to the target of a dissection already in Lean
-- is tiled by k²·n copies of the model, as a `LadderFam.TFam` ready for `pack_exists'`.  UNAUDITED.
-- Ingredients: Ladder.ladder (thm:ladder), SssCongruent, Mazur-Ulam transport (DissectionMap).  Idea of macro dissections: Laczkovich, Herdt; seeds Paliy.
import Erdos634.Draft.LadderFam
import Erdos634.Ladder
import Erdos634.Draft.FDBBaseBetaE1

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.MacroPiece
open Erdos634.Draft.LadderFam Erdos634.Ladder Erdos634.Subdivision Erdos634.DissectionMap

open Erdos634.Draft.WFrameF Erdos634.Draft.WBrickF Erdos634.Draft.S2L

theorem hY_of_three (Y T : Tri) (k : ℝ)
    (h01 : dist (Y.pts 0) (Y.pts 1) = k * dist (T.pts 0) (T.pts 1))
    (h12 : dist (Y.pts 1) (Y.pts 2) = k * dist (T.pts 1) (T.pts 2))
    (h20 : dist (Y.pts 2) (Y.pts 0) = k * dist (T.pts 2) (T.pts 0)) :
    ∀ p q : Fin 3, dist (Y.pts p) (Y.pts q) = k * dist (T.pts p) (T.pts q) := by
  intro p q
  fin_cases p <;> fin_cases q <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, dist_self, mul_zero] <;>
    first | exact h01 | exact h12 | exact h20 | (rw [dist_comm, h01, dist_comm]) | (rw [dist_comm, h12, dist_comm]) |
      (rw [dist_comm, h20, dist_comm])

theorem macroTFam_gen {n : ℕ} (D : CongruentDissection n) (k : ℕ) (hk : 0 < k) (Y M : Tri)
    (hM : D.model.Congruent M)
    (hC : ∀ T0 : Tri, (∀ i j : Fin 3, dist (T0.pts i) (T0.pts j) = k * dist (D.target.pts i) (D.target.pts j)) →
      T0.Congruent Y) :
    Nonempty (TFam Y.carrier M (k * k * n)) := by
  have hT : D.target = (⟨![D.target.pts 0, D.target.pts 1, D.target.pts 2], by
      have := D.target.indep
      convert this using 1; funext i; fin_cases i <;> rfl⟩ : Tri) := by
    cases hD : D.target with
    | mk p ip => congr 1; funext i; fin_cases i <;> rfl
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder _ _ _ _ D hT k hk
  have hd : ∀ (A B C : Plane), dist (A + (k : ℝ) • (B - A)) (A + (k : ℝ) • (C - A)) = k * dist B C := by
    intro A B C
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_natCast]
    congr 2; abel
  have hd0 : ∀ (A B : Plane), dist A (A + (k : ℝ) • (B - A)) = k * dist A B := by
    intro A B
    rw [dist_eq_norm, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_natCast, ← norm_neg (B - A)]
    simp
  have hbd : ∀ i j : Fin 3, dist (E.target.pts i) (E.target.pts j) = k * dist (D.target.pts i) (D.target.pts j) := by
    rw [hEt]
    refine hY_of_three _ _ _ ?_ ?_ ?_
    · rw [bigTri_pts0, bigTri_pts1]; unfold P; simp only [Nat.cast_zero, zero_smul, add_zero]
      exact hd0 _ _
    · rw [bigTri_pts1, bigTri_pts2]; unfold P; simp only [Nat.cast_zero, zero_smul, add_zero, zero_add]
      exact hd _ _ _
    · rw [bigTri_pts2, bigTri_pts0]; unfold P; simp only [Nat.cast_zero, zero_smul, add_zero, zero_add]
      rw [dist_comm, hd0, dist_comm]
  have hcong : (E.target).Congruent Y := hC _ hbd
  obtain ⟨f, σ, hf⟩ := hcong
  have hcar : f '' E.target.carrier = Y.carrier := Erdos634.CongruentArea.image_carrier_of_congruent hf
  refine ⟨{ tile := fun i => mapTri (isoAff f) (E.tile i), sub := ?_, disj := ?_, cong := ?_ }⟩
  · intro i
    rw [mapTri_carrier, isoAff_coe, ← hcar]
    exact Set.image_mono (by rw [← E.covers]; exact Set.subset_iUnion (fun i => (E.tile i).carrier) i)
  · intro i j hij
    rw [mapTri_carrier, mapTri_carrier, isoAff_coe]
    have := f.toHomeomorph.image_interior (E.tile i).carrier
    have h2 := f.toHomeomorph.image_interior (E.tile j).carrier
    simp only [IsometryEquiv.coe_toHomeomorph] at this h2
    rw [← this, ← h2]
    exact (Set.disjoint_image_iff f.injective).mpr (E.interiors_disjoint hij)
  · intro i
    exact (congruent_mapTri f (E.tile i)).symm.trans ((E.tiles_congruent i).trans (by rw [hEm]; exact hM))

theorem macroTFam {n : ℕ} (D : CongruentDissection n) (k : ℕ) (hk : 0 < k) (Y M : Tri)
    (hM : D.model.Congruent M)
    (hY : ∀ i j : Fin 3, dist (Y.pts i) (Y.pts j) = k * dist (D.target.pts i) (D.target.pts j)) :
    Nonempty (TFam Y.carrier M (k * k * n)) :=
  macroTFam_gen D k hk Y M hM (fun T0 h => Erdos634.SssCongruent.congruent_of_dist_three
    (by rw [h, hY]) (by rw [h, hY]) (by rw [h, hY]))

theorem macroTFam_sides {n : ℕ} (D : CongruentDissection n) {sa sb sc : ℝ}
    (hS : Erdos634.Draft.FDBBaseBetaE1.HasSides D.target sa sb sc) (k : ℕ) (hk : 0 < k) (Y M : Tri)
    (hM : D.model.Congruent M)
    (h12 : dist (Y.pts 1) (Y.pts 2) = k * sa) (h20 : dist (Y.pts 2) (Y.pts 0) = k * sb)
    (h01 : dist (Y.pts 0) (Y.pts 1) = k * sc) :
    Nonempty (TFam Y.carrier M (k * k * n)) := by
  obtain ⟨τ, ha, hb, hc⟩ := hS
  refine macroTFam_gen D k hk Y M hM (fun T0 h => ?_)
  refine Erdos634.Draft.FDBBaseBetaE1.congruent_of_hasSides (a := k * sa) (b := k * sb) (c := k * sc)
    ⟨τ, by rw [h, ha], by rw [h, hb], by rw [h, hc]⟩ h12 h20 h01

theorem dist_Phi_scale {f : ℝ} (hf : 1 < f) (a b c d : ℝ × ℝ) (k : ℝ) (hk : 0 ≤ k)
    (h : (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 + (a.1 - b.1) * (a.2 - b.2) / f
      = k ^ 2 * ((c.1 - d.1) ^ 2 + (c.2 - d.2) ^ 2 + (c.1 - d.1) * (c.2 - d.2) / f)) :
    dist (Phi f a) (Phi f b) = k * dist (Phi f c) (Phi f d) := by
  apply Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg (mul_nonneg hk dist_nonneg)
  rw [sq_Phi hf, mul_pow, sq_Phi hf]; exact h

theorem dist_Phi_eq {f : ℝ} (hf : 1 < f) (a b : ℝ × ℝ) (v : ℝ) (hv : 0 ≤ v)
    (h : (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 + (a.1 - b.1) * (a.2 - b.2) / f = v ^ 2) :
    dist (Phi f a) (Phi f b) = v := by
  apply Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg hv
  rw [sq_Phi hf]; exact h

theorem Preg_zero_eq (a b c : ℝ × ℝ) (k : ℕ) :
    Preg a b c (((0:ℕ):ℝ) / ((k:ℕ):ℝ)) = convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  simp only [Nat.cast_zero, zero_div]
  apply Set.Subset.antisymm
  · rintro p ⟨α, β, h0, h1, -, h3, rfl⟩
    refine mem_hull3 (A := a) (B := b) (C := c) (1 - α - β) α β (by linarith) h0 h1 (by ring) _ ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub] <;> ring
  · apply convexHull_min _ (Preg_convex a b c 0)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, 0, le_rfl, le_rfl, by norm_num, by norm_num, by simp⟩
    · exact ⟨1, 0, by norm_num, le_rfl, by norm_num, by norm_num, by simp⟩
    · exact ⟨0, 1, le_rfl, by norm_num, by norm_num, by norm_num, by simp⟩

theorem macro_fam_of_ex {f : ℝ} (hf : 1 < f) (a b c : ℝ × ℝ)
    (h : (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2) ≠ 0) {n : ℕ} {M T : Tri}
    (hex : ∃ D : CongruentDissection n, D.model = M ∧ D.target = T) (k : ℕ) (hk : 0 < k)
    (hY : ∀ p q : Fin 3, dist ((triC f hf a b c h).pts p) ((triC f hf a b c h).pts q)
      = k * dist (T.pts p) (T.pts q)) :
    Nonempty (TFam (Phi f '' Preg a b c (((0:ℕ):ℝ) / ((k:ℕ):ℝ))) M (k * k * n)) := by
  obtain ⟨D, hDm, hDt⟩ := hex
  have := macroTFam D k hk (triC f hf a b c h) M (by rw [hDm]; exact Tri.Congruent.refl _)
    (by intro p q; rw [hDt]; exact hY p q)
  rw [Preg_zero_eq, ← carrier_triC]
  exact this

theorem macro_fam_sides {f : ℝ} (hf : 1 < f) (a b c : ℝ × ℝ)
    (h : (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2) ≠ 0) {n : ℕ} {M : Tri}
    (D : CongruentDissection n) {sa sb sc : ℝ} (hS : Erdos634.Draft.FDBBaseBetaE1.HasSides D.target sa sb sc)
    (hM : D.model.Congruent M) (k : ℕ) (hk : 0 < k)
    (h12 : dist (Phi f b) (Phi f c) = k * sa) (h20 : dist (Phi f c) (Phi f a) = k * sb)
    (h01 : dist (Phi f a) (Phi f b) = k * sc) :
    Nonempty (TFam (Phi f '' Preg a b c (((0:ℕ):ℝ) / ((k:ℕ):ℝ))) M (k * k * n)) := by
  have := macroTFam_sides D hS k hk (triC f hf a b c h) M hM (by rw [triC_pts]; exact h12)
    (by rw [triC_pts]; exact h20) (by rw [triC_pts]; exact h01)
  rw [Preg_zero_eq, ← carrier_triC]
  exact this

end Erdos634.Draft.MacroPiece
