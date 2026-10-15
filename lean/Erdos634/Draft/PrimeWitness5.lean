-- Draft/PrimeWitness5.lean — non-vacuity control: a `CongruentDissection 5` (N = 5 prime, ≡ 1 mod 4):
-- the right triangle with hypotenuse `[0,5]` and apex `(1,2)` = 1 tile + 2·(tile).
-- Imported by All.lean.
import Erdos634.Draft.PrimeWitness2

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RWGlue Erdos634.Draft.RWPieces
  Erdos634.Draft.RAAssemble Erdos634.Draft.RWEast
open Erdos634.RouteOneCrossing (selfDissection)

namespace Erdos634.Draft.PrimeWitness5

theorem dd {a b c d e f g h : ℝ} (hh : (a - c) ^ 2 + (b - d) ^ 2 = (e - g) ^ 2 + (f - h) ^ 2) :
    dist (mkPt a b) (mkPt c d) = dist (mkPt e f) (mkPt g h) := by
  refine eq_of_sq_eq dist_nonneg dist_nonneg ?_
  rw [dist_sq_mkPt, dist_sq_mkPt]; exact hh

theorem dT : det3 1 2 0 0 5 0 ≠ 0 := by unfold det3; norm_num
theorem dT1 : det3 1 2 0 0 1 0 ≠ 0 := by unfold det3; norm_num
theorem dT2 : det3 1 2 1 0 5 0 ≠ 0 := by unfold det3; norm_num
theorem dM : det3 1 0 0 0 0 2 ≠ 0 := by unfold det3; norm_num

noncomputable def T : Tri := mkTri 1 2 0 0 5 0 dT
noncomputable def T1 : Tri := mkTri 1 2 0 0 1 0 dT1
noncomputable def T2 : Tri := mkTri 1 2 1 0 5 0 dT2
noncomputable def M : Tri := mkTri 1 0 0 0 0 2 dM

theorem T1_cong_M : T1.Congruent M := by
  refine (T1.congruent_relabel (finRotate 3)).trans ?_
  refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · show dist (mkPt (0 : ℝ) 0) (mkPt 1 0) = dist (mkPt (1 : ℝ) 0) (mkPt 0 0)
    exact dd (by norm_num)
  · show dist (mkPt (1 : ℝ) 0) (mkPt 1 2) = dist (mkPt (0 : ℝ) 0) (mkPt 0 2)
    exact dd (by norm_num)
  · show dist (mkPt (1 : ℝ) 2) (mkPt 0 0) = dist (mkPt (0 : ℝ) 2) (mkPt 1 0)
    exact dd (by norm_num)

theorem exists_dissection_5 : Nonempty (CongruentDissection 5) ∧ Nat.Prime 5 := by
  obtain ⟨hind, heta⟩ := tri_eta M
  set D0 : CongruentDissection 1 :=
    { toDissection := selfDissection M, model := M, tiles_congruent := fun _ => Tri.Congruent.refl M }
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (M.pts 0) (M.pts 1) (M.pts 2) hind D0 heta 2 (by norm_num)
  have hd := dist_bigTri (M.pts 0) (M.pts 1) (M.pts 2) hind 2 (by norm_num)
  have hE2 : E.target.Congruent T2 := by
    rw [hEt]
    refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · rw [hd 0 1]
      show (2 : ℕ) * dist (mkPt (1 : ℝ) 0) (mkPt 0 0) = dist (mkPt (1 : ℝ) 2) (mkPt 1 0)
      have : dist (mkPt (1 : ℝ) 0) (mkPt 0 0) = 1 := by
        refine eq_of_sq_eq dist_nonneg (by norm_num) ?_; rw [dist_sq_mkPt]; norm_num
      have h2 : dist (mkPt (1 : ℝ) 2) (mkPt 1 0) = 2 := by
        refine eq_of_sq_eq dist_nonneg (by norm_num) ?_; rw [dist_sq_mkPt]; norm_num
      rw [this, h2]; norm_num
    · rw [hd 1 2]
      show (2 : ℕ) * dist (mkPt (0 : ℝ) 0) (mkPt 0 2) = dist (mkPt (1 : ℝ) 0) (mkPt 5 0)
      have : dist (mkPt (0 : ℝ) 0) (mkPt 0 2) = 2 := by
        refine eq_of_sq_eq dist_nonneg (by norm_num) ?_; rw [dist_sq_mkPt]; norm_num
      have h2 : dist (mkPt (1 : ℝ) 0) (mkPt 5 0) = 4 := by
        refine eq_of_sq_eq dist_nonneg (by norm_num) ?_; rw [dist_sq_mkPt]; norm_num
      rw [this, h2]; norm_num
    · rw [hd 2 0]
      show (2 : ℕ) * dist (mkPt (0 : ℝ) 2) (mkPt 1 0) = dist (mkPt (5 : ℝ) 0) (mkPt 1 2)
      refine eq_of_sq_eq (by positivity) dist_nonneg ?_
      rw [mul_pow, dist_sq_mkPt, dist_sq_mkPt]; norm_num
  set D1 : CongruentDissection 1 :=
    { toDissection := selfDissection T1, model := M, tiles_congruent := fun _ => T1_cong_M }
  have hlm : AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt 5 0) (1 / 5 : ℝ) = mkPt 1 0 := by
    rw [lm]; congr 1; norm_num
  obtain ⟨D, -, -⟩ := glue_two T T1 T2 (1 / 5) (by norm_num) (by norm_num)
    (by show mkPt (1 : ℝ) 2 = mkPt 1 2; rfl) (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl)
    (by show mkPt (1 : ℝ) 0 = AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt 5 0) (1 / 5); rw [hlm])
    (by show mkPt (1 : ℝ) 2 = mkPt 1 2; rfl)
    (by show mkPt (1 : ℝ) 0 = AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt 5 0) (1 / 5); rw [hlm])
    (by show mkPt (5 : ℝ) 0 = mkPt 5 0; rfl)
    D1 E (by rw [hEm]; exact Tri.Congruent.refl _) (Tri.Congruent.refl _) hE2
  exact ⟨⟨D⟩, by norm_num⟩

end Erdos634.Draft.PrimeWitness5

#print axioms Erdos634.Draft.PrimeWitness5.exists_dissection_5
