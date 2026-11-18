/-
Draft/StripStepScaled.lean -- a triangle whose sides are `k` times the sides of the model tile is tiled by `k * k` copies of the
model, wherever it sits in the plane (Erdos #634; work item internal working notes).

`scaled_tiled (M X : Tri) (k) (hk : 0 < k) (h01 h12 h20 : dist (X.pts i) (X.pts j) = k * dist (M.pts i) (M.pts j)) :
   Tiled X.carrier M (k * k)`        (region tiling in the sense of `F1StripGeom.Tiled`).

PROOF: `Ladder.ladder` on the trivial dissection of `M` gives `k * k` copies in the scaled triangle `bigTri`; the three side lengths
of `bigTri` are `k` times those of `M` (`dist_bigTri_*`); SSS (`SssCongruent.congruent_of_dist_three`) gives an isometry of the plane
carrying `bigTri` onto `X`; `RTiling.map` transports the tiling.  This is the region version of the scaled-tile gluing used in
`ZhangF1.f1_real` (`ladRT`) and is the one placement lemma needed by the F1 -> Iso transfer and by the F1 strip cap.
CREDIT: the scaled-tile gluing is Zhang's (arXiv 2512.22696, Props 8, 9), Paliy's transfers; the ladder is the project's `thm:ladder`.
UNAUDITED beyond the internal build.  No sorry, no native_decide.
-/
import Erdos634.Draft.F1StripGeom
import Erdos634.Draft.TileCountFamilies
import Erdos634.CellCoord
import Erdos634.SssCongruent

namespace Erdos634.Draft.StripStepScaled

open Erdos634.Geometry Erdos634.Subdivision Erdos634.Draft.RegionTiling Erdos634.Draft.F1StripGeom

noncomputable section

theorem tri_eta (M : Tri) (h : AffineIndependent ℝ ![M.pts 0, M.pts 1, M.pts 2]) :
    (⟨![M.pts 0, M.pts 1, M.pts 2], h⟩ : Tri) = M := by
  cases M with
  | mk p ip => congr 1; funext i; fin_cases i <;> rfl

section dist
variable (A B C : Plane) (h : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k)

theorem dist_bigTri_01 :
    dist ((bigTri A B C h k hk).pts 0) ((bigTri A B C h k hk).pts 1) = k * dist A B := by
  show dist A (P A B C k 0) = _
  have e : A - P A B C k 0 = -((k : ℝ) • (B - A)) := by simp [P]
  rw [dist_eq_norm, e, norm_neg, norm_smul, Real.norm_natCast, dist_eq_norm, norm_sub_rev]

theorem dist_bigTri_12 :
    dist ((bigTri A B C h k hk).pts 1) ((bigTri A B C h k hk).pts 2) = k * dist B C := by
  show dist (P A B C k 0) (P A B C 0 k) = _
  have e : P A B C k 0 - P A B C 0 k = (k : ℝ) • (B - C) := by simp only [P]; push_cast; module
  rw [dist_eq_norm, e, norm_smul, Real.norm_natCast, dist_eq_norm]

theorem dist_bigTri_20 :
    dist ((bigTri A B C h k hk).pts 2) ((bigTri A B C h k hk).pts 0) = k * dist C A := by
  show dist (P A B C 0 k) A = _
  have e : P A B C 0 k - A = (k : ℝ) • (C - A) := by simp [P]
  rw [dist_eq_norm, e, norm_smul, Real.norm_natCast, dist_eq_norm]

end dist

/-- **A triangle with sides `k` times the model's is tiled by `k*k` model tiles.** -/
theorem scaled_tiled (M X : Tri) (k : ℕ) (hk : 0 < k)
    (h01 : dist (X.pts 0) (X.pts 1) = k * dist (M.pts 0) (M.pts 1))
    (h12 : dist (X.pts 1) (X.pts 2) = k * dist (M.pts 1) (M.pts 2))
    (h20 : dist (X.pts 2) (X.pts 0) = k * dist (M.pts 2) (M.pts 0)) :
    Tiled X.carrier M (k * k) := by
  have hind : AffineIndependent ℝ ![M.pts 0, M.pts 1, M.pts 2] := by
    have := M.indep
    convert this using 1; funext i; fin_cases i <;> rfl
  let D0 : CongruentDissection 1 :=
    { toDissection := Erdos634.RouteOneCrossing.selfDissection M
      model := M
      tiles_congruent := fun _ => Tri.Congruent.refl _ }
  have hT : D0.target = (⟨![M.pts 0, M.pts 1, M.pts 2], hind⟩ : Tri) := (tri_eta M hind).symm
  obtain ⟨E, hE, hEm⟩ := Erdos634.Ladder.ladder (M.pts 0) (M.pts 1) (M.pts 2) hind D0 hT k hk
  have R : RTiling E.target.carrier E.model (k * k * 1) := ofCD E
  rw [hE, hEm] at R
  have hc : (bigTri (M.pts 0) (M.pts 1) (M.pts 2) hind k hk).Congruent X := by
    refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · rw [dist_bigTri_01, h01]
    · rw [dist_bigTri_12, h12]
    · rw [dist_bigTri_20, h20]
  obtain ⟨f, σ, hf⟩ := hc
  have himg := Erdos634.CongruentArea.image_carrier_of_congruent hf
  have R2 := Erdos634.Draft.RegionTiling.map R f
  rw [himg] at R2
  exact ⟨by simpa using R2⟩

end

end Erdos634.Draft.StripStepScaled

#print axioms Erdos634.Draft.StripStepScaled.scaled_tiled
