-- Draft/CollarLayerLib.lean — generic lemmas for the collar layer step (half-planes of trapezoid regions, triangle membership,
-- tile families from region tilings, brickU ≅ brickL).  UNAUDITED.  No sorry, no native_decide.
-- Credit: Paliy (collar idea; alpha-isosceles counts and eventual up-set, docs/eventual-rational-families.md, 2026-09-29),
-- Laczkovich (macro-dissections), Beeson–Roșu (S2L skew frame); this file is infrastructure of our independent formalization.
import Erdos634.Draft.LadderFam
import Erdos634.Draft.TileCountFamilies

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.CollarLayer
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.LadderFam

/-- A half-plane bound on a trapezoid region `Preg a V1 V2 σ` follows from the four vertex values. -/
theorem preg_le (a V1 V2 : ℝ × ℝ) (σ u w c : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (h1 : u * (a.1 + σ * (V1.1 - a.1)) + w * (a.2 + σ * (V1.2 - a.2)) ≤ c)
    (h2 : u * (a.1 + σ * (V2.1 - a.1)) + w * (a.2 + σ * (V2.2 - a.2)) ≤ c)
    (h3 : u * V1.1 + w * V1.2 ≤ c) (h4 : u * V2.1 + w * V2.2 ≤ c) :
    ∀ p ∈ Preg a V1 V2 σ, u * p.1 + w * p.2 ≤ c := by
  rintro p ⟨α, β, hα, hβ, hs0, hs1, rfl⟩
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
  set la := u * a.1 + w * a.2 with hla
  set l1 := u * (V1.1 - a.1) + w * (V1.2 - a.2) with hl1
  set l2 := u * (V2.1 - a.1) + w * (V2.2 - a.2) with hl2
  have e : u * (a.1 + α * (V1.1 - a.1) + β * (V2.1 - a.1)) + w * (a.2 + α * (V1.2 - a.2) + β * (V2.2 - a.2))
      = la + α * l1 + β * l2 := by simp only [hla, hl1, hl2]; ring
  rw [e]
  have C1 : 0 ≤ c - la - σ * l1 := by simp only [hla, hl1]; nlinarith
  have C2 : 0 ≤ c - la - σ * l2 := by simp only [hla, hl2]; nlinarith
  have C3 : 0 ≤ c - la - l1 := by simp only [hla, hl1]; nlinarith
  have C4 : 0 ≤ c - la - l2 := by simp only [hla, hl2]; nlinarith
  by_cases hσ : σ = 1
  · subst hσ
    have hb : β = 1 - α := by linarith
    subst hb
    nlinarith [mul_nonneg hα C3, mul_nonneg hβ C4]
  · have hσ' : σ < 1 := lt_of_le_of_ne hσ1 hσ
    by_cases hs : α + β = 0
    · have : α = 0 := by linarith
      have : β = 0 := by linarith
      subst_vars
      have : σ = 0 := by linarith
      subst this
      nlinarith
    · have hspos : 0 < α + β := lt_of_le_of_ne (by linarith) (Ne.symm hs)
      have key : 0 ≤ (1 - σ) * (α + β) * (c - (la + α * l1 + β * l2)) := by
        have : (1 - σ) * (α + β) * (c - (la + α * l1 + β * l2)) =
            (1 - (α + β)) * α * (c - la - σ * l1) + (1 - (α + β)) * β * (c - la - σ * l2)
            + ((α + β) - σ) * α * (c - la - l1) + ((α + β) - σ) * β * (c - la - l2) := by ring
        rw [this]
        have a1 : 0 ≤ 1 - (α + β) := by linarith
        have a2 : 0 ≤ (α + β) - σ := by linarith
        positivity
      have hpos : 0 < (1 - σ) * (α + β) := by apply mul_pos <;> linarith
      have := nonneg_of_mul_nonneg_right key hpos
      linarith

theorem preg_ge (a V1 V2 : ℝ × ℝ) (σ u w c : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (h1 : c ≤ u * (a.1 + σ * (V1.1 - a.1)) + w * (a.2 + σ * (V1.2 - a.2)))
    (h2 : c ≤ u * (a.1 + σ * (V2.1 - a.1)) + w * (a.2 + σ * (V2.2 - a.2)))
    (h3 : c ≤ u * V1.1 + w * V1.2) (h4 : c ≤ u * V2.1 + w * V2.2) :
    ∀ p ∈ Preg a V1 V2 σ, c ≤ u * p.1 + w * p.2 := by
  intro p hp
  have := preg_le a V1 V2 σ (-u) (-w) (-c) hσ0 hσ1 (by linarith) (by linarith) (by linarith) (by linarith) p hp
  linarith

/-- Membership in the isosceles-type triangle `(0,0),(B,0),(xA,yA)` by three linear inequalities. -/
theorem mem_tri_iso {B xA yA X Y : ℝ} (hB : 0 < B) (hy : 0 < yA) (h1 : 0 ≤ Y)
    (h2 : 0 ≤ yA * X - xA * Y) (h3 : 0 ≤ yA * (B - X) - (B - xA) * Y) :
    (X, Y) ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (B, 0), (xA, yA)} : Set (ℝ × ℝ)) := by
  refine Erdos634.Draft.S2L.mem_hull3' (yA * B) (yA * (B - X) - (B - xA) * Y) (yA * X - xA * Y) (Y * B)
    (by positivity) h3 h2 (by positivity) (by ring) _ ?_ ?_ <;> simp <;> ring

/-- A tile family from a region tiling. -/
def TFam.ofR {S : Set Plane} {M : Tri} {N : ℕ} (R : RTiling S M N) : TFam S M N where
  tile := R.tile
  sub := fun i => (Set.subset_iUnion (fun i => (R.tile i).carrier) i).trans R.covers.le
  disj := R.disj
  cong := R.cong

def TFam.remodel {S : Set Plane} {M M' : Tri} {n : ℕ} (T : TFam S M n) (h : M.Congruent M') : TFam S M' n where
  tile := T.tile
  sub := T.sub
  disj := T.disj
  cong := fun i => (T.cong i).trans h

theorem brickU_cong_brickL {f : ℝ} (hf : 1 < f) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (brickU f hf A B hA hB).Congruent (brickL f hf A B hA hB) := by
  refine ((brickU f hf _ _ hA hB).congruent_relabel (Equiv.swap (0 : Fin 3) 2)).trans ?_
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [Tri.relabel, brickL, brickU, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi hf, sq_Phi hf]; ring)

end Erdos634.Draft.CollarLayer
