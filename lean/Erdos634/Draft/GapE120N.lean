import Erdos634.Draft.GapE120Exc
import Erdos634.Refl.ME60Sound
import Erdos634.Refl.ME56Sound

/-! Draft/GapE120N.lean -- `GapE120 60` and `GapE120 56`, discharged.

The pair tables leave exactly one square-`D` pair each: `{10, 18}` at `N = 60` (tile `l·(3,5,7)`, equilateral target of
side `30 l`) and `{12, 14}` at `N = 56` (tile `l·(7,8,13)`, side `56 l`).  Both are closed by the kernel-checked
free-branch-point certificates `Refl.ME60.not_dissection` (14,763 nodes) and `Refl.ME56.not_dissection` (4,655 nodes).

Composite-N leaves (`thm:frontier3` rows 56 and 60); not prime-case work. -/

open scoped Classical
open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeE5Gen
open Erdos634.Draft.GapE120Exc

namespace Erdos634.Draft.GapE120N

theorem TGT60_sides : dist (Refl.ME60.TGT.pts 0) (Refl.ME60.TGT.pts 1) = 30 ∧
    dist (Refl.ME60.TGT.pts 1) (Refl.ME60.TGT.pts 2) = 30 ∧
    dist (Refl.ME60.TGT.pts 0) (Refl.ME60.TGT.pts 2) = 30 :=
  model_sides_rp Refl.ME60.hDn Refl.ME60.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem TGT56_sides : dist (Refl.ME56.TGT.pts 0) (Refl.ME56.TGT.pts 1) = 56 ∧
    dist (Refl.ME56.TGT.pts 1) (Refl.ME56.TGT.pts 2) = 56 ∧
    dist (Refl.ME56.TGT.pts 0) (Refl.ME56.TGT.pts 2) = 56 :=
  model_sides_rp Refl.ME56.hDn Refl.ME56.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-! ## N = 60 -/

theorem e120pair_60_10_18 : E120Pair 60 10 18 := by
  intro D α a b c hα h hE h1 h2 harea
  have hS0 := D.target.oppLen_pos 0
  obtain ⟨t1, t2, t3⟩ := h.tri_ineq
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  push_cast at h1 h2 harea
  obtain ⟨hc, ha', hb'⟩ := shape_of_pair (D.target.oppLen 0) a b c 10 18 60 30 7 2 8 hS0 ha hb (by norm_num)
    (by norm_num) h1 h2 harea (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact close_of_cert D hα h hE Refl.ME60.TGT Refl.ME60.MODEL 30 3 5 7 (D.target.oppLen 0 / 30) (by positivity)
    TGT60_sides Refl.ME60.MODEL_sides (by ring) hc (Or.inl ⟨by rw [hb']; ring, by rw [ha']; ring⟩)
    (fun D' hT hM => Refl.ME60.not_dissection D' hT hM)

theorem e120pair_60_18_10 : E120Pair 60 18 10 := by
  intro D α a b c hα h hE h1 h2 harea
  have hS0 := D.target.oppLen_pos 0
  obtain ⟨t1, t2, t3⟩ := h.tri_ineq
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  push_cast at h1 h2 harea
  obtain ⟨hc, ha', hb'⟩ := shape_of_pair (D.target.oppLen 0) a b c 18 10 60 30 7 (-2) 8 hS0 ha hb (by norm_num)
    (by norm_num) h1 h2 harea (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact close_of_cert D hα h hE Refl.ME60.TGT Refl.ME60.MODEL 30 3 5 7 (D.target.oppLen 0 / 30) (by positivity)
    TGT60_sides Refl.ME60.MODEL_sides (by ring) hc (Or.inr ⟨by rw [ha']; ring, by rw [hb']; ring⟩)
    (fun D' hT hM => Refl.ME60.not_dissection D' hT hM)

theorem pairs120_60 : ∀ s t : ℤ, 1 ≤ s → s ≤ ((60 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((60 : ℕ) : ℤ) → s * t = 3 * ((60 : ℕ) : ℤ) →
    (s = 10 ∧ t = 18) ∨ (s = 18 ∧ t = 10) ∨
    (¬ IsSquare ((t - s) ^ 2 + 16 * ((60 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((60 : ℕ) : ℤ) ≠ r * (s + t)) := by
  intro s t h1 h2 h3 h4 h5
  push_cast at *
  interval_cases s <;>
    first
    | (exfalso; omega)
    | (interval_cases t <;> first | (exfalso; omega) | (left; exact ⟨rfl, rfl⟩) | (right; left; exact ⟨rfl, rfl⟩) |
        (right; right; exact ⟨by decide +kernel, fun r hr => by omega⟩))

/-- **`GapE120 60`**: no `CongruentDissection 60` has a `2π/3` tile with `α ∉ ℚπ` and an equilateral target. -/
theorem gapE120_60 : GapE120 60 :=
  gapE120_of_pairs_exc 60 (by norm_num) 10 18 e120pair_60_10_18 e120pair_60_18_10 pairs120_60

/-! ## N = 56 -/

theorem e120pair_56_12_14 : E120Pair 56 12 14 := by
  intro D α a b c hα h hE h1 h2 harea
  have hS0 := D.target.oppLen_pos 0
  obtain ⟨t1, t2, t3⟩ := h.tri_ineq
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  push_cast at h1 h2 harea
  obtain ⟨hc, ha', hb'⟩ := shape_of_pair (D.target.oppLen 0) a b c 12 14 56 56 13 1 15 hS0 ha hb (by norm_num)
    (by norm_num) h1 h2 harea (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact close_of_cert D hα h hE Refl.ME56.TGT Refl.ME56.MODEL 56 7 8 13 (D.target.oppLen 0 / 56) (by positivity)
    TGT56_sides Refl.ME56.MODEL_sides (by ring) hc (Or.inl ⟨by rw [hb']; ring, by rw [ha']; ring⟩)
    (fun D' hT hM => Refl.ME56.not_dissection D' hT hM)

theorem e120pair_56_14_12 : E120Pair 56 14 12 := by
  intro D α a b c hα h hE h1 h2 harea
  have hS0 := D.target.oppLen_pos 0
  obtain ⟨t1, t2, t3⟩ := h.tri_ineq
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  push_cast at h1 h2 harea
  obtain ⟨hc, ha', hb'⟩ := shape_of_pair (D.target.oppLen 0) a b c 14 12 56 56 13 (-1) 15 hS0 ha hb (by norm_num)
    (by norm_num) h1 h2 harea (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact close_of_cert D hα h hE Refl.ME56.TGT Refl.ME56.MODEL 56 7 8 13 (D.target.oppLen 0 / 56) (by positivity)
    TGT56_sides Refl.ME56.MODEL_sides (by ring) hc (Or.inr ⟨by rw [ha']; ring, by rw [hb']; ring⟩)
    (fun D' hT hM => Refl.ME56.not_dissection D' hT hM)

theorem pairs120_56 : ∀ s t : ℤ, 1 ≤ s → s ≤ ((56 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((56 : ℕ) : ℤ) → s * t = 3 * ((56 : ℕ) : ℤ) →
    (s = 12 ∧ t = 14) ∨ (s = 14 ∧ t = 12) ∨
    (¬ IsSquare ((t - s) ^ 2 + 16 * ((56 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((56 : ℕ) : ℤ) ≠ r * (s + t)) := by
  intro s t h1 h2 h3 h4 h5
  push_cast at *
  interval_cases s <;>
    first
    | (exfalso; omega)
    | (interval_cases t <;> first | (exfalso; omega) | (left; exact ⟨rfl, rfl⟩) | (right; left; exact ⟨rfl, rfl⟩) |
        (right; right; exact ⟨by decide +kernel, fun r hr => by omega⟩))

/-- **`GapE120 56`**. -/
theorem gapE120_56 : GapE120 56 :=
  gapE120_of_pairs_exc 56 (by norm_num) 12 14 e120pair_56_12_14 e120pair_56_14_12 pairs120_56

end Erdos634.Draft.GapE120N

#print axioms Erdos634.Draft.GapE120N.gapE120_60
#print axioms Erdos634.Draft.GapE120N.gapE120_56
