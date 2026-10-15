-- Draft/WAdd.lean — step (d) of the 7m² plan: W-addition.  With
-- Wt m = {p | p1 ≤ 6m, p2 ≤ 7m, 42m ≤ 7p1+6p2} (vertices (6m,0),(6m,7m),(0,7m)),
-- Wt (m1+m2) = Sh(6m2,0)(Wt m1) ∪ Rect(6m2..6s, 7m1..7s) ∪ Sh(0,7m1)(Wt m2).
import Erdos634.Draft.WGrid

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (s15 s15_pos s15_sq Tset Rect RTiling.cast RTiling.castN
  interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.WAdd
open Erdos634.Draft.WFrame Erdos634.Draft.RegionTiling Erdos634.Draft.WBrick Erdos634.Draft.WPgram
  Erdos634.Draft.WGrid

def Wt (m : ℝ) : Set (ℝ × ℝ) := {p | p.1 ≤ 6 * m ∧ p.2 ≤ 7 * m ∧ 42 * m ≤ 7 * p.1 + 6 * p.2}

theorem Wt_add (m1 m2 : ℝ) (h1 : 0 ≤ m1) (h2 : 0 ≤ m2) :
    (Sh (6 * m2, 0) (Wt m1) ∪ Rect (6 * m2) (6 * (m1 + m2)) (7 * m1) (7 * (m1 + m2)))
      ∪ Sh (0, 7 * m1) (Wt m2) = Wt (m1 + m2) := by
  ext p
  simp only [Sh, Wt, Rect, Set.mem_union, Set.mem_setOf_eq, Prod.fst_sub, Prod.snd_sub, sub_zero]
  constructor
  · rintro ((⟨a, b, c⟩ | ⟨a, b, c, d⟩) | ⟨a, b, c⟩)
    · exact ⟨by linarith, by linarith, by linarith⟩
    · exact ⟨b, d, by linarith⟩
    · exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨a, b, c⟩
    by_cases hp2 : p.2 ≤ 7 * m1
    · left; left; exact ⟨by linarith, hp2, by linarith⟩
    · by_cases hp1 : 6 * m2 ≤ p.1
      · left; right; exact ⟨hp1, a, by linarith, b⟩
      · right; exact ⟨by linarith, by linarith, by linarith⟩

/-- **Step (d).** W-addition as a region tiling: `W_{m1+1+m2+1}` from `W_{m1+1}`, `W_{m2+1}` and the
grid parallelogram. -/
noncomputable def wadd (k l : ℕ) {N₁ N₂ : ℕ}
    (RA : RTiling (Phi '' Wt ((k : ℝ) + 1)) MW N₁) (RB : RTiling (Phi '' Wt ((l : ℝ) + 1)) MW N₂) :
    RTiling (Phi '' Wt (((k : ℝ) + 1) + ((l : ℝ) + 1))) MW (N₁ + 14 * (k + 1) * (l + 1) + N₂) := by
  set m1 : ℝ := (k : ℝ) + 1 with hm1
  set m2 : ℝ := (l : ℝ) + 1 with hm2
  have p1 : 0 ≤ m1 := by positivity
  have p2 : 0 ≤ m2 := by positivity
  have hA := shiftR RA (6 * m2, 0)
  have hG := shift_rect (grid k l) (6 * m2) (7 * m1) (6 * (m1 + m2)) (7 * (m1 + m2))
    (by rw [hm1, hm2]; ring) (by rw [hm1, hm2]; ring)
  have hC := shiftR RB (0, 7 * m1)
  have hd1 : Disjoint (interior (Phi '' Sh (6 * m2, 0) (Wt m1)))
      (interior (Phi '' Rect (6 * m2) (6 * (m1 + m2)) (7 * m1) (7 * (m1 + m2)))) := by
    refine disjoint_image (interior_disj_snd (7 * m1) ?_ ?_)
    · rintro p ⟨a, b, c⟩; simp only [Prod.snd_sub, sub_zero] at b; exact b
    · rintro p ⟨a, b, c, d⟩; exact c
  have hd2 : Disjoint (interior (Phi '' Sh (6 * m2, 0) (Wt m1) ∪
        Phi '' Rect (6 * m2) (6 * (m1 + m2)) (7 * m1) (7 * (m1 + m2))))
      (interior (Phi '' Sh (0, 7 * m1) (Wt m2))) := by
    rw [← Set.image_union]
    refine disjoint_image (interior_disj_fst (6 * m2) ?_ ?_).symm
    · rintro p ⟨a, b, c⟩; simp only [Prod.fst_sub, sub_zero] at a; exact a
    · rintro p (⟨a, b, c⟩ | ⟨a, b, c, d⟩)
      · simp only [Prod.fst_sub, Prod.snd_sub, sub_zero] at a b c; linarith
      · exact a
  have U := union (union hA hG hd1) hC hd2
  refine RTiling.castN (by ring) (RTiling.cast ?_ U)
  rw [← Set.image_union, ← Set.image_union, Wt_add m1 m2 p1 p2]

end Erdos634.Draft.WAdd

#print axioms Erdos634.Draft.WAdd.wadd
