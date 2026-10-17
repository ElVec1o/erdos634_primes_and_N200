/-
Draft/LaczBase.lean — generic separation / containment helpers for the Laczkovich macro-dissection (Lead 1 of
private/ROOM/DISCOVERY/leads4.md): `cross`, separation of two convex hulls / a hull and an axis rectangle by an
edge line (`sep3X`, `sep3RX`, `sepR3X`), nonnegativity of an affine form on a rectangle from its four corners.
UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.S2All

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Rect interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.LaczFamily
open Erdos634.Draft.S2L (tri_le tri_ge rect_subset mem_hull3')

/-- `cross X Y p`: the (signed, doubled) area of the triangle `X Y p`. -/
def cross (X Y p : ℝ × ℝ) : ℝ := (Y.1 - X.1) * (p.2 - X.2) - (Y.2 - X.2) * (p.1 - X.1)

theorem nonneg_of_eq {E G : ℝ} (e : E = G) (h : 0 ≤ G) : 0 ≤ E := e ▸ h
theorem pos_of_eq {E G : ℝ} (e : E = G) (h : 0 < G) : 0 < E := e ▸ h

/-- a line separates two sets (both coefficients not zero). -/
theorem sepL {A B : Set (ℝ × ℝ)} (a b c : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hA : ∀ p ∈ A, a * p.1 + b * p.2 ≤ c) (hB : ∀ p ∈ B, c ≤ a * p.1 + b * p.2) :
    Disjoint (interior A) (interior B) := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
    subst ha
    rcases lt_or_gt_of_ne hb with hb | hb
    · refine (interior_disj_snd (c / b) (fun p hp => ?_) (fun p hp => ?_)).symm
      · have := hB p hp
        rw [le_div_iff_of_neg hb]; linarith
      · have := hA p hp
        rw [div_le_iff_of_neg hb]; linarith
    · refine interior_disj_snd (c / b) (fun p hp => ?_) (fun p hp => ?_)
      · have := hA p hp
        rw [le_div_iff₀ hb]; linarith
      · have := hB p hp
        rw [div_le_iff₀ hb]; linarith
  · exact Erdos634.Draft.WBrickF.interior_disj_lin a b c ha hA hB

theorem cross_eq (X Y p : ℝ × ℝ) (s : ℝ) : s * cross X Y p =
    (-(s * (Y.2 - X.2))) * p.1 + (s * (Y.1 - X.1)) * p.2
      - ((-(s * (Y.2 - X.2))) * X.1 + (s * (Y.1 - X.1)) * X.2) := by
  unfold cross; ring

/-- separation by the edge line `X Y`: `A` on the side where `-s·cross ≥ 0`, `B` on `s·cross ≥ 0`, strictly somewhere. -/
theorem sepX (X Y : ℝ × ℝ) (s : ℝ) {A B : Set (ℝ × ℝ)}
    (hA : ∀ p ∈ A, 0 ≤ -s * cross X Y p) (hB : ∀ p ∈ B, 0 ≤ s * cross X Y p)
    (hs : ∃ q ∈ B, 0 < s * cross X Y q) : Disjoint (interior A) (interior B) := by
  refine sepL (-(s * (Y.2 - X.2))) (s * (Y.1 - X.1))
    ((-(s * (Y.2 - X.2))) * X.1 + (s * (Y.1 - X.1)) * X.2) ?_ ?_ ?_
  · obtain ⟨q, -, hq⟩ := hs
    by_contra hcon
    push_neg at hcon
    rw [cross_eq, hcon.1, hcon.2] at hq
    simp at hq
  · intro p hp
    have := hA p hp
    have e : -s * cross X Y p = -(s * cross X Y p) := by ring
    rw [e, cross_eq] at this
    linarith
  · intro p hp
    have := hB p hp
    rw [cross_eq] at this
    linarith

theorem convex_cross (X Y : ℝ × ℝ) (s : ℝ) : Convex ℝ {p : ℝ × ℝ | 0 ≤ s * cross X Y p} := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_setOf_eq] at hp hq ⊢
  have e : s * cross X Y (a • p + b • q) = a * (s * cross X Y p) + b * (s * cross X Y q) := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [e]
  exact add_nonneg (mul_nonneg ha hp) (mul_nonneg hb hq)

theorem hull3_nonneg {A1 A2 A3 : ℝ × ℝ} (X Y : ℝ × ℝ) (s : ℝ) (h1 : 0 ≤ s * cross X Y A1)
    (h2 : 0 ≤ s * cross X Y A2) (h3 : 0 ≤ s * cross X Y A3) :
    ∀ p ∈ convexHull ℝ ({A1, A2, A3} : Set (ℝ × ℝ)), 0 ≤ s * cross X Y p := by
  intro p hp
  have hsub : convexHull ℝ ({A1, A2, A3} : Set (ℝ × ℝ)) ⊆ {p : ℝ × ℝ | 0 ≤ s * cross X Y p} := by
    refine convexHull_min ?_ (convex_cross X Y s)
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  exact hsub hp

theorem rect_nonneg {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (X Y : ℝ × ℝ) (s : ℝ)
    (c00 : 0 ≤ s * cross X Y (0, 0)) (c10 : 0 ≤ s * cross X Y (U, 0))
    (c01 : 0 ≤ s * cross X Y (0, V)) (c11 : 0 ≤ s * cross X Y (U, V)) :
    ∀ p ∈ Rect 0 U 0 V, 0 ≤ s * cross X Y p := fun p hp =>
  rect_subset (K := {p : ℝ × ℝ | 0 ≤ s * cross X Y p}) (convex_cross X Y s) hU hV c00 c10 c01 c11 hp

/-- two triangles. -/
theorem sep33 {A1 A2 A3 B1 B2 B3 : ℝ × ℝ} (X Y : ℝ × ℝ) (s : ℝ)
    (a1 : 0 ≤ -s * cross X Y A1) (a2 : 0 ≤ -s * cross X Y A2) (a3 : 0 ≤ -s * cross X Y A3)
    (b1 : 0 ≤ s * cross X Y B1) (b2 : 0 ≤ s * cross X Y B2) (b3 : 0 ≤ s * cross X Y B3)
    (hs : 0 < s * cross X Y B1 ∨ 0 < s * cross X Y B2 ∨ 0 < s * cross X Y B3) :
    Disjoint (interior (convexHull ℝ ({A1, A2, A3} : Set (ℝ × ℝ))))
      (interior (convexHull ℝ ({B1, B2, B3} : Set (ℝ × ℝ)))) := by
  refine sepX X Y s (hull3_nonneg X Y (-s) a1 a2 a3) (hull3_nonneg X Y s b1 b2 b3) ?_
  rcases hs with h | h | h
  · exact ⟨B1, subset_convexHull ℝ _ (by simp), h⟩
  · exact ⟨B2, subset_convexHull ℝ _ (by simp), h⟩
  · exact ⟨B3, subset_convexHull ℝ _ (by simp), h⟩

/-- triangle `A` against the rectangle `[0,U]×[0,V]` (rectangle on the `s·cross ≥ 0` side). -/
theorem sep3R {A1 A2 A3 : ℝ × ℝ} {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (X Y : ℝ × ℝ) (s : ℝ)
    (a1 : 0 ≤ -s * cross X Y A1) (a2 : 0 ≤ -s * cross X Y A2) (a3 : 0 ≤ -s * cross X Y A3)
    (c00 : 0 ≤ s * cross X Y (0, 0)) (c10 : 0 ≤ s * cross X Y (U, 0))
    (c01 : 0 ≤ s * cross X Y (0, V)) (c11 : 0 ≤ s * cross X Y (U, V))
    (hs : 0 < s * cross X Y (0, 0) ∨ 0 < s * cross X Y (U, 0) ∨ 0 < s * cross X Y (0, V)
      ∨ 0 < s * cross X Y (U, V)) :
    Disjoint (interior (convexHull ℝ ({A1, A2, A3} : Set (ℝ × ℝ)))) (interior (Rect 0 U 0 V)) := by
  refine sepX X Y s (hull3_nonneg X Y (-s) a1 a2 a3) (rect_nonneg hU hV X Y s c00 c10 c01 c11) ?_
  rcases hs with h | h | h | h
  · exact ⟨(0, 0), ⟨le_refl _, hU.le, le_refl _, hV.le⟩, h⟩
  · exact ⟨(U, 0), ⟨hU.le, le_refl _, le_refl _, hV.le⟩, h⟩
  · exact ⟨(0, V), ⟨le_refl _, hU.le, hV.le, le_refl _⟩, h⟩
  · exact ⟨(U, V), ⟨hU.le, le_refl _, hV.le, le_refl _⟩, h⟩

/-- the rectangle `[0,U]×[0,V]` on the `-s·cross ≥ 0` side against a triangle. -/
theorem sepR3 {B1 B2 B3 : ℝ × ℝ} {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (X Y : ℝ × ℝ) (s : ℝ)
    (c00 : 0 ≤ -s * cross X Y (0, 0)) (c10 : 0 ≤ -s * cross X Y (U, 0))
    (c01 : 0 ≤ -s * cross X Y (0, V)) (c11 : 0 ≤ -s * cross X Y (U, V))
    (b1 : 0 ≤ s * cross X Y B1) (b2 : 0 ≤ s * cross X Y B2) (b3 : 0 ≤ s * cross X Y B3)
    (hs : 0 < s * cross X Y B1 ∨ 0 < s * cross X Y B2 ∨ 0 < s * cross X Y B3) :
    Disjoint (interior (Rect 0 U 0 V)) (interior (convexHull ℝ ({B1, B2, B3} : Set (ℝ × ℝ)))) := by
  refine sepX X Y s (rect_nonneg hU hV X Y (-s) c00 c10 c01 c11) (hull3_nonneg X Y s b1 b2 b3) ?_
  rcases hs with h | h | h
  · exact ⟨B1, subset_convexHull ℝ _ (by simp), h⟩
  · exact ⟨B2, subset_convexHull ℝ _ (by simp), h⟩
  · exact ⟨B3, subset_convexHull ℝ _ (by simp), h⟩

end Erdos634.Draft.LaczFamily
