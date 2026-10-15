import Mathlib.Tactic
import Erdos634.Draft.GLCCase1
import Erdos634.Draft.GLCCase2
import Erdos634.Draft.T30LL4Corner

/-!
# Target-triangle coordinates for the G2 wiring

`tri_coords`: the barycentric coordinates of `O + s (A − O) + t (B − O)` (`O, A, B` the vertices `v, w, z`) are `(1 − s − t, s, t)`.
`openSeg_interior3`: if the coordinates of two such points are `≥ 0` and each coordinate is `> 0` at one of them, the open segment lies in the interior of the target.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.C2Forward Erdos634.Pi3F6

theorem tri_coords (T : Tri) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) (s t : ℝ) (m : Fin 3) :
    T.basis.coord m (T.pts v + s • (T.pts w - T.pts v) + t • (T.pts z - T.pts v)) =
      (if m = v then 1 - s - t else 0) + (if m = w then s else 0) + (if m = z then t else 0) := by
  have hcd : ∀ (m n : Fin 3), T.basis.coord m (T.pts n) = if m = n then 1 else 0 :=
    fun m n => AffineBasis.coord_apply T.basis m n
  rw [coord_lin3, hcd, hcd, hcd]
  rcases cover3 v w z m hvw hvz hwz with h | h | h
  · subst h; simp [hvw, hvz]; ring
  · subst h; simp [hvw.symm, hwz]
  · subst h; simp [hvz.symm, hwz.symm]

theorem openSeg_interior3 (T : Tri) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (s1 t1 s2 t2 : ℝ) (h1 : 0 ≤ 1 - s1 - t1) (h2 : 0 ≤ s1) (h3 : 0 ≤ t1)
    (h4 : 0 ≤ 1 - s2 - t2) (h5 : 0 ≤ s2) (h6 : 0 ≤ t2)
    (c1 : 0 < 1 - s1 - t1 ∨ 0 < 1 - s2 - t2) (c2 : 0 < s1 ∨ 0 < s2) (c3 : 0 < t1 ∨ 0 < t2) :
    openSegment ℝ (T.pts v + s1 • (T.pts w - T.pts v) + t1 • (T.pts z - T.pts v))
      (T.pts v + s2 • (T.pts w - T.pts v) + t2 • (T.pts z - T.pts v)) ⊆ interior T.carrier := by
  have hint : interior T.carrier = {x | ∀ i, 0 < T.basis.coord i x} := by
    have : T.carrier = convexHull ℝ (Set.range (T.basis : Fin 3 → Plane)) := rfl
    rw [this]
    exact AffineBasis.interior_convexHull T.basis
  rw [hint]
  rintro y ⟨a, b, ha, hb, hab, rfl⟩ m
  rw [aff_comb _ _ _ _ _ hab, tri_coords T v w z hvw hvz hwz, tri_coords T v w z hvw hvz hwz]
  rcases cover3 v w z m hvw hvz hwz with h | h | h
  · subst h; simp [hvw, hvz]
    rcases c1 with c | c <;> nlinarith [mul_pos ha hb, mul_nonneg ha.le h1, mul_nonneg hb.le h4]
  · subst h; simp [hvw.symm, hwz]
    rcases c2 with c | c <;> nlinarith [mul_nonneg ha.le h2, mul_nonneg hb.le h5]
  · subst h; simp [hvz.symm, hwz.symm]
    rcases c3 with c | c <;> nlinarith [mul_nonneg ha.le h3, mul_nonneg hb.le h6]

end Erdos634.GLC
