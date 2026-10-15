import Mathlib.Tactic
import Erdos634.Draft.GLISum

/-!
# The reversed wall and its chain (to read the far end of a side as the start of its reverse)

`Wall.rev w` has `a := w.b`, `b := w.a`, `dir := -w.dir`, same `g`.  `IsChain.rev_zero`: if `E'` is a chain of `w.rev`, then
`E' 0 = E (n-1)` and `E' 1 = E (n-2)` (for `1 < n`).  `wAng_rev`: the west angle for `-dir` is the east angle for `dir`.
-/

namespace Erdos634.GLI

open Erdos634.Geometry Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.GLG
  Erdos634.BaseChain

variable {N : ℕ}

noncomputable def Wall.rev {D : Dissection N} (w : Wall D) : Wall D where
  g := w.g
  dir := -w.dir
  a := w.b
  b := w.a
  hab := w.hab.symm
  hker := fun v h1 h2 => w.hker v h1 (by simpa using h2)
  hne := w.hne
  hwall := w.hwall
  hbase := by rw [segment_symm]; exact w.hbase
  hline := fun y hy => w.hline y (by rw [segment_symm]; exact hy)
  hface := fun y hy h0 => by rw [segment_symm]; exact w.hface y hy h0
  hiso := fun p q hp hq => by
    rw [w.hiso p q hp hq]
    simp only [LinearMap.neg_apply]
    rw [show -w.dir p - -w.dir q = -(w.dir p - w.dir q) by ring, abs_neg]
  hdirab := by simp only [LinearMap.neg_apply]; exact neg_le_neg w.hdirab
  hvert := fun j h => (w.hvert j h).symm

theorem edgePos_neg (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3) :
    edgePos D (-dir) e = -(edgeEnd D dir e) := by
  unfold edgePos edgeEnd; simp only [LinearMap.neg_apply]; exact min_neg_neg _ _

theorem edgeEnd_neg (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3) :
    edgeEnd D (-dir) e = -(edgePos D dir e) := by
  unfold edgePos edgeEnd; simp only [LinearMap.neg_apply]; exact max_neg_neg _ _

theorem wAng_rev (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3)
    (hne : dir ((D.tile e.1).pts e.2) ≠ dir ((D.tile e.1).pts (e.2 + 1))) :
    wAng D (-dir) e = eAng D dir e := by
  unfold wAng eAng westIdx eastIdx
  simp only [LinearMap.neg_apply, neg_le_neg_iff]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : ¬ (dir ((D.tile e.1).pts (e.2 + 1)) ≤ dir ((D.tile e.1).pts e.2)) := not_le.mpr hlt
    simp only [h1, hlt.le, if_false, if_true]
  · have h1 : ¬ (dir ((D.tile e.1).pts e.2) ≤ dir ((D.tile e.1).pts (e.2 + 1))) := not_le.mpr hgt
    simp only [h1, hgt.le, if_false, if_true]

namespace IsChain

variable {D : Dissection N} {w : Wall D} {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain w E n)
include C

theorem dir_ne {m : ℕ} (hm : m < n) :
    w.dir ((D.tile (E m).1).pts (E m).2) ≠ w.dir ((D.tile (E m).1).pts ((E m).2 + 1)) := by
  intro e
  have := C.nondeg m hm
  unfold edgePos edgeEnd at this
  rw [e, min_self, max_self] at this
  exact lt_irrefl _ this

theorem rev_zero {E' : ℕ → Fin N × Fin 3} {n' : ℕ} (C' : IsChain w.rev E' n') :
    n' = n ∧ E' 0 = E (n - 1) ∧ (1 < n → E' 1 = E (n - 2)) := by
  have hn : n' = n := C'.n_eq.trans C.n_eq.symm
  have hn1 : n - 1 < n := by have := C.n_pos; omega
  have hmem0 : E' 0 ∈ wallList D w.g 0 := C'.mem 0 C'.n_pos
  have R1 : E' 0 = E (n - 1) := by
    apply C.unique_by_end hmem0 hn1
    have h1 : (-w.dir) w.b = edgePos D (-w.dir) (E' 0) := by
      have := dir_edgeWest D w.rev.dir (E' 0)
      rw [C'.west0] at this
      exact this
    have h2 := edgePos_neg D w.dir (E' 0)
    have h3 : edgeEnd D w.dir (E (n - 1)) = w.dir w.b := by
      rw [← dir_edgeEast, C.east_last]
    simp only [LinearMap.neg_apply] at h1
    rw [h3]; linarith
  refine ⟨hn, R1, fun h1n => ?_⟩
  have hmem1 : E' 1 ∈ wallList D w.g 0 := C'.mem 1 (by omega)
  apply C.unique_by_end hmem1 (by omega : n - 2 < n)
  have e1 := C'.edgePos_next (m := 0) (by omega)
  have e2 := edgeEnd_neg D w.dir (E' 0)
  have e3 := edgePos_neg D w.dir (E' 1)
  have e4 := C.edgePos_next (m := n - 2) (by omega)
  rw [show n - 2 + 1 = n - 1 by omega] at e4
  have e5 : edgePos D w.rev.dir (E' (0 + 1)) = edgeEnd D w.rev.dir (E' 0) := e1
  have e6 : edgePos D (-w.dir) (E' 1) = edgeEnd D (-w.dir) (E' 0) := e5
  rw [R1] at e6 e2
  linarith

end IsChain

end Erdos634.GLI

#print axioms Erdos634.GLI.IsChain.rev_zero
#print axioms Erdos634.GLI.wAng_rev
