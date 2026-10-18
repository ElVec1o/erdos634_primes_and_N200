import Mathlib.Tactic
import Erdos634.Ladder
import Erdos634.AngleSumDissection
import Erdos634.E1NormalForm

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (3)): isometries preserve corner angles and local angles  

`iso_angle` : `cornerAngle (g p) (g q) (g r) = cornerAngle p q r` for an isometry `g` of the plane.
`localAngle_iso` : if a triangle `T'` has the vertices `g (T.pts m)` then `T'.localAngle (g p) = T.localAngle p`
(barycentric coordinates are affine invariants, the corner angle is an isometry invariant).
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry

theorem iso_angle (g : Plane ≃ᵢ Plane) (p q r : Plane) :
    cornerAngle (g p) (g q) (g r) = cornerAngle p q r := by
  unfold cornerAngle
  have := (g.toRealAffineIsometryEquiv.toAffineIsometry).angle_map p q r
  simpa [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] using this

theorem coord_iso (g : Plane ≃ᵢ Plane) {T T' : Tri} (h : ∀ m, T'.pts m = g (T.pts m)) (k : Fin 3) (p : Plane) :
    T'.basis.coord k (g p) = T.basis.coord k p := by
  classical
  have hp := T.basis.affineCombination_coord_eq_self p
  have hw := T.basis.sum_coord_apply_eq_one p
  have e1 : g p = Finset.univ.affineCombination ℝ (fun i => T'.basis i) (fun i => T.basis.coord i p) := by
    conv_lhs => rw [← hp]
    have := Finset.univ.map_affineCombination (fun i => T.basis i) (fun i => T.basis.coord i p) hw
      (Erdos634.Ladder.isoAff g).toAffineMap
    simp only [AffineEquiv.coe_toAffineMap] at this
    rw [show (g (Finset.univ.affineCombination ℝ (fun i => T.basis i) fun i => T.basis.coord i p)) =
      (Erdos634.Ladder.isoAff g) (Finset.univ.affineCombination ℝ (fun i => T.basis i) fun i => T.basis.coord i p) from rfl]
    have hfun : (Erdos634.Ladder.isoAff g) ∘ (fun i => T.basis i) = fun i => T'.basis i := by
      funext i
      show Erdos634.Ladder.isoAff g (T.pts i) = T'.pts i
      rw [h i]; rfl
    rw [this, hfun]
  rw [e1]
  exact T'.basis.coord_apply_combination_of_mem (Finset.mem_univ k) hw

theorem localAngle_iso (g : Plane ≃ᵢ Plane) {T T' : Tri} (h : ∀ m, T'.pts m = g (T.pts m)) (p : Plane) :
    T'.localAngle (g p) = T.localAngle p := by
  classical
  unfold Tri.localAngle
  by_cases hv : ∃ j, p = T.pts j
  · have hv' : ∃ j, g p = T'.pts j := by
      obtain ⟨j, hj⟩ := hv; exact ⟨j, by rw [h j, hj]⟩
    rw [dif_pos hv, dif_pos hv']
    have e1 : hv'.choose = hv.choose := by
      have a1 : g p = T'.pts hv'.choose := hv'.choose_spec
      have a2 : p = T.pts hv.choose := hv.choose_spec
      apply T'.indep.injective
      have : g p = g (T.pts hv.choose) := congrArg g a2
      rw [← a1, this, h]
    rw [e1, h, h, h, iso_angle]
  · have hv' : ¬ ∃ j, g p = T'.pts j := by
      rintro ⟨j, hj⟩
      apply hv
      exact ⟨j, g.injective (by rw [hj, h j])⟩
    rw [dif_neg hv, dif_neg hv']
    simp only [coord_iso g h]

#print axioms iso_angle
#print axioms localAngle_iso
end Erdos634.Draft.ThmDRun
