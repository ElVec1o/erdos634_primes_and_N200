/-
Draft/AddLawWitness.lean -- the hypotheses of `AddLawFull.thm_addlaw` are satisfiable, and one instance.

* `addlaw_hypotheses_witness`: the certified 44-tiling (`Tiling44Bridge.dissection`, coordinates at scale 8), scaled
  by `1/8`, is a `CongruentDissection 44` whose target is congruent to `Δ_2` of the member `(1, 2)` (sides
  `22, 16, 16`) and whose model is congruent to the tile `(2, 3, 4)`.
* `addlaw_instance`: hence `Δ_4` of `(1, 2)` (sides `44, 32, 32`) is cut into `176 = 44 + 88 + 44` copies of the tile.
  This reproduces a known tiling count (`11 m²` at `m = 4`, `thm:realize12`); it is a control, not a new value. not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.AddLawFull
import Erdos634.Draft.CollarInputs

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (RTiling.cast RTiling.castN)

namespace Erdos634.Draft.AddLawWitness

open Erdos634.Draft.RegionTiling Erdos634.Draft.WideColFull Erdos634.Draft.AddLawFull
open Erdos634.Draft.CollarInputs (mapHom cong_of_scaled M44 M44_sq)
open Erdos634.Realizable (homothetyEquiv)

def sw : Equiv.Perm (Fin 3) := Equiv.swap 0 1

theorem sw0 : sw 0 = 1 := by decide
theorem sw1 : sw 1 = 0 := by decide
theorem sw2 : sw 2 = 2 := by decide

/-- **The hypotheses of the addition law hold at `(e, f) = (1, 2)`, `m = 2`.** -/
theorem addlaw_hypotheses_witness :
    ∃ D : CongruentDissection 44,
      D.target.Congruent (DTn 1 2 2 le_rfl (by norm_num) (by norm_num)) ∧
      D.model.Congruent (MTn 1 2 le_rfl (by norm_num)) := by
  have h := mapHom (ofCD Erdos634.Tiling44Bridge.dissection) (0 : Plane) (1 / 8) (by norm_num)
  have h2 := RTiling.castN (by decide : Tiling44.tiles.length = 44)
    (RTiling.cast (Erdos634.DissectionMap.mapTri_carrier _ _).symm h)
  obtain ⟨a1, a2, a3⟩ := Erdos634.Tiling44Bridge.targetTri_sides
  obtain ⟨b1, b2, b3⟩ := M44_sq
  obtain ⟨d1, d2, d3⟩ := DTn_sides 1 2 2 le_rfl (by norm_num) (by norm_num)
  obtain ⟨t1, t2, t3⟩ := MTn_sides 1 2 le_rfl (by norm_num)
  refine ⟨toCD h2, ?_, ?_⟩
  · show (Erdos634.DissectionMap.mapTri (homothetyEquiv (0 : Plane) (1 / 8) _)
      Erdos634.Tiling44Bridge.targetTri).Congruent _
    refine cong_of_scaled (by norm_num) _ _ ?_ ?_ ?_
    · rw [mul_pow, a1, d1]
      push_cast
      norm_num
    · rw [mul_pow, a2, d2]
      push_cast
      norm_num
    · rw [mul_pow, a3, d3]
      push_cast
      norm_num
  · show (Erdos634.DissectionMap.mapTri (homothetyEquiv (0 : Plane) (1 / 8) _) M44).Congruent _
    refine (cong_of_scaled (by norm_num) M44 ((MTn 1 2 le_rfl (by norm_num)).relabel sw) ?_ ?_ ?_).trans
      ((MTn 1 2 le_rfl (by norm_num)).congruent_relabel sw).symm
    · rw [Tri.relabel_pts, Tri.relabel_pts, sw0, sw1, mul_pow, b1, dist_comm, t1]
      push_cast
      norm_num
    · rw [Tri.relabel_pts, Tri.relabel_pts, sw1, sw2, mul_pow, b2, dist_comm, t3]
      push_cast
      norm_num
    · rw [Tri.relabel_pts, Tri.relabel_pts, sw2, sw0, mul_pow, b3, dist_comm, t2]
      push_cast
      norm_num

/-- **An instance of the addition law:** `Δ_4` of the member `(1, 2)` from two copies of `Δ_2`. -/
theorem addlaw_instance :
    ∃ D : CongruentDissection 176,
      D.target = DTn 1 2 4 le_rfl (by norm_num) (by norm_num) ∧ D.model = MTn 1 2 le_rfl (by norm_num) := by
  obtain ⟨D, hT, hM⟩ := addlaw_hypotheses_witness
  obtain ⟨D', h1, h2⟩ := thm_addlaw 1 2 2 2 le_rfl (by norm_num) (by norm_num) (by norm_num) (Or.inr rfl)
    D D hT hM hT hM
  exact ⟨D', h1, h2⟩

end Erdos634.Draft.AddLawWitness

#print axioms Erdos634.Draft.AddLawWitness.addlaw_hypotheses_witness
#print axioms Erdos634.Draft.AddLawWitness.addlaw_instance
