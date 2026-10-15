import Erdos634.ATDWit

namespace Erdos634.Draft.ATDWitWrap
open Erdos634.ATDL2
open Erdos634.Geometry Erdos634.BADL2
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)

variable {N : ℕ}

/-- Applying atomDiv_L2_full via the AHyp bundled hypotheses. -/
theorem wrap_apply_atom (D : CongruentDissection N) (e f : ℤ) (h0 : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f) (X Y : ℝ) (h : AHyp e f X Y D) :
    ∃ μ : ℤ, X = (f : ℝ) * μ ∧ Y = (e : ℝ) * μ ∧ (f ^ 2 - e ^ 2) ∣ μ :=
  apply_atom D e f h0 hef hcop X Y h

/-- Angle sum is preserved under vertex permutation. -/
theorem wrap_angle_sum_perm (T : Tri) (ρ : Equiv.Perm (Fin 3)) :
    T.angleAt (ρ 0) + T.angleAt (ρ 1) + T.angleAt (ρ 2) = Real.pi :=
  angle_sum_perm T ρ

/-- The real A4 witness: 48-tile dissection satisfying AHyp 1 2 24 12. -/
theorem wrap_witness_A4 : ∃ D : CongruentDissection G3CAtomTiling.tiles.length,
    HasSides D.model 2 3 4 ∧ AHyp 1 2 24 12 D :=
  witness_A4

/-- Applying the theorem to A4: μ = 12, 3 ∣ 12, 48 = 3·4². -/
theorem wrap_atom_A4 : ∃ D : CongruentDissection G3CAtomTiling.tiles.length,
    AHyp 1 2 24 12 D ∧ ∃ μ : ℤ, μ = 12 ∧ ((2 : ℤ) ^ 2 - 1 ^ 2) ∣ μ ∧
      ∃ r : ℤ, ((G3CAtomTiling.tiles.length : ℕ) : ℤ) = ((2 : ℤ) ^ 2 - 1 ^ 2) * r ^ 2 :=
  atom_A4

example : True := trivial

#print axioms wrap_witness_A4

end Erdos634.Draft.ATDWitWrap
