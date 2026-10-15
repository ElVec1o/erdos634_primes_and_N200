/-
Draft/E60Mod9B.lean — the finite arithmetic of the mod-9 obstruction for `E60Pair 87 29 9` (π/3 tile, equilateral target,
`N = 87`, invariant pair `(m₁, m₂) = (29, 9)`; `a + b = 19S/87`, `c = 10S/87`, `(87(a−b))² = 13 S²`).
Two integer weights `g0, g1 : ℤ/6 × ℤ/3 → ℤ` (odd under `x ↦ x + (3,0)`), a tile of type (vertex ↔ {α,β,γ} injection `t`,
orientation `o`, position `x`) has coefficient triple `coef g t pos s` (the integer multiplying the side `a`,`b`,`c`), and
`ν = 38(P₀+Q₀) + 40 R₀ + (P₁ − Q₁)` is divisible by 9 for EVERY type (216 cases, `decide`), while the boundary value is
`g0(0,0)+g0(2,0)+g0(4,0) = 1`.  (The certificate was found by an integer-lattice computation on the direction-class system
and is verified by `ν mod 9` over all 216 types.)  No sorry, no native_decide.
-/
import Erdos634.Draft.E60Mod9A

open scoped Classical

namespace Erdos634.Draft.E60Mod9

open Erdos634.Geometry

def sg (j : ZMod 6) : ℤ := if j.val < 3 then 1 else -1

def tab0 (m k : ℕ) : ℤ :=
  if m = 0 ∧ k = 2 then 1 else if m = 1 ∧ k = 0 then -1 else if m = 2 ∧ k = 1 then 1 else 0

def tab1 (m k : ℕ) : ℤ :=
  if m = 0 ∧ k = 1 then -2 else if m = 0 ∧ k = 2 then 2 else if m = 1 ∧ k = 0 then -2
  else if m = 1 ∧ k = 1 then 2 else 0

def g0 (x : GZ) : ℤ := sg x.1 * tab0 (x.1.val % 3) x.2.val
def g1 (x : GZ) : ℤ := sg x.1 * tab1 (x.1.val % 3) x.2.val

theorem g0_odd : ∀ x : GZ, g0 (x + (3, 0)) = - g0 x := by decide
theorem g1_odd : ∀ x : GZ, g1 (x + (3, 0)) = - g1 x := by decide

/-- Exterior-angle positions of the angles `α, β = 2π/3 − α, γ = π/3`:
`π − α = 3·(π/3) − α ↦ (3, −1) = (3,2)`, `π − β = π/3 + α ↦ (1,1)`, `π − γ = 2·(π/3) ↦ (2,0)`. -/
def E3 : Fin 3 → GZ := ![(3, 2), (1, 1), (2, 0)]

/-- Positions of `leftUnit 0, 1, 2` of a ccw tile whose vertex `k` carries the angle of type `t k`. -/
def posP (t : Fin 3 → Fin 3) (x : GZ) : Fin 3 → GZ := ![x, x + E3 (t 1), x + E3 (t 1) + E3 (t 2)]
/-- The same for a cw tile (`x` = position of `leftUnit 2`). -/
def posM (t : Fin 3 → Fin 3) (y : GZ) : Fin 3 → GZ := ![y + E3 (t 2) + E3 (t 1), y + E3 (t 2), y]

def pk (o : Bool) (t : Fin 3 → Fin 3) (x : GZ) : Fin 3 → GZ := if o then posP t x else posM t x

/-- Integer coefficient of the side of type `s` (`a, b, c` for `s = 0, 1, 2`): edge `k` has length `oppLen (k+2)`. -/
def coef (g : GZ → ℤ) (t : Fin 3 → Fin 3) (pos : Fin 3 → GZ) (s : Fin 3) : ℤ :=
  ∑ k : Fin 3, if t (k + 2) = s then g (pos k) else 0

def nu (t : Fin 3 → Fin 3) (pos : Fin 3 → GZ) : ℤ :=
  38 * (coef g0 t pos 0 + coef g0 t pos 1) + 40 * coef g0 t pos 2 + (coef g1 t pos 0 - coef g1 t pos 1)

/-- **The finite check.**  For every type (injection `t`, orientation `o`, position `x`), `9 ∣ ν`. -/
theorem nu_div : ∀ t : Fin 3 → Fin 3, Function.Injective t → ∀ (o : Bool) (x : GZ),
    (9 : ℤ) ∣ nu t (pk o t x) := by
  decide +kernel

theorem boundary_g0 : g0 (0, 0) + g0 (2, 0) + g0 (4, 0) = 1 := by decide

theorem sum_coef (a b c : ℝ) (t : Fin 3 → Fin 3) (pos : Fin 3 → GZ) (g : GZ → ℤ) :
    ∑ k : Fin 3, ![a, b, c] (t (k + 2)) * (g (pos k) : ℝ) =
      a * (coef g t pos 0 : ℝ) + b * (coef g t pos 1 : ℝ) + c * (coef g t pos 2 : ℝ) := by
  have lg : ∀ (x : ℝ) (u : Fin 3), ![a, b, c] u * x =
      a * (if u = 0 then x else 0) + b * (if u = 1 then x else 0) + c * (if u = 2 then x else 0) := by
    intro x u; fin_cases u <;> simp
  unfold coef
  simp only [Fin.sum_univ_three, lg]
  push_cast
  ring

end Erdos634.Draft.E60Mod9

#print axioms Erdos634.Draft.E60Mod9.nu_div
#print axioms Erdos634.Draft.E60Mod9.sum_coef
