-- Draft/BADCorFull.lean — Lean-level `cor:basealphadiv`: for each of the seven rows
-- (e,f,w,N) of `BADInstances.seven_rows`, no CongruentDissection N with model sides (ef, f²-e², f²)
-- and target isosceles (legs X, base Y, base angles α at two vertices) exists.
-- Proof: ARA.theoremA_N_form_full gives N = r² (f²-e²)(2f²-e²); for each row, N < (f²-e²)(2f²-e²),
-- so r²=0 (hence N=0), contradiction.
import Erdos634.ARAForm

namespace Erdos634.Draft.BADCorFull

open Erdos634.Geometry Erdos634.ARA

-- Helper: nonzero integer has square ≥ 1.
private theorem int_sq_ge_one {r : ℤ} (h : r ≠ 0) : 1 ≤ r ^ 2 := by
  have hna : 1 ≤ r.natAbs := Int.natAbs_pos.mpr h
  calc 1 ≤ (r.natAbs : ℤ) ^ 2 := by exact_mod_cast Nat.one_le_pow 2 _ hna
       _ = r ^ 2 := Int.natAbs_sq r

/-- Generic impossibility: if N < (f²-e²)(2f²-e²) then no base-α dissection with model (ef,b,f²) exists. -/
theorem noTiling_baseAlpha {N : ℕ} (hN : 0 < N) (D : CongruentDissection N) (e f : ℤ)
    (h0 : 0 < e) (hef : e < f) (hcop : IsCoprime e f) (X Y : ℝ)
    (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (e : ℝ) * f)
    (l1 : D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (l2 : D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y)
    (hlt : (N : ℤ) < (f ^ 2 - e ^ 2) * (2 * f ^ 2 - e ^ 2)) : False := by
  obtain ⟨r, hr⟩ := theoremA_N_form_full D e f h0 hef hcop X Y σ l0 l1 l2 τ a0 a1 m0 m1 m2
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rcases eq_or_ne r 0 with rfl | h_ne
  · simp at hr; linarith
  · have h_bQ_pos : 0 < (f ^ 2 - e ^ 2) * (2 * f ^ 2 - e ^ 2) := by nlinarith
    nlinarith [int_sq_ge_one h_ne]

-- The seven instances of cor:basealphadiv (impossibility at the dissection level).

/-- Row 1: (e,f,N) = (1,3,34), b=8, Q=17. No CongruentDissection 34 with model (3,8,9) and
    isosceles target (base angles α). -/
theorem noTiling_34 (D : CongruentDissection 34) (X Y : ℝ)
    (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (1 : ℝ) * 3) (l1 : D.model.oppLen (σ 1) = (3 : ℝ) ^ 2 - 1 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (3 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((1 : ℤ) : ℝ) * (3 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((3 : ℤ) : ℝ) ^ 2 - ((1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((3 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noTiling_baseAlpha (by norm_num) D 1 3 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2 (by norm_num)

/-- Row 2: (e,f,N) = (3,5,164). -/
theorem noTiling_164 (D : CongruentDissection 164) (X Y : ℝ)
    (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (3 : ℝ) * 5) (l1 : D.model.oppLen (σ 1) = (5 : ℝ) ^ 2 - 3 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (5 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((3 : ℤ) : ℝ) * (5 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((5 : ℤ) : ℝ) ^ 2 - ((3 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((5 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noTiling_baseAlpha (by norm_num) D 3 5 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2 (by norm_num)

/-- Row 3: (e,f,N) = (5,7,438). -/
theorem noTiling_438 (D : CongruentDissection 438) (X Y : ℝ)
    (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (5 : ℝ) * 7) (l1 : D.model.oppLen (σ 1) = (7 : ℝ) ^ 2 - 5 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (7 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((5 : ℤ) : ℝ) * (7 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((7 : ℤ) : ℝ) ^ 2 - ((5 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((7 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noTiling_baseAlpha (by norm_num) D 5 7 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2 (by norm_num)

/-- Row 4: (e,f,N) = (1,5,294). -/
theorem noTiling_294 (D : CongruentDissection 294) (X Y : ℝ)
    (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (1 : ℝ) * 5) (l1 : D.model.oppLen (σ 1) = (5 : ℝ) ^ 2 - 1 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (5 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((1 : ℤ) : ℝ) * (5 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((5 : ℤ) : ℝ) ^ 2 - ((1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((5 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noTiling_baseAlpha (by norm_num) D 1 5 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2 (by norm_num)

/-- Row 5: (e,f,N) = (3,7,890). -/
theorem noTiling_890 (D : CongruentDissection 890) (X Y : ℝ)
    (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (3 : ℝ) * 7) (l1 : D.model.oppLen (σ 1) = (7 : ℝ) ^ 2 - 3 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (7 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((3 : ℤ) : ℝ) * (7 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((7 : ℤ) : ℝ) ^ 2 - ((3 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((7 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noTiling_baseAlpha (by norm_num) D 3 7 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2 (by norm_num)

/-- Row 6: (e,f,N) = (1,7,291). -/
theorem noTiling_291 (D : CongruentDissection 291) (X Y : ℝ)
    (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (1 : ℝ) * 7) (l1 : D.model.oppLen (σ 1) = (7 : ℝ) ^ 2 - 1 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (7 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((1 : ℤ) : ℝ) * (7 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((7 : ℤ) : ℝ) ^ 2 - ((1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((7 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noTiling_baseAlpha (by norm_num) D 1 7 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2 (by norm_num)

/-- Row 7: (e,f,N) = (7,9,226). -/
theorem noTiling_226 (D : CongruentDissection 226) (X Y : ℝ)
    (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (7 : ℝ) * 9) (l1 : D.model.oppLen (σ 1) = (9 : ℝ) ^ 2 - 7 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (9 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((7 : ℤ) : ℝ) * (9 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((9 : ℤ) : ℝ) ^ 2 - ((7 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((9 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noTiling_baseAlpha (by norm_num) D 7 9 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2 (by norm_num)

end Erdos634.Draft.BADCorFull

#print axioms Erdos634.Draft.BADCorFull.noTiling_34
#print axioms Erdos634.Draft.BADCorFull.noTiling_226
