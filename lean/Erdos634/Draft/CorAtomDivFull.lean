-- Draft/CorAtomDivFull.lean — Lean-level `cor:atomdiv` (12 instances)
-- For each (e,f,N) row of cor:atomdiv, no CongruentDissection N with model (ef,f²-e²,f²)
-- and atom target (equal angles α+β at two vertices) exists.
-- Proof: ARA.atomDiv_N_form_full gives N = (f²-e²)*r²; for each row, (f²-e²)∤N.
import Erdos634.ARAForm

namespace Erdos634.Draft.CorAtomDivFull

open Erdos634.Geometry Erdos634.ARA

/-- Generic impossibility: if (f²-e²)∤N then no atom dissection exists. -/
theorem noAtomTiling {N : ℕ} (D : CongruentDissection N) (e f : ℤ)
    (h0 : 0 < e) (hef : e < f) (hcop : IsCoprime e f) (X Y : ℝ)
    (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (e : ℝ) * f)
    (l1 : D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (l2 : D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y)
    (hndvd : ¬ (f ^ 2 - e ^ 2 : ℤ) ∣ (N : ℤ)) : False := by
  obtain ⟨_, r, _, _, _, hr⟩ :=
    atomDiv_N_form_full D e f h0 hef hcop X Y σ l0 l1 l2 τ a0 a1 m0 m1 m2
  exact hndvd ⟨r ^ 2, hr⟩

-- (e,f) = (1,3), b = 8

theorem noAtom_2 (D : CongruentDissection 2) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (1 : ℝ) * 3) (l1 : D.model.oppLen (σ 1) = (3 : ℝ) ^ 2 - 1 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (3 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((1 : ℤ) : ℝ) * (3 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((3 : ℤ) : ℝ) ^ 2 - ((1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((3 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 1 3 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

theorem noAtom_18 (D : CongruentDissection 18) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (1 : ℝ) * 3) (l1 : D.model.oppLen (σ 1) = (3 : ℝ) ^ 2 - 1 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (3 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((1 : ℤ) : ℝ) * (3 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((3 : ℤ) : ℝ) ^ 2 - ((1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((3 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 1 3 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

theorem noAtom_50 (D : CongruentDissection 50) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (1 : ℝ) * 3) (l1 : D.model.oppLen (σ 1) = (3 : ℝ) ^ 2 - 1 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (3 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((1 : ℤ) : ℝ) * (3 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((3 : ℤ) : ℝ) ^ 2 - ((1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((3 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 1 3 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

theorem noAtom_98 (D : CongruentDissection 98) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (1 : ℝ) * 3) (l1 : D.model.oppLen (σ 1) = (3 : ℝ) ^ 2 - 1 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (3 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((1 : ℤ) : ℝ) * (3 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((3 : ℤ) : ℝ) ^ 2 - ((1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((3 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 1 3 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

-- (e,f) = (1,5), b = 24

theorem noAtom_6 (D : CongruentDissection 6) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (1 : ℝ) * 5) (l1 : D.model.oppLen (σ 1) = (5 : ℝ) ^ 2 - 1 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (5 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((1 : ℤ) : ℝ) * (5 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((5 : ℤ) : ℝ) ^ 2 - ((1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((5 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 1 5 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

theorem noAtom_54 (D : CongruentDissection 54) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (1 : ℝ) * 5) (l1 : D.model.oppLen (σ 1) = (5 : ℝ) ^ 2 - 1 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (5 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((1 : ℤ) : ℝ) * (5 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((5 : ℤ) : ℝ) ^ 2 - ((1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((5 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 1 5 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

-- (e,f) = (3,5), b = 16

theorem noAtom_9_e3f5 (D : CongruentDissection 9) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (3 : ℝ) * 5) (l1 : D.model.oppLen (σ 1) = (5 : ℝ) ^ 2 - 3 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (5 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((3 : ℤ) : ℝ) * (5 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((5 : ℤ) : ℝ) ^ 2 - ((3 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((5 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 3 5 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

theorem noAtom_25_e3f5 (D : CongruentDissection 25) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (3 : ℝ) * 5) (l1 : D.model.oppLen (σ 1) = (5 : ℝ) ^ 2 - 3 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (5 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((3 : ℤ) : ℝ) * (5 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((5 : ℤ) : ℝ) ^ 2 - ((3 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((5 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 3 5 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

-- (e,f) = (4,5), b = 9

theorem noAtom_4 (D : CongruentDissection 4) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (4 : ℝ) * 5) (l1 : D.model.oppLen (σ 1) = (5 : ℝ) ^ 2 - 4 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (5 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((4 : ℤ) : ℝ) * (5 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((5 : ℤ) : ℝ) ^ 2 - ((4 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((5 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 4 5 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

theorem noAtom_16 (D : CongruentDissection 16) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (4 : ℝ) * 5) (l1 : D.model.oppLen (σ 1) = (5 : ℝ) ^ 2 - 4 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (5 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((4 : ℤ) : ℝ) * (5 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((5 : ℤ) : ℝ) ^ 2 - ((4 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((5 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 4 5 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

theorem noAtom_25_e4f5 (D : CongruentDissection 25) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (4 : ℝ) * 5) (l1 : D.model.oppLen (σ 1) = (5 : ℝ) ^ 2 - 4 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (5 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((4 : ℤ) : ℝ) * (5 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((5 : ℤ) : ℝ) ^ 2 - ((4 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((5 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 4 5 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

theorem noAtom_49 (D : CongruentDissection 49) (X Y : ℝ) (σ τ : Equiv.Perm (Fin 3))
    (l0 : D.model.oppLen (σ 0) = (4 : ℝ) * 5) (l1 : D.model.oppLen (σ 1) = (5 : ℝ) ^ 2 - 4 ^ 2)
    (l2 : D.model.oppLen (σ 2) = (5 : ℝ) ^ 2)
    (a0 : D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (a1 : D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1))
    (m0 : D.target.oppLen (τ 0) = X) (m1 : D.target.oppLen (τ 1) = X)
    (m2 : D.target.oppLen (τ 2) = Y) : False := by
  have l0' : D.model.oppLen (σ 0) = ((4 : ℤ) : ℝ) * (5 : ℤ) := by exact_mod_cast l0
  have l1' : D.model.oppLen (σ 1) = ((5 : ℤ) : ℝ) ^ 2 - ((4 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l1
  have l2' : D.model.oppLen (σ 2) = ((5 : ℤ) : ℝ) ^ 2 := by exact_mod_cast l2
  exact noAtomTiling D 4 5 (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) X Y σ τ l0' l1' l2' a0 a1 m0 m1 m2
    (by decide)

end Erdos634.Draft.CorAtomDivFull

#print axioms Erdos634.Draft.CorAtomDivFull.noAtom_2
#print axioms Erdos634.Draft.CorAtomDivFull.noAtom_49
