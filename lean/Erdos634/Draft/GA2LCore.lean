/-
GA2L, atom P4 (**group core of the top step**, GA2Y_NOTES Lemma A3, Steps 1-3), r = 1, j >= 2,
for GENERAL i = k+3 >= 3 and general j >= 2.

Hypothesis `Hyp k j z5 z2 z3 c`: psi(z5) eta2(z2) eta3(z3) = c for every ODD chi = psi eta2 eta3 in the
admissible top family: psi primitive mod 5, eta2 primitive mod 2^i, eta3 a NONTRIVIAL character mod 3^j
(for j >= 2 the paper's Steps 1-3 only ever use nontrivial eta3, so the hypothesis is the weaker one).
Conclusion (`group_core`): there are s, e in {0,1} with
    z5 = (-1)^s (mod 5),  z3 = (-1)^s (mod 3^j),  z2 = (-1)^s (1 + 2^(i-1))^e (mod 2^i),  c = (-1)^(s+e).
Converse (`group_core_converse`, the witness): every such (z5,z2,z3,s,e) satisfies `Hyp` with
c = (-1)^(s+e).  So the hypothesis is satisfiable and the conclusion is sharp.

Pieces: `const_nontriv` (I3'), `five_odd` (5-part, r = 1), `two_part_core` (Step 1, from
GA2LPar.two_adic_par), assembly.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2LPar

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2LCore

open Erdos634.GA2LPar
open Erdos634.LemmaSGpp (sum_prim)

/-! ## (I3') constancy over nontrivial characters -/

theorem const_nontriv (n : ℕ) [NeZero n] (g : ZMod n) (hg : IsUnit g) (hg1 : g ≠ 1)
    (hn : 3 ≤ n.totient) (c : ℂ) (h : ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 → χ g = c) : False := by
  have hS : ∑ χ : DirichletCharacter ℂ n, χ g = 0 :=
    DirichletCharacter.sum_characters_eq_zero ℂ hg1
  have hN : Fintype.card (DirichletCharacter ℂ n) = n.totient := by
    have := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ n
    rwa [Nat.card_eq_fintype_card] at this
  have h1 : (1 : DirichletCharacter ℂ n) g = 1 := MulChar.one_apply hg
  have hsplit : ∑ χ : DirichletCharacter ℂ n, χ g =
      (1 : DirichletCharacter ℂ n) g + ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ n), χ g :=
    (add_sum_erase univ _ (mem_univ (1 : DirichletCharacter ℂ n))).symm
  have hrest : ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ n), χ g =
      ((Fintype.card (DirichletCharacter ℂ n) : ℂ) - 1) * c := by
    rw [sum_congr rfl (fun χ hχ => h χ (mem_erase.1 hχ).1), sum_const, card_erase_of_mem (mem_univ _),
      nsmul_eq_mul, card_univ]
    have : 1 ≤ Fintype.card (DirichletCharacter ℂ n) := by omega
    push_cast [Nat.cast_sub this]; ring
  have hne : Nontrivial (DirichletCharacter ℂ n) := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨χ0, hχ0⟩ := exists_ne (1 : DirichletCharacter ℂ n)
  have hcn : ‖c‖ = 1 := by
    rw [← h χ0 hχ0]; simpa using χ0.unit_norm_eq_one hg.unit
  rw [hsplit, h1, hrest] at hS
  have h2 : ((Fintype.card (DirichletCharacter ℂ n) : ℂ) - 1) * c = -1 := by linear_combination hS
  have h3 := congrArg norm h2
  rw [norm_mul, hcn, mul_one, norm_neg, NormOneClass.norm_one] at h3
  have h4 : ((Fintype.card (DirichletCharacter ℂ n) : ℂ) - 1) =
      (((Fintype.card (DirichletCharacter ℂ n) - 1 : ℕ) : ℝ) : ℂ) := by
    have : 1 ≤ Fintype.card (DirichletCharacter ℂ n) := by omega
    push_cast [Nat.cast_sub this]; ring
  rw [h4, Complex.norm_real, Real.norm_natCast] at h3
  have : Fintype.card (DirichletCharacter ℂ n) - 1 = 1 := by exact_mod_cast h3
  omega

/-! ## The 5-part (r = 1) -/

instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact5pow : NeZero (5 ^ 1) := ⟨by norm_num⟩

theorem S_five (z : ℤ) (hz : IsUnit ((z : ZMod (5 ^ 1)))) :
    (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (5 ^ 1) => χ.IsPrimitive),
        χ (z : ZMod (5 ^ 1))) =
      (((if z ≡ 1 [ZMOD 5] then 3 else -1 : ℤ)) : ℂ) := by
  set g : (ZMod (5 ^ 1))ˣ := hz.unit with hg
  have hgz : (g : ZMod (5 ^ 1)) = (z : ZMod _) := rfl
  have hS := sum_prim (q := 5) (v := 1) (by omega) g
  rw [hgz] at hS
  rw [hS]
  have hsub : Subsingleton (ZMod (5 ^ (1 - 1))) := by
    show Subsingleton (ZMod 1); infer_instance
  have e0 : (((z : ℤ) : ZMod (5 ^ 1)).cast : ZMod (5 ^ (1 - 1))) = 1 := Subsingleton.elim _ _
  have t0 : (5 ^ (1 - 1)).totient = 1 := by
    show Nat.totient 1 = 1; exact Nat.totient_one
  have t1 : (5 ^ 1).totient = 4 := by
    rw [pow_one, Nat.totient_prime (by norm_num)]
  have e1 : ((z : ℤ) : ZMod (5 ^ 1)) = 1 ↔ z ≡ 1 [ZMOD 5] := by
    rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff]; push_cast; rfl
  rw [if_pos e0, t0, t1]
  by_cases h : z ≡ 1 [ZMOD 5]
  · simp only [e1, h, if_true]; push_cast; ring
  · simp only [e1, h, if_false]; push_cast; ring

theorem key5 (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (z : ℤ) (hz : IsUnit ((z : ZMod (5 ^ 1)))) :
    2 * ∑ χ ∈ PrimPar 5 1 ε, χ (z : ZMod (5 ^ 1)) =
      ((if z ≡ 1 [ZMOD 5] then 3 else -1 : ℤ) : ℂ) +
        ε * ((if -z ≡ 1 [ZMOD 5] then 3 else -1 : ℤ) : ℂ) := by
  have h := parsum (q := 5) (v := 1) ε hε (z : ZMod (5 ^ 1))
  have e : -((z : ℤ) : ZMod (5 ^ 1)) = ((-z : ℤ) : ZMod (5 ^ 1)) := by push_cast; rfl
  rw [e] at h
  rw [h, S_five z hz, S_five (-z) (by rw [← e]; exact hz.neg)]

theorem card_five (ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    (PrimPar 5 1 ε).card = if ε = 1 then 1 else 2 := by
  have h := key5 ε hε 1 (by simp)
  have e1 : ∀ χ ∈ PrimPar 5 1 ε, χ (((1 : ℤ)) : ZMod (5 ^ 1)) = 1 := by
    intro χ _; simp
  rw [sum_congr rfl e1, sum_const, nsmul_eq_mul, mul_one] at h
  have hA : (1 : ℤ) ≡ 1 [ZMOD 5] := rfl
  have hn : ¬ (-1 : ℤ) ≡ 1 [ZMOD 5] := by decide
  rw [if_pos hA, if_neg hn] at h
  rcases hε with rfl | rfl
  · have : ((PrimPar 5 1 1).card : ℂ) = 1 := by push_cast at h; linear_combination h / 2
    simp only [if_true]; exact_mod_cast this
  · have : ((PrimPar 5 1 (-1)).card : ℂ) = 2 := by push_cast at h; linear_combination h / 2
    simp only [if_neg (by norm_num : (-1 : ℂ) ≠ 1)]; exact_mod_cast this

/-- Odd characters mod 5: constancy of psi(z) forces z = ±1 and c = the sign. -/
theorem five_odd (z : ℤ) (hz : IsUnit ((z : ZMod (5 ^ 1)))) (c : ℂ)
    (hc : ∀ ψ ∈ PrimPar 5 1 (-1), ψ (z : ZMod (5 ^ 1)) = c) :
    (z ≡ 1 [ZMOD 5] ∧ c = 1) ∨ (z ≡ -1 [ZMOD 5] ∧ c = -1) := by
  have hk := key5 (-1) (Or.inr rfl) z hz
  have hcd := card_five (-1) (Or.inr rfl)
  rw [if_neg (by norm_num : (-1 : ℂ) ≠ 1)] at hcd
  rw [sum_congr rfl hc, sum_const, nsmul_eq_mul, hcd] at hk
  have hpos : (PrimPar 5 1 (-1)).Nonempty := by rw [← card_pos, hcd]; norm_num
  obtain ⟨ψ0, h0⟩ := hpos
  have hcn : ‖c‖ = 1 := by
    rw [← hc ψ0 h0]
    have := ψ0.unit_norm_eq_one hz.unit
    simpa using this
  by_cases h1 : z ≡ 1 [ZMOD 5]
  · have h2 : ¬ (-z ≡ 1 [ZMOD 5]) := by
      unfold Int.ModEq at h1 ⊢; omega
    rw [if_pos h1, if_neg h2] at hk
    left; refine ⟨h1, ?_⟩
    push_cast at hk; linear_combination hk / 4
  · by_cases h2 : -z ≡ 1 [ZMOD 5]
    · rw [if_neg h1, if_pos h2] at hk
      right; refine ⟨?_, ?_⟩
      · unfold Int.ModEq at h2 ⊢; omega
      · push_cast at hk; linear_combination hk / 4
    · rw [if_neg h1, if_neg h2] at hk
      exfalso
      have : c = 0 := by push_cast at hk; linear_combination hk / 4
      rw [this, norm_zero] at hcn; exact zero_ne_one hcn


/-! ## Step 1 (2-part) as a standalone group-core lemma -/

theorem zm {k : ℕ} {z w : ℤ} (h : z ≡ w [ZMOD 2 ^ (k + 3)]) :
    ((z : ℤ) : ZMod (2 ^ (k + 3))) = (w : ZMod (2 ^ (k + 3))) := by
  rw [ZMod.intCast_eq_intCast_iff]; push_cast; exact h

theorem mem_PrimPar {q v : ℕ} [Fact q.Prime] {ε : ℂ} {ψ : DirichletCharacter ℂ (q ^ v)} :
    ψ ∈ PrimPar q v ε ↔ ψ.IsPrimitive ∧ ψ (-1) = ε := by
  haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  simp [PrimPar]

theorem nz {n : ℕ} (χ : DirichletCharacter ℂ n) (z : ZMod n) (hz : IsUnit z) : χ z ≠ 0 := by
  intro h0
  have := χ.unit_norm_eq_one hz.unit
  simp [h0] at this

theorem sign_val {n : ℕ} (χ : DirichletCharacter ℂ n) : χ (-1) = 1 ∨ χ (-1) = -1 :=
  χ.even_or_odd

/-- **Step 1 of Lemma A3.** If psi-free constancy of eta2(z) over the primitive characters mod 2^i of ONE
parity holds (i >= 3), then z = (-1)^s (1+2^(i-1))^e and eta2(z) = eps^s (-1)^e for primitive
eta2 of EVERY parity eps. -/
theorem two_part_core (k : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (z : ℤ)
    (hz : IsUnit ((z : ZMod (2 ^ (k + 3)))))
    (h : ∃ c : ℂ, ∀ η ∈ PrimPar 2 (k + 3) ε, η (z : ZMod (2 ^ (k + 3))) = c) :
    ∃ s e : ℕ, s < 2 ∧ e < 2 ∧
      ((z : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e) ∧
      ∀ ε' : ℂ, (ε' = 1 ∨ ε' = -1) → ∀ η ∈ PrimPar 2 (k + 3) ε',
        η (z : ZMod (2 ^ (k + 3))) = ε' ^ s * (-1) ^ e := by
  have h4 := (two_adic_par k ε hε z hz).1 h
  rcases h4 with h1 | h2 | h3 | h4
  · refine ⟨0, 0, by norm_num, by norm_num, ?_, fun ε' hε' η hη => ?_⟩
    · have := zm h1; simpa using this
    · have := (two_adic_par_value k ε' hε' z hz).1 h1 η hη; simpa using this
  · refine ⟨0, 1, by norm_num, by norm_num, ?_, fun ε' hε' η hη => ?_⟩
    · have := zm h2; push_cast at this; simpa using this
    · have := (two_adic_par_value k ε' hε' z hz).2.1 h2 η hη; simpa using this
  · refine ⟨1, 0, by norm_num, by norm_num, ?_, fun ε' hε' η hη => ?_⟩
    · have := zm h3; push_cast at this; simpa using this
    · have := (two_adic_par_value k ε' hε' z hz).2.2.1 h3 η hη; simpa using this
  · refine ⟨1, 1, by norm_num, by norm_num, ?_, fun ε' hε' η hη => ?_⟩
    · have := zm h4; push_cast at this; simpa using this
    · have := (two_adic_par_value k ε' hε' z hz).2.2.2 h4 η hη; simpa using this

end Erdos634.GA2LCore

#print axioms Erdos634.GA2LCore.const_nontriv
#print axioms Erdos634.GA2LCore.five_odd
#print axioms Erdos634.GA2LCore.card_five
#print axioms Erdos634.GA2LCore.two_part_core
