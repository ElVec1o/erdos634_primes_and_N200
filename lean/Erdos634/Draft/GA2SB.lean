/-
GA2S, atom B: the PARITY-SWAPPED product-group orbit lemma (the K-a analogue of GA2QK2.even_of_top), r >= 2.

For the 2-part chi_4 (odd) the equations are on the EVEN products psi eta (psi primitive mod 5^r, eta mod 3^j, psi(-1) eta(-1) = 1).
Let F(g) = sum_t [g = y_t] c_t on Z/(5^r 3^j).  If
  (A)  sum_t c_t psi(y_t) eta(y_t) = 0 for all primitive psi, all eta with psi(-1) eta(-1) = 1, and
  (B)  every fibre of g -> g mod 5^(r-1) 3^j meets P (a set containing all +-y_t) in at most 4 points,
then F is ODD:  F(g) + F(-g) = 0 for every g.        (`odd_of_top`)
Proof: S(g) = F(g) + F(-g) is orthogonal to every psi x eta with psi primitive (odd products trivially, even by (A)), hence invariant
under N = ker((Z/5^r 3^j)^x -> (Z/5^(r-1) 3^j)^x), of order exactly 5 for r >= 2 (`card_ker5`); a nonzero S would put a full 5-point orbit in P.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2QK2

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SB

open DirichletCharacter Erdos634.DirichletCRT Erdos634.GA2PC
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.GA2QK2

noncomputable def Sd {ι : Type*} (r j : ℕ) (V : Finset ι) (y : ι → ZMod (5 ^ r * 3 ^ j)) (c : ι → ℂ)
    (g : (ZMod (5 ^ r * 3 ^ j))ˣ) : ℂ :=
  Fv r j V y c (g : ZMod (5 ^ r * 3 ^ j)) + Fv r j V y c (-(g : ZMod (5 ^ r * 3 ^ j)))

theorem S_formula' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (Φ : ZMod N → ℂ) :
    ∑ u : (ZMod N)ˣ, χ (u : ZMod N) * (Φ (u : ZMod N) + Φ (-(u : ZMod N))) =
      (1 + χ (-1)) * ∑ u : (ZMod N)ˣ, χ (u : ZMod N) * Φ (u : ZMod N) := by
  have := neg_sum χ Φ
  have e : ∀ u : (ZMod N)ˣ, χ (u : ZMod N) * (Φ (u : ZMod N) + Φ (-(u : ZMod N))) =
      χ (u : ZMod N) * Φ (u : ZMod N) + χ (u : ZMod N) * Φ (-(u : ZMod N)) := fun u => by ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, this]
  ring

theorem S_inv {ι : Type*} (r j : ℕ) (hr : 1 ≤ r) (V : Finset ι) (y : ι → ZMod (5 ^ r * 3 ^ j)) (c : ι → ℂ)
    (hy : ∀ t ∈ V, c t ≠ 0 → IsUnit (y t))
    (hA : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = 1 →
      ∑ t ∈ V, c t * (ψ (c5 r j (y t)) * η (c3 r j (y t))) = 0)
    (n : (ZMod (5 ^ r * 3 ^ j))ˣ) (hn : ZMod.unitsMap (dvdM r j) n = 1)
    (g : (ZMod (5 ^ r * 3 ^ j))ˣ) : Sd r j V y c (g * n) = Sd r j V y c g := by
  refine sub_eq_zero.1 (fourier_zero (fun u => Sd r j V y c (u * n) - Sd r j V y c u) ?_ g)
  intro χ
  set ψ := comp₁ (cop5 r j) χ with hψ
  set η := comp₂ (cop5 r j) χ with hη
  have e := decomp5 r j χ
  have hχ : ∀ u : (ZMod (5 ^ r * 3 ^ j))ˣ, χ (u : ZMod (5 ^ r * 3 ^ j)) =
      ψ (c5 r j (u : ZMod (5 ^ r * 3 ^ j))) * η (c3 r j (u : ZMod (5 ^ r * 3 ^ j))) := by
    intro u
    have := congrArg (fun χ' : DirichletCharacter ℂ (5 ^ r * 3 ^ j) => χ' (u : ZMod (5 ^ r * 3 ^ j))) e
    simp only at this
    rw [pc_apply] at this
    exact this
  set S : ℂ := ∑ u : (ZMod (5 ^ r * 3 ^ j))ˣ, χ (u : ZMod (5 ^ r * 3 ^ j)) * Sd r j V y c u with hS
  set A : ℂ := ∑ u : (ZMod (5 ^ r * 3 ^ j))ˣ, χ (u : ZMod (5 ^ r * 3 ^ j)) * Sd r j V y c (u * n) with hA'
  have hshift : χ (n : ZMod (5 ^ r * 3 ^ j)) * A = S := by
    rw [hS, ← Equiv.sum_comp (Equiv.mulRight n) (fun u : (ZMod (5 ^ r * 3 ^ j))ˣ =>
      χ (u : ZMod (5 ^ r * 3 ^ j)) * Sd r j V y c u), hA', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    simp only [Equiv.coe_mulRight, Units.val_mul, map_mul]
    ring
  have hgoal : ∑ u : (ZMod (5 ^ r * 3 ^ j))ˣ, χ (u : ZMod (5 ^ r * 3 ^ j)) *
      (Sd r j V y c (u * n) - Sd r j V y c u) = A - S := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rfl
  rw [hgoal]
  have hχn : χ (n : ZMod (5 ^ r * 3 ^ j)) ≠ 0 := unit_val_ne_zero χ n
  by_cases hψp : ψ.IsPrimitive
  · have hSz : S = 0 := by
      have hS2 : S = (1 + χ (-1)) * ∑ u : (ZMod (5 ^ r * 3 ^ j))ˣ, χ (u : ZMod (5 ^ r * 3 ^ j)) *
          Fv r j V y c (u : ZMod (5 ^ r * 3 ^ j)) := S_formula' χ (Fv r j V y c)
      have hT : ∑ u : (ZMod (5 ^ r * 3 ^ j))ˣ, χ (u : ZMod (5 ^ r * 3 ^ j)) *
          Fv r j V y c (u : ZMod (5 ^ r * 3 ^ j)) = ∑ t ∈ V, c t * (ψ (c5 r j (y t)) * η (c3 r j (y t))) := by
        rw [sum_Fv r j V y c hy χ]
        refine Finset.sum_congr rfl (fun t ht => ?_)
        by_cases hct : c t = 0
        · simp [hct]
        obtain ⟨u, hu⟩ := hy t ht hct
        rw [← hu, hχ u]
      have hneg1 : χ (-1) = ψ (-1) * η (-1) := by
        have := hχ (-1)
        simp only [Units.val_neg, Units.val_one, map_neg, map_one] at this
        exact this
      rw [hS2, hT]
      rcases DirichletCharacter.even_or_odd ψ with h1 | h1 <;>
        rcases DirichletCharacter.even_or_odd η with h2 | h2
      · have hA0 := hA ψ hψp η (by rw [h1, h2]; norm_num)
        rw [hA0]; ring
      · rw [hneg1, h1, h2]; ring
      · rw [hneg1, h1, h2]; ring
      · have hA0 := hA ψ hψp η (by rw [h1, h2]; norm_num)
        rw [hA0]; ring
    rw [hSz] at hshift
    have : A = 0 := (mul_eq_zero.1 hshift).resolve_left hχn
    rw [this, hSz]; ring
  · -- ψ factors through 5^(r-1), and n is trivial there and mod 3^j: χ n = 1
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hf : ψ.FactorsThrough (5 ^ (r - 1)) :=
      not_not.1 (fun h' => hψp ((Erdos634.LemmaSN.isPrimitive_iff_not_factorsThrough hr ψ).2 h'))
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := ψ) (pred_dvd 5 r)] at hf
    have hn5 : ZMod.unitsMap (Nat.dvd_mul_right (5 ^ r) (3 ^ j)) n ∈ (ZMod.unitsMap (pred_dvd 5 r)).ker := by
      rw [MonoidHom.mem_ker]
      have h1 : ZMod.unitsMap (pred_dvd 5 r) (ZMod.unitsMap (Nat.dvd_mul_right (5 ^ r) (3 ^ j)) n) =
          ZMod.unitsMap (Nat.dvd_mul_right (5 ^ (r - 1)) (3 ^ j)) (ZMod.unitsMap (dvdM r j) n) := by
        rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ZMod.unitsMap_comp, ZMod.unitsMap_comp]
      rw [h1, hn, map_one]
    have h5 := hf hn5
    rw [MonoidHom.mem_ker] at h5
    have hψn : ψ (c5 r j (n : ZMod (5 ^ r * 3 ^ j))) = 1 := by
      have : c5 r j (n : ZMod (5 ^ r * 3 ^ j)) =
          ((ZMod.unitsMap (Nat.dvd_mul_right (5 ^ r) (3 ^ j)) n : (ZMod (5 ^ r))ˣ) : ZMod (5 ^ r)) := by
        rw [ZMod.unitsMap_val]; rfl
      rw [this, ← MulChar.coe_toUnitHom, h5, Units.val_one]
    have hc3n : c3 r j (n : ZMod (5 ^ r * 3 ^ j)) = 1 := by
      have h1 : ZMod.unitsMap (Nat.dvd_mul_left (3 ^ j) (5 ^ r)) n =
          ZMod.unitsMap (Nat.dvd_mul_left (3 ^ j) (5 ^ (r - 1))) (ZMod.unitsMap (dvdM r j) n) := by
        rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp]
      rw [hn, map_one] at h1
      have := congrArg (fun w : (ZMod (3 ^ j))ˣ => (w : ZMod (3 ^ j))) h1
      simp only [ZMod.unitsMap_val, Units.val_one] at this
      exact this
    have h1 : χ (n : ZMod (5 ^ r * 3 ^ j)) = 1 := by
      rw [hχ n, hc3n, MulChar.map_one, hψn, one_mul]
    rw [h1, one_mul] at hshift
    rw [hshift]; ring

theorem card_ker5 (r j : ℕ) (hr : 2 ≤ r) :
    5 ≤ (Finset.univ.filter (fun n : (ZMod (5 ^ r * 3 ^ j))ˣ =>
      ZMod.unitsMap (dvdM r j) n = 1)).card := by
  have h := Erdos634.LemmaSC.fiber_card (n := 5 ^ r * 3 ^ j) (d := 5 ^ (r - 1) * 3 ^ j) (dvdM r j)
  have hφM : 0 < (5 ^ (r - 1) * 3 ^ j).totient := Nat.totient_pos.2 (by positivity)
  have h' : ((Finset.univ.filter (fun n : (ZMod (5 ^ r * 3 ^ j))ˣ =>
      ZMod.unitsMap (dvdM r j) n = 1)).card) * (5 ^ (r - 1) * 3 ^ j).totient = (5 ^ r * 3 ^ j).totient := by
    have h0 : ((5 ^ (r - 1) * 3 ^ j).totient : ℂ) ≠ 0 := by exact_mod_cast hφM.ne'
    rw [eq_div_iff h0] at h
    exact_mod_cast h
  rw [Nat.totient_mul (cop5 r j), Nat.totient_mul (Nat.Coprime.pow _ _ (by norm_num))] at h'
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have e1 : (5 ^ (m + 2)).totient = 5 ^ (m + 1) * 4 := by
    rw [Nat.totient_prime_pow (by norm_num) (by omega)]; simp
  have e2 : (5 ^ (m + 2 - 1)).totient = 5 ^ m * 4 := by
    rw [show m + 2 - 1 = m + 1 by omega, Nat.totient_prime_pow (by norm_num) (by omega)]; simp
  have hφ3 : 0 < (3 ^ j).totient := Nat.totient_pos.2 (by positivity)
  rw [e1, e2] at h'
  have hpos : 0 < 5 ^ m * 4 * (3 ^ j).totient := by positivity
  have : (Finset.univ.filter (fun n : (ZMod (5 ^ (m + 2) * 3 ^ j))ˣ =>
      ZMod.unitsMap (dvdM (m + 2) j) n = 1)).card * (5 ^ m * 4 * (3 ^ j).totient) =
      5 * (5 ^ m * 4 * (3 ^ j).totient) := by
    rw [h']; ring
  exact (Nat.eq_of_mul_eq_mul_right hpos this).ge

theorem odd_of_top {ι : Type*} (r j : ℕ) (hr : 2 ≤ r) (V : Finset ι) (y : ι → ZMod (5 ^ r * 3 ^ j)) (c : ι → ℂ)
    (hy : ∀ t ∈ V, c t ≠ 0 → IsUnit (y t))
    (hA : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = 1 →
      ∑ t ∈ V, c t * (ψ (c5 r j (y t)) * η (c3 r j (y t))) = 0)
    (P : Finset (ZMod (5 ^ r * 3 ^ j))) (hP : ∀ t ∈ V, c t ≠ 0 → y t ∈ P ∧ -(y t) ∈ P)
    (hcount : ∀ k : ZMod (5 ^ (r - 1) * 3 ^ j), (P.filter (fun g => cM r j g = k)).card ≤ 4) :
    ∀ g : ZMod (5 ^ r * 3 ^ j), Fv r j V y c g + Fv r j V y c (-g) = 0 := by
  intro g
  by_cases hg : IsUnit g
  · obtain ⟨u, rfl⟩ := hg
    by_contra hne
    have hD : Sd r j V y c u ≠ 0 := hne
    set K := Finset.univ.filter (fun n : (ZMod (5 ^ r * 3 ^ j))ˣ =>
      ZMod.unitsMap (dvdM r j) n = 1) with hK
    have hinj : K.card ≤ (P.filter (fun g => cM r j g = cM r j (u : ZMod (5 ^ r * 3 ^ j)))).card := by
      refine Finset.card_le_card_of_injOn (fun n => ((u * n : (ZMod (5 ^ r * 3 ^ j))ˣ) : ZMod (5 ^ r * 3 ^ j))) ?_ ?_
      · intro n hn
        have hn' := (Finset.mem_filter.1 hn).2
        have hcMn : cM r j (n : ZMod (5 ^ r * 3 ^ j)) = 1 := by
          have := congrArg (fun w : (ZMod (5 ^ (r - 1) * 3 ^ j))ˣ => (w : ZMod (5 ^ (r - 1) * 3 ^ j))) hn'
          simp only [ZMod.unitsMap_val, Units.val_one] at this
          exact this
        have hDn : Sd r j V y c (u * n) ≠ 0 := by rw [S_inv r j (by omega) V y c hy hA n hn' u]; exact hD
        simp only [Finset.mem_coe, Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · by_cases h1 : Fv r j V y c ((u * n : (ZMod (5 ^ r * 3 ^ j))ˣ) : ZMod (5 ^ r * 3 ^ j)) = 0
          · have h2 : Fv r j V y c (-((u * n : (ZMod (5 ^ r * 3 ^ j))ˣ) : ZMod (5 ^ r * 3 ^ j))) ≠ 0 := by
              intro h2
              apply hDn
              unfold Sd
              rw [h1, h2]; ring
            obtain ⟨t, ht, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
            have hcond : -((u * n : (ZMod (5 ^ r * 3 ^ j))ˣ) : ZMod (5 ^ r * 3 ^ j)) = y t ∧ c t ≠ 0 := by
              by_cases hh : -((u * n : (ZMod (5 ^ r * 3 ^ j))ˣ) : ZMod (5 ^ r * 3 ^ j)) = y t
              · rw [if_pos hh] at hne2; exact ⟨hh, hne2⟩
              · rw [if_neg hh] at hne2; exact absurd rfl hne2
            have := (hP t ht hcond.2).2
            rw [← hcond.1, neg_neg] at this
            exact this
          · obtain ⟨t, ht, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
            have hcond : ((u * n : (ZMod (5 ^ r * 3 ^ j))ˣ) : ZMod (5 ^ r * 3 ^ j)) = y t ∧ c t ≠ 0 := by
              by_cases hh : ((u * n : (ZMod (5 ^ r * 3 ^ j))ˣ) : ZMod (5 ^ r * 3 ^ j)) = y t
              · rw [if_pos hh] at hne2; exact ⟨hh, hne2⟩
              · rw [if_neg hh] at hne2; exact absurd rfl hne2
            rw [hcond.1]; exact (hP t ht hcond.2).1
        · rw [Units.val_mul, map_mul, hcMn, mul_one]
      · intro n _ n' _ h
        have := mul_left_cancel (Units.ext h : u * n = u * n')
        exact this
    have := hcount (cM r j (u : ZMod (5 ^ r * 3 ^ j)))
    have h4 := card_ker5 r j hr
    rw [← hK] at h4
    omega
  · have hz : ∀ x : ZMod (5 ^ r * 3 ^ j), ¬ IsUnit x → Fv r j V y c x = 0 := by
      intro x hx
      unfold Fv
      refine Finset.sum_eq_zero (fun t ht => ?_)
      by_cases hct : c t = 0
      · simp [hct]
      rw [if_neg]
      intro hh; exact hx (hh ▸ hy t ht hct)
    rw [hz g hg, hz (-g) (fun h => hg (by simpa using h))]; ring

end Erdos634.GA2SB

#print axioms Erdos634.GA2SB.S_inv
#print axioms Erdos634.GA2SB.card_ker5
#print axioms Erdos634.GA2SB.odd_of_top
