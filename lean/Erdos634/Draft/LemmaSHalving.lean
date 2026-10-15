/-
# Lemma S, class EVEN entry: Lemma H (halving), n = 2n′ with n′ odd

  **Lemma H** (T1–T3; n = 2n′ with n′ odd). A = {j : a_j odd} has two elements. With
  y_j := x_j − ½[j ∈ A]:  e ∈ R(a) ⟺ Σ_{j∉A} e_j[y_j] + Σ_{j∈A} e_j([2y_j] − [y_j]) = 0 on (ℤ/n′)^×.
  Also: reduction (ℤ/n)^× → (ℤ/n′)^× is a bijection; ((t)) + ((t + ½)) = ((2t)) for all t;
  and (via Lemma C) [2y]_χ = χ*(2)[y]_χ.

Encoding: y_j ∈ (1/n′)ℤ/ℤ is written y_j = b_j/n′ with b_j := a_j/2 (a_j even) and
b_j := (a_j + n′)/2 (a_j odd); indeed (a_j + n′)/(2n′) = x_j + ½ ≡ x_j − ½ (mod 1).
"[y] on (ℤ/n′)^×" is k ↦ ((k y)) for k prime to n′.
-/
import Mathlib
import Erdos634.Draft.LemmaSCCrit

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSHalf

open Erdos634.LemmaS (saw relSpace mem_relSpace)

theorem saw_add_int (t : ℚ) (m : ℤ) : saw (t + m) = saw t := by
  unfold saw; rw [Int.fract_add_intCast]

theorem saw_of_mem {x : ℚ} (h0 : 0 ≤ x) (h1 : x < 1) : saw x = if x = 0 then 0 else x - 1 / 2 := by
  unfold saw; rw [Int.fract_eq_self.2 ⟨h0, h1⟩]

/-- **The ℓ = 2 distribution relation** `((t)) + ((t + ½)) = ((2t))`, for every rational t. -/
theorem saw_add_saw_add_half (t : ℚ) : saw t + saw (t + 1 / 2) = saw (2 * t) := by
  set f := Int.fract t with hf
  have ht : t = f + (⌊t⌋ : ℤ) := by rw [hf, Int.fract_add_floor]
  have hf0 : 0 ≤ f := Int.fract_nonneg t
  have hf1 : f < 1 := Int.fract_lt_one t
  have e1 : saw t = saw f := by rw [ht, saw_add_int]
  have e2 : saw (t + 1 / 2) = saw (f + 1 / 2) := by
    rw [ht, show f + (⌊t⌋ : ℤ) + 1 / 2 = (f + 1 / 2) + (⌊t⌋ : ℤ) by ring, saw_add_int]
  have e3 : saw (2 * t) = saw (2 * f) := by
    rw [ht, show 2 * (f + (⌊t⌋ : ℤ)) = 2 * f + ((2 * ⌊t⌋ : ℤ) : ℚ) by push_cast; ring, saw_add_int]
  rw [e1, e2, e3]
  rcases lt_or_ge f (1 / 2) with hlt | hge
  · rw [saw_of_mem hf0 hf1, saw_of_mem (by linarith) (by linarith),
      saw_of_mem (by linarith) (by linarith)]
    by_cases h0 : f = 0
    · simp only [h0]; norm_num
    · rw [if_neg h0, if_neg (by linarith), if_neg (by intro h; apply h0; linarith)]; ring
  · have e4 : saw (f + 1 / 2) = saw (f - 1 / 2) := by
      have := saw_add_int (f - 1 / 2) 1
      rw [show (f - 1 / 2) + ((1 : ℤ) : ℚ) = f + 1 / 2 by push_cast; ring] at this
      exact this
    have e5 : saw (2 * f) = saw (2 * f - 1) := by
      have := saw_add_int (2 * f - 1) 1
      rw [show (2 * f - 1) + ((1 : ℤ) : ℚ) = 2 * f by push_cast; ring] at this
      exact this
    rw [e4, e5, saw_of_mem hf0 hf1, saw_of_mem (by linarith) (by linarith),
      saw_of_mem (by linarith) (by linarith)]
    by_cases h0 : f = 1 / 2
    · simp only [h0]; norm_num
    · rw [if_neg (by intro h; linarith), if_neg (by intro h; apply h0; linarith),
        if_neg (by intro h; apply h0; linarith)]; ring

/-- |A| = 2. -/
theorem card_A {n n' : ℕ} (a : Fin 3 → ℕ) (hsum : ∑ i, a i = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (hn : n = 2 * n') :
    (univ.filter (fun j => Odd (a j))).card = 2 := by
  have hs3 : a 0 + a 1 + a 2 = n := by simpa [Fin.sum_univ_three] using hsum
  have hne : ¬ (a 0 % 2 = 0 ∧ a 1 % 2 = 0 ∧ a 2 % 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    have : 2 ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) :=
      Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0)
        (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2))
    rw [hgcd] at this; omega
  rw [card_filter, Fin.sum_univ_three]
  simp only [Nat.odd_iff]
  split_ifs <;> omega

/-- The reduction `(ℤ/2n′)^× → (ℤ/n′)^×` is a bijection for n′ odd. -/
theorem unitsMap_bijective {n' : ℕ} (hodd : Odd n') :
    Function.Bijective (ZMod.unitsMap (Dvd.intro_left 2 rfl : n' ∣ 2 * n')) := by
  have hn' : n' ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hodd)
  haveI : NeZero n' := ⟨hn'⟩
  haveI : NeZero (2 * n') := ⟨by omega⟩
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨ZMod.unitsMap_surjective _, ?_⟩
  rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient,
    Nat.totient_mul ((Nat.coprime_two_left).2 hodd), Nat.totient_two, one_mul]

/-- `b_j`, the numerator of `y_j` over `n′`. -/
def bnum (n' a : ℕ) : ℕ := if Odd a then (a + n') / 2 else a / 2

/-- The halved term `T_j(k)`: `((k y_j))` if `a_j` even, `((2k y_j)) − ((k y_j))` if `a_j` odd. -/
noncomputable def halfTerm (n' a k : ℕ) : ℚ :=
  if Odd a then saw (((2 * k * bnum n' a : ℕ) : ℚ) / n') - saw (((k * bnum n' a : ℕ) : ℚ) / n')
  else saw (((k * bnum n' a : ℕ) : ℚ) / n')

theorem saw_period {n' b k : ℕ} (hn' : n' ≠ 0) (c : ℕ) :
    saw ((((k + c * n') * b : ℕ) : ℚ) / n') = saw (((k * b : ℕ) : ℚ) / n') := by
  have hq : ((((k + c * n') * b : ℕ) : ℚ) / n') = ((k * b : ℕ) : ℚ) / n' + ((c * b : ℕ) : ℚ) := by
    have : (n' : ℚ) ≠ 0 := by exact_mod_cast hn'
    push_cast; field_simp
  rw [hq, Erdos634.LemmaSC.saw_add_nat]

theorem halfTerm_period {n' a k : ℕ} (hn' : n' ≠ 0) (c : ℕ) :
    halfTerm n' a (k + c * n') = halfTerm n' a k := by
  unfold halfTerm
  have h2 : 2 * (k + c * n') * bnum n' a = (2 * k + (2 * c) * n') * bnum n' a := by ring
  have h2' : 2 * k * bnum n' a = (2 * k) * bnum n' a := rfl
  rw [h2, saw_period hn', saw_period hn' c]

/-- Pointwise halving: for k odd, `((k x_j)) = T_j(k)`. -/
theorem saw_eq_halfTerm {n n' a k : ℕ} (hn : n = 2 * n') (hodd : Odd n') (hk : Odd k) :
    saw (((k * a : ℕ) : ℚ) / n) = halfTerm n' a k := by
  have hn' : (n' : ℚ) ≠ 0 := by
    have : n' ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hodd
    exact_mod_cast this
  unfold halfTerm bnum
  by_cases ha : Odd a
  · rw [if_pos ha, if_pos ha]
    obtain ⟨m, rfl⟩ := hk
    have hb : ((a + n') / 2 : ℕ) * 2 = a + n' := by
      have : Even (a + n') := Odd.add_odd ha hodd
      exact Nat.div_mul_cancel (even_iff_two_dvd.1 this)
    set b := (a + n') / 2 with hbdef
    have hbq : (a : ℚ) = 2 * b - n' := by
      have : ((b * 2 : ℕ) : ℚ) = ((a + n' : ℕ) : ℚ) := by rw [hb]
      push_cast at this; linarith
    set t : ℚ := ((2 * m + 1) * b : ℕ) / (n' : ℚ) with ht
    have hx : (((2 * m + 1) * a : ℕ) : ℚ) / n = (t + 1 / 2) + ((-(m : ℤ) - 1 : ℤ) : ℚ) := by
      rw [ht, hn]; push_cast; rw [hbq]; field_simp; ring
    have h2t : (((2 * (2 * m + 1) * b : ℕ) : ℚ) / n') = 2 * t := by rw [ht]; push_cast; ring
    rw [hx, saw_add_int, h2t, ← saw_add_saw_add_half t]; ring
  · rw [if_neg ha, if_neg ha]
    have he : Even a := Nat.not_odd_iff_even.1 ha
    obtain ⟨c, rfl⟩ := he
    have : (c + c) / 2 = c := by omega
    rw [this, hn]; congr 1; push_cast; field_simp; ring

/-- **Lemma H** (halving equivalence). -/
theorem lemmaH {n n' : ℕ} (a : Fin 3 → ℕ) (hn : n = 2 * n') (hodd : Odd n') (e : Fin 3 → ℚ) :
    e ∈ relSpace n a ↔ ∀ k : ℕ, k.Coprime n' → ∑ i, e i * halfTerm n' (a i) k = 0 := by
  have hn'0 : n' ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hodd
  constructor
  · intro he k hk
    -- an odd representative of k mod n′
    set k' := if Odd k then k else k + 1 * n' with hk'
    have hk'odd : Odd k' := by
      rw [hk']; split_ifs with h
      · exact h
      · rw [one_mul]; exact Even.add_odd (Nat.not_odd_iff_even.1 h) hodd
    have hk'cop : k'.Coprime n := by
      rw [hn]
      refine Nat.Coprime.mul_right ((Nat.coprime_two_right).2 hk'odd) ?_
      rw [hk']; split_ifs
      · exact hk
      · rw [one_mul, Nat.coprime_add_self_left]; exact hk
    have hrel := (mem_relSpace.1 he) k' hk'cop
    have hper : ∀ i, halfTerm n' (a i) k' = halfTerm n' (a i) k := by
      intro i; rw [hk']; split_ifs
      · rfl
      · exact halfTerm_period hn'0 1
    rw [← hrel]
    refine sum_congr rfl (fun i _ => ?_)
    rw [← hper i, ← saw_eq_halfTerm hn hodd hk'odd, mul_comm]
  · intro h
    rw [mem_relSpace]
    intro k hk
    have hkodd : Odd k := by
      rw [hn] at hk
      exact (Nat.coprime_two_right).1 (Nat.Coprime.coprime_mul_right_right hk)
    have hkn' : k.Coprime n' := by rw [hn] at hk; exact Nat.Coprime.coprime_mul_left_right hk
    rw [← h k hkn']
    refine sum_congr rfl (fun i _ => ?_)
    rw [saw_eq_halfTerm hn hodd hkodd, mul_comm]

/-- `[2y]_χ = χ*(2)[y]_χ` at odd level n′ (from Lemma C's bracket). -/
theorem bracket_two {n' : ℕ} [NeZero n'] (hodd : Odd n') (χ : DirichletCharacter ℂ n') (b : ℕ) :
    Erdos634.LemmaSC.bracket χ (2 * b)
      = χ.primitiveCharacter (2 : ZMod χ.conductor) * Erdos634.LemmaSC.bracket χ b := by
  have hg : n'.gcd (2 * b) = n'.gcd b := by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul_left_cancel b ((Nat.coprime_two_left).2 hodd),
      Nat.gcd_comm]
  have hdiv : 2 * b / n'.gcd b = 2 * (b / n'.gcd b) :=
    Nat.mul_div_assoc 2 (Nat.gcd_dvd_right n' b)
  unfold Erdos634.LemmaSC.bracket
  rw [hg, hdiv]
  split_ifs
  · push_cast; rw [map_mul]; ring
  · ring

/-! ## Witness: the paper's control tile (2,5,7)/14 = the half-tile family n = 2p·(odd), p = 7,
n′ = 7: all hypotheses hold, |A| = 2 (a₂ = 5, a₃ = 7 odd), and the halving equivalence fires. -/

theorem lemmaH_witness :
    (univ.filter (fun j => Odd ((![2, 5, 7] : Fin 3 → ℕ) j))).card = 2 ∧
    ((Pi.single 2 1 : Fin 3 → ℚ) ∈ relSpace 14 ![2, 5, 7] ↔
      ∀ k : ℕ, k.Coprime 7 → ∑ i, (Pi.single 2 1 : Fin 3 → ℚ) i *
        halfTerm 7 ((![2, 5, 7] : Fin 3 → ℕ) i) k = 0) := by
  have hsum : ∑ i, (![2, 5, 7] : Fin 3 → ℕ) i = 14 := by simp [Fin.sum_univ_three]
  have hgcd : Nat.gcd ((![2, 5, 7] : Fin 3 → ℕ) 0)
      (Nat.gcd ((![2, 5, 7] : Fin 3 → ℕ) 1) ((![2, 5, 7] : Fin 3 → ℕ) 2)) = 1 := by decide
  have ho : Odd 7 := ⟨3, by norm_num⟩
  exact ⟨card_A (n := 14) (n' := 7) _ hsum hgcd (by norm_num),
    lemmaH (n := 14) (n' := 7) _ (by norm_num) ho _⟩

end Erdos634.LemmaSHalf

#print axioms Erdos634.LemmaSHalf.saw_add_saw_add_half
#print axioms Erdos634.LemmaSHalf.card_A
#print axioms Erdos634.LemmaSHalf.unitsMap_bijective
#print axioms Erdos634.LemmaSHalf.lemmaH
#print axioms Erdos634.LemmaSHalf.bracket_two
#print axioms Erdos634.LemmaSHalf.lemmaH_witness
