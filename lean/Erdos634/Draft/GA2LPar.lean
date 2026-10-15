/-
GA2L, atom P3/P4 (part 1): **parity-restricted character sums over primitive characters mod q^v**,
and the **2-adic parity-fixed Lemma G'** (GA2Y_NOTES, Theorem A, Step 1).

* `parsum`: 2 Σ_{χ prim, χ(-1)=ε} χ(g) = Σ_prim χ(g) + ε Σ_prim χ(-g)    (any q^v).
* `S_two` : at 2^(k+3) the primitive-character sum is 4P[z≡1 (2^i)] - 2P[z≡1 (2^(i-1))], P = 2^k.
* `card_par_two`: exactly P = 2^(i-3) primitive characters of each parity mod 2^i, i ≥ 3 (F6).
* `two_adic_par`: for i ≥ 3, ε = ±1, z a unit mod 2^i: χ(z) is constant over the primitive χ mod 2^i
  of parity ε iff z ∈ {1, -1, 1+2^(i-1), -(1+2^(i-1))} (mod 2^i); and the constant is then
  1, ε, -1, -ε respectively (= ε^s (-1)^e).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.LemmaSGpp

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2LPar

open Erdos634.LemmaSGpp (sum_prim card_prim all_neg_one)
open Erdos634.LemmaSN (pred_dvd)

section General
variable {q v : ℕ} [hq : Fact q.Prime]

/-- Primitive characters mod q^v of a prescribed parity. -/
noncomputable def PrimPar (q v : ℕ) [Fact q.Prime] (ε : ℂ) : Finset (DirichletCharacter ℂ (q ^ v)) :=
  haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  univ.filter (fun χ => χ.IsPrimitive ∧ χ (-1) = ε)

theorem parsum (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (g : ZMod (q ^ v)) :
    haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
    2 * ∑ χ ∈ PrimPar q v ε, χ g =
      (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive), χ g)
      + ε * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive), χ (-g) := by
  haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  have hsplit : PrimPar q v ε = (univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) =>
      χ.IsPrimitive)).filter (fun χ => χ (-1) = ε) := by
    ext χ; simp [PrimPar, and_assoc]
  rw [hsplit, sum_filter, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun χ _ => ?_)
  have hm : χ (-g) = χ (-1) * χ g := by rw [← map_mul]; ring_nf
  rw [hm]
  rcases (show χ (-1) = 1 ∨ χ (-1) = -1 from χ.even_or_odd) with h | h <;> rcases hε with rfl | rfl <;> simp [h]
  all_goals first | (intro hh; norm_num at hh) | ring

end General

section Two

/-- The primitive-character sum mod 2^(k+3), on an integer representative of a unit. -/
theorem S_two (k : ℕ) (z : ℤ) (hz : IsUnit ((z : ZMod (2 ^ (k + 3))))) :
    haveI : NeZero (2 ^ (k + 3)) := ⟨pow_ne_zero _ two_ne_zero⟩
    (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (2 ^ (k + 3)) => χ.IsPrimitive),
        χ (z : ZMod (2 ^ (k + 3)))) =
      (((if z ≡ 1 [ZMOD 2 ^ (k + 3)] then 4 * 2 ^ k else 0) -
        (if z ≡ 1 [ZMOD 2 ^ (k + 2)] then 2 * 2 ^ k else 0) : ℤ) : ℂ) := by
  haveI : NeZero (2 ^ (k + 3)) := ⟨pow_ne_zero _ two_ne_zero⟩
  set g : (ZMod (2 ^ (k + 3)))ˣ := hz.unit with hg
  have hgz : (g : ZMod (2 ^ (k + 3))) = (z : ZMod _) := rfl
  have hS := sum_prim (q := 2) (v := k + 3) (by omega) g
  rw [hgz] at hS
  rw [hS]
  have e1 : ((z : ℤ) : ZMod (2 ^ (k + 3))) = 1 ↔ z ≡ 1 [ZMOD 2 ^ (k + 3)] := by
    rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff]; push_cast; rfl
  have e0 : (((z : ℤ) : ZMod (2 ^ (k + 3))).cast : ZMod (2 ^ (k + 3 - 1))) = 1 ↔
      z ≡ 1 [ZMOD 2 ^ (k + 2)] := by
    rw [ZMod.cast_intCast (pred_dvd 2 (k + 3)), ← Int.cast_one, ZMod.intCast_eq_intCast_iff]
    push_cast; rfl
  have t1 : (2 ^ (k + 3)).totient = 4 * 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp [pow_succ]; ring
  have t0 : (2 ^ (k + 3 - 1)).totient = 2 * 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp [pow_succ]; ring
  rw [t1, t0]
  by_cases h1 : z ≡ 1 [ZMOD 2 ^ (k + 3)] <;> by_cases h0 : z ≡ 1 [ZMOD 2 ^ (k + 2)] <;>
    simp only [e1, e0, h1, h0, if_true, if_false] <;> push_cast <;> ring

end Two

/-! ## Integer congruence lemmas (m = 2^(i-1)) -/
section Ints
variable {m z : ℤ}

theorem modEq_dvd_iff {n a b : ℤ} : a ≡ b [ZMOD n] ↔ n ∣ b - a := Int.modEq_iff_dvd

theorem L_down (hz : z ≡ 1 [ZMOD 2 * m]) : z ≡ 1 [ZMOD m] := by
  rw [modEq_dvd_iff] at hz ⊢
  exact dvd_trans ⟨2, by ring⟩ hz

theorem L_split (hz : z ≡ 1 [ZMOD m]) : z ≡ 1 [ZMOD 2 * m] ∨ z ≡ 1 + m [ZMOD 2 * m] := by
  rw [modEq_dvd_iff] at hz
  obtain ⟨a, ha⟩ := hz
  obtain ⟨b, hb | hb⟩ := Int.even_or_odd' a
  · left; rw [modEq_dvd_iff]; exact ⟨b, by rw [ha, hb]; ring⟩
  · right; rw [modEq_dvd_iff]; exact ⟨b + 1, by rw [show 1 + m - z = m + (1 - z) by ring, ha, hb]; ring⟩

theorem L_both (hm : 3 ≤ m) (h1 : z ≡ 1 [ZMOD m]) (h2 : -z ≡ 1 [ZMOD m]) : False := by
  rw [modEq_dvd_iff] at h1 h2
  have : m ∣ 2 := by
    have := dvd_add h1 h2
    have e : (1 - z) + (1 - -z) = 2 := by ring
    rwa [e] at this
  have := Int.le_of_dvd (by norm_num) this
  omega

theorem L_negone (hm : 3 ≤ m) : ¬ ((-1 : ℤ) ≡ 1 [ZMOD m]) := by
  intro h
  rw [modEq_dvd_iff] at h
  have : m ∣ 2 := by simpa using h
  have := Int.le_of_dvd (by norm_num) this
  omega

theorem L_excl (hm : 0 < m) (h1 : z ≡ 1 [ZMOD 2 * m]) (h2 : z ≡ 1 + m [ZMOD 2 * m]) : False := by
  rw [modEq_dvd_iff] at h1 h2
  have h3 : 2 * m ∣ (1 - z) - (1 + m - z) := dvd_sub h1 h2
  have e : (1 - z) - (1 + m - z) = -m := by ring
  rw [e, dvd_neg] at h3
  have := Int.le_of_dvd hm h3
  omega

theorem L_neg_one_iff : -z ≡ 1 [ZMOD m] ↔ z ≡ -1 [ZMOD m] := by
  rw [modEq_dvd_iff, modEq_dvd_iff, ← dvd_neg]
  constructor <;> intro h <;> convert h using 1 <;> ring

theorem L_neg_one_m_iff : -z ≡ 1 + m [ZMOD 2 * m] ↔ z ≡ -(1 + m) [ZMOD 2 * m] := by
  rw [modEq_dvd_iff, modEq_dvd_iff, ← dvd_neg]
  constructor <;> intro h <;> convert h using 1 <;> ring

end Ints

/-! ## Unit-modulus sums -/

theorem all_eq_sign {ι : Type*} (s : Finset ι) (w : ι → ℂ) (v0 : ℂ) (hv : v0 = 1 ∨ v0 = -1)
    (hn : ∀ i ∈ s, ‖w i‖ = 1) (hs : ∑ i ∈ s, w i = (s.card : ℂ) * v0) : ∀ i ∈ s, w i = v0 := by
  rcases hv with rfl | rfl
  · have h := all_neg_one s (fun i => - w i) (by intro i hi; simpa using hn i hi)
      (by rw [sum_neg_distrib, hs]; simp)
    intro i hi; have := h i hi; linear_combination -this
  · exact all_neg_one s w hn (by rw [hs]; ring)

section Two2

/-- Integer form of the primitive sum. -/
def Sint (k : ℕ) (z : ℤ) : ℤ :=
  (if z ≡ 1 [ZMOD 2 ^ (k + 3)] then 4 * 2 ^ k else 0) -
    (if z ≡ 1 [ZMOD 2 ^ (k + 2)] then 2 * 2 ^ k else 0)

theorem pow_m (k : ℕ) : (2 : ℤ) ^ (k + 3) = 2 * 2 ^ (k + 2) := by ring

theorem m_ge (k : ℕ) : (4 : ℤ) ≤ 2 ^ (k + 2) := by
  have : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have e : (2 : ℤ) ^ (k + 2) = 4 * 2 ^ k := by ring
  omega

/-- The key identity. -/
theorem key (k : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (z : ℤ)
    (hz : IsUnit ((z : ZMod (2 ^ (k + 3))))) :
    2 * ∑ χ ∈ PrimPar 2 (k + 3) ε, χ (z : ZMod (2 ^ (k + 3))) =
      ((Sint k z : ℤ) : ℂ) + ε * ((Sint k (-z) : ℤ) : ℂ) := by
  have h := parsum (q := 2) (v := k + 3) ε hε (z : ZMod (2 ^ (k + 3)))
  have e : -((z : ℤ) : ZMod (2 ^ (k + 3))) = ((-z : ℤ) : ZMod (2 ^ (k + 3))) := by push_cast; rfl
  rw [e] at h
  rw [h, S_two k z hz, S_two k (-z) (by rw [← e]; exact hz.neg)]
  rfl

theorem Sint_A (k : ℕ) {z : ℤ} (h : z ≡ 1 [ZMOD 2 ^ (k + 3)]) : Sint k z = 2 * 2 ^ k := by
  have hB : z ≡ 1 [ZMOD 2 ^ (k + 2)] := by
    rw [pow_m] at h; exact L_down h
  simp only [Sint, if_pos h, if_pos hB]; ring

theorem Sint_B (k : ℕ) {z : ℤ} (h : z ≡ 1 + 2 ^ (k + 2) [ZMOD 2 ^ (k + 3)]) :
    Sint k z = -(2 * 2 ^ k) := by
  have hm := m_ge k
  have hB : z ≡ 1 [ZMOD 2 ^ (k + 2)] := by
    rw [pow_m] at h
    have this : 2 ^ (k + 2) ∣ 1 + 2 ^ (k + 2) - z :=
      dvd_trans ⟨2, by ring⟩ (modEq_dvd_iff.1 h)
    rw [modEq_dvd_iff]
    have e : (1 : ℤ) - z = (1 + 2 ^ (k + 2) - z) - 2 ^ (k + 2) := by ring
    rw [e]; exact dvd_sub this dvd_rfl
  have hA : ¬ z ≡ 1 [ZMOD 2 ^ (k + 3)] := by
    intro hA; rw [pow_m] at h hA; exact L_excl (by omega) hA h
  simp only [Sint, if_neg hA, if_pos hB]; ring

theorem Sint_zero (k : ℕ) {z : ℤ} (h : ¬ z ≡ 1 [ZMOD 2 ^ (k + 2)]) : Sint k z = 0 := by
  have hA : ¬ z ≡ 1 [ZMOD 2 ^ (k + 3)] := fun hA => h (by rw [pow_m] at hA; exact L_down hA)
  simp only [Sint, if_neg hA, if_neg h]; ring

/-- Number of primitive characters of each parity mod 2^(k+3): exactly 2^k. -/
theorem card_par_two (k : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    (PrimPar 2 (k + 3) ε).card = 2 ^ k := by
  haveI : NeZero (2 ^ (k + 3)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hm := m_ge k
  have h := key k ε hε 1 (by simp)
  have e1 : ∀ χ ∈ PrimPar 2 (k + 3) ε, χ (((1 : ℤ)) : ZMod (2 ^ (k + 3))) = 1 := by
    intro χ _; simp
  rw [sum_congr rfl e1, sum_const, nsmul_eq_mul, mul_one] at h
  have hA : (1 : ℤ) ≡ 1 [ZMOD 2 ^ (k + 3)] := rfl
  have hn : ¬ (-1 : ℤ) ≡ 1 [ZMOD 2 ^ (k + 2)] := L_negone (by omega)
  rw [Sint_A k hA, Sint_zero k hn] at h
  have : ((PrimPar 2 (k + 3) ε).card : ℂ) = 2 ^ k := by
    push_cast at h
    linear_combination h / 2
  exact_mod_cast this

end Two2


section Main2

theorem Bexcl (k : ℕ) {z : ℤ} (h : z ≡ 1 [ZMOD 2 ^ (k + 2)]) : ¬ (-z ≡ 1 [ZMOD 2 ^ (k + 2)]) :=
  fun h' => L_both (by have := m_ge k; omega) h h'

theorem B1l (k : ℕ) {z : ℤ} (h : z ≡ 1 [ZMOD 2 ^ (k + 3)]) : z ≡ 1 [ZMOD 2 ^ (k + 2)] := by
  rw [pow_m] at h; exact L_down h

theorem B2l (k : ℕ) {z : ℤ} (h : z ≡ 1 + 2 ^ (k + 2) [ZMOD 2 ^ (k + 3)]) :
    z ≡ 1 [ZMOD 2 ^ (k + 2)] := by
  rw [pow_m] at h
  have : 2 ^ (k + 2) ∣ 1 + 2 ^ (k + 2) - z := dvd_trans ⟨2, by ring⟩ (modEq_dvd_iff.1 h)
  rw [modEq_dvd_iff]
  have e : (1 : ℤ) - z = (1 + 2 ^ (k + 2) - z) - 2 ^ (k + 2) := by ring
  rw [e]; exact dvd_sub this dvd_rfl

/-- Σ over the primitive characters of parity ε of χ(z), when z is in the 2-adic exceptional set. -/
theorem par_sum_vals (k : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (z : ℤ)
    (hz : IsUnit ((z : ZMod (2 ^ (k + 3))))) :
    (z ≡ 1 [ZMOD 2 ^ (k + 3)] → 2 * ∑ χ ∈ PrimPar 2 (k + 3) ε, χ (z : ZMod (2 ^ (k + 3))) = 2 * 2 ^ k) ∧
    (z ≡ 1 + 2 ^ (k + 2) [ZMOD 2 ^ (k + 3)] →
      2 * ∑ χ ∈ PrimPar 2 (k + 3) ε, χ (z : ZMod (2 ^ (k + 3))) = -(2 * 2 ^ k)) ∧
    (z ≡ -1 [ZMOD 2 ^ (k + 3)] →
      2 * ∑ χ ∈ PrimPar 2 (k + 3) ε, χ (z : ZMod (2 ^ (k + 3))) = ε * (2 * 2 ^ k)) ∧
    (z ≡ -(1 + 2 ^ (k + 2)) [ZMOD 2 ^ (k + 3)] →
      2 * ∑ χ ∈ PrimPar 2 (k + 3) ε, χ (z : ZMod (2 ^ (k + 3))) = -(ε * (2 * 2 ^ k))) := by
  have hk := key k ε hε z hz
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [hk, Sint_A k h, Sint_zero k (Bexcl k (B1l k h))]; push_cast; ring
  · rw [hk, Sint_B k h, Sint_zero k (Bexcl k (B2l k h))]; push_cast; ring
  · have h' : -z ≡ 1 [ZMOD 2 ^ (k + 3)] := L_neg_one_iff.2 h
    have hnb : ¬ z ≡ 1 [ZMOD 2 ^ (k + 2)] := fun hb => Bexcl k hb (B1l k h')
    rw [hk, Sint_A k h', Sint_zero k hnb]; push_cast; ring
  · have h' : -z ≡ 1 + 2 ^ (k + 2) [ZMOD 2 ^ (k + 3)] := by
      rw [pow_m] at h ⊢; exact L_neg_one_m_iff.2 h
    have hnb : ¬ z ≡ 1 [ZMOD 2 ^ (k + 2)] := fun hb => Bexcl k hb (B2l k h')
    rw [hk, Sint_B k h', Sint_zero k hnb]; push_cast; ring

/-- Values of a character at z (unit) all have modulus 1. -/
theorem norm_one (k : ℕ) (z : ℤ) (hz : IsUnit ((z : ZMod (2 ^ (k + 3)))))
    (χ : DirichletCharacter ℂ (2 ^ (k + 3))) : ‖χ (z : ZMod (2 ^ (k + 3)))‖ = 1 := by
  have := χ.unit_norm_eq_one hz.unit
  simpa using this

/-- **The 2-adic parity-fixed Lemma G′ (value form).** For i = k+3 ≥ 3 and ε = ±1, z a unit mod 2^i
in the exceptional set, χ(z) takes the value 1, −1, ε, −ε on every primitive χ mod 2^i with
χ(−1) = ε, according as z ≡ 1, 1+2^(i−1), −1, −(1+2^(i−1)). -/
theorem two_adic_par_value (k : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (z : ℤ)
    (hz : IsUnit ((z : ZMod (2 ^ (k + 3))))) :
    (z ≡ 1 [ZMOD 2 ^ (k + 3)] → ∀ χ ∈ PrimPar 2 (k + 3) ε, χ (z : ZMod (2 ^ (k + 3))) = 1) ∧
    (z ≡ 1 + 2 ^ (k + 2) [ZMOD 2 ^ (k + 3)] →
      ∀ χ ∈ PrimPar 2 (k + 3) ε, χ (z : ZMod (2 ^ (k + 3))) = -1) ∧
    (z ≡ -1 [ZMOD 2 ^ (k + 3)] → ∀ χ ∈ PrimPar 2 (k + 3) ε, χ (z : ZMod (2 ^ (k + 3))) = ε) ∧
    (z ≡ -(1 + 2 ^ (k + 2)) [ZMOD 2 ^ (k + 3)] →
      ∀ χ ∈ PrimPar 2 (k + 3) ε, χ (z : ZMod (2 ^ (k + 3))) = -ε) := by
  obtain ⟨p1, p2, p3, p4⟩ := par_sum_vals k ε hε z hz
  have hc := card_par_two k ε hε
  have hn : ∀ χ ∈ PrimPar 2 (k + 3) ε, ‖χ (z : ZMod (2 ^ (k + 3)))‖ = 1 :=
    fun χ _ => norm_one k z hz χ
  have P0 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have hεn : ε = 1 ∨ ε = -1 := hε
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · refine all_eq_sign _ _ 1 (Or.inl rfl) hn ?_
    have := p1 h; rw [hc]; push_cast
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0); linear_combination this
  · refine all_eq_sign _ _ (-1) (Or.inr rfl) hn ?_
    have := p2 h; rw [hc]; push_cast
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0); linear_combination this
  · refine all_eq_sign _ _ ε hεn hn ?_
    have := p3 h; rw [hc]; push_cast
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0); linear_combination this
  · refine all_eq_sign _ _ (-ε) (by rcases hεn with rfl | rfl <;> simp) hn ?_
    have := p4 h; rw [hc]; push_cast
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0); linear_combination this

/-- **The 2-adic parity-fixed Lemma G′ (iff form).** -/
theorem two_adic_par (k : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (z : ℤ)
    (hz : IsUnit ((z : ZMod (2 ^ (k + 3))))) :
    (∃ c : ℂ, ∀ χ ∈ PrimPar 2 (k + 3) ε, χ (z : ZMod (2 ^ (k + 3))) = c) ↔
      (z ≡ 1 [ZMOD 2 ^ (k + 3)] ∨ z ≡ 1 + 2 ^ (k + 2) [ZMOD 2 ^ (k + 3)] ∨
        z ≡ -1 [ZMOD 2 ^ (k + 3)] ∨ z ≡ -(1 + 2 ^ (k + 2)) [ZMOD 2 ^ (k + 3)]) := by
  obtain ⟨v1, v2, v3, v4⟩ := two_adic_par_value k ε hε z hz
  have hc := card_par_two k ε hε
  have hpos : (PrimPar 2 (k + 3) ε).Nonempty := by
    rw [← card_pos, hc]; positivity
  constructor
  · rintro ⟨c, hc'⟩
    obtain ⟨χ0, h0⟩ := hpos
    have hcn : ‖c‖ = 1 := by rw [← hc' χ0 h0]; exact norm_one k z hz χ0
    obtain ⟨p1, p2, p3, p4⟩ := par_sum_vals k ε hε z hz
    have hk := key k ε hε z hz
    rw [sum_congr rfl hc', sum_const, nsmul_eq_mul, hc] at hk
    by_cases hb : z ≡ 1 [ZMOD 2 ^ (k + 2)] ∨ -z ≡ 1 [ZMOD 2 ^ (k + 2)]
    · rcases hb with hb | hb
      · rw [pow_m] at *
        rcases L_split hb with h | h
        · left; exact h
        · right; left; exact h
      · rcases L_split hb with h | h
        · right; right; left; exact L_neg_one_iff.1 (by rw [pow_m]; exact h)
        · right; right; right
          rw [pow_m]; exact L_neg_one_m_iff.1 h
    · exfalso
      push Not at hb
      rw [Sint_zero k hb.1, Sint_zero k hb.2] at hk
      have : (2 : ℂ) * (2 ^ k * c) = 0 := by push_cast at hk ⊢; linear_combination hk
      have hne : (2 : ℂ) * 2 ^ k ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ two_ne_zero)
      have : c = 0 := by
        have h2 : (2 : ℂ) * 2 ^ k * c = 0 := by linear_combination this
        exact (mul_eq_zero.1 h2).resolve_left hne
      rw [this, norm_zero] at hcn; exact zero_ne_one hcn
  · rintro (h | h | h | h)
    · exact ⟨1, v1 h⟩
    · exact ⟨-1, v2 h⟩
    · exact ⟨ε, v3 h⟩
    · exact ⟨-ε, v4 h⟩

end Main2

#print axioms two_adic_par
#print axioms two_adic_par_value
#print axioms card_par_two

end Erdos634.GA2LPar
