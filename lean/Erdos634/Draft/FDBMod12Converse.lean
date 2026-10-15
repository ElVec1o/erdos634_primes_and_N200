-- Draft/FDBMod12Converse.lean -- the converse half of the mod-12 theorem.
--
-- Statement: "Let p>3 be prime with p=3f^2-e^2 for some coprime e,f. Then
-- p = 11 (mod 12). Conversely every prime p = 11 (mod 12) is of that form. Hence the base-beta
-- candidates among the primes are exactly the primes = 11 (mod 12)."
-- Forward half: `BaseBetaMod12.basebeta_prime_mod_twelve` (standard axioms).
-- This file: the converse, by (a) quadratic reciprocity (3 is a QR mod p), (b) Thue's pigeonhole,
-- (c) the value x^2-3y^2 in {-2p,-p,0}, (d) coprimality (g^2 | p), and (e) a Pell-unit descent to
-- reach the base-beta range 1 <= e < f, which the phrase "base-beta candidate" needs
-- (the converse sentence only says "of that form" for coprime e,f; the hence-clause needs
-- 1 <= e < f, so that is what is proved).  Pure number theory, no geometry.
-- Imported by `All`.  No sorry, no native_decide.
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Rat.Lemmas
import Erdos634.BaseBetaMod12

namespace Erdos634.Draft.FDBMod12Converse

/-- (a) `3` is a square mod `p` for a prime `p ≡ 3 (mod 4)`, `p ≡ 2 (mod 3)`. -/
theorem three_isSquare_zmod (p : ℕ) [Fact p.Prime] (h4 : p % 4 = 3) (h3 : p % 3 = 2) :
    IsSquare ((3 : ℕ) : ZMod p) := by
  have key : ∀ r : ZMod 3, ¬ (2 : ZMod 3) = r * r := by decide
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : p ≠ 3 := by omega
  rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := p) (q := 3) h4 (by norm_num) hne]
  rintro ⟨r, hr⟩
  have hp3 : ((p : ℕ) : ZMod 3) = 2 := by
    have : (p : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
    rw [this, h3]; rfl
  rw [hp3] at hr
  exact key r hr

/-- A prime is not a perfect square, in the form `Nat.sqrt p * Nat.sqrt p < p`. -/
theorem sqrt_mul_self_lt (p : ℕ) (hp : p.Prime) : Nat.sqrt p * Nat.sqrt p < p := by
  have h1 := Nat.sqrt_le p
  rcases Nat.lt_or_eq_of_le h1 with h | h
  · exact h
  · exfalso
    have hd : Nat.sqrt p ∣ p := ⟨Nat.sqrt p, h.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hd with h' | h'
    · rw [h'] at h; have := hp.two_le; omega
    · rw [h'] at h
      have := hp.two_le
      nlinarith

/-- (b) Thue's lemma: for any `r` mod a prime `p` there are integers `x, y`, not both `0`, with
`x^2 < p`, `y^2 < p` and `x ≡ r y (mod p)`. -/
theorem thue (p : ℕ) (hp : p.Prime) (r : ZMod p) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ x ^ 2 < p ∧ y ^ 2 < p ∧ ((x : ZMod p) = r * (y : ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set k := Nat.sqrt p with hk
  have hkk : k * k < p := sqrt_mul_self_lt p hp
  have hlt : p < (k + 1) * (k + 1) := Nat.lt_succ_sqrt p
  let s : Finset (ℕ × ℕ) := Finset.range (k + 1) ×ˢ Finset.range (k + 1)
  let t : Finset (ZMod p) := Finset.univ
  have hcard : t.card < s.card := by
    simp only [s, t, Finset.card_product, Finset.card_range, Finset.card_univ, ZMod.card]
    exact hlt
  let f : ℕ × ℕ → ZMod p := fun uv => (uv.1 : ZMod p) - r * (uv.2 : ZMod p)
  obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := f)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  simp only [s, Finset.mem_product, Finset.mem_range] at ha hb
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [f] at hfab
  refine ⟨(a1 : ℤ) - b1, (a2 : ℤ) - b2, ?_, ?_, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hab
    have h1 : (a1 : ℤ) = b1 := by linarith [hcon.1]
    have h2 : (a2 : ℤ) = b2 := by linarith [hcon.2]
    have h1' : a1 = b1 := by exact_mod_cast h1
    have h2' : a2 = b2 := by exact_mod_cast h2
    rw [h1', h2']
  · have hk' : ((k : ℤ)) * k < p := by exact_mod_cast hkk
    have : (a1 : ℤ) ≤ k := by have := ha.1; omega
    have : (b1 : ℤ) ≤ k := by have := hb.1; omega
    nlinarith [(by positivity : (0 : ℤ) ≤ a1), (by positivity : (0 : ℤ) ≤ b1)]
  · have hk' : ((k : ℤ)) * k < p := by exact_mod_cast hkk
    have : (a2 : ℤ) ≤ k := by have := ha.2; omega
    have : (b2 : ℤ) ≤ k := by have := hb.2; omega
    nlinarith [(by positivity : (0 : ℤ) ≤ a2), (by positivity : (0 : ℤ) ≤ b2)]
  · push_cast
    linear_combination hfab

/-- `x^2 = 3 y^2` over `ℤ` forces `y = 0` (irrationality of `√3`, via `ℚ`). -/
theorem sq_eq_three_sq (x y : ℤ) (h : x ^ 2 = 3 * y ^ 2) : y = 0 := by
  by_contra hy
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have hq : ((3 : ℕ) : ℚ) = ((x : ℚ) / y) * ((x : ℚ) / y) := by
    have h' : (x : ℚ) ^ 2 = 3 * (y : ℚ) ^ 2 := by exact_mod_cast h
    field_simp
    push_cast
    linear_combination -h'
  have hsq : IsSquare ((3 : ℕ) : ℚ) := ⟨_, hq⟩
  rw [Rat.isSquare_natCast_iff] at hsq
  obtain ⟨r, hr⟩ := hsq
  have : r ≤ 3 := by nlinarith
  interval_cases r <;> omega

/-- (a)-(c): a prime `p ≡ 11 (mod 12)` has integers `x, y` with `3 y^2 - x^2 = p`, `y ≠ 0`. -/
theorem exists_rep_int (p : ℕ) (hp : p.Prime) (h12 : p % 12 = 11) :
    ∃ x y : ℤ, 3 * y ^ 2 - x ^ 2 = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h4 : p % 4 = 3 := by omega
  have h3 : p % 3 = 2 := by omega
  obtain ⟨r, hr⟩ := three_isSquare_zmod p h4 h3
  obtain ⟨x, y, hxy, hx, hy, hmod⟩ := thue p hp r
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hzero : (((x ^ 2 - 3 * y ^ 2 : ℤ)) : ZMod p) = 0 := by
    push_cast
    have : ((3 : ℕ) : ZMod p) = 3 := by norm_num
    rw [this] at hr
    rw [hmod, hr]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
  obtain ⟨c, hc⟩ := hzero
  have hxn : 0 ≤ x ^ 2 := sq_nonneg x
  have hyn : 0 ≤ y ^ 2 := sq_nonneg y
  have hc1 : c < 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hc2 : -3 < c := by
    by_contra hcon
    push Not at hcon
    nlinarith
  interval_cases c
  · -- c = -2 : x^2 ≡ 2 (mod 3), impossible
    exfalso
    have h1 : x ^ 2 - 3 * y ^ 2 = -2 * p := by linarith
    have hpz : (p : ℤ) % 3 = 2 := by omega
    have hx3 : x ^ 2 % 3 = 2 := by omega
    have : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
    rcases this with h | h | h <;> simp [pow_two, Int.mul_emod, h] at hx3
  · exact ⟨x, y, by linarith⟩
  · -- c = 0
    exfalso
    have h0 : x ^ 2 = 3 * y ^ 2 := by linarith
    have hy0 := sq_eq_three_sq x y h0
    subst hy0
    have : x = 0 := by nlinarith
    rcases hxy with h | h <;> contradiction

/-- (e) Pell-unit descent: from any integer solution of `3 f^2 - e^2 = p` (`p` prime, `p ≠ 2`)
get one with `0 ≤ e < f`. -/
theorem descend (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ n : ℕ, ∀ e f : ℤ, f.natAbs = n → 0 < f → 0 ≤ e → 3 * f ^ 2 - e ^ 2 = p →
      ∃ e' f' : ℤ, 0 ≤ e' ∧ e' < f' ∧ 3 * f' ^ 2 - e' ^ 2 = p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e f hn hf he heq
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    rcases lt_trichotomy e f with h | h | h
    · exact ⟨e, f, he, h, heq⟩
    · exfalso
      subst h
      have h2 : (p : ℤ) = 2 * e ^ 2 := by linarith
      have : 2 ∣ p := by
        have : (2 : ℤ) ∣ p := ⟨e ^ 2, h2⟩
        exact_mod_cast this
      rcases hp.eq_one_or_self_of_dvd 2 this with h' | h' <;> omega
    · -- e > f : descend
      have he2 : e < 2 * f := by nlinarith
      have hf' : 0 < 2 * f - e := by omega
      have hlt : (2 * f - e).natAbs < n := by omega
      obtain ⟨e', f', h1, h2, h3⟩ := ih _ hlt (|2 * e - 3 * f|) (2 * f - e) rfl hf' (abs_nonneg _)
        (by rw [sq_abs]; nlinarith)
      exact ⟨e', f', h1, h2, h3⟩

/-- (d) coprimality: `3 f^2 - e^2 = p` prime forces `gcd(e,f) = 1` (indeed `g^2 ∣ p`). -/
theorem coprime_of_rep (p : ℕ) (hp : p.Prime) (e f : ℕ) (h : p + e ^ 2 = 3 * f ^ 2) :
    Nat.Coprime e f := by
  have hge : Nat.gcd e f ∣ e := Nat.gcd_dvd_left e f
  have hgf : Nat.gcd e f ∣ f := Nat.gcd_dvd_right e f
  have h1 : Nat.gcd e f ^ 2 ∣ e ^ 2 := pow_dvd_pow_of_dvd hge 2
  have h2 : Nat.gcd e f ^ 2 ∣ 3 * f ^ 2 := Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hgf 2) 3
  have h3 : Nat.gcd e f ^ 2 ∣ p + e ^ 2 := h ▸ h2
  have h4 : Nat.gcd e f ^ 2 ∣ p := (Nat.dvd_add_left h1).mp h3
  have h5 : Nat.gcd e f ∣ p := (dvd_pow_self _ two_ne_zero).trans h4
  rcases hp.eq_one_or_self_of_dvd _ h5 with h6 | h6
  · exact h6
  · exfalso
    rw [h6] at h4
    have := Nat.le_of_dvd hp.pos h4
    have := hp.two_le
    nlinarith

/-- **`thm:mod12`, converse, in the base-beta range.**  Every prime `p ≡ 11 (mod 12)` is
`3 f^2 - e^2` with `1 ≤ e < f` and `gcd(e,f) = 1`. -/
theorem mod12_converse (p : ℕ) (hp : p.Prime) (h12 : p % 12 = 11) :
    ∃ e f : ℕ, 1 ≤ e ∧ e < f ∧ Nat.Coprime e f ∧ p + e ^ 2 = 3 * f ^ 2 := by
  obtain ⟨x, y, hxy⟩ := exists_rep_int p hp h12
  have hp2 : p ≠ 2 := by omega
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hy : 0 < |y| := by
    rcases (abs_nonneg y).lt_or_eq with h | h
    · exact h
    · exfalso
      have : y = 0 := abs_eq_zero.mp h.symm
      subst this
      nlinarith [sq_nonneg x]
  obtain ⟨e', f', h0, hlt, heq⟩ := descend p hp hp2 (|y|).natAbs |x| |y| rfl hy (abs_nonneg x)
    (by rw [sq_abs, sq_abs]; exact hxy)
  have hf0 : 0 ≤ f' := by omega
  lift e' to ℕ using h0
  lift f' to ℕ using hf0
  have hnat : p + e' ^ 2 = 3 * f' ^ 2 := by
    have : (p : ℤ) + (e' : ℤ) ^ 2 = 3 * (f' : ℤ) ^ 2 := by linarith
    exact_mod_cast this
  have hlt' : e' < f' := by exact_mod_cast hlt
  have he1 : 1 ≤ e' := by
    by_contra hcon
    have h00 : e' = 0 := by omega
    subst h00
    have h3p : 3 ∣ p := ⟨f' ^ 2, by simpa using hnat⟩
    rcases hp.eq_one_or_self_of_dvd 3 h3p with h | h <;> omega
  exact ⟨e', f', he1, hlt', coprime_of_rep p hp e' f' hnat, hnat⟩

/-- **`thm:mod12`, both directions, as the paper states it** (integers `e,f`, any coprime pair
with `p = 3 f^2 - e^2`; and the base-beta form `1 ≤ e < f`): for a prime `p > 3`,
`p` is of the form `3 f^2 - e^2` with coprime `e, f` iff `p ≡ 11 (mod 12)`, iff `p` is a base-beta
candidate. -/
theorem thm_mod12 (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    ((∃ e f : ℕ, Nat.Coprime e f ∧ p + e ^ 2 = 3 * f ^ 2) ↔ p % 12 = 11) ∧
    ((∃ e f : ℕ, 1 ≤ e ∧ e < f ∧ Nat.Coprime e f ∧ p + e ^ 2 = 3 * f ^ 2) ↔ p % 12 = 11) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨e, f, hc, h⟩
    exact Erdos634.BaseBetaMod12.basebeta_prime_mod_twelve p e f hp hp3 hc h
  · intro h12
    obtain ⟨e, f, -, -, hc, h⟩ := mod12_converse p hp h12
    exact ⟨e, f, hc, h⟩
  · rintro ⟨e, f, -, -, hc, h⟩
    exact Erdos634.BaseBetaMod12.basebeta_prime_mod_twelve p e f hp hp3 hc h
  · exact mod12_converse p hp

/-- Controls: the hypotheses are satisfied (`11`, `23`, `47`, `59` are primes `≡ 11 (mod 12)`) and the
conclusion yields the expected representations; the forward half rejects `7` (`≡ 7`). -/
theorem controls :
    (∃ e f : ℕ, 1 ≤ e ∧ e < f ∧ Nat.Coprime e f ∧ 11 + e ^ 2 = 3 * f ^ 2) ∧
    (∃ e f : ℕ, 1 ≤ e ∧ e < f ∧ Nat.Coprime e f ∧ 23 + e ^ 2 = 3 * f ^ 2) ∧
    (∃ e f : ℕ, 1 ≤ e ∧ e < f ∧ Nat.Coprime e f ∧ 47 + e ^ 2 = 3 * f ^ 2) ∧
    ¬ (∃ e f : ℕ, Nat.Coprime e f ∧ 7 + e ^ 2 = 3 * f ^ 2) := by
  refine ⟨mod12_converse 11 (by norm_num) rfl, mod12_converse 23 (by norm_num) rfl,
    mod12_converse 47 (by norm_num) rfl, ?_⟩
  intro h
  have := ((thm_mod12 7 (by norm_num) (by norm_num)).1).1 h
  omega

end Erdos634.Draft.FDBMod12Converse

#print axioms Erdos634.Draft.FDBMod12Converse.three_isSquare_zmod
#print axioms Erdos634.Draft.FDBMod12Converse.thue
#print axioms Erdos634.Draft.FDBMod12Converse.exists_rep_int
#print axioms Erdos634.Draft.FDBMod12Converse.descend
#print axioms Erdos634.Draft.FDBMod12Converse.coprime_of_rep
#print axioms Erdos634.Draft.FDBMod12Converse.mod12_converse
#print axioms Erdos634.Draft.FDBMod12Converse.thm_mod12
#print axioms Erdos634.Draft.FDBMod12Converse.controls
