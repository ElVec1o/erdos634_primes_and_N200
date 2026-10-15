/-
Draft/GAUBridge.lean -- Case A (all tile angles in `ℚπ`) for `N = d s²`, `d ∈ {15, 30}`: the reduction to the tile tables.

For `N = d s²` with `d ∈ {15, 30}`:
* arithmetic, uniform in `s`: `N` is not a sum of two squares, `NQ N`, `HArith N`, and `v₃(N)`, `v₅(N)` are odd, so Lemma V
  gives `15 ∣ n` for the common denominator `n` of the tile angles (`fifteen_dvd`);
* `gapAcomp_of_residual`: as at `N = 60` (`N60ACase`), every level `n` except the tiles with `R ≠ R₀` at `n = 30, 60`
  is closed by Lemma S, `N30Case.relTriv_smooth` and `NSQCaseA.r0c_core_nsq`;
* `exc_of_excChk`: at `n = 30, 60` the tiles with `R ≠ R₀` lie in an explicit list `L` (Bool table `excChk n L` of
  `GAUExc`, built on the certificates `LemmaS.cert`), up to a permutation of the tile's angles;
* `idQ_of_idFin`: the identity of `CaseALemmaVDissection.star` with the constant `d s²` and natural coefficients `c` is
  the identity with the constant `d` and the rational coefficients `c / s` (`GAU.IdQ`), which `GAUCheck` refutes tile by
  tile; `idQ_perm`: permutation of the tile's angles.

Composite-N statement; not prime-case work.  No sorry, no native_decide.
-/
import Mathlib
import Erdos634.Draft.GAURow
import Erdos634.Draft.N60AC
import Erdos634.Draft.N60ACase
import Erdos634.Draft.CaseACorF
import Erdos634.Draft.GAUExc

open scoped BigOperators
open scoped Classical

namespace Erdos634.Draft.GAU

open Erdos634.Geometry Erdos634.LemmaS Erdos634.CaseA.R0c Erdos634.N30K
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi lemmaV target_angle_nat star)
open Erdos634.Geometry.CaseA.LemmaH (HArith)

/-! ## Arithmetic of `N = d s²` -/

theorem val_odd {p d s : ℕ} (hp : p.Prime) (hd : padicValNat p d = 1) (hs : 0 < s) :
    ¬ Even (padicValNat p (d * s ^ 2)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hd
  rw [padicValNat.mul hd0 (pow_ne_zero 2 hs.ne'), padicValNat.pow 2 hs.ne', hd]
  rintro ⟨r, hr⟩
  omega

/-- `c r² ≠ M` when `p ∤ c` and `v_p(M)` is odd -/
theorem ne_of_val {p c M : ℕ} (hp : p.Prime) (hc : ¬ p ∣ c) (hM : ¬ Even (padicValNat p M)) (r : ℕ) :
    c * r ^ 2 ≠ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  apply hM
  rw [← h]
  by_cases hr : r = 0
  · subst hr; simp
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (dvd_zero p)
  rw [padicValNat.mul hc0 (pow_ne_zero 2 hr), padicValNat.pow 2 hr, padicValNat.eq_zero_of_not_dvd hc]
  exact ⟨padicValNat p r, by ring⟩

theorem val_two_mul {p M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hM0 : M ≠ 0) (hM : ¬ Even (padicValNat p M)) :
    ¬ Even (padicValNat p (2 * M)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : ¬ p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  rw [padicValNat.mul (by norm_num) hM0, padicValNat.eq_zero_of_not_dvd h2, zero_add]
  exact hM

theorem val3_15 : padicValNat 3 15 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [show (15 : ℕ) = 3 * 5 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem val5_15 : padicValNat 5 15 = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [show (15 : ℕ) = 5 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem val3_30 : padicValNat 3 30 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [show (30 : ℕ) = 3 * 10 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem val5_30 : padicValNat 5 30 = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [show (30 : ℕ) = 5 * 6 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- the arithmetic hypotheses of the Case A chain, for `N` with `v₃(N)`, `v₅(N)` odd -/
theorem harith_of_val {N : ℕ} (h3 : ¬ Even (padicValNat 3 N)) (h5 : ¬ Even (padicValNat 5 N)) : HArith N := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at h3
  have h5' := val_two_mul Nat.prime_five (by norm_num) hN0 h5
  refine ⟨Nat.pos_of_ne_zero hN0, fun r => ne_of_val Nat.prime_five (by norm_num) h5 r,
    fun t => ?_, fun y => ne_of_val Nat.prime_five (by norm_num) h5' y, fun t => ?_,
    fun x => ne_of_val Nat.prime_five (by norm_num) h5 x, fun r => ne_of_val Nat.prime_three (by norm_num) h3 r⟩
  · have := ne_of_val (c := 1) Nat.prime_five (by norm_num) h5 t
    simpa using this
  · have := ne_of_val (c := 1) Nat.prime_five (by norm_num) h5' t
    simpa using this

theorem nsq_of_val {N : ℕ} (h3 : ¬ Even (padicValNat 3 N)) : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  intro h
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at h3
  have h3d : 3 ∣ N := by
    by_contra hnd
    apply h3
    rw [padicValNat.eq_zero_of_not_dvd hnd]
    exact Even.zero
  exact h3 (Nat.eq_sq_add_sq_iff.mp h 3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3d, hN0⟩) (by norm_num))

theorem nq_of_sq {d s : ℕ} (hd : d = 15 ∨ d = 30) (hs : 0 < s) : NQ (d * s ^ 2) := by
  rcases hd with rfl | rfl
  · exact ⟨s, 15, hs, by decide +kernel, by ring, by norm_num, Or.inr (Or.inr (by norm_num))⟩
  · exact ⟨s, 30, hs, by decide +kernel, by ring, by norm_num, Or.inl (by norm_num)⟩

/-! ## The chain -/

/-- The residual of `GapA N`: only the rows `n = 30, 60`, and only tiles with `R ≠ R₀`. -/
def GapAResidual (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (n : ℕ) (a : Fin 3 → ℕ), 0 < n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ k, D.model.angleAt k = a k * Real.pi / n) →
    (n = 30 ∨ n = 60) → relSpace n a ≠ trivSpace n a → False

theorem fifteen_dvd {N : ℕ} (h3 : ¬ Even (padicValNat 3 N)) (h5 : ¬ Even (padicValNat 5 N))
    (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) : 15 ∣ n := by
  have hd : ∀ p : ℕ, p.Prime → (p = 3 ∨ p = 5) → p ∣ n := by
    intro p hp hp35
    by_contra h
    have hl : ¬ p ∣ 2 * n := by
      intro hh
      rcases (Nat.Prime.dvd_mul hp).mp hh with h' | h'
      · rcases hp35 with rfl | rfl <;> (have := Nat.le_of_dvd (by norm_num) h'; omega)
      · exact h h'
    have hv := lemmaV D hn a ha hp hl
    rcases hp35 with rfl | rfl
    · exact h3 hv
    · exact h5 hv
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (hd 3 Nat.prime_three (Or.inl rfl))
    (hd 5 Nat.prime_five (Or.inr rfl))

/-- **`GapA N` from the residual**, for `N` with `NQ N` and `v₃(N)`, `v₅(N)` odd. -/
theorem gapA_of_residual {N : ℕ} (hNQ : NQ N) (h3 : ¬ Even (padicValNat 3 N)) (h5 : ¬ Even (padicValNat 5 N))
    (R : GapAResidual N) : Erdos634.Draft.Chain15.GapA N := by
  intro D hrat
  have hS := Erdos634.LemmaSAll.lemmaS
  obtain ⟨n₀, hn₀, a₀, ha₀⟩ := exists_nat_angles D.model hrat
  obtain ⟨n, hn, a, hgcd, ha⟩ := exists_primitive D.model hn₀ a₀ ha₀
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have h15 := fifteen_dvd h3 h5 D hn a ha
  have h15n : 15 ≤ n := Nat.le_of_dvd hn h15
  have core : relSpace n a = trivSpace n a → False := fun hSn =>
    Erdos634.Draft.NSQCaseA.r0c_core_nsq D hNQ (nsq_of_val h3) (harith_of_val h3 h5) hn a ha hSn (by omega)
  by_cases hp : ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p ∣ n
  · obtain ⟨p, hpp, hp7, hpn⟩ := hp
    exact core (hS n a hpos hsum hgcd p hpp hp7 hpn)
  · push Not at hp
    have hsm : ∀ p : ℕ, p.Prime → p ∣ n → p < 7 := fun p hpp hpn => by
      by_contra hlt; push Not at hlt; exact absurd hpn (hp p hpp hlt)
    by_cases hex : n = 30 ∨ n = 60
    · by_cases hSn : relSpace n a = trivSpace n a
      · exact core hSn
      · exact R D n a hn hgcd ha hex hSn
    · push Not at hex
      exact core (Erdos634.N30Case.relTriv_smooth n a hn hpos hsum hgcd h15 hsm hex.1 hex.2)

/-! ## The identity -/

/-- **The identity of a dissection into `N` tiles with all angles multiples of `π/n`.** -/
theorem identityN {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    (∀ k, 1 ≤ a k) ∧ ∑ k, a k = n ∧
    ∃ (b c : Fin 3 → ℕ), (∀ k, 1 ≤ b k) ∧ ∑ k, b k = n ∧ IdFinF N n a (b 0) (b 1) (b 2) c := by
  choose b hb using target_angle_nat D hn a ha
  obtain ⟨c, hc⟩ := star D
  refine ⟨fun k => (nat_bounds hn (ha k) (angle_pos _ k) (angle_lt_pi _ k)).1,
    Erdos634.CaseA.R0c.sum_of_angles hn ha, b, c,
    fun k => (nat_bounds hn (hb k) (angle_pos _ k) (angle_lt_pi _ k)).1,
    Erdos634.CaseA.R0c.sum_of_angles hn hb, ?_⟩
  simp only [ha, hb] at hc
  unfold IdFinF
  rw [Fin.prod_univ_three]
  push_cast at hc
  linear_combination (-1 : ℝ) * hc

/-- the identity with the constant `d s²` and natural coefficients is the identity with the constant `d` and the
coefficients `c / s` -/
theorem idQ_of_idFin {d s n : ℕ} (hs : 0 < s) {a : Fin 3 → ℕ} {A B C : ℕ} {c : Fin 3 → ℕ}
    (h : IdFinF (d * s ^ 2) n a A B C c) : IdQ d n a A B C (fun k => (c k : ℚ) / s) := by
  unfold IdFinF at h
  show (∑ k, (((c k : ℚ) / s : ℚ) : ℝ) * Real.sin (a k * Real.pi / n)) ^ 2 * Real.sin (B * Real.pi / n) *
      Real.sin (C * Real.pi / n) = (d : ℝ) * Real.sin (A * Real.pi / n) * ∏ k, Real.sin (a k * Real.pi / n)
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have e : ∑ k, (((c k : ℚ) / s : ℚ) : ℝ) * Real.sin (a k * Real.pi / n)
      = (∑ k, (c k : ℝ) * Real.sin (a k * Real.pi / n)) / s := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [e]
  set S := ∑ k, (c k : ℝ) * Real.sin (a k * Real.pi / n) with hS
  set P := ∏ k, Real.sin (a k * Real.pi / n) with hP
  have h' : S ^ 2 * Real.sin (B * Real.pi / n) * Real.sin (C * Real.pi / n)
      = (d : ℝ) * (s : ℝ) ^ 2 * Real.sin (A * Real.pi / n) * P := by
    rw [h]; push_cast; ring
  have e2 : (S / s) ^ 2 * Real.sin (B * Real.pi / n) * Real.sin (C * Real.pi / n)
      = (S ^ 2 * Real.sin (B * Real.pi / n) * Real.sin (C * Real.pi / n)) / (s : ℝ) ^ 2 := by
    rw [div_pow]; ring
  rw [e2, h', div_eq_iff (pow_ne_zero 2 hs')]
  ring

/-- permutation of the tile's angles -/
theorem idQ_perm {d n : ℕ} {a a₀ : Fin 3 → ℕ} {A B C : ℕ} {m : Fin 3 → ℚ} (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ k, a (σ k) = a₀ k) (h : IdQ d n a A B C m) : IdQ d n a₀ A B C (fun k => m (σ k)) := by
  unfold IdQ at h
  show (∑ k, ((m (σ k) : ℚ) : ℝ) * Real.sin (a₀ k * Real.pi / n)) ^ 2 * Real.sin (B * Real.pi / n) *
      Real.sin (C * Real.pi / n) = (d : ℝ) * Real.sin (A * Real.pi / n) * ∏ k, Real.sin (a₀ k * Real.pi / n)
  have e1 := Equiv.sum_comp σ (fun k => (m k : ℝ) * Real.sin (a k * Real.pi / n))
  have e2 := Equiv.prod_comp σ (fun k => Real.sin (a k * Real.pi / n))
  simp only [hσ] at e1 e2
  rw [e1, e2]
  exact h

/-! ## The exceptional tiles -/

theorem perm_of_isPerm3 {a : Fin 3 → ℕ} {t : ℕ × ℕ × ℕ} (h : isPerm3 (a 0) (a 1) (a 2) t = true) :
    ∃ σ : Equiv.Perm (Fin 3), a (σ 0) = t.1 ∧ a (σ 1) = t.2.1 ∧ a (σ 2) = t.2.2 := by
  unfold isPerm3 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ((((⟨⟨h0, h1⟩, h2⟩ | ⟨⟨h0, h1⟩, h2⟩) | ⟨⟨h0, h1⟩, h2⟩) | ⟨⟨h0, h1⟩, h2⟩) | ⟨⟨h0, h1⟩, h2⟩) |
    ⟨⟨h0, h1⟩, h2⟩
  · exact ⟨Equiv.refl _, h0, h1, h2⟩
  · refine ⟨Equiv.swap 1 2, ?_, ?_, ?_⟩
    · rw [show (Equiv.swap (1 : Fin 3) 2) 0 = 0 by decide]; exact h0
    · rw [show (Equiv.swap (1 : Fin 3) 2) 1 = 2 by decide]; exact h1
    · rw [show (Equiv.swap (1 : Fin 3) 2) 2 = 1 by decide]; exact h2
  · refine ⟨Equiv.swap 0 1, ?_, ?_, ?_⟩
    · rw [show (Equiv.swap (0 : Fin 3) 1) 0 = 1 by decide]; exact h0
    · rw [show (Equiv.swap (0 : Fin 3) 1) 1 = 0 by decide]; exact h1
    · rw [show (Equiv.swap (0 : Fin 3) 1) 2 = 2 by decide]; exact h2
  · refine ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1), ?_, ?_, ?_⟩
    · rw [show ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1)) 0 = 1 by decide]; exact h0
    · rw [show ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1)) 1 = 2 by decide]; exact h1
    · rw [show ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1)) 2 = 0 by decide]; exact h2
  · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 1 2), ?_, ?_, ?_⟩
    · rw [show ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2)) 0 = 2 by decide]; exact h0
    · rw [show ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2)) 1 = 0 by decide]; exact h1
    · rw [show ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2)) 2 = 1 by decide]; exact h2
  · refine ⟨Equiv.swap 0 2, ?_, ?_, ?_⟩
    · rw [show (Equiv.swap (0 : Fin 3) 2) 0 = 2 by decide]; exact h0
    · rw [show (Equiv.swap (0 : Fin 3) 2) 1 = 1 by decide]; exact h1
    · rw [show (Equiv.swap (0 : Fin 3) 2) 2 = 0 by decide]; exact h2

/-- **The tiles with `R ≠ R₀` at a level with a table.** -/
theorem exc_of_excChk {n : ℕ} {L : List (ℕ × ℕ × ℕ)} (h : excChk n L = true) (a : Fin 3 → ℕ)
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hne : relSpace n a ≠ trivSpace n a) :
    ∃ t ∈ L, ∃ σ : Equiv.Perm (Fin 3), a (σ 0) = t.1 ∧ a (σ 1) = t.2.1 ∧ a (σ 2) = t.2.2 := by
  rw [Fin.sum_univ_three] at hsum
  have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
  have hn : 0 < n := by omega
  have ha2 : a 2 = n - a 0 - a 1 := by omega
  unfold excChk at h
  simp only [List.all_eq_true, List.mem_range] at h
  have hr := h (a 0) (by omega)
  unfold excRow at hr
  simp only [List.all_eq_true, List.mem_range] at hr
  have hc := hr (a 1) (by omega)
  rw [← ha2, if_pos ⟨h0, h1, by omega, hgcd⟩] at hc
  rw [Bool.or_eq_true] at hc
  rcases hc with hc | hL
  · exact absurd (le_antisymm (fun e he => cert_sound hn hc he) (trivSpace_le n a)) hne
  · obtain ⟨t, ht, hp⟩ := List.any_eq_true.mp hL
    exact ⟨t, ht, perm_of_isPerm3 hp⟩

/-- transport of a tile table along a permutation of the tile's angles -/
theorem kill_perm {d n : ℕ} {a₀ : Fin 3 → ℕ}
    (kill : ∀ {A B C : ℕ}, 1 ≤ A → 1 ≤ B → 1 ≤ C → A + B + C = n → ∀ m : Fin 3 → ℚ, IdQ d n a₀ A B C m → False)
    {a : Fin 3 → ℕ} (σ : Equiv.Perm (Fin 3)) (h0 : a (σ 0) = a₀ 0) (h1 : a (σ 1) = a₀ 1) (h2 : a (σ 2) = a₀ 2)
    {A B C : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) (hs : A + B + C = n) (m : Fin 3 → ℚ)
    (hid : IdQ d n a A B C m) : False := by
  have hσ : ∀ k, a (σ k) = a₀ k := by
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  exact kill hA hB hC hs _ (idQ_perm σ hσ hid)

/-- **Non-vacuity of `IdQ`.**  For a square constant `k²` the identity has a rational solution (target similar to the
tile, coefficients `(k, 0, 0)`): the tables of `GAUCheck` refute `IdQ d …` for `d = 15, 30` only. -/
theorem idQ_square_witness (n : ℕ) (a : Fin 3 → ℕ) (k : ℕ) :
    IdQ (k ^ 2) n a (a 0) (a 1) (a 2) (fun i => if i = 0 then (k : ℚ) else 0) := by
  unfold IdQ
  rw [Fin.sum_univ_three, Fin.prod_univ_three]
  simp
  ring

end Erdos634.Draft.GAU

#print axioms Erdos634.Draft.GAU.gapA_of_residual
#print axioms Erdos634.Draft.GAU.idQ_of_idFin
#print axioms Erdos634.Draft.GAU.exc_of_excChk
