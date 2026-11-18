/-
Draft/WGapLightPure2.lean -- 16 November 2026 (work item internal working notes).  UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.
Imports only WGapLightPure (Mathlib `Squarefree` only).  Measured on N = 100028 (WGapPureP_*): S2ChkSq (about 2N kernel iterations) and the loops of NoF2/NoF3z/NoF4z (about N each)
are killed above 12 GB (about 17-60 KB of kernel cache per iteration).  This module replaces the O(N)-iteration conjuncts by O(sqrt N)-iteration forms, each with a soundness lemma
INTO the original conjunct of WGapLightPure (so the heavy link WGapLightLink2 is unchanged):
* `AsqChk2` (s <= sqrt N), `EllChk2D` (divisor d <= sqrt N, primality by trial division to sqrt l): `cell2_of_D : (EllChk2D N or AsqChk2 N) -> (EllChk2 N or AsqChk N)`;
* `NoF4zS`, `NoF2S`, `NoF3zS`: the second variable is the exact square-root solution of the defining equation (single loop): `noF4z_of_S`, `noF2_of_S`, `noF3z_of_S`;
* `S2D`: enumerate the divisor A = 2q^2 - p^2 of 4N (cover_divisors) and q, p = sqrt(2q^2 - A): `s2_of_D`.
`CNzFixP2 N -> CNzFixP N` (`cnzFixP_of_P2`).  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLightPure

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.WGapPure

/-! ## AsqChk, EllChk2 -/

def AsqChk2 (N : ℕ) : Prop := ∃ s ≤ Nat.sqrt N, 0 < s ∧ (N = 15 * (s * s) ∨ N = 30 * (s * s))
instance (N : ℕ) : Decidable (AsqChk2 N) := by unfold AsqChk2; infer_instance

theorem asq_of_2 {N : ℕ} (h : AsqChk2 N) : AsqChk N := by
  obtain ⟨s, hs, h0, h1⟩ := h
  exact ⟨s, le_trans hs (Nat.sqrt_le_self N), h0, h1⟩

def PrimeT (l : ℕ) : Prop := ∀ m ≤ Nat.sqrt l, 2 ≤ m → ¬ m ∣ l
instance (l : ℕ) : Decidable (PrimeT l) := by unfold PrimeT; infer_instance

def EllQ (N l : ℕ) : Prop := 7 ≤ l ∧ ¬ l * l ∣ N ∧ PrimeT l
instance (N l : ℕ) : Decidable (EllQ N l) := by unfold EllQ; infer_instance

def EllChk2D (N : ℕ) : Prop := ∃ d ≤ Nat.sqrt N, 0 < d ∧ d ∣ N ∧ (EllQ N d ∨ EllQ N (N / d))
instance (N : ℕ) : Decidable (EllChk2D N) := by unfold EllChk2D; infer_instance

theorem primeT_of {l : ℕ} (h7 : 7 ≤ l) (h : PrimeT l) : ∀ m < l, m ∣ l → m = 1 := by
  intro m hm hd
  by_contra hne
  obtain ⟨k, hk⟩ := hd
  have hm0 : m ≠ 0 := by
    rintro rfl; omega
  have hm2 : 2 ≤ m := by omega
  have hk2 : 2 ≤ k := by
    by_contra hk'
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · rw [Nat.mul_zero] at hk; omega
    · rw [Nat.mul_one] at hk; omega
  by_cases hms : m ≤ Nat.sqrt l
  · exact h m hms hm2 ⟨k, hk⟩
  · push Not at hms
    have hks : k ≤ Nat.sqrt l := by
      by_contra hkk
      push Not at hkk
      have h1 : l < Nat.succ (Nat.sqrt l) * Nat.succ (Nat.sqrt l) := Nat.lt_succ_sqrt l
      have h2 : Nat.succ (Nat.sqrt l) * Nat.succ (Nat.sqrt l) ≤ m * k := Nat.mul_le_mul hms hkk
      omega
    exact h k hks hk2 ⟨m, by rw [hk, Nat.mul_comm]⟩

theorem ell_of_D {N : ℕ} (h : EllChk2D N) : EllChk2 N := by
  obtain ⟨d, hd, hd0, hdN, hq⟩ := h
  have hdN' : d ≤ N := le_trans hd (Nat.sqrt_le_self N)
  rcases hq with ⟨h7, hn, hp⟩ | ⟨h7, hn, hp⟩
  · exact ⟨d, hdN', h7, hdN, hn, primeT_of h7 hp⟩
  · exact ⟨N / d, Nat.div_le_self N d, h7, Nat.div_dvd_of_dvd hdN, hn, primeT_of h7 hp⟩

def Cell2 (N : ℕ) : Prop := EllChk2D N ∨ AsqChk2 N
instance (N : ℕ) : Decidable (Cell2 N) := by unfold Cell2; infer_instance

theorem cell2_of_D {N : ℕ} (h : Cell2 N) : EllChk2 N ∨ AsqChk N :=
  h.elim (fun h => Or.inl (ell_of_D h)) (fun h => Or.inr (asq_of_2 h))

/-! ## NoF2, NoF3z, NoF4z: single loops -/

theorem root_r {N x r : ℕ} (h : N = (x + r) * (2 * x + r)) : r = (Nat.sqrt (x * x + 4 * N) - 3 * x) / 2 := by
  have hsq : x * x + 4 * N = (2 * r + 3 * x) * (2 * r + 3 * x) := by rw [h]; ring
  rw [hsq, Nat.sqrt_eq]
  omega

def NoF4zS (N : ℕ) : Prop :=
  ∀ x ≤ Nat.sqrt N, 0 < x → x * x ≤ N →
    0 < (Nat.sqrt (x * x + 4 * N) - 3 * x) / 2 → ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) ≤ N →
    N = (x + (Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * (2 * x + (Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) →
    Nat.sqrt (x * x + x * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) + ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2)) *
      Nat.sqrt (x * x + x * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) + ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2)) ≠
      x * x + x * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) + ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2)
instance (N : ℕ) : Decidable (NoF4zS N) := by unfold NoF4zS; infer_instance

theorem noF4z_of_S {N : ℕ} (h : NoF4zS N) : NoF4zChkSq N := by
  intro x hx hx0 hxN r hr hr0 hrN hN
  have hr' := root_r hN
  have := h x hx hx0 hxN
  rw [← hr'] at this
  exact this hr0 hrN hN

def NoF2S (N : ℕ) : Prop :=
  (∀ z ≤ Nat.sqrt N, 3 * (z * z) ≠ N) ∧
  (∀ x ≤ Nat.sqrt N, 0 < x → x * x ≤ N →
    0 < (Nat.sqrt (x * x + 4 * N) - 3 * x) / 2 → ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) ≤ N →
    N = (x + (Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * (2 * x + (Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) →
    ¬ ((N + x * x) % 3 = 0 ∧
      Nat.sqrt ((N + x * x) / 3) * Nat.sqrt ((N + x * x) / 3) = (N + x * x) / 3))
instance (N : ℕ) : Decidable (NoF2S N) := by unfold NoF2S; infer_instance

theorem noF2_of_S {N : ℕ} (h : NoF2S N) : NoF2ChkSq N := by
  refine ⟨h.1, ?_⟩
  intro x hx hx0 hxN r hr hr0 hrN hN
  have hr' := root_r hN
  have := h.2 x hx hx0 hxN
  rw [← hr'] at this
  exact this hr0 hrN hN

theorem root_s {N j s : ℕ} (h : 4 * N = 3 * (s + j) * (s + 3 * j)) :
    s = Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j := by
  have hsq : (4 * N + 3 * (j * j)) / 3 = (s + 2 * j) * (s + 2 * j) := by
    have : 4 * N + 3 * (j * j) = 3 * ((s + 2 * j) * (s + 2 * j)) := by rw [h]; ring
    rw [this]; omega
  rw [hsq, Nat.sqrt_eq]
  omega

def NoF3zS (N : ℕ) : Prop :=
  ∀ j ≤ Nat.sqrt N, 0 < j → j * j ≤ N →
    (Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j) ≤ Nat.sqrt (2 * N) → j < (Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j) →
    (Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j) * (Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j) ≤ 2 * N →
    4 * N = 3 * ((Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j) + j) * ((Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j) + 3 * j) →
    ¬ ((((Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j) * (Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j)) + 3 * (j * j)) % 4 = 0 ∧
        Nat.sqrt ((((Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j) * (Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j)) + 3 * (j * j)) / 4) *
          Nat.sqrt ((((Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j) * (Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j)) + 3 * (j * j)) / 4) =
          (((Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j) * (Nat.sqrt ((4 * N + 3 * (j * j)) / 3) - 2 * j)) + 3 * (j * j)) / 4)
instance (N : ℕ) : Decidable (NoF3zS N) := by unfold NoF3zS; infer_instance

theorem noF3z_of_S {N : ℕ} (h : NoF3zS N) : NoF3zChkSq N := by
  intro j hj hj0 hjN s hs hjs hsN hN
  have hs' := root_s hN
  have := h j hj hj0 hjN
  rw [← hs'] at this
  exact this hs hjs hsN hN

/-! ## S2 by divisors of 4N -/

def S2Q (N A : ℕ) : Prop :=
  ∀ q ≤ Nat.sqrt (4 * N), q * q < 4 * N →
    Nat.sqrt (2 * (q * q) - A) * Nat.sqrt (2 * (q * q) - A) = 2 * (q * q) - A →
    Nat.sqrt (2 * (q * q) - A) < q → 0 < Nat.sqrt (2 * (q * q) - A) → Nat.gcd (Nat.sqrt (2 * (q * q) - A)) q = 1 →
    ¬ (s2A (Nat.sqrt (2 * (q * q) - A)) q * s2B (Nat.sqrt (2 * (q * q) - A)) q ∣ s2X N (Nat.sqrt (2 * (q * q) - A)) q ∧
       sqChk (s2X N (Nat.sqrt (2 * (q * q) - A)) q / (s2A (Nat.sqrt (2 * (q * q) - A)) q * s2B (Nat.sqrt (2 * (q * q) - A)) q)))
def S2D (N : ℕ) : Prop := ∀ d ≤ Nat.sqrt (4 * N), 0 < d → d ∣ 4 * N → S2Q N d ∧ S2Q N (4 * N / d)
instance (N A : ℕ) : Decidable (S2Q N A) := by unfold S2Q s2A s2B s2X sqChk; infer_instance
instance (N : ℕ) : Decidable (S2D N) := by unfold S2D; infer_instance

theorem s2_of_D {N : ℕ} (hN : 0 < N) (h : S2D N) : S2ChkSq N := by
  intro q hq hqN p hpq hp0 hg hdv
  have hQ : S2Q N (s2A p q) := cover_divisors (4 * N) (by omega) (S2Q N) h (s2A p q) hdv
  have hpp : p * p < q * q := Nat.mul_self_lt_mul_self hpq
  have hA : 2 * (q * q) - s2A p q = p * p := by
    unfold s2A; omega
  have hsp : Nat.sqrt (2 * (q * q) - s2A p q) = p := by rw [hA, Nat.sqrt_eq]
  have := hQ q hq hqN
  rw [hsp] at this
  rw [hA] at this
  exact this rfl hpq hp0 hg

/-! ## assembled -/

def CNzFixP2 (N : ℕ) : Prop :=
  NQChkW N ∧ Cell2 N ∧ NSqChkSq N ∧ HArithChkSq N ∧
    (N % 2 = 1 ∨ (N % 2 = 0 ∧ NHSqChkSq N)) ∧ LeafEsqSR N ∧ (N % 4 = 2 ∨ F1ChkParW N) ∧ S2D N ∧ S3newChk N ∧ IsoH9bChkW N ∧
    (NoF2S N ∧ NoF3zS N ∧ NoF4zS N) ∧ GammaChkDW N ∧ S1UBChkW N ∧ RWChkWl N ∧ S5wChkW N
instance (N : ℕ) : Decidable (CNzFixP2 N) := by unfold CNzFixP2; infer_instance

theorem cnzFixP_of_P2 {N : ℕ} (h : CNzFixP2 N) : CNzFixP N := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ⟨h11a, h11b, h11c⟩, h12, h13, h14, h15⟩ := h
  exact ⟨h1, cell2_of_D h2, h3, h4, h5, h6, h7, s2_of_D h4.1 h8, h9, h10, ⟨noF2_of_S h11a, noF3z_of_S h11b, noF4z_of_S h11c⟩,
    h12, h13, h14, h15⟩

end Erdos634.Draft.WGapPure

#print axioms Erdos634.Draft.WGapPure.cnzFixP_of_P2
