/-
Draft/NSQChk.lean — Decidable (bounded) forms of the arithmetic hypotheses of the
non-squarefree leaves, each with its implication lemma quantified over ALL `N`:

  S1Chk N     ⇒ NSQS1.S1Free N        (no `t ≥ 2`, coprime `0<p<q` with `N = t² (3q²−p²)`)
  RWChk N     ⇒ NSQRW.RWFree N        (no `S' ≥ 2`, coprime `0<e<f` with `N = S'² (2f²−e²)`)
  F1ChkPar N  ⇒ the hypothesis of `NSQF1.f1MaGt1par_of_list`  ⇒ GapF1 N   (6 < N)
`F1ChkPar` is `AllNExclusion.F1Chk` restricted to factorisations `Ma ≡ Mb ≡ N (mod 2)` (parity of `Paper.cor_int`).  No sorry, no native_decide.
-/
import Erdos634.Draft.AllNExclusionArith2
import Erdos634.Draft.NSQF1
import Erdos634.Draft.NSQS1
import Erdos634.Draft.NSQRW

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQChk

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.AllNExclusion
open Erdos634.Draft.NSQS1 Erdos634.Draft.NSQRW

/-! ## F1 with parity -/

def F1ChkPar (N : ℕ) : Prop :=
  ∀ a ≤ N, 1 < a → a * a < N → a ∣ N → a % 2 = N % 2 → (N / a) % 2 = N % 2 →
    a + 2 ≤ N / a ∧ (N / a - a) % 2 = 0 ∧ ¬ sqChk ((a + N / a) ^ 2 + 12 * N) ∧
      a * a + (N / a) * (N / a) ≠ 4 * a * (N / a)

instance (N : ℕ) : Decidable (F1ChkPar N) := by unfold F1ChkPar sqChk; infer_instance

theorem f1listpar_of_chk {N : ℕ} (h : F1ChkPar N) :
    ∀ Ma Mb : ℕ, 1 < Ma → Ma < Mb → Ma * Mb = N → Ma % 2 = N % 2 → Mb % 2 = N % 2 →
      ∃ κ : ℕ, 0 < κ ∧ Mb = Ma + 2 * κ ∧ ¬ IsSquare (((Ma : ℤ) + Mb) ^ 2 + 12 * (N : ℤ)) ∧
        Ma ^ 2 + Mb ^ 2 ≠ 4 * Ma * Mb := by
  intro Ma Mb h1 h2 h3 hpa hpb
  have hMa0 : 0 < Ma := by omega
  have hdvd : Ma ∣ N := ⟨Mb, h3.symm⟩
  have hdiv : N / Ma = Mb := by rw [← h3]; exact Nat.mul_div_cancel_left _ hMa0
  have hlt : Ma * Ma < N := by rw [← h3]; exact Nat.mul_lt_mul_of_pos_left h2 hMa0
  have hle : Ma ≤ N := by nlinarith
  obtain ⟨e1, e2, e3, e4⟩ := h Ma hle h1 hlt hdvd hpa (by rw [hdiv]; exact hpb)
  rw [hdiv] at e1 e2 e3 e4
  refine ⟨(Mb - Ma) / 2, by omega, by omega, ?_, ?_⟩
  · exact not_isSquare_of_chk ((Ma + Mb) ^ 2 + 12 * N) _ (by push_cast; ring) e3
  · intro hcon; apply e4; nlinarith [hcon]

theorem gapF1_of_chkpar {N : ℕ} (h6 : 6 < N) (h : F1ChkPar N) : GapF1 N :=
  Erdos634.Draft.NSQF1.gapF1_of_MaGt1par N h6 (Erdos634.Draft.NSQF1.f1MaGt1par_of_list N (f1listpar_of_chk h))

/-! ## S1 and RW -/

def S1Chk (N : ℕ) : Prop :=
  ∀ t ≤ N, 2 ≤ t → t * t ∣ N → ∀ q ≤ N, N / (t * t) ≤ 3 * q * q →
    ¬ (sqChk (3 * q * q - N / (t * t)) ∧ 0 < Nat.sqrt (3 * q * q - N / (t * t)) ∧
       Nat.sqrt (3 * q * q - N / (t * t)) < q ∧ Nat.Coprime (Nat.sqrt (3 * q * q - N / (t * t))) q)

instance (N : ℕ) : Decidable (S1Chk N) := by unfold S1Chk sqChk; infer_instance

theorem s1Free_of_chk {N : ℕ} (h : S1Chk N) : S1Free N := by
  intro t p q ht hp hpq hcop hN
  lift t to ℕ using (by omega)
  lift p to ℕ using hp.le
  lift q to ℕ using (by omega)
  have hN' : N = t * t * (3 * q * q - p * p) := by
    have hle : p * p ≤ 3 * q * q := by
      have : (p : ℤ) < q := hpq
      have : p < q := by exact_mod_cast this
      nlinarith
    have : (N : ℤ) = ((t * t * (3 * q * q - p * p) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hle]; rw [hN]; ring
    exact_mod_cast this
  have hpq' : p < q := by exact_mod_cast hpq
  have hp' : 0 < p := by exact_mod_cast hp
  have ht2 : 2 ≤ t := by exact_mod_cast ht
  have hpp : p * p < q * q := Nat.mul_self_lt_mul_self hpq'
  have hqq : q ≤ q * q := Nat.le_mul_self q
  have hYpos : 0 < 3 * q * q - p * p := by
    apply Nat.sub_pos_of_lt; nlinarith
  have hYq : q ≤ 3 * q * q - p * p := Nat.le_sub_of_add_le (by nlinarith)
  have hdiv : N / (t * t) = 3 * q * q - p * p := by
    rw [hN']; exact Nat.mul_div_cancel_left _ (by positivity)
  have htt : t * t ∣ N := ⟨_, hN'⟩
  have htN : t ≤ N := by
    have : t * t ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_right _ hYpos
    nlinarith
  have hqN : q ≤ N := by
    have h1 : t * t ≥ 1 := by nlinarith
    have : 3 * q * q - p * p ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hle : N / (t * t) ≤ 3 * q * q := by rw [hdiv]; omega
  have hsub : 3 * q * q - N / (t * t) = p * p := by rw [hdiv]; omega
  apply h t htN ht2 htt q hqN hle
  rw [hsub, Nat.sqrt_eq]
  refine ⟨?_, hp', hpq', ?_⟩
  · unfold sqChk; rw [Nat.sqrt_eq]
  · have : Int.gcd (p : ℤ) (q : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
    simpa [Int.gcd_natCast_natCast] using this

def RWChk (N : ℕ) : Prop :=
  ∀ s ≤ N, 2 ≤ s → s * s ∣ N → ∀ f ≤ N, N / (s * s) ≤ 2 * f * f →
    ¬ (sqChk (2 * f * f - N / (s * s)) ∧ 0 < Nat.sqrt (2 * f * f - N / (s * s)) ∧
       Nat.sqrt (2 * f * f - N / (s * s)) < f ∧ Nat.Coprime (Nat.sqrt (2 * f * f - N / (s * s))) f)

instance (N : ℕ) : Decidable (RWChk N) := by unfold RWChk sqChk; infer_instance

theorem rwFree_of_chk {N : ℕ} (h : RWChk N) : RWFree N := by
  intro s e f hs he hef hcop hN
  lift s to ℕ using (by omega)
  lift e to ℕ using he.le
  lift f to ℕ using (by omega)
  have hef' : e < f := by exact_mod_cast hef
  have he' : 0 < e := by exact_mod_cast he
  have hs2 : 2 ≤ s := by exact_mod_cast hs
  have hle : e * e ≤ 2 * f * f := by nlinarith
  have hN' : N = s * s * (2 * f * f - e * e) := by
    have : (N : ℤ) = ((s * s * (2 * f * f - e * e) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hle]; rw [hN]; ring
    exact_mod_cast this
  have hee : e * e < f * f := Nat.mul_self_lt_mul_self hef'
  have hff : f ≤ f * f := Nat.le_mul_self f
  have hYpos : 0 < 2 * f * f - e * e := by
    apply Nat.sub_pos_of_lt; nlinarith
  have hYf : f ≤ 2 * f * f - e * e := Nat.le_sub_of_add_le (by nlinarith)
  have hdiv : N / (s * s) = 2 * f * f - e * e := by
    rw [hN']; exact Nat.mul_div_cancel_left _ (by positivity)
  have hss : s * s ∣ N := ⟨_, hN'⟩
  have hsN : s ≤ N := by
    have : s * s ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_right _ hYpos
    nlinarith
  have hfN : f ≤ N := by
    have h1 : s * s ≥ 1 := by nlinarith
    have : 2 * f * f - e * e ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hle2 : N / (s * s) ≤ 2 * f * f := by rw [hdiv]; omega
  have hsub : 2 * f * f - N / (s * s) = e * e := by rw [hdiv]; omega
  apply h s hsN hs2 hss f hfN hle2
  rw [hsub, Nat.sqrt_eq]
  refine ⟨?_, he', hef', ?_⟩
  · unfold sqChk; rw [Nat.sqrt_eq]
  · have : Int.gcd (e : ℤ) (f : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
    simpa [Int.gcd_natCast_natCast] using this

end Erdos634.Draft.NSQChk

#print axioms Erdos634.Draft.NSQChk.gapF1_of_chkpar
#print axioms Erdos634.Draft.NSQChk.s1Free_of_chk
#print axioms Erdos634.Draft.NSQChk.rwFree_of_chk
