/-
Draft/NSQWin2.lean -- second windowing step: the LINEAR leaf loops of `CN'zETWD4` (`NSQWin`) are replaced by sqrt-windowed equivalents,
each with a soundness lemma `W-check -> old check` valid for ALL `N`:
* `S1t2ChkW`, `RWChkT2W`: `t <= sqrt N` (since `t*t | N`) and `q` (resp. `f`) `<= sqrt (N/t^2)` (from `p < q`, `p^2 = 3q^2 - n` resp. `2f^2 - n`).
* `S5wChkW`: `t <= sqrt N`, `a <= sqrt (N/t^2)` (from `a < n/a`).
* `GammaChkDW`: `M <= sqrt N` (from `3M < N/M`).   `F1ChkParW`: `a <= sqrt N` (from `a*a < N`).
`CN'zETWD5 N -> CN'zETWD4 N` (`cnzETWD4_of_D5`), hence `not_tile_of_conditionsNSQzETWD5`.
Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.NSQMain
open Erdos634.Draft.NSQChk Erdos634.Draft.NSQS1T2 Erdos634.Draft.NSQRWT2

theorem key_s1 (n q p : ℕ) (h1 : n ≤ 3 * q * q) (h2 : p * p = 3 * q * q - n) (h3 : p < q) : q * q ≤ n := by
  have h4 := Nat.mul_lt_mul'' h3 h3
  have e : 3 * q * q = 3 * (q * q) := by ring
  rw [e] at h1 h2
  generalize q * q = Q at *
  generalize p * p = P at *
  omega

theorem key_rw (n f p : ℕ) (h1 : n ≤ 2 * f * f) (h2 : p * p = 2 * f * f - n) (h3 : p < f) : f * f ≤ n := by
  have h4 := Nat.mul_lt_mul'' h3 h3
  have e : 2 * f * f = 2 * (f * f) := by ring
  rw [e] at h1 h2
  generalize f * f = Q at *
  generalize p * p = P at *
  omega

def S1t2ChkW (N : ℕ) : Prop :=
  ∀ t ≤ Nat.sqrt N, 2 ≤ t → t * t ∣ N → ∀ q ≤ Nat.sqrt (N / (t * t)), N / (t * t) ≤ 3 * q * q →
    ¬ (sqChk (3 * q * q - N / (t * t)) ∧ 0 < Nat.sqrt (3 * q * q - N / (t * t)) ∧
       Nat.sqrt (3 * q * q - N / (t * t)) < q ∧ Nat.Coprime (Nat.sqrt (3 * q * q - N / (t * t))) q ∧
       q ≤ 2 * t * Nat.sqrt (3 * q * q - N / (t * t)) ∧
       ¬ (Nat.sqrt (3 * q * q - N / (t * t)) = 1 ∧ q = 2 * t))

set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 2000000 in
instance (N : ℕ) : Decidable (S1t2ChkW N) := by unfold S1t2ChkW sqChk; infer_instance

theorem s1t2Chk_of_W {N : ℕ} (h : S1t2ChkW N) : S1t2Chk N := by
  intro t ht h2 hd q hq hn hb
  have hN : 0 < N := by omega
  have hts : t ≤ Nat.sqrt N := Nat.le_sqrt.mpr (Nat.le_of_dvd hN hd)
  have hqs : q ≤ Nat.sqrt (N / (t * t)) := by
    apply Nat.le_sqrt.mpr
    have hs : Nat.sqrt (3 * q * q - N / (t * t)) * Nat.sqrt (3 * q * q - N / (t * t)) = 3 * q * q - N / (t * t) := hb.1
    exact key_s1 _ q _ hn hs hb.2.2.1
  exact h t hts h2 hd q hqs hn hb

def RWChkT2W (N : ℕ) : Prop :=
  ∀ s ≤ Nat.sqrt N, 2 ≤ s → s * s ∣ N → ∀ f ≤ Nat.sqrt (N / (s * s)), N / (s * s) ≤ 2 * f * f →
    ¬ (sqChk (2 * f * f - N / (s * s)) ∧ 0 < Nat.sqrt (2 * f * f - N / (s * s)) ∧
       Nat.sqrt (2 * f * f - N / (s * s)) < f ∧ Nat.Coprime (Nat.sqrt (2 * f * f - N / (s * s))) f ∧
       f ≤ s * Nat.sqrt (2 * f * f - N / (s * s)) ∧
       Nat.sqrt (2 * f * f - N / (s * s)) < s * (f - Nat.sqrt (2 * f * f - N / (s * s))) ∧
       ¬ (2 ≤ Nat.sqrt (2 * f * f - N / (s * s)) ∧ s < f ∧
          s * (f - Nat.sqrt (2 * f * f - N / (s * s))) ≤ Nat.sqrt (2 * f * f - N / (s * s)) + 1))

instance (N : ℕ) : Decidable (RWChkT2W N) := by unfold RWChkT2W sqChk; infer_instance

theorem rwChkT2_of_W {N : ℕ} (h : RWChkT2W N) : RWChkT2 N := by
  intro s hs h2 hd f hf hn hb
  have hN : 0 < N := by omega
  have hss : s ≤ Nat.sqrt N := Nat.le_sqrt.mpr (Nat.le_of_dvd hN hd)
  have hfs : f ≤ Nat.sqrt (N / (s * s)) := by
    apply Nat.le_sqrt.mpr
    have hq : Nat.sqrt (2 * f * f - N / (s * s)) * Nat.sqrt (2 * f * f - N / (s * s)) = 2 * f * f - N / (s * s) := hb.1
    exact key_rw _ f _ hn hq hb.2.2.1
  exact h s hss h2 hd f hfs hn hb

def S5wChkW (N : ℕ) : Prop :=
  ∀ t ≤ Nat.sqrt N, 2 ≤ t → t * t ∣ N → ∀ a ≤ Nat.sqrt (N / (t * t)), a ∣ N / (t * t) → 0 < a → a < N / (t * t) / a →
    a % 2 = (N / (t * t) / a) % 2 →
    Nat.Coprime ((N / (t * t) / a - a) / 2) ((a + N / (t * t) / a) / 2) →
    ¬ WordN t ((N / (t * t) / a - a) / 2) ((a + N / (t * t) / a) / 2)

instance (N : ℕ) : Decidable (S5wChkW N) := by unfold S5wChkW; infer_instance

theorem s5wChk_of_W {N : ℕ} (h : S5wChkW N) : S5wChk N := by
  intro t ht h2 hd a ha hdv h0 hlt hpar hcop
  have hN : 0 < N := by omega
  have hts : t ≤ Nat.sqrt N := Nat.le_sqrt.mpr (Nat.le_of_dvd hN hd)
  have has : a ≤ Nat.sqrt (N / (t * t)) := by
    apply Nat.le_sqrt.mpr
    have h1 : a * a < a * (N / (t * t) / a) := Nat.mul_lt_mul_of_pos_left hlt h0
    have h2' : a * (N / (t * t) / a) = N / (t * t) := Nat.mul_div_cancel' hdv
    omega
  exact h t hts h2 hd a has hdv h0 hlt hpar hcop

def GammaChkDW (N : ℕ) : Prop :=
  ∀ M ≤ Nat.sqrt N, 0 < M → M ∣ N → 3 * M < N / M → M % 2 = N % 2 → (N / M) % 2 = N % 2 →
    Nat.Coprime (((N / M) - M) / 2) N ∨ (M = 2 ∧ (N / M) % 4 = 2 ∧ 3 ≤ (N / M) / 4) ∨ Erdos634.Draft.ThmD.thmDChk M (N / M)

section
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000
instance (N : ℕ) : Decidable (GammaChkDW N) := by unfold GammaChkDW; infer_instance
end

theorem gammaChkD_of_W {N : ℕ} (h : GammaChkDW N) : Erdos634.Draft.ThmD.GammaChkD N := by
  intro M hM h0 hd h3 h4 h5
  have hMs : M ≤ Nat.sqrt N := by
    apply Nat.le_sqrt.mpr
    have h1 : M * M ≤ M * (N / M) := Nat.mul_le_mul_left M (by omega)
    have h2 : M * (N / M) = N := Nat.mul_div_cancel' hd
    omega
  exact h M hMs h0 hd h3 h4 h5

def F1ChkParW (N : ℕ) : Prop :=
  ∀ a ≤ Nat.sqrt N, 1 < a → a * a < N → a ∣ N → a % 2 = N % 2 → (N / a) % 2 = N % 2 →
    a + 2 ≤ N / a ∧ (N / a - a) % 2 = 0 ∧ ¬ sqChk ((a + N / a) ^ 2 + 12 * N) ∧
      a * a + (N / a) * (N / a) ≠ 4 * a * (N / a)

instance (N : ℕ) : Decidable (F1ChkParW N) := by unfold F1ChkParW sqChk; infer_instance

theorem f1ChkPar_of_W {N : ℕ} (h : F1ChkParW N) : F1ChkPar N :=
  fun a _ h1 h2 hd hp hp' => h a (Nat.le_sqrt.mpr h2.le) h1 h2 hd hp hp'

def CN'zETWD5 (N : ℕ) : Prop :=
  NQChkW N ∧ (EllChk2 N ∨ AsqChk N) ∧ NSqChkSq N ∧ HArithChkSq N ∧
    (N % 2 = 1 ∨ (N % 2 = 0 ∧ NHSqChkSq N)) ∧ LeafEsqN N ∧ (N % 4 = 2 ∨ F1ChkParW N) ∧ S2ChkSq N ∧ S3ChkSq N ∧ LeafIso N ∧
    (NoF2ChkSq N ∧ NoF3zChkSq N ∧ NoF4zChkSq N) ∧ GammaChkDW N ∧ S1t2ChkW N ∧ RWChkT2W N ∧ S5wChkW N

instance (N : ℕ) : Decidable (CN'zETWD5 N) := by unfold CN'zETWD5; infer_instance

theorem cnzETWD4_of_D5 {N : ℕ} (h : CN'zETWD5 N) : CN'zETWD4 N := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, h8, h9, h10, h11, gammaChkD_of_W h12, s1t2Chk_of_W h13, rwChkT2_of_W h14, s5wChk_of_W h15⟩
  rcases h7 with h | h
  · exact Or.inl h
  · exact Or.inr (f1ChkPar_of_W h)

theorem not_tile_of_conditionsNSQzETWD5 (N : ℕ) (h : CN'zETWD5 N) (D : CongruentDissection N) : False :=
  not_tile_of_conditionsNSQzETWD4 N (cnzETWD4_of_D5 h) D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETWD5
