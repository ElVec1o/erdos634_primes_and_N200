/-
Draft/WGapLightPure.lean -- 16 November 2026 (work item internal working notes).  UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.
SELF-CONTAINED copy of the 15 conjuncts of `NSQM.CNzFixW` (WGapLink2): it imports only Mathlib's `Squarefree` for `NQChkW`, NOT the geometry closure
(measured: importing WGapLightDefs costs 5.76 GB at load, the same as WGapLink2; the geometry closure is the fixed cost).  Every definition is a verbatim copy of the
original (source file in the comment); the heavy link `WGapLightLink2.cnzFixW_of_P : CNzFixP N -> CNzFixW N` checks each copy by definitional unfolding, so a transcription
error cannot go unnoticed (the link would fail to elaborate).  The two O(N) loops of `LeafEsqS` are the divisor-pair forms `Pairs60R`/`Pairs120R` (sqrt(3N) bound).
No sorry, no native_decide.  Credit: Beeson-Rosu, Paliy, Laczkovich, Zhang (the checks themselves).
-/
import Mathlib.Data.Nat.Squarefree

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.WGapPure

/-- AllNExclusionArith2.lean:25 -/
def sqChk (v : ℕ) : Prop := Nat.sqrt v * Nat.sqrt v = v

/-- NSQWin.lean:20 -/
def NQChkW (N : ℕ) : Prop :=
  ∃ s ≤ Nat.sqrt N, 0 < s ∧ s * s ∣ N ∧ Squarefree (N / (s * s)) ∧ 7 ≤ N / (s * s) ∧
    (17 ≤ N / (s * s) ∨ (N / (s * s)) % 4 = 2 ∨ (N / (s * s)) % 4 = 3)
instance (N : ℕ) : Decidable (NQChkW N) := by unfold NQChkW; infer_instance

/-- NSQMain.lean:107 -/
def EllChk2 (N : ℕ) : Prop :=
  ∃ ℓ ≤ N, 7 ≤ ℓ ∧ ℓ ∣ N ∧ ¬ ℓ * ℓ ∣ N ∧ ∀ m < ℓ, m ∣ ℓ → m = 1
instance (N : ℕ) : Decidable (EllChk2 N) := by unfold EllChk2; infer_instance

/-- SlimNSQA.lean:30 -/
def AsqChk (N : ℕ) : Prop := ∃ s, s ≤ N ∧ 0 < s ∧ (N = 15 * (s * s) ∨ N = 30 * (s * s))
instance (N : ℕ) : Decidable (AsqChk N) := by unfold AsqChk; infer_instance

/-- AllNExclusionArith.lean:231 -/
def NSqChkSq (N : ℕ) : Prop :=
  ∀ x ≤ Nat.sqrt N, x * x ≤ N → Nat.sqrt (N - x * x) * Nat.sqrt (N - x * x) ≠ N - x * x
instance (N : ℕ) : Decidable (NSqChkSq N) := by unfold NSqChkSq; infer_instance

/-- AllNExclusionArith.lean:247 -/
def HArithChkSq (N : ℕ) : Prop :=
  0 < N ∧
  (∀ r ≤ Nat.sqrt N, 2 * (r * r) ≠ N) ∧
  (∀ t ≤ Nat.sqrt N, t * t ≠ N) ∧
  (∀ y ≤ Nat.sqrt N, 3 * (y * y) ≠ 2 * N) ∧
  (∀ t ≤ Nat.sqrt (2 * N), t * t ≠ 2 * N) ∧
  (∀ x ≤ Nat.sqrt N, 3 * (x * x) ≠ N) ∧
  (∀ r ≤ Nat.sqrt N, 10 * (r * r) ≠ N)
instance (N : ℕ) : Decidable (HArithChkSq N) := by unfold HArithChkSq; infer_instance

/-- AllNExclusionArith.lean:238 -/
def NHSqChkSq (N : ℕ) : Prop :=
  ∀ x ≤ Nat.sqrt (N / 2), 2 * (x * x) ≤ N →
    Nat.sqrt (N / 2 - x * x) * Nat.sqrt (N / 2 - x * x) ≠ N / 2 - x * x
instance (N : ℕ) : Decidable (NHSqChkSq N) := by unfold NHSqChkSq; infer_instance

/-- divisor-pair covering lemma (O(sqrt K) loops) -/
theorem cover_divisors (K : ℕ) (hK : 0 < K) (Q : ℕ → Prop)
    (h : ∀ d ≤ Nat.sqrt K, 0 < d → d ∣ K → Q d ∧ Q (K / d)) (m : ℕ) (hm : m ∣ K) : Q m := by
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm hK
  by_cases hs : m ≤ Nat.sqrt K
  · exact (h m hs hm0 hm).1
  · push Not at hs
    obtain ⟨d, hd⟩ := hm
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0; omega
      · exact h0
    have hKm : K < m * m := by
      have := Nat.lt_succ_sqrt K
      have h2 : Nat.succ (Nat.sqrt K) ≤ m := hs
      calc K < Nat.succ (Nat.sqrt K) * Nat.succ (Nat.sqrt K) := this
        _ ≤ m * m := Nat.mul_le_mul h2 h2
    have hdm : d < m := by
      by_contra hge
      push Not at hge
      have : m * m ≤ m * d := Nat.mul_le_mul_left m hge
      omega
    have hdK : d ∣ K := ⟨m, by rw [hd, Nat.mul_comm]⟩
    have hds : d ≤ Nat.sqrt K := by
      apply Nat.le_sqrt.mpr
      calc d * d ≤ m * d := Nat.mul_le_mul_right d hdm.le
        _ = K := hd.symm
    have hdiv : K / d = m := by rw [hd, Nat.mul_comm, Nat.mul_div_cancel_left m hd0]
    have := (h d hds hd0 hdK).2
    rwa [hdiv] at this

/-- body of `E60Irr.Pairs60ChkSq N []` at `m` -/
def Q60 (N m : ℕ) : Prop :=
  m ≤ N → 1 ≤ m → m ∣ 3 * N → 3 * N / m ≤ N → 3 * N / m < m →
    (m = N ∧ 3 * N / m = 3) ∨ (m % 2 ≠ N % 2 ∨ (3 * N / m) % 2 ≠ N % 2) ∨
    (16 * N ≤ (m + 3 * N / m) ^ 2 → ¬ sqChk ((m + 3 * N / m) ^ 2 - 16 * N))
/-- body of `E120Irr.Pairs120ChkSq N []` at `m` -/
def Q120 (N m : ℕ) : Prop :=
  m ≤ N → 1 ≤ m → m ∣ 3 * N → 3 * N / m ≤ N →
    (m % 2 ≠ N % 2 ∨ (3 * N / m) % 2 ≠ N % 2) ∨
    ¬ sqChk ((m + 3 * N / m) ^ 2 + 16 * N - 4 * (3 * N))
def Pairs60R (N : ℕ) : Prop := ∀ d ≤ Nat.sqrt (3 * N), 0 < d → d ∣ 3 * N → Q60 N d ∧ Q60 N (3 * N / d)
def Pairs120R (N : ℕ) : Prop := ∀ d ≤ Nat.sqrt (3 * N), 0 < d → d ∣ 3 * N → Q120 N d ∧ Q120 N (3 * N / d)
instance (N : ℕ) : Decidable (Pairs60R N) := by unfold Pairs60R Q60 sqChk; infer_instance
instance (N : ℕ) : Decidable (Pairs120R N) := by unfold Pairs120R Q120 sqChk; infer_instance
/-- LeafFixE.lean:21 with the divisor-pair forms -/
def LeafEsqSR (N : ℕ) : Prop := N % 4 = 2 ∨ (11 ≤ N ∧ Pairs60R N ∧ Pairs120R N)
instance (N : ℕ) : Decidable (LeafEsqSR N) := by unfold LeafEsqSR; infer_instance

/-- NSQMS5W.lean:24 -/
def WordN (t e f : ℕ) : Prop :=
  ∃ z < t * e * (f * f - e * e) / (f * f) + 1, f ≤ z ∧
    ∃ y < t * e * (f * f - e * e) / (f * f - e * e) + 1,
      z * (f * f) + y * (f * f - e * e) ≤ t * e * (f * f - e * e) ∧
      e * f ∣ t * e * (f * f - e * e) - z * (f * f) - y * (f * f - e * e)
instance (t e f : ℕ) : Decidable (WordN t e f) := by unfold WordN; infer_instance

/-- NSQWin2.lean:78 -/
def S5wChkW (N : ℕ) : Prop :=
  ∀ t ≤ Nat.sqrt N, 2 ≤ t → t * t ∣ N → ∀ a ≤ Nat.sqrt (N / (t * t)), a ∣ N / (t * t) → 0 < a → a < N / (t * t) / a →
    a % 2 = (N / (t * t) / a) % 2 →
    Nat.Coprime ((N / (t * t) / a - a) / 2) ((a + N / (t * t) / a) / 2) →
    ¬ WordN t ((N / (t * t) / a - a) / 2) ((a + N / (t * t) / a) / 2)
instance (N : ℕ) : Decidable (S5wChkW N) := by unfold S5wChkW; infer_instance

/-- ThmCPair.lean:68 -/
def Gd (M M' : ℕ) : ℕ := Nat.gcd (M' - M) (M' + M)
/-- ThmDPair.lean:15 -/
def thmDChk (M M' : ℕ) : Prop :=
  2 ≤ Gd M M' / 2 ∧ (Gd M M' / 2 - 1) * (2 * M / Gd M M') < (M' - M) / Gd M M'
instance (M M' : ℕ) : Decidable (thmDChk M M') := by unfold thmDChk; infer_instance
/-- NSQWin2.lean:97 -/
def GammaChkDW (N : ℕ) : Prop :=
  ∀ M ≤ Nat.sqrt N, 0 < M → M ∣ N → 3 * M < N / M → M % 2 = N % 2 → (N / M) % 2 = N % 2 →
    Nat.Coprime (((N / M) - M) / 2) N ∨ (M = 2 ∧ (N / M) % 4 = 2 ∧ 3 ≤ (N / M) / 4) ∨ thmDChk M (N / M)
instance (N : ℕ) : Decidable (GammaChkDW N) := by unfold GammaChkDW; infer_instance

/-- NSQWin2.lean:116 -/
def F1ChkParW (N : ℕ) : Prop :=
  ∀ a ≤ Nat.sqrt N, 1 < a → a * a < N → a ∣ N → a % 2 = N % 2 → (N / a) % 2 = N % 2 →
    a + 2 ≤ N / a ∧ (N / a - a) % 2 = 0 ∧ ¬ sqChk ((a + N / a) ^ 2 + 12 * N) ∧
      a * a + (N / a) * (N / a) ≠ 4 * a * (N / a)
instance (N : ℕ) : Decidable (F1ChkParW N) := by unfold F1ChkParW sqChk; infer_instance

/-- AllNExclusionArith2.lean:45-47, 99 -/
def s2A (p q : ℕ) : ℕ := 2 * (q * q) - p * p
def s2B (p q : ℕ) : ℕ := 3 * (q * q) - p * p
def s2X (N p q : ℕ) : ℕ := N * ((q - p) * (2 * q + p)) ^ 2
def S2ChkSq (N : ℕ) : Prop :=
  ∀ q ≤ Nat.sqrt (4 * N), q * q < 4 * N → ∀ p < q, 0 < p → Nat.gcd p q = 1 → s2A p q ∣ 4 * N →
    ¬ (s2A p q * s2B p q ∣ s2X N p q ∧
       sqChk (s2X N p q / (s2A p q * s2B p q)))
instance (N : ℕ) : Decidable (S2ChkSq N) := by unfold S2ChkSq s2A s2B s2X sqChk; infer_instance

/-- LeafFixS3.lean:124 -/
def S3newChk (N : ℕ) : Prop :=
  ∀ f ≤ Nat.sqrt N, 2 ≤ f → f * f * f ≤ N → ∀ e < f, 1 ≤ e → Nat.Coprime e f →
    (f * f - e * e) * (2 * f * f - e * e) ∣ N →
    ¬ (Nat.sqrt (N / ((f * f - e * e) * (2 * f * f - e * e))) * Nat.sqrt (N / ((f * f - e * e) * (2 * f * f - e * e)))
        = N / ((f * f - e * e) * (2 * f * f - e * e)))
instance (N : ℕ) : Decidable (S3newChk N) := by unfold S3newChk; infer_instance

/-- AllNExclusionArith.lean:206 -/
def IsoBad (N a b : ℕ) : Prop :=
  Nat.sqrt (a ^ 2 + a * b + b ^ 2) * Nat.sqrt (a ^ 2 + a * b + b ^ 2) = a ^ 2 + a * b + b ^ 2 ∧
  Nat.sqrt (b * (N / (a + 2 * b))) * Nat.sqrt (b * (N / (a + 2 * b))) = b * (N / (a + 2 * b)) ∧
  ((Nat.sqrt (b * (N / (a + 2 * b))) : ℤ) * ((Nat.sqrt (a ^ 2 + a * b + b ^ 2) : ℤ) - a - b)) % b = 0 ∧
  ((((Nat.sqrt (b * (N / (a + 2 * b))) : ℤ) * ((Nat.sqrt (a ^ 2 + a * b + b ^ 2) : ℤ) - a - b)) / b - N) % 2 = 0)
instance (N a b : ℕ) : Decidable (IsoBad N a b) := by unfold IsoBad; infer_instance
/-- NSQWin3.lean:74, 80 -/
def IsoQ (N e : ℕ) : Prop :=
  e < N → 3 ≤ e → ∀ k ≤ Nat.sqrt (N / 2), N / e ∣ k * k → 0 < k * k / (N / e) → 2 * (k * k / (N / e)) < e →
    Nat.gcd (k * k / (N / e)) e = 1 → ¬ IsoBad N (e - 2 * (k * k / (N / e))) (k * k / (N / e))
instance (N e : ℕ) : Decidable (IsoQ N e) := by unfold IsoQ; infer_instance
def IsoH9bChkW (N : ℕ) : Prop :=
  ∀ d ≤ Nat.sqrt N, 0 < d → d ∣ N → IsoQ N d ∧ IsoQ N (N / d)
instance (N : ℕ) : Decidable (IsoH9bChkW N) := by unfold IsoH9bChkW; infer_instance

/-- AllNExclusionArith2.lean:272, AllN3Cond.lean:74, AllNExclusionArith2.lean:260 -/
def NoF2ChkSq (N : ℕ) : Prop :=
  (∀ z ≤ Nat.sqrt N, 3 * (z * z) ≠ N) ∧
  (∀ x ≤ Nat.sqrt N, 0 < x → x * x ≤ N → ∀ r ≤ Nat.sqrt N, 0 < r → r * r ≤ N →
    N = (x + r) * (2 * x + r) →
    ¬ ((N + x * x) % 3 = 0 ∧
      Nat.sqrt ((N + x * x) / 3) * Nat.sqrt ((N + x * x) / 3) = (N + x * x) / 3))
instance (N : ℕ) : Decidable (NoF2ChkSq N) := by unfold NoF2ChkSq; infer_instance
def NoF3zChkSq (N : ℕ) : Prop :=
  ∀ j ≤ Nat.sqrt N, 0 < j → j * j ≤ N → ∀ s ≤ Nat.sqrt (2 * N), j < s → s * s ≤ 2 * N →
    4 * N = 3 * (s + j) * (s + 3 * j) →
    ¬ ((s * s + 3 * (j * j)) % 4 = 0 ∧
        Nat.sqrt ((s * s + 3 * (j * j)) / 4) * Nat.sqrt ((s * s + 3 * (j * j)) / 4) =
          (s * s + 3 * (j * j)) / 4)
instance (N : ℕ) : Decidable (NoF3zChkSq N) := by unfold NoF3zChkSq; infer_instance
def NoF4zChkSq (N : ℕ) : Prop :=
  ∀ x ≤ Nat.sqrt N, 0 < x → x * x ≤ N → ∀ r ≤ Nat.sqrt N, 0 < r → r * r ≤ N →
    N = (x + r) * (2 * x + r) →
    Nat.sqrt (x * x + x * r + r * r) * Nat.sqrt (x * x + x * r + r * r) ≠ x * x + x * r + r * r
instance (N : ℕ) : Decidable (NoF4zChkSq N) := by unfold NoF4zChkSq; infer_instance

/-- S1BandLeaf.lean:295 -/
def S1UBChkW (N : ℕ) : Prop :=
  ∀ t ≤ Nat.sqrt N, 2 ≤ t → t * t ∣ N → ∀ q ≤ Nat.sqrt (N / (t * t)), N / (t * t) ≤ 3 * q * q →
    ¬ (sqChk (3 * q * q - N / (t * t)) ∧ 0 < Nat.sqrt (3 * q * q - N / (t * t)) ∧
       Nat.sqrt (3 * q * q - N / (t * t)) < q ∧ Nat.Coprime (Nat.sqrt (3 * q * q - N / (t * t))) q ∧
       q ≤ 2 * t * Nat.sqrt (3 * q * q - N / (t * t)) ∧
       ¬ (Nat.sqrt (3 * q * q - N / (t * t)) = 1 ∧ q = 2 * t) ∧
       ¬ (2 ≤ Nat.sqrt (3 * q * q - N / (t * t)) ∧
          (2 * t * Nat.sqrt (3 * q * q - N / (t * t)) ≤ q + 2 ∨
           2 * t * Nat.sqrt (3 * q * q - N / (t * t)) < q + Nat.sqrt (3 * q * q - N / (t * t)))))
instance (N : ℕ) : Decidable (S1UBChkW N) := by unfold S1UBChkW sqChk; infer_instance

/-- WGapLink2.lean RWChkW -/
def RWChkWl (N : ℕ) : Prop :=
  ∀ s ≤ Nat.sqrt N, 2 ≤ s → s * s ∣ N → ∀ f ≤ Nat.sqrt (N / (s * s)), N / (s * s) ≤ 2 * f * f →
    ¬ (sqChk (2 * f * f - N / (s * s)) ∧ 0 < Nat.sqrt (2 * f * f - N / (s * s)) ∧
       Nat.sqrt (2 * f * f - N / (s * s)) < f ∧ Nat.Coprime (Nat.sqrt (2 * f * f - N / (s * s))) f ∧
       f ≤ s * Nat.sqrt (2 * f * f - N / (s * s)) ∧
       ¬ (2 ≤ Nat.sqrt (2 * f * f - N / (s * s)) ∧ s * (f - Nat.sqrt (2 * f * f - N / (s * s))) < f))
instance (N : ℕ) : Decidable (RWChkWl N) := by unfold RWChkWl sqChk; infer_instance

def CNzFixP (N : ℕ) : Prop :=
  NQChkW N ∧ (EllChk2 N ∨ AsqChk N) ∧ NSqChkSq N ∧ HArithChkSq N ∧
    (N % 2 = 1 ∨ (N % 2 = 0 ∧ NHSqChkSq N)) ∧ LeafEsqSR N ∧ (N % 4 = 2 ∨ F1ChkParW N) ∧ S2ChkSq N ∧ S3newChk N ∧ IsoH9bChkW N ∧
    (NoF2ChkSq N ∧ NoF3zChkSq N ∧ NoF4zChkSq N) ∧ GammaChkDW N ∧ S1UBChkW N ∧ RWChkWl N ∧ S5wChkW N
instance (N : ℕ) : Decidable (CNzFixP N) := by unfold CNzFixP; infer_instance

end Erdos634.Draft.WGapPure
