/-
Draft/WGapLightChunk.lean -- 16 November 2026 (work item internal working notes).  UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.
Range chunking for the bounded-search conjuncts of `CNzFixP2` (WGapLightPure2), so that one kernel `decide` never holds more than one chunk:
* `RangeAll lo hi p := forall i < hi - lo, p (lo + i)` (decidable for decidable `p`);
* `rangeAll_append`, `forall_le_of_rangeAll`  (consecutive chunks cover `[0, B]`);
* the conjuncts that are `forall x <= B, Q x` are restated with their loop body `Q` as a definition, with `*_of_Q : (forall x <= B, Q N x) -> conjunct N` (by definitional unfolding / `fun`),
  so that a chunk module proves `RangeAll lo hi (Q N)` by `decide +kernel` and a combiner module assembles.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLightPure2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.WGapPure

def RangeAll (lo hi : ℕ) (p : ℕ → Prop) : Prop := ∀ i < hi - lo, p (lo + i)

instance (lo hi : ℕ) (p : ℕ → Prop) [DecidablePred p] : Decidable (RangeAll lo hi p) := by
  unfold RangeAll; infer_instance

theorem rangeAll_append {lo mid hi : ℕ} {p : ℕ → Prop} (h1 : RangeAll lo mid p) (h2 : RangeAll mid hi p)
    (hlm : lo ≤ mid) (hmh : mid ≤ hi) : RangeAll lo hi p := by
  intro i hi'
  by_cases hc : i < mid - lo
  · exact h1 i hc
  · have := h2 (i - (mid - lo)) (by omega)
    have e : mid + (i - (mid - lo)) = lo + i := by omega
    rwa [e] at this

theorem rangeAll_empty {lo hi : ℕ} {p : ℕ → Prop} (h : hi ≤ lo) : RangeAll lo hi p := by
  intro i hi'; omega

theorem forall_le_of_rangeAll {B : ℕ} {p : ℕ → Prop} (h : RangeAll 0 (B + 1) p) : ∀ x ≤ B, p x := by
  intro x hx
  have := h x (by omega)
  simpa using this

/-! loop bodies of the chunked conjuncts -/

def NoF4zQ (N x : ℕ) : Prop :=
  0 < x → x * x ≤ N →
    0 < (Nat.sqrt (x * x + 4 * N) - 3 * x) / 2 → ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) ≤ N →
    N = (x + (Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * (2 * x + (Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) →
    Nat.sqrt (x * x + x * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) + ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2)) *
      Nat.sqrt (x * x + x * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) + ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2)) ≠
      x * x + x * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) + ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2) * ((Nat.sqrt (x * x + 4 * N) - 3 * x) / 2)
instance (N x : ℕ) : Decidable (NoF4zQ N x) := by unfold NoF4zQ; infer_instance
theorem noF4zS_of_Q {N : ℕ} (h : ∀ x ≤ Nat.sqrt N, NoF4zQ N x) : NoF4zS N := h

/-- S2 divisor loop body: `S2Q N A` is already `forall q <= sqrt(4N), body`; its body as a definition -/
def S2B (N A q : ℕ) : Prop :=
  q * q < 4 * N →
    Nat.sqrt (2 * (q * q) - A) * Nat.sqrt (2 * (q * q) - A) = 2 * (q * q) - A →
    Nat.sqrt (2 * (q * q) - A) < q → 0 < Nat.sqrt (2 * (q * q) - A) → Nat.gcd (Nat.sqrt (2 * (q * q) - A)) q = 1 →
    ¬ (s2A (Nat.sqrt (2 * (q * q) - A)) q * s2B (Nat.sqrt (2 * (q * q) - A)) q ∣ s2X N (Nat.sqrt (2 * (q * q) - A)) q ∧
       sqChk (s2X N (Nat.sqrt (2 * (q * q) - A)) q / (s2A (Nat.sqrt (2 * (q * q) - A)) q * s2B (Nat.sqrt (2 * (q * q) - A)) q)))
instance (N A q : ℕ) : Decidable (S2B N A q) := by unfold S2B s2A s2B s2X sqChk; infer_instance
theorem s2Q_of_B {N A : ℕ} (h : ∀ q ≤ Nat.sqrt (4 * N), S2B N A q) : S2Q N A := h

end Erdos634.Draft.WGapPure
