/-
Draft/NSQWin4.lean -- CHUNKED forms of the five double-loop leaves of the windowed chain `CN'zETWD6` (`NSQWin3`): `S2ChkSq` (outer `q`), `S3ChkSq` (outer `e`),
`NoF2ChkSq` (`x`), `NoF3zChkSq` (`j`), `NoF4zChkSq` (`x`).  Each is `forall outer <= B, P outer` for a decidable predicate `P` (`S2P`, `S3P`, `F2P`, `F3zP`, `F4zP`);
`ChunkP P a b` says `P q` for `a <= q < b`; chunks append (`chunk_append`) and `ChunkP P 0 (B+1)` gives the leaf (`chunk_full`).  A per-value module then decides the
chunks in SEPARATE kernel declarations, so the kernel peak is one chunk, not the whole double loop.  All soundness lemmas hold for every `N`.
Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.NSQMain

def ChunkP (P : ℕ → Prop) (a b : ℕ) : Prop := ∀ q < b, a ≤ q → P q

instance (P : ℕ → Prop) [DecidablePred P] (a b : ℕ) : Decidable (ChunkP P a b) := by unfold ChunkP; infer_instance

theorem chunk_append {P : ℕ → Prop} {a b c : ℕ} (h1 : ChunkP P a b) (h2 : ChunkP P b c) : ChunkP P a c := by
  intro q hq haq
  by_cases h : q < b
  · exact h1 q h haq
  · exact h2 q hq (by omega)

theorem chunk_full {P : ℕ → Prop} {B : ℕ} (h : ChunkP P 0 (B + 1)) : ∀ q ≤ B, P q :=
  fun q hq => h q (by omega) (Nat.zero_le _)

def S2P (N q : ℕ) : Prop :=
  q * q < 4 * N → ∀ p < q, 0 < p → Nat.gcd p q = 1 → s2A p q ∣ 4 * N →
    ¬ (s2A p q * s2B p q ∣ s2X N p q ∧ sqChk (s2X N p q / (s2A p q * s2B p q)))
instance (N q : ℕ) : Decidable (S2P N q) := by unfold S2P s2A s2B s2X sqChk; infer_instance
theorem s2Sq_of_P {N : ℕ} (h : ∀ q ≤ Nat.sqrt (4 * N), S2P N q) : S2ChkSq N := fun q hq => h q hq

def S3P (N e : ℕ) : Prop :=
  1 ≤ e → e * e ≤ N →
  ∀ d ≤ Nat.sqrt (N / 2), 1 ≤ d → 2 * (d * d) ≤ N → qQ e d ∣ N →
    ¬ (kK e d ∣ N * d ∧ Nat.sqrt (N * d / kK e d) * Nat.sqrt (N * d / kK e d) = N * d / kK e d)
instance (N e : ℕ) : Decidable (S3P N e) := by unfold S3P qQ kK; infer_instance
theorem s3Sq_of_P {N : ℕ} (h : ∀ e ≤ Nat.sqrt N, S3P N e) : S3ChkSq N := fun e he => h e he

def F4zP (N x : ℕ) : Prop :=
  0 < x → x * x ≤ N → ∀ r ≤ Nat.sqrt N, 0 < r → r * r ≤ N →
    N = (x + r) * (2 * x + r) →
    Nat.sqrt (x * x + x * r + r * r) * Nat.sqrt (x * x + x * r + r * r) ≠ x * x + x * r + r * r
instance (N x : ℕ) : Decidable (F4zP N x) := by unfold F4zP; infer_instance
theorem f4zSq_of_P {N : ℕ} (h : ∀ x ≤ Nat.sqrt N, F4zP N x) : NoF4zChkSq N := fun x hx => h x hx

def F2P (N x : ℕ) : Prop :=
  0 < x → x * x ≤ N → ∀ r ≤ Nat.sqrt N, 0 < r → r * r ≤ N →
    N = (x + r) * (2 * x + r) →
    ¬ ((N + x * x) % 3 = 0 ∧
      Nat.sqrt ((N + x * x) / 3) * Nat.sqrt ((N + x * x) / 3) = (N + x * x) / 3)
instance (N x : ℕ) : Decidable (F2P N x) := by unfold F2P; infer_instance
def F2z (N : ℕ) : Prop := ∀ z ≤ Nat.sqrt N, 3 * (z * z) ≠ N
instance (N : ℕ) : Decidable (F2z N) := by unfold F2z; infer_instance
theorem f2Sq_of_P {N : ℕ} (h0 : F2z N) (h : ∀ x ≤ Nat.sqrt N, F2P N x) : NoF2ChkSq N := ⟨h0, fun x hx => h x hx⟩

def F3zP (N j : ℕ) : Prop :=
  0 < j → j * j ≤ N → ∀ s ≤ Nat.sqrt (2 * N), j < s → s * s ≤ 2 * N →
    4 * N = 3 * (s + j) * (s + 3 * j) →
    ¬ ((s * s + 3 * (j * j)) % 4 = 0 ∧
        Nat.sqrt ((s * s + 3 * (j * j)) / 4) * Nat.sqrt ((s * s + 3 * (j * j)) / 4) =
          (s * s + 3 * (j * j)) / 4)
instance (N j : ℕ) : Decidable (F3zP N j) := by unfold F3zP; infer_instance
theorem f3zSq_of_P {N : ℕ} (h : ∀ j ≤ Nat.sqrt N, F3zP N j) : NoF3zChkSq N := fun j hj => h j hj

/-- `AsqChk` with `s <= sqrt N`; ordered FIRST so that `N = 15 s^2`, `30 s^2` never runs the O(N) prime search of `EllChk2` to exhaustion. -/
def AsqChkW (N : ℕ) : Prop := ∃ s ≤ Nat.sqrt N, 0 < s ∧ (N = 15 * (s * s) ∨ N = 30 * (s * s))
instance (N : ℕ) : Decidable (AsqChkW N) := by unfold AsqChkW; infer_instance
def EllOrAsqW (N : ℕ) : Prop := AsqChkW N ∨ EllChk2 N
instance (N : ℕ) : Decidable (EllOrAsqW N) := by unfold EllOrAsqW; infer_instance
theorem ellAsq_of_W {N : ℕ} (h : EllOrAsqW N) : EllChk2 N ∨ AsqChk N := by
  rcases h with ⟨s, hs, h0, hd⟩ | h
  · exact Or.inr ⟨s, le_trans hs (Nat.sqrt_le_self N), h0, hd⟩
  · exact Or.inl h

/-- an explicit witness form of `EllChk2` with the primality test windowed to `m <= sqrt l`. -/
def EllAt (N l : ℕ) : Prop :=
  l ≤ N ∧ 7 ≤ l ∧ l ∣ N ∧ ¬ l * l ∣ N ∧ ∀ m ≤ Nat.sqrt l, 2 ≤ m → ¬ m ∣ l
instance (N l : ℕ) : Decidable (EllAt N l) := by unfold EllAt; infer_instance
theorem ellChk2_of_at {N l : ℕ} (h : EllAt N l) : EllChk2 N := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hp : l.Prime := Nat.prime_def_le_sqrt.mpr ⟨by omega, fun m hm hms => h5 m hms hm⟩
  refine ⟨l, h1, h2, h3, h4, fun m hm hd => ?_⟩
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact h
  · omega

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.chunk_full
#print axioms Erdos634.Draft.NSQM.f2Sq_of_P
