/-
Draft/E60Parity.lean: the parity clause (E4) of `Row5.theoremE_sixty` / `Row5.theoremE_twoPiThree` as a pair kill.

`Row5.theoremE_sixty` gives, for a `π/3` tile on an equilateral target, the pair `(m₁, m₂)` with `m₁ m₂ = 3N` and
`m₁ ≡ m₂ ≡ N (mod 2)`.  The pair tables `E60Cert.Pairs60ChkExc` and `AllNExclusion.Pairs120Chk` do not use the
parity, so they leave pairs that no dissection has: `(52, 9)` and `(39, 12)` of `N = 156`, both pairs of `N = 198`,
the `2π/3` pair `(13, 36)` of `N = 156`.

* `e60Pair_of_parity`: a pair violating the parity is not the pair of any dissection (`E60Pair N m₁ m₂`).
* `gapE120_of_pairs_par`, `Pairs120ChkP`, `gapE120_of_chkP`: the `2π/3` pair table restricted to pairs of the right
  parity.

No sorry, no native_decide.
-/
import Erdos634.Draft.E60Cert

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.E60Parity

open Erdos634.Draft.AllNExclusion

/-- `Pairs120Chk` restricted to the pairs with `s ≡ t ≡ N (mod 2)` -/
def Pairs120ChkP (N : ℕ) : Prop :=
  ∀ s ≤ N, 1 ≤ s → s ∣ 3 * N → 3 * N / s ≤ N →
    (s % 2 ≠ N % 2 ∨ (3 * N / s) % 2 ≠ N % 2) ∨
    (¬ sqChk ((s + 3 * N / s) ^ 2 + 4 * N) ∧ ¬ (s + 3 * N / s ∣ 2 * N))

instance (N : ℕ) : Decidable (Pairs120ChkP N) := by unfold Pairs120ChkP sqChk; infer_instance

/-- counterexample to the table: at `N = 15` the rational pair `(5, 9)` has the right parity and survives
(`GapE120Dis.gapE120_15` closes it by a certificate), so the parity table is false there -/
example : ¬ Pairs120ChkP 15 := by decide +kernel

end Erdos634.Draft.E60Parity

open scoped Classical
open Erdos634.Geometry
open Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeE5Gen
open Erdos634.Draft.AllNExclusion

namespace Erdos634.Draft.E60Parity

/-- **Parity kill, `π/3`.**  A pair with `m₁ ≢ N` or `m₂ ≢ N (mod 2)` is not the pair of any dissection: the pair
of a dissection is determined by the side equations, and `Row5.theoremE_sixty` (E4) gives its parity. -/
theorem e60Pair_of_parity (N : ℕ) (m₁ m₂ : ℤ)
    (hpar : ¬ (2 : ℤ) ∣ m₁ - N ∨ ¬ (2 : ℤ) ∣ m₂ - N) : E60Pair N m₁ m₂ := by
  intro D α a b c hα h hE hS1 hS2
  obtain ⟨n₁, n₂, h1, h2, -, -, -, -, hT1, hT2, -, -, -, -⟩ := Row5.theoremE_sixty D hα h hE
  have hS : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have e1 : m₁ = n₁ := by
    have hne : a + b - c ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hT1; linarith
    have : (m₁ : ℝ) = n₁ := mul_right_cancel₀ hne (hS1.trans hT1.symm)
    exact_mod_cast this
  have e2 : m₂ = n₂ := by
    have hne : a + b + c ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hT2; linarith
    have : (m₂ : ℝ) = n₂ := mul_right_cancel₀ hne (hS2.trans hT2.symm)
    exact_mod_cast this
  subst e1; subst e2
  rcases hpar with hp | hp
  · exact hp h1
  · exact hp h2

/-- **`GapE120 N` from the pair table, pairs of the right parity only** (`gapE120_of_pairs` keeping E4). -/
theorem gapE120_of_pairs_par (N : ℕ) (hN : 0 < N)
    (hpairs : ∀ s t : ℤ, 1 ≤ s → s ≤ N → 1 ≤ t → t ≤ N → s * t = 3 * (N : ℤ) →
      (2 : ℤ) ∣ s - N → (2 : ℤ) ∣ t - N →
      ¬ IsSquare ((t - s) ^ 2 + 16 * (N : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * (N : ℤ) ≠ r * (s + t)) : GapE120 N := by
  intro D α a b c hα h hE
  obtain ⟨s, t, hp1, hp2, hs1, hsN, ht1, htN, hS1, hS2, harea, hprod, -⟩ := Row5.theoremE_twoPiThree D hα h hE
  obtain ⟨p, q, r, hpqr⟩ := Row5TwoPiThreeFull.side_decomposition D h
  obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0
    (fun k => D.model.data_angles_mem hα h 0 k) hE
  have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
    rw [← e2]; unfold Tri.oppLen; rfl
  rw [hd] at hpqr
  obtain ⟨hD, hno⟩ := hpairs s t hs1 hsN ht1 htN hprod hp1 hp2
  exact twoPiThree_side_kill (N := N) (a := a) (b := b) (c := c) (S := D.target.oppLen 0) s t hN hS1 hS2 harea hprod
    (D.target.oppLen_pos 0) (p : ℤ) (q : ℤ) (r : ℤ) (by positivity) (by positivity)
    (by rw [hpqr]; push_cast; ring) hD (hno (r : ℤ) (by positivity))

theorem gapE120_of_chkP {N : ℕ} (hN : 0 < N) (h : Pairs120ChkP N) : GapE120 N := by
  refine gapE120_of_pairs_par N hN ?_
  intro s t h1 h2 h3 h4 hp hs2 ht2
  lift s to ℕ using (by omega)
  lift t to ℕ using (by omega)
  have hp' : s * t = 3 * N := by exact_mod_cast hp
  have hs1 : 1 ≤ s := by exact_mod_cast h1
  have hsN : s ≤ N := by exact_mod_cast h2
  have htN : t ≤ N := by exact_mod_cast h4
  have hdvd : s ∣ 3 * N := ⟨t, hp'.symm⟩
  have hdiv : 3 * N / s = t := by rw [← hp']; exact Nat.mul_div_cancel_left _ hs1
  have hall := h s hsN hs1 hdvd (by rw [hdiv]; exact htN)
  rw [hdiv] at hall
  rcases hall with hpar | ⟨hA, hB⟩
  · exfalso
    rcases hpar with hpar | hpar
    · omega
    · omega
  refine ⟨not_isSquare_of_chk ((s + t) ^ 2 + 4 * N) _ ?_ hA, ?_⟩
  · push_cast; nlinarith [hp]
  · intro r hr hcon
    apply hB
    lift r to ℕ using hr
    exact ⟨r, by have : (2 * N : ℤ) = r * (s + t) := by exact_mod_cast hcon
                 have : 2 * N = r * (s + t) := by exact_mod_cast this
                 linarith⟩

/-- the `2π/3` leaf of `N = 156`: the only pair left by the arithmetic, `(13, 36)`, has the wrong parity -/
theorem gapE120_156 : GapE120 156 := gapE120_of_chkP (by norm_num) (by decide +kernel)

end Erdos634.Draft.E60Parity

#print axioms Erdos634.Draft.E60Parity.e60Pair_of_parity
#print axioms Erdos634.Draft.E60Parity.gapE120_of_chkP
#print axioms Erdos634.Draft.E60Parity.gapE120_156
