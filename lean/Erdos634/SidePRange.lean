import Erdos634.SideNoB
import Erdos634.TilePlacement

/-!
# The arithmetic core of the `c`-corner side lemma

If a corner tile lays `c` on the base it lays `a` on the side, so that side's `a`-count `P'` is
positive; by quantization `P'=fp`, hence `P'≥f`, and with `pe+R'=f` and the `γ`-trap `R'≥1` one gets
`1≤p≤(f-1)/e`.

`SideNoB.side_a_quantized` gives the `P'=fp` quantization from the raw `f³`-scale walk.
`TilePlacement.p_bounds`/`.p_le_of_bounds` give the bound from the level equation. This file
derives the level equation `p·e+R'=f` itself from the quantized walk, and assembles the chain from
`P>0` through to `1≤p≤(f-1)/e` (`side_p_range`).

Not covered here: that a real corner tile's forced `a`-edge (`c_corner_side_a`, a single-triangle
edge-length fact) contributes to the side's walk count `P` of a real `CongruentDissection`, i.e.
`P > 0` for the dissection's own side walk rather than as a named hypothesis. This is a
tile-placement question (identifying the corner tile's edge with a specific chain entry, per
`WallEndpoints.chain_starts_at_a`).

Axiom-clean; no `sorry`.
-/

open Erdos634.SideNoB Erdos634.TilePlacement

/-- **`lem:ccornerside`'s arithmetic core.** On a side whose `a`-count `P` is positive, the
parameter `p` (with `P = f·p`) satisfies `1 ≤ p ≤ (f-1)/e`. -/
theorem side_p_range {e f P Q R : ℕ} (hco : Nat.Coprime e f) (hef : e < f)
    (b : ℕ) (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) (he : 1 ≤ e) (hPpos : 0 < P) :
    ∃ p, P = f * p ∧ 1 ≤ p ∧ p ≤ (f - 1) / e := by
  have hf : 0 < f := by omega
  have hQ0 : Q = 0 := side_no_b_uncond hco hef hb hwalk hgamma
  subst hQ0
  simp only [Nat.zero_mul, Nat.add_zero] at hwalk
  have hkey : f * (P * e + R * f) = f * (f * f) := by
    have h1 : f * (P * e + R * f) = P * (e * f) + R * (f * f) := by ring
    rw [h1, hwalk]; ring
  have hred : P * e + R * f = f * f := Nat.eq_of_mul_eq_mul_left hf hkey
  have hfP : f ∣ P := side_quantized hf hco hred
  obtain ⟨p, hp⟩ := hfP
  refine ⟨p, hp, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos p with h0 | h1
    · exfalso; rw [hp, h0, Nat.mul_zero] at hPpos; exact absurd hPpos (lt_irrefl 0)
    · exact h1
  · have hlevel : p * e + R = f := by
      have : f * (p * e + R) = f * f := by
        rw [hp] at hred; nlinarith [hred]
      exact Nat.eq_of_mul_eq_mul_left hf this
    have hbound : p * e + 1 ≤ f := by omega
    exact p_le_of_bounds p e f he hbound
