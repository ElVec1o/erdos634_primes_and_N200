import Erdos634.LadderInvariant

/-!
# LadderInvariant — ladder step identity and march bounds: wrapper

Key results:
- `flush_overrun_mem`: apex lies on the c-edge segment
- `flush_split_lengths`: split distances
- `flush_overrun_unit`: unit direction overrun is exactly c−b
- `ladder_step_identity`: apex lands at distance exactly b from next pin
- `march_bounded`: march block count is at most L/a
- `terminal_kill`: terminal stub equation x·f + y·(f²−1) + z·f² = 1 is impossible

No sorry; standard axioms.
-/

namespace Erdos634.Draft.LadderInvariantWrap

open Erdos634.LadderInvariant Erdos634.Geometry

theorem li_flush_overrun_mem (P : Plane) (u : Plane) (b c : ℝ)
    (hb : 0 ≤ b) (hbc : b ≤ c) :
    P + b • u ∈ segment ℝ P (P + c • u) :=
  flush_overrun_mem P u b c hb hbc

theorem li_flush_split_lengths (P : Plane) (u : Plane) (b c : ℝ)
    (hb : 0 ≤ b) (hbc : b ≤ c) :
    dist (P + b • u) (P + c • u) = (c - b) * ‖u‖ ∧
    dist P (P + b • u) = b * ‖u‖ :=
  flush_split_lengths P u b c hb hbc

theorem li_flush_overrun_unit (P : Plane) (u : Plane) (hu : ‖u‖ = 1) (b c : ℝ)
    (hb : 0 ≤ b) (hbc : b ≤ c) :
    dist (P + b • u) (P + c • u) = c - b :=
  flush_overrun_unit P u hu b c hb hbc

theorem li_ladder_step_identity (a b c w₁ w₂ : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hunit : w₁ ^ 2 + w₂ ^ 2 = 1) (hcos : 2 * a * c * w₁ = a ^ 2 + c ^ 2 - b ^ 2) :
    (c * w₁ - a) ^ 2 + (c * w₂) ^ 2 = b ^ 2 :=
  ladder_step_identity a b c w₁ w₂ ha hc hunit hcos

theorem li_march_bounded (a L x₀ : ℕ) (ha : 0 < a) (k : ℕ) (hin : x₀ + k * a ≤ L) :
    k ≤ L / a :=
  march_bounded a L x₀ ha k hin

theorem li_terminal_kill (f x y z : ℕ) (hf : 2 ≤ f)
    (hcover : x * f + y * (f ^ 2 - 1) + z * f ^ 2 = 1) : False :=
  terminal_kill f x y z hf hcover

-- Non-vacuity: march_bounded gives a concrete bound
example : 2 ≤ 10 / 3 := li_march_bounded 3 10 1 (by norm_num) 2 (by norm_num)

#print axioms li_ladder_step_identity
#print axioms li_terminal_kill

end Erdos634.Draft.LadderInvariantWrap
