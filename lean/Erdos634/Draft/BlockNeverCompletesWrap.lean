import Erdos634.BlockNeverCompletes

/-!
# A corner block never completes: wrapper

Re-exports results of `BlockNeverCompletes`:
- `run_stops_short`: L ≤ f−1 → L·f < f²
- `run_length_bound`: min p q − 1 ≤ f − 1
- `block_never_completes`: L ≤ f−1 → L ≠ f
- `every_corner_breaks`: if block doesn't complete then base or side break
- `at_most_one_base_break`: at most one base break
- `side_break_exists`: west ∨ east count ≤ 1 → one is false

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BlockNeverCompletesWrap

open Erdos634.BlockNeverCompletes

theorem bnc_run_stops_short (f L : ℕ) (hf : 2 ≤ f) (hL : L ≤ f - 1) : L * f < f ^ 2 :=
  run_stops_short f L hf hL

theorem bnc_run_length_bound (f p q : ℕ) (hq3 : 3 ≤ q) (hqf : q ≤ f) (hp2 : 2 ≤ p) :
    min p q - 1 ≤ f - 1 :=
  run_length_bound f p q hq3 hqf hp2

theorem bnc_block_never_completes (f L : ℕ) (hf : 2 ≤ f) (hL : L ≤ f - 1) : L ≠ f :=
  block_never_completes f L hf hL

theorem bnc_every_corner_breaks (completes baseBreak sideBreak : Prop)
    (htri : completes ∨ baseBreak ∨ sideBreak) (hno : ¬ completes) :
    baseBreak ∨ sideBreak :=
  every_corner_breaks completes baseBreak sideBreak htri hno

theorem bnc_at_most_one_base_break (breaks nc : ℕ) (hc : nc = 1) (hle : breaks ≤ nc) :
    breaks ≤ 1 :=
  at_most_one_base_break breaks nc hc hle

theorem bnc_side_break_exists (west east : Bool)
    (hcount : (if west then 1 else 0) + (if east then 1 else 0) ≤ 1) :
    west = false ∨ east = false :=
  side_break_exists west east hcount

-- Non-vacuity: block_never_completes with f=3, L=2
example : (2:ℕ) ≠ 3 := bnc_block_never_completes 3 2 (by norm_num) (by norm_num)

#print axioms bnc_run_stops_short
#print axioms bnc_every_corner_breaks

end Erdos634.Draft.BlockNeverCompletesWrap
