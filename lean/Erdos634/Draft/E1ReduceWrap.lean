import Erdos634.BaseBetaWalkArith
import Erdos634.BaseCountsE1

/-!
# The e=1 subfamily reduces to one walk: wrapper

At e=1, m=1, f≥3, in any hypothetical tiling:

(i) Neither equal side carries a b-edge; each equal side has nc≥2 c-edges.
(ii) The base carries exactly one b-edge and exactly one c-edge (the walls form (f,1,1)).

Lean content (the arithmetic spine):
1. **`e1reduce_equal_side_no_b`**: equal side arithmetic: nb=0 (BaseBetaWalkArith.equal_side_no_b
   with e=1, requires nc≥1 which gammatrap gives).
2. **`e1reduce_equal_side_shape`**: nb=0 forces na=fk, nc=f-k (equal_side_shape).
3. **`e1reduce_base_b_count`**: base arithmetic: nb=1 (base_b_count with e=1).
4. **`e1reduce_base_nc_one`**: base has nc=1 after nc=2 excluded via the corner parallelogram (BaseCountsE1.base_counts_corner).

No sorry, standard axioms.
-/

namespace Erdos634.Draft.E1ReduceWrap

open Erdos634.BaseBetaWalkArith Erdos634.BaseCountsE1

/-- thm:e1reduce (i, arithmetic): equal side carries no b-edge at e=1 (equal_side_no_b). -/
theorem e1reduce_equal_side_no_b (f b na nb nc : ℤ) (hf : 3 ≤ f)
    (hcop : IsCoprime 1 f)
    (hb : b + 1 ^ 2 = f ^ 2)
    (hna : 0 ≤ na) (hnb : 0 ≤ nb) (hnc : 1 ≤ nc)
    (hwalk : na * (1 * f) + nb * b + nc * f ^ 2 = f ^ 3) :
    nb = 0 := by
  apply equal_side_no_b 1 f b na nb nc (by norm_num) (by linarith) hcop hb _ hna hnb hnc hwalk
  nlinarith

/-- thm:e1reduce (i, shape): at e=1, nb=0 forces na=fk and nc=f-k on the equal side. -/
theorem e1reduce_equal_side_shape (f k na nc : ℤ) (hf : 1 < f) (hk : na = f * k)
    (hwalk : na * (1 * f) + nc * f ^ 2 = f ^ 3) :
    nc = f - k * 1 := by
  have : na * (1 * f) = na * f := by ring
  rw [this] at hwalk
  exact equal_side_shape 1 f k na nc (by norm_num) (by linarith) hk (by linarith)

/-- thm:e1reduce (ii, arithmetic): base carries exactly one b-edge at e=1 (base_b_count). -/
theorem e1reduce_base_nb_one (f b na nb nc : ℤ) (hf : 3 ≤ f)
    (hcop : IsCoprime 1 f)
    (hb : b + 1 ^ 2 = f ^ 2)
    (hna : 0 ≤ na) (hnb : 0 ≤ nb) (hnc : 1 ≤ nc)
    (hwalk : na * (1 * f) + nb * b + nc * f ^ 2 = 1 * (3 * f ^ 2 - 1 ^ 2)) :
    nb = 1 := by
  apply base_b_count 1 f b na nb nc (by norm_num) (by linarith) hcop hb _ hna hnb hnc hwalk
  nlinarith

/-- thm:e1reduce (ii, nc=1): with nc=2 excluded by cornerpara and nc≥1 from gammatrap,
    base has na=f, nc=1. (BaseCountsE1.base_counts_corner; nc≥1 is a hypothesis here.) -/
theorem e1reduce_base_nc_one (f na nc : ℤ) (hf : 3 ≤ f)
    (hna : 0 ≤ na) (hnc : 1 ≤ nc)
    (heq : na * f + 1 * (f ^ 2 - 1) + nc * f ^ 2 = 3 * f ^ 2 - 1)
    (hcorner : nc = 2 → False) :
    na = f ∧ nc = 1 := by
  have h := base_counts_corner f na 1 nc hf hna (by norm_num) (by linarith) heq hcorner
  obtain ⟨-, (hcase1 | hcase2)⟩ := h
  · exact hcase1
  · -- case nc=0: contradicts hnc (nc≥1 from gammatrap)
    exact absurd hcase2.2 (by omega)

#print axioms e1reduce_equal_side_no_b
#print axioms e1reduce_base_nb_one
#print axioms e1reduce_base_nc_one

end Erdos634.Draft.E1ReduceWrap
