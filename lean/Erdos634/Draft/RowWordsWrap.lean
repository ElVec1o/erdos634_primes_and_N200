import Erdos634.Inflation
import Erdos634.SideNoB
import Erdos634.RogueMirror

/-!
# Boundary words at scale k: wrapper

For `k < f` the three side words of `Δ_k` are forced outright:
the base reads `b^k` (`Inflation.b_side_rigid`), the a-side reads `a^k` (`Inflation.a_side_rigid`),
and the c-side carries no b-edge (`Inflation.c_side_no_b`). At the wall scale `k = f` the same
three readings hold: the c-side by the γ-trap (`SideNoB.side_no_b_uncond`), the base by the
corner coupling (`RogueMirror.wall_base_reading`), and the a-side is `a^f` or `c^e`
(`Inflation.a_side_words`; the c^e branch is the transverse configuration).

Lean content:
1. **`rowwords_b_side`**: base side of Δ_k is b^k for k < f (`Inflation.b_side_rigid`).
2. **`rowwords_a_side`**: a-side of Δ_k is a^k for k < f (`Inflation.a_side_rigid`).
3. **`rowwords_c_side_no_b`**: c-side of Δ_k carries no b-edge for k < f (`Inflation.c_side_no_b`).
4. **`rowwords_c_side_uncond`**: c-side has no b-edge unconditionally (`SideNoB.side_no_b_uncond`).
5. **`rowwords_wall_base`**: at k = f the base reads b^f (`RogueMirror.wall_base_reading`).
6. **`rowwords_a_side_words`**: a-side word is a^{k−qf} c^{qe} at wall scale (`Inflation.a_side_words`).

The statements are arithmetic and side-word statements; the Δ_k occurrence is not defined as a placed region here.
0 sorry, standard axioms.
-/

namespace Erdos634.Draft.RowWordsWrap

open Erdos634.Inflation Erdos634.SideNoB Erdos634.RogueMirror

/-- lem:rowwords (base): the base side of Δ_k is b^k for k < f (Inflation.b_side_rigid). -/
theorem rowwords_b_side (e f b k na nb nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hb : b + e ^ 2 = f ^ 2) (hco : Nat.Coprime e f) (hkf : k < f)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = k * b) :
    na = 0 ∧ nb = k ∧ nc = 0 :=
  b_side_rigid e f b k na nb nc he hef hco hb hkf heq

/-- lem:rowwords (a-side): the a-side of Δ_k is a^k for k < f (Inflation.a_side_rigid). -/
theorem rowwords_a_side (e f k na nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hkf : k < f)
    (heq : na * (e * f) + nc * f ^ 2 = k * (e * f)) :
    na = k ∧ nc = 0 :=
  a_side_rigid e f k na nc he hef hcop hkf heq

/-- lem:rowwords (c-side, k < f): c-side of Δ_k carries no b-edge (Inflation.c_side_no_b). -/
theorem rowwords_c_side_no_b (e f b k na nb nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hb : b + e ^ 2 = f ^ 2) (hco : Nat.Coprime e f) (hkf : k < f)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = k * f ^ 2) :
    nb = 0 :=
  c_side_no_b e f b k na nb nc he hef hco hb hkf heq

/-- lem:rowwords (c-side, unconditional): c-side has no b-edge for any k (SideNoB.side_no_b_uncond). -/
theorem rowwords_c_side_uncond (e f b P Q R : ℕ) (hco : Nat.Coprime e f) (hef : e < f)
    (hb : b + e * e = f * f) (hgamma : 1 ≤ R)
    (heq : P * (e * f) + Q * b + R * (f * f) = f * f * f) :
    Q = 0 :=
  side_no_b_uncond hco hef hb heq hgamma

/-- lem:rowwords (wall base): at k = f the base reads b^f (RogueMirror.wall_base_reading). -/
theorem rowwords_wall_base (e f b na nb nc P Q R : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hb : b + e ^ 2 = f ^ 2) (hco : Nat.Coprime e f)
    (hbase : na * (e * f) + nb * b + nc * f ^ 2 = f * b)
    (hcside : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) (hflank : 1 ≤ nb ∨ 1 ≤ Q) :
    na = 0 ∧ nb = f ∧ nc = 0 :=
  wall_base_reading e f b na nb nc P Q R he hef hco hb hbase hcside hgamma hflank

/-- lem:rowwords (a-side words): a-side word at wall scale (Inflation.a_side_words). -/
theorem rowwords_a_side_words (e f k na nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f)
    (heq : na * (e * f) + nc * f ^ 2 = k * (e * f)) :
    ∃ q, na + q * f = k ∧ nc = q * e :=
  a_side_words e f k na nc he hef hcop heq

#print axioms rowwords_b_side
#print axioms rowwords_a_side
#print axioms rowwords_c_side_no_b
#print axioms rowwords_c_side_uncond
#print axioms rowwords_wall_base
#print axioms rowwords_a_side_words

end Erdos634.Draft.RowWordsWrap
