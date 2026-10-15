import Erdos634.Inflation

/-!
# The crux, on f² tiles: wrapper

At m=1 the inflated c-side is the whole equal side,
so the two c-side words of the inflated boundary description are exactly p=0 and p=1.

The arithmetic spine: at k=f (the c-side scaled by f), `c_side_words_scale` gives
  ∃ q, na = q·f ∧ q·e + nc = f
so the a-count is a multiple of f and nc = f - q·e. In particular:
- p=0 word: q=0, na=0, nc=f.
- p=1 word: q=1, na=f, nc=f-e.
Both are exhibited by `inflcrux_p0_word` and `inflcrux_p1_word`.

Arithmetic kernel only: 0 sorry, standard axioms.

Not covered here:
- The identification "inflated c-side = whole equal side at m=1" is geometric (m=1
  forces k=f); k=f is a hypothesis here.
- "Exactly two" words (ruling out q≥2) needs the boundary description of the inflated tile
  (`InflBdy`), which is not used here.
-/

namespace Erdos634.Draft.InflCruxWrap

open Erdos634.Inflation

/-- cor:inflcrux arithmetic: at k=f the c-side na-count is a multiple of f and nc = f - q·e. -/
theorem inflcrux_quantization (e f na nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f)
    (heq : na * (e * f) + nc * f ^ 2 = f * f ^ 2) :
    ∃ q, na = q * f ∧ q * e + nc = f :=
  c_side_words_scale e f f na nc he hef hcop heq

/-- cor:inflcrux (p=0 word): na=0, nc=f solves the c-side equation at k=f. -/
theorem inflcrux_p0_word (e f : ℕ) :
    0 * (e * f) + f * f ^ 2 = f * f ^ 2 := by ring

/-- cor:inflcrux (p=1 word): na=f, nc=f-e solves the c-side equation at k=f when e ≤ f. -/
theorem inflcrux_p1_word (e f : ℕ) (hef : e ≤ f) :
    f * (e * f) + (f - e) * f ^ 2 = f * f ^ 2 := by
  zify [hef]; ring

#print axioms inflcrux_quantization
#print axioms inflcrux_p0_word
#print axioms inflcrux_p1_word

end Erdos634.Draft.InflCruxWrap
