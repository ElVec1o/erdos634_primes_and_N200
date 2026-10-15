/-
Draft/F1PairPar.lean -- the `F₁` leaf pair by pair, with the parity `Ma ≡ Mb ≡ N (mod 2)` of `Paper.cor_int`.

`NSQF1.F1MaGt1par N` from `F1PairCert.F1Pair N Ma Mb` for the pairs of the right parity only (for even `N` the pairs
with an odd member do not occur).

Composite-N statement; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.F1PairCert
import Erdos634.Draft.NSQF1

open scoped Classical

namespace Erdos634.Draft.F1PairCert

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.NSQF1

/-- **`F1MaGt1par N` from the pairs of the right parity.** -/
theorem f1MaGt1par_of_pairs (N : ℕ)
    (h : ∀ Ma Mb : ℕ, 1 < Ma → Ma < Mb → Ma * Mb = N → Ma % 2 = N % 2 → Mb % 2 = N % 2 → F1Pair N Ma Mb) :
    F1MaGt1par N := by
  intro D α a b c μ hirr hm hF1 hμ Ma Mb h1 hp hpa hpb e1 e2
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hlt : Ma < Mb := by
    have : (Ma : ℝ) * b < (Mb : ℝ) * b := by rw [e1, e2]; nlinarith
    have := lt_of_mul_lt_mul_right this hb0.le
    exact_mod_cast this
  exact h Ma Mb h1 hlt hp hpa hpb D α a b c μ hirr hm hF1 hμ e1 e2

end Erdos634.Draft.F1PairCert

#print axioms Erdos634.Draft.F1PairCert.f1MaGt1par_of_pairs
