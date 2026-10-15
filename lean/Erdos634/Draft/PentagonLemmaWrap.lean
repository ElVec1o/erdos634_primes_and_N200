import Erdos634.PentagonLemma

namespace Erdos634.Draft.PentagonLemmaWrap
open Erdos634.PentagonLemma

theorem wrap_pentagon_lemma {e f a b c : ℕ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (ha : a = e * f) (hb : b + e * e = f * f) (hc : c = f * f) :
    (0 < e * e % b ∧ ¬ Partitionable a b c (e * e % b)) ∧
    (∀ t, (a + t = b ∨ b + t = a) → 0 < t ∧ ¬ Partitionable a b c t) :=
  pentagon_lemma hco he hef ha hb hc

example : True := trivial
#print axioms wrap_pentagon_lemma

end Erdos634.Draft.PentagonLemmaWrap
