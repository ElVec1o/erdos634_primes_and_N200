import Erdos634.CosetPropagation

/-!
# CosetPropagation: coset propagation along connected adjacency, wrapper
Key results: `sub_mem_of_reach`, `image_subset_coset`, `exists_shift`.
No sorry, standard axioms.
-/

namespace Erdos634.Draft.CosetPropagationWrap
open Erdos634.CosetPropagation

variable {V : Type*} {A : Type*} [AddCommGroup A]

/-- Any two reachable vertices' f-values differ by an element of H. -/
theorem wrap_sub_mem_of_reach {adj : V → V → Prop} {f : V → A} {H : AddSubgroup A}
    (hstep : ∀ u v, adj u v → f u - f v ∈ H) {u v : V} (h : Reach adj u v) :
    f u - f v ∈ H :=
  sub_mem_of_reach hstep h

/-- With a base point reachable from everything, every f-value lies in one coset. -/
theorem wrap_image_subset_coset {adj : V → V → Prop} {f : V → A} {H : AddSubgroup A}
    (hstep : ∀ u v, adj u v → f u - f v ∈ H) (v₀ : V) (hconn : ∀ v, Reach adj v v₀) :
    ∀ v, f v - f v₀ ∈ H :=
  image_subset_coset hstep v₀ hconn

/-- Every direction is the reference direction shifted by an element of the angle subgroup. -/
theorem wrap_exists_shift {adj : V → V → Prop} {f : V → A} {H : AddSubgroup A}
    (hstep : ∀ u v, adj u v → f u - f v ∈ H) (v₀ : V) (hconn : ∀ v, Reach adj v v₀) (v : V) :
    ∃ h ∈ H, f v = f v₀ + h :=
  exists_shift hstep v₀ hconn v

-- Non-vacuity: the trivial graph (single vertex) satisfies all hypotheses.
example : ∀ v : Unit, Reach (fun _ _ => False) v () :=
  fun _ => Reach.refl ()

#print axioms wrap_sub_mem_of_reach
#print axioms wrap_image_subset_coset
#print axioms wrap_exists_shift

end Erdos634.Draft.CosetPropagationWrap
