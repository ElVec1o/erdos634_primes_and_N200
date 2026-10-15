import Erdos634.LayerLink
namespace Erdos634.Draft.LayerLinkWrap
open Erdos634.Geometry Erdos634.StripRigid

theorem wrap_layer_rigid_of_exclusions {N : ℕ} (D : CongruentDissection N) (idx : ℕ → Fin N)
    (base_excl : ¬ (D.tile (idx 0)).Reflected D.model)
    (step_excl : ∀ j, D.UnreflectedAt (idx j) → ¬ (D.tile (idx (j + 1))).Reflected D.model) :
    ∀ j, D.UnreflectedAt (idx j) :=
  layer_rigid_of_exclusions D idx base_excl step_excl

theorem wrap_strip_layer_rigid {N : ℕ} (D : CongruentDissection N) (idx : ℕ → Fin N) (e f : ℤ)
    (he : 0 < e) (hef : e < f)
    (mast : (D.tile (idx 0)).Reflected D.model →
      e * (3 * f ^ 2 - e ^ 2) ≤ 2 * (e * f) * f)
    (overlap : ∀ j, D.UnreflectedAt (idx j) → (D.tile (idx (j + 1))).Reflected D.model →
      e * (3 * f ^ 2 - e ^ 2) ≤ 2 * (e * f) * f) :
    ∀ j, D.UnreflectedAt (idx j) :=
  strip_layer_rigid D idx e f he hef mast overlap

theorem wrap_c_layer_rigid_link {N : ℕ} (D : CongruentDissection N) (idx : ℕ → Fin N) (e f : ℤ)
    (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (left_gap : (D.tile (idx 0)).Reflected D.model →
      ∃ n : ℤ, 0 ≤ n ∧ n * f ^ 4 = f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2))
    (mixed_gap : ∀ j, D.UnreflectedAt (idx j) → (D.tile (idx (j + 1))).Reflected D.model →
      ∃ n : ℤ, 0 ≤ n ∧ n * f ^ 4 = 2 * f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2)) :
    ∀ j, D.UnreflectedAt (idx j) :=
  c_layer_rigid_link D idx e f he hef hcop left_gap mixed_gap

example : True := trivial
#print axioms wrap_layer_rigid_of_exclusions
end Erdos634.Draft.LayerLinkWrap
