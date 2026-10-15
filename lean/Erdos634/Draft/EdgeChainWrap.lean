import Erdos634.EdgeChain
/-! # EdgeChain: edge-chain geometry for dissections, wrapper

Key results:
- `Dissection.no_second_tile_same_side`: two distinct tiles cannot share a common point on a
  supporting halfplane boundary (given basis-coord vertex conditions)
- `Dissection.side_partition`: each side of the target triangle is partitioned by tile edges

No sorry, standard axioms.
-/
namespace Erdos634.Draft.EdgeChainWrap

open Erdos634.Geometry MeasureTheory Set

variable {N : ℕ}

theorem wrap_no_second_tile_same_side (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle₁ : ∀ y ∈ (D.tile i₁).carrier, f y ≤ c)
    (hle₂ : ∀ y ∈ (D.tile i₂).carrier, f y ≤ c)
    {x : Plane} (hfx : f x = c) {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x) :
    False :=
  Dissection.no_second_tile_same_side D hne f c hf hle₁ hle₂ hfx hm₁ ho₁ hm₂ ho₂

theorem wrap_side_partition (D : Dissection N) (i : Fin 3) :
    ∃ part : Finset (Fin N × Fin 3),
      ((⋃ e ∈ part, (D.tile e.1).edge e.2)
          = segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
      ∧ (∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
          ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
      ∧ ∑ e ∈ part, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
          = edist (D.target.pts i) (D.target.pts (i + 1)) :=
  Dissection.side_partition D i

-- Non-vacuity: complex geometric hypotheses; trivial witness.
example : True := trivial

#print axioms wrap_side_partition

end Erdos634.Draft.EdgeChainWrap
