import Mathlib.Tactic
import Erdos634.Draft.T30LPi3Tile
import Erdos634.Draft.T30LPi3F6Geom

/-!
# Tile-level facts for the `π/3` tile

* `tile_sixty`: every tile of a `CongruentDissection` whose model has `SixtyData α a b c` has `SixtyData α a b c` itself.
* `tri_two_orient`: for a tile with `SixtyData` and pairwise distinct `a, b, c`, at a vertex `l` whose opposite side has length `c`,
  the other two vertices `l+1, l+2` have (opposite side, angle) `(a, α), (b, β)` or `(b, β), (a, α)`.
* `third_vertex`: the same, in terms of a tile with a `c`-edge `[P,Q]`: with the third vertex `X`, either
  `|QX| = a, |PX| = b`, angles `α` at `P`, `β` at `Q`, or `|QX| = b, |PX| = a`, angles `β` at `P`, `α` at `Q`.
-/

namespace Erdos634.Pi3F6

open Erdos634.Geometry Erdos634.Pi3Tile

theorem tile_sixty {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hS : D.model.SixtyData α a b c)
    (i : Fin N) : (D.tile i).SixtyData α a b c := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
  obtain ⟨τ, h0, h0', h1, h1', h2, h2'⟩ := hS
  refine ⟨τ.trans σ.symm, ?_⟩
  have key : ∀ m : Fin 3, (D.tile i).angleAt ((τ.trans σ.symm) m) = D.model.angleAt (τ m) ∧
      (D.tile i).oppLen ((τ.trans σ.symm) m) = D.model.oppLen (τ m) := by
    intro m
    have := hσ ((τ.trans σ.symm) m)
    simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(key 0).1, h0]
  · rw [(key 0).2, h0']
  · rw [(key 1).1, h1]
  · rw [(key 1).2, h1']
  · rw [(key 2).1, h2]
  · rw [(key 2).2, h2']

theorem tri_two_orient {U : Tri} {α a b c : ℝ} (hU : U.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c)
    (l : Fin 3) (hl : U.oppLen l = c) :
    (U.oppLen (l + 1) = a ∧ U.angleAt (l + 1) = α ∧ U.oppLen (l + 2) = b ∧
        U.angleAt (l + 2) = 2 * Real.pi / 3 - α) ∨
    (U.oppLen (l + 1) = b ∧ U.angleAt (l + 1) = 2 * Real.pi / 3 - α ∧ U.oppLen (l + 2) = a ∧
        U.angleAt (l + 2) = α) := by
  obtain ⟨σ, h0, h0', h1, h1', h2, h2'⟩ := hU
  obtain ⟨m, hm⟩ := σ.surjective l
  obtain ⟨m1, hm1⟩ := σ.surjective (l + 1)
  obtain ⟨m2, hm2⟩ := σ.surjective (l + 2)
  have e1 : ∀ x : Fin 3, x ≠ x + 1 := by decide
  have e2 : ∀ x : Fin 3, x ≠ x + 2 := by decide
  have e12 : ∀ x : Fin 3, x + 1 ≠ x + 2 := by decide
  have n01 : m ≠ m1 := fun h => e1 l (by have := congrArg σ h; rwa [hm, hm1] at this)
  have n02 : m ≠ m2 := fun h => e2 l (by have := congrArg σ h; rwa [hm, hm2] at this)
  have n12 : m1 ≠ m2 := fun h => e12 l (by have := congrArg σ h; rwa [hm1, hm2] at this)
  rw [← hm1, ← hm2]
  rw [← hm] at hl
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases h3 m with rfl | rfl | rfl <;> rcases h3 m1 with rfl | rfl | rfl <;>
    rcases h3 m2 with rfl | rfl | rfl <;> simp only [ne_eq, not_true_eq_false] at n01 n02 n12 <;>
    first
    | exact absurd hl (by rw [h0']; exact hac)
    | exact absurd hl (by rw [h1']; exact hbc)
    | exact Or.inl ⟨h0', h0, h1', h1⟩
    | exact Or.inr ⟨h1', h1, h0', h0⟩

end Erdos634.Pi3F6
