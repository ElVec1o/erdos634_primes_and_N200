import Mathlib.Tactic
import Erdos634.Draft.TraceCovering
import Erdos634.PinPlumbing
import Erdos634.Congruence
import Erdos634.CongruentAngles

/-!
# Blocked-end quantization (formal statement)

**Statement**: Let [X,Y] be a tile edge whose extension beyond X is blocked.
Then every vertex of the tiling in the relative interior of [X,Y] is at distance from X
belonging to the numerical semigroup ⟨a,b,c⟩.

**Lean** formalizes the quantization step: if X is not straddled and p is a junction endpoint
of the line chain within [X, X+x₀•u], then dist X p = na·a + nb·b + nc·c (na nb nc : ℕ).

Uses:
- `TraceCovering.junction_partial_sum`: the filtered chain sum = dist X p
- Direct ℝ-induction: a sum of terms each in {A,B,C} is na·A+nb·B+nc·C
- `CongruentAngles.congruent_corner_angles_aux`: each tile edge = some model side

The Lean statement is about junction endpoints, not about all tiling vertices in the relative
interior.  Every tiling vertex on the line is a junction endpoint, by `trace_covering`; that step
is not wired here.

Non-vacuity: any junction at distance A (first tile edge) gives (1,0,0).
No `sorry`; axioms: [propext, Classical.choice, Quot.sound].
-/

namespace Erdos634.Draft.AnchorClearFormal

open Erdos634.Geometry Erdos634.Draft.TraceCovering
open Set

variable {N : ℕ}

/-! ## ℝ-valued sum_three_valued (mirrors PinPlumbing.sum_of_three_valued in ℝ) -/

private theorem sum_three_real {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (A B C : ℝ)
    (h : ∀ e ∈ S, φ e = A ∨ φ e = B ∨ φ e = C) :
    ∃ na nb nc : ℕ, ∑ e ∈ S, φ e = na * A + nb * B + nc * C := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨na, nb, nc, hS⟩ := ih (fun e he => h e (Finset.mem_insert_of_mem he))
    rcases h a (Finset.mem_insert_self a s) with rfl | rfl | rfl
    · exact ⟨na + 1, nb, nc, by rw [Finset.sum_insert ha, hS]; push_cast; ring⟩
    · exact ⟨na, nb + 1, nc, by rw [Finset.sum_insert ha, hS]; push_cast; ring⟩
    · exact ⟨na, nb, nc + 1, by rw [Finset.sum_insert ha, hS]; push_cast; ring⟩

/-! ## edist → dist bridge -/

private theorem edist_eq_to_dist_eq {a b c d : Plane} (h : edist a b = edist c d) :
    dist a b = dist c d := by
  have := congr_arg ENNReal.toReal h
  rwa [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
       edist_dist, ENNReal.toReal_ofReal dist_nonneg] at this

/-! ## The anchor-clear semigroup theorem -/

/-- **`lem:anchorclear` (junction form)**: if X is not straddled and p is a junction endpoint
    of the chain within [X, X+x₀•u], then dist X p ∈ ⟨a,b,c⟩. -/
theorem anchor_clear_semigroup
    (D : CongruentDissection N) (f g : Plane →ₗ[ℝ] ℝ) (c d : ℝ)
    (hg : g ≠ 0) (hgd : ∀ y, g y = d ↔ f y = c)
    (hf : f ≠ 0) (X u : Plane) (hX : f X = c) (hu : f u = 0) (hu1 : ‖u‖ = 1)
    (x₀ : ℝ) (hx0 : 0 ≤ x₀)
    (hint : ∀ x ∈ Ioo 0 x₀, X + x • u ∈ interior D.target.carrier)
    (hwall : ∀ x ∈ Ioo 0 x₀, ∀ i, X + x • u ∉ interior (D.tile i).carrier)
    (h0 : ¬ Straddled D.toDissection g d X)
    (e : Fin N × Fin 3) (he : e ∈ D.toDissection.lineChain g d)
    (hin : (D.toDissection.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u))
    (p : Plane) (hp : p = (D.toDissection.tile e.1).pts e.2 ∨
                       p = (D.toDissection.tile e.1).pts (e.2 + 1)) :
    ∃ na nb nc : ℕ,
      na * dist (D.model.pts 0) (D.model.pts 1) +
      nb * dist (D.model.pts 1) (D.model.pts 2) +
      nc * dist (D.model.pts 0) (D.model.pts 2) = dist X p := by
  classical
  set S := (D.toDissection.lineChain g d).filter
      (fun e' => (D.toDissection.tile e'.1).edge e'.2 ⊆ segment ℝ X p)
  -- (1) sum of edge lengths in S = dist X p
  have hsum : ∑ e' ∈ S, dist ((D.toDissection.tile e'.1).pts e'.2)
      ((D.toDissection.tile e'.1).pts (e'.2 + 1)) = dist X p :=
    junction_partial_sum hg hgd hf hX hu hu1 hx0 hint hwall h0 he hin hp
  -- (2) each term is a model side
  have hcong : ∀ i, D.model.Congruent (D.toDissection.tile i) := fun i =>
    (D.tiles_congruent i).symm
  have hval : ∀ e' ∈ S,
      dist ((D.toDissection.tile e'.1).pts e'.2) ((D.toDissection.tile e'.1).pts (e'.2 + 1)) =
      dist (D.model.pts 0) (D.model.pts 1) ∨
      dist ((D.toDissection.tile e'.1).pts e'.2) ((D.toDissection.tile e'.1).pts (e'.2 + 1)) =
      dist (D.model.pts 1) (D.model.pts 2) ∨
      dist ((D.toDissection.tile e'.1).pts e'.2) ((D.toDissection.tile e'.1).pts (e'.2 + 1)) =
      dist (D.model.pts 0) (D.model.pts 2) := by
    intro e' _
    obtain ⟨i, i', hii, hd⟩ :=
      Erdos634.Geometry.congruent_corner_angles_aux (hcong e'.1)
        e'.2 (e'.2 + 1) (fin3_succ_ne e'.2)
    rcases Erdos634.PinPlumbing.model_three_lengths D.model i i' hii with h | h | h
    · left;  rw [hd]; exact edist_eq_to_dist_eq h
    · right; left;  rw [hd]; exact edist_eq_to_dist_eq h
    · right; right; rw [hd]; exact edist_eq_to_dist_eq h
  -- (3) extract ℕ-coefficients from the sum
  obtain ⟨na, nb, nc, hS⟩ := sum_three_real S
    (fun e' => dist ((D.toDissection.tile e'.1).pts e'.2)
      ((D.toDissection.tile e'.1).pts (e'.2 + 1)))
    (dist (D.model.pts 0) (D.model.pts 1))
    (dist (D.model.pts 1) (D.model.pts 2))
    (dist (D.model.pts 0) (D.model.pts 2)) hval
  exact ⟨na, nb, nc, by linarith [hS.symm.trans hsum]⟩

#check @anchor_clear_semigroup

end Erdos634.Draft.AnchorClearFormal
