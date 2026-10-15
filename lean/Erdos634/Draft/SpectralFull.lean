/-
Draft/SpectralFull.lean -- `rem:spectral` (obstructions paper): the dual graph of the certified 44-tiling as a
`SimpleGraph`, its connected components, and the count-criterion statement.

* `dual`: tiles `i ≠ j` are adjacent iff they share a full edge (`DualGraph44.sharesEdge`, decided on the exact
  coordinates of `Tiling44`).
* `reachable_iff`: `dual.Reachable i j ↔ lbl i = lbl j` for an explicit labelling `lbl : Fin 44 → Fin 5`.
  Adjacent tiles have equal labels (kernel table `adj_same`), and inside each class an explicit spanning tree
  (`par`, `dep`) joins every tile to the root of its class (kernel table `tree_ok`).  No breadth-first search is run
  in the kernel.
* `dual_components`: every tile is reachable from one of five roots, distinct roots are not joined, and the five
  components have orders `2, 4, 8, 14, 16`.  The orders are pairwise distinct (`orders_nodup`), so no two components
  are isomorphic.
* `count_criterion_holds_at_a_prime`: any criterion that is a consequence of the vertex-figure counts of
  `prop:globalsys` alone holds at some prime order (`GlobalSystem.prime_solution_exists`), so it cannot exclude all
  prime orders. not prime-case work.  No sorry, no native_decide.
-/
import Mathlib
import Erdos634.DualGraph44
import Erdos634.GlobalSystem

open scoped Classical

namespace Erdos634.Draft.SpectralFull

open Erdos634.DualGraph44

/-- the dual graph of the 44-tiling -/
def dual : SimpleGraph (Fin 44) := SimpleGraph.fromRel fun i j => sharesEdge i j = true

theorem dual_adj {i j : Fin 44} : dual.Adj i j ↔ i ≠ j ∧ sharesEdge i j = true := by
  unfold dual
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h1, by rw [sharesEdge_symm]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inl h2⟩

/-- component label of each tile (components listed by increasing order) -/
def lblL : List ℕ := [4, 4, 4, 4, 4, 4, 4, 2, 3, 2, 2, 2, 2, 0, 0, 3, 3, 2, 2, 2, 3, 3, 4, 4, 4, 4, 4, 3, 1, 1, 3, 1, 1, 3, 3, 4, 4, 4, 3, 3, 3, 3, 4, 3]

/-- parent of each tile in a spanning tree of its component (a root is its own parent) -/
def parL : List ℕ := [0, 2, 0, 4, 1, 6, 3, 7, 8, 10, 7, 12, 9, 13, 13, 16, 8, 10, 12, 17, 21, 15, 2, 4, 22, 6, 23, 20, 28, 28, 16, 29, 31, 21, 30, 24, 26, 35, 33, 40, 38, 34, 37, 41]

/-- depth of each tile in that tree -/
def depL : List ℕ := [0, 2, 1, 4, 3, 6, 5, 0, 0, 2, 1, 4, 3, 0, 1, 2, 1, 2, 4, 3, 4, 3, 2, 4, 3, 6, 5, 5, 0, 1, 2, 2, 3, 4, 3, 4, 6, 5, 5, 7, 6, 4, 6, 5]

def lbl (i : Fin 44) : Fin 5 := ⟨lblL.getD i.val 0 % 5, Nat.mod_lt _ (by decide)⟩

def par (i : Fin 44) : Fin 44 := ⟨parL.getD i.val 0 % 44, Nat.mod_lt _ (by decide)⟩

def dep (i : Fin 44) : ℕ := depL.getD i.val 0

/-- the root of each component -/
def root : Fin 5 → Fin 44 := ![13, 28, 7, 8, 0]

/-- tiles sharing a full edge have the same label -/
theorem adj_same : ∀ i j : Fin 44, sharesEdge i j = true → lbl i = lbl j := by decide +kernel

/-- every tile is the root of its class, or shares a full edge with its parent, which is one step nearer the root -/
theorem tree_ok : ∀ j : Fin 44, (dep j = 0 ∧ j = root (lbl j)) ∨
    (sharesEdge (par j) j = true ∧ par j ≠ j ∧ dep (par j) < dep j ∧ lbl (par j) = lbl j) := by decide +kernel

theorem lbl_root : ∀ c : Fin 5, lbl (root c) = c := by decide +kernel

theorem class_orders : ∀ c : Fin 5,
    (Finset.univ.filter fun j : Fin 44 => lbl j = c).card = ![2, 4, 8, 14, 16] c := by decide +kernel

theorem walk_lbl {u v : Fin 44} (w : dual.Walk u v) : lbl u = lbl v := by
  induction w with
  | nil => rfl
  | cons hadj p ih => exact (adj_same _ _ (dual_adj.mp hadj).2).trans ih

theorem reach_root : ∀ n : ℕ, ∀ j : Fin 44, dep j = n → dual.Reachable (root (lbl j)) j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hj
    rcases tree_ok j with ⟨_, h2⟩ | ⟨h1, h2, h3, h4⟩
    · rw [← h2]
    · have hp := ih (dep (par j)) (by rw [← hj]; exact h3) (par j) rfl
      rw [h4] at hp
      exact hp.trans (dual_adj.mpr ⟨h2, h1⟩).reachable

/-- **The connected components of the dual graph are the label classes.** -/
theorem reachable_iff (i j : Fin 44) : dual.Reachable i j ↔ lbl i = lbl j := by
  constructor
  · rintro ⟨w⟩
    exact walk_lbl w
  · intro h
    have hi := reach_root _ i rfl
    have hj := reach_root _ j rfl
    rw [h] at hi
    exact hi.symm.trans hj

/-- **The dual graph of the certified 44-tiling has exactly five connected components, of orders
`2, 4, 8, 14, 16`.** -/
theorem dual_components :
    (∀ i : Fin 44, ∃ c : Fin 5, dual.Reachable (root c) i) ∧
    (∀ c c' : Fin 5, c ≠ c' → ¬ dual.Reachable (root c) (root c')) ∧
    (∀ c : Fin 5, (Finset.univ.filter fun j => dual.Reachable (root c) j).card = ![2, 4, 8, 14, 16] c) := by
  refine ⟨fun i => ⟨lbl i, reach_root _ i rfl⟩, ?_, ?_⟩
  · intro c c' hne hreach
    have := (reachable_iff _ _).mp hreach
    rw [lbl_root, lbl_root] at this
    exact hne this
  · intro c
    have h : (Finset.univ.filter fun j => dual.Reachable (root c) j)
        = (Finset.univ.filter fun j : Fin 44 => lbl j = c) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [reachable_iff, lbl_root]
      exact eq_comm
    rw [h]
    exact class_orders c

/-- the five orders are pairwise distinct: no two components are isomorphic -/
theorem orders_nodup : ([2, 4, 8, 14, 16] : List ℕ).Nodup := by decide

/-- **A criterion that follows from the vertex-figure counts alone holds at a prime order.** -/
theorem count_criterion_holds_at_a_prime (C : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (hC : ∀ N n₁ n₂ v₁ v₂ v₃ v₄ : ℕ,
      3 + n₁ + 3 * n₂ + 2 * v₂ + 4 * v₃ + 6 * v₄ = N →
      2 + n₁ + 2 * n₂ + v₁ + 2 * v₂ + 3 * v₃ + 4 * v₄ = N →
      n₁ + 3 * v₁ + 2 * v₂ + v₃ = N →
      N = 2 * (v₁ + v₂ + v₃ + v₄) + (n₁ + n₂) + 1 → C N n₁ n₂ v₁ v₂ v₃ v₄) :
    ∃ N n₁ n₂ v₁ v₂ v₃ v₄ : ℕ, Nat.Prime N ∧ C N n₁ n₂ v₁ v₂ v₃ v₄ := by
  obtain ⟨N, n₁, n₂, v₁, v₂, v₃, v₄, hp, e1, e2, e3, e4⟩ := Erdos634.GlobalSystem.prime_solution_exists
  exact ⟨N, n₁, n₂, v₁, v₂, v₃, v₄, hp, hC N n₁ n₂ v₁ v₂ v₃ v₄ e1 e2 e3 e4⟩

end Erdos634.Draft.SpectralFull

#print axioms Erdos634.Draft.SpectralFull.reachable_iff
#print axioms Erdos634.Draft.SpectralFull.dual_components
#print axioms Erdos634.Draft.SpectralFull.count_criterion_holds_at_a_prime
