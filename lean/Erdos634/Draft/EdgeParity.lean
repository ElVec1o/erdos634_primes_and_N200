/-
Draft/EdgeParity.lean: the edge count of an edge-to-edge dissection.

A dissection is *edge-to-edge* if every tile edge lies on the boundary of the target or coincides, as a set, with
exactly one other tile edge.

* `edge_count_parity`: in an edge-to-edge dissection into `N` tiles with `B` tile edges on the boundary of the
  target, `3N − B` is even (the interior edges are paired by a fixed-point-free involution).
* `inflparity`: an edge-to-edge dissection into `f²` tiles with `4f − e` tile edges on the boundary (`e < f`) has
  `e ≡ f (mod 2)`.  For the inflated tile, `4f − e` is the number of boundary edges of the `p = 1` boundary:
  `f` on the `a`-side, `f` on the `b`-side, `2f − e` on the `c`-side.

Any dissection, any target.  No sorry, no native_decide.
-/
import Erdos634.Dissection
import Mathlib

open scoped Classical

namespace Erdos634.Draft.EdgeParity

open Erdos634.Geometry

variable {N : ℕ}

/-- the edge `e = (tile, index)` as a set -/
def eset (D : Dissection N) (e : Fin N × Fin 3) : Set Plane := (D.tile e.1).edge e.2

/-- the edge lies on the boundary of the target -/
def OnBoundary (D : Dissection N) (e : Fin N × Fin 3) : Prop := eset D e ⊆ frontier D.target.carrier

/-- every tile edge lies on the boundary of the target or coincides with exactly one other tile edge -/
def EdgeToEdge (D : Dissection N) : Prop :=
  ∀ e : Fin N × Fin 3, OnBoundary D e ∨ ∃! e' : Fin N × Fin 3, e' ≠ e ∧ eset D e' = eset D e

/-- the number of tile edges on the boundary of the target -/
noncomputable def boundaryCount (D : Dissection N) : ℕ :=
  (Finset.univ.filter (fun e : Fin N × Fin 3 => OnBoundary D e)).card

/-- the partner of an edge: itself on the boundary, the other tile edge on the same segment otherwise -/
noncomputable def partner (D : Dissection N) (h : EdgeToEdge D) (e : Fin N × Fin 3) : Fin N × Fin 3 :=
  if hb : OnBoundary D e then e else ((h e).resolve_left hb).exists.choose

theorem partner_boundary (D : Dissection N) (h : EdgeToEdge D) {e : Fin N × Fin 3} (hb : OnBoundary D e) :
    partner D h e = e := by
  unfold partner; rw [dif_pos hb]

theorem partner_spec (D : Dissection N) (h : EdgeToEdge D) {e : Fin N × Fin 3} (hb : ¬ OnBoundary D e) :
    partner D h e ≠ e ∧ eset D (partner D h e) = eset D e := by
  unfold partner; rw [dif_neg hb]
  exact ((h e).resolve_left hb).exists.choose_spec

theorem partner_not_boundary (D : Dissection N) (h : EdgeToEdge D) {e : Fin N × Fin 3}
    (hb : ¬ OnBoundary D e) : ¬ OnBoundary D (partner D h e) := by
  intro hb'
  apply hb
  unfold OnBoundary at hb' ⊢
  rw [← (partner_spec D h hb).2]
  exact hb'

theorem partner_involutive (D : Dissection N) (h : EdgeToEdge D) : Function.Involutive (partner D h) := by
  intro e
  by_cases hb : OnBoundary D e
  · rw [partner_boundary D h hb, partner_boundary D h hb]
  · have hb' := partner_not_boundary D h hb
    obtain ⟨h1, h2⟩ := partner_spec D h hb
    obtain ⟨h3, h4⟩ := partner_spec D h hb'
    -- `e` and `partner (partner e)` are both partners of `partner e`
    have huniq := (h (partner D h e)).resolve_left hb'
    exact huniq.unique ⟨h3, h4⟩ ⟨fun heq => h1 heq.symm, h2.symm⟩

theorem boundaryCount_le (D : Dissection N) : boundaryCount D ≤ 3 * N := by
  unfold boundaryCount
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  omega

/-- **Edge count.**  In an edge-to-edge dissection into `N` tiles with `B` tile edges on the boundary of the
target, `3N − B` is even. -/
theorem edge_count_parity (D : Dissection N) (h : EdgeToEdge D) : Even (3 * N - boundaryCount D) := by
  set σ : Equiv.Perm (Fin N × Fin 3) := (partner_involutive D h).toPerm with hσ
  have hσ2 : σ ^ 2 = 1 := by
    rw [sq]
    refine Equiv.ext (fun e => ?_)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    show partner D h (partner D h e) = e
    exact partner_involutive D h e
  have hsupp : σ.support = Finset.univ.filter (fun e : Fin N × Fin 3 => ¬ OnBoundary D e) := by
    ext e
    simp only [Equiv.Perm.mem_support, Finset.mem_filter, Finset.mem_univ, true_and, hσ,
      Function.Involutive.coe_toPerm]
    constructor
    · intro hne hb
      exact hne (partner_boundary D h hb)
    · intro hb
      exact (partner_spec D h hb).1
  have h2 : 2 ∣ (Finset.univ.filter (fun e : Fin N × Fin 3 => ¬ OnBoundary D e)).card := by
    rw [← hsupp]
    exact Equiv.Perm.two_dvd_card_support hσ2
  have hcard : (Finset.univ.filter (fun e : Fin N × Fin 3 => OnBoundary D e)).card
      + (Finset.univ.filter (fun e : Fin N × Fin 3 => ¬ OnBoundary D e)).card = 3 * N := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
    ring
  unfold boundaryCount
  rw [even_iff_two_dvd]
  have : 3 * N - (Finset.univ.filter (fun e : Fin N × Fin 3 => OnBoundary D e)).card
      = (Finset.univ.filter (fun e : Fin N × Fin 3 => ¬ OnBoundary D e)).card := by omega
  rw [this]
  exact h2

/-- **`prop:inflparity`.**  An edge-to-edge dissection into `f²` tiles with `4f − e` tile edges on the boundary
(`e < f`) has `e ≡ f (mod 2)`. -/
theorem inflparity {e f : ℕ} (hef : e < f) (D : Dissection (f ^ 2)) (h : EdgeToEdge D)
    (hB : boundaryCount D = 4 * f - e) : e % 2 = f % 2 := by
  have hpar := edge_count_parity D h
  rw [hB] at hpar
  have hle : 4 * f - e ≤ 3 * f ^ 2 := hB ▸ boundaryCount_le D
  rcases Nat.even_or_odd f with hf | hf <;> rcases Nat.even_or_odd e with he | he
  · obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := he; omega
  · exfalso
    obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := he; obtain ⟨c, hc⟩ := hpar
    have h1 : f ^ 2 = 4 * a ^ 2 := by rw [ha]; ring
    omega
  · exfalso
    obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := he; obtain ⟨c, hc⟩ := hpar
    have h1 : f ^ 2 = 4 * a ^ 2 + 4 * a + 1 := by rw [ha]; ring
    omega
  · obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := he; omega

end Erdos634.Draft.EdgeParity

#print axioms Erdos634.Draft.EdgeParity.edge_count_parity
#print axioms Erdos634.Draft.EdgeParity.inflparity
