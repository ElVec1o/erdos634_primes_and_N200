import Erdos634.TP_erdos
import Erdos634.EdgeWordConversion

/-!
# `ChordFar`: the far side of a boundary chord

`TPErdos.chain_edge_lengths_sum` is the whole-edge partition for the *near* chain `lineChain f c`
of a chord whose two ends are clamped by supporting functionals of the target.  The hand proofs
use it on the *far* side of a tile's own edge (the chord `PR` is an edge of the corner tile `T`,
and the tiles ACROSS it must cover it by whole edges).  Here:

* `chord_far_sum`: the same statement for the far chain `lineChain (-f) (-c)` (real-valued), and
  the near chain, from the clamps only; `hS` is derived from the end values and `hwall` is
  discharged when the chord lies inside a tile edge (`Dissection.edge_point_not_interior`).
* `chord_far_sum_tile_edge`: the tile-edge form: the chord is the edge `[pts k, pts (k+1)]` of
  tile `j`; both chains sum to its length.
* `far_chain_single_of_length_eq`: if one far-chain edge already has the chord's length, the
  far chain is exactly that edge.
* Witness: `wallDissection` (a real `Dissection 2`, `TPErdos`), whose median is a chord clamped on
  the base and the hypotenuse.  Counterexample: the half chord (unclamped end) breaks the
  conclusion, so the clamp hypotheses are doing the work.
-/

namespace Erdos634.ChordFar

open Erdos634.Geometry Erdos634.TPErdos
open scoped ENNReal

/-- An open segment inside a tile edge is a wall: no tile interior meets it. -/
theorem hwall_of_tile_edge {N : ℕ} (D : Dissection N) (j : Fin N) (k : Fin 3) :
    ∀ y ∈ openSegment ℝ ((D.tile j).pts k) ((D.tile j).pts (k + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := fun y hy =>
  D.edge_point_not_interior (openSegment_subset_segment ℝ _ _ hy : y ∈ (D.tile j).edge k)

/-- A segment whose two ends lie on a level line lies on it. -/
theorem segment_sub_level (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {P Q : Plane}
    (hP : f P = c) (hQ : f Q = c) : segment ℝ P Q ⊆ {y | f y = c} := by
  rintro y ⟨a, b, ha, hb, hab, rfl⟩
  simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul, hP, hQ]
  rw [← add_mul, hab, one_mul]

/-- **W1, ENNReal form, near AND far.**  For a chord `PQ` clamped at both ends by supporting
functionals of the target, lying on `{f = c}`, inside the target, and a wall, the whole-edge
partition holds on both sides: `lineChain f c` and `lineChain (-f) (-c)`. -/
theorem chord_far_sum {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) {P Q : Plane} (hPQ : P ≠ Q) (hfP : f P = c) (hfQ : f Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier) :
    (∑ e ∈ D.lineChain f c,
        ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist P Q)) ∧
    (∑ e ∈ D.lineChain (-f) (-c),
        ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist P Q)) := by
  refine ⟨chain_edge_lengths_sum D f hf c hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP
    (segment_sub_level f c hfP hfQ) hint hwall, ?_⟩
  refine chain_edge_lengths_sum D (-f) (neg_ne_zero.mpr hf) (-c) hPQ (by simp [hfP])
    (by simp [hfQ]) g cg hg hgP hgQ h ch hh hhQ hhP ?_ hint hwall
  exact segment_sub_level (-f) (-c) (by simp [hfP]) (by simp [hfQ])

/-- Real-valued form of a chain sum. -/
theorem chain_sum_real {N : ℕ} (D : Dissection N) (S : Finset (Fin N × Fin 3)) (L : ℝ)
    (hL : 0 ≤ L)
    (h : ∑ e ∈ S, ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
        = ENNReal.ofReal L) :
    ∑ e ∈ S, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => dist_nonneg)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun e _ => dist_nonneg) hL).mp h

/-- **W1, tile-edge form (what the hand proofs use).**  Let `[X,Y]` be the edge `k` of tile `j`,
with `X`, `Y` clamped on the target boundary as in `chain_edge_lengths_sum`.  Then for the level
functional `f` of that edge, both the near chain and the far chain (the tiles across the edge)
consist of edges whose lengths sum, in `ℝ`, to `dist X Y`. -/
theorem chord_far_sum_tile_edge {N : ℕ} (D : Dissection N) (j : Fin N) (k : Fin 3)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g ((D.tile j).pts k) = cg) (hgQ : g ((D.tile j).pts (k + 1)) < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h ((D.tile j).pts (k + 1)) = ch) (hhP : h ((D.tile j).pts k) < ch)
    (hint : openSegment ℝ ((D.tile j).pts k) ((D.tile j).pts (k + 1))
      ⊆ interior D.target.carrier) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ y ∈ (D.tile j).edge k, f y = c) ∧
      (∑ e ∈ D.lineChain f c,
          dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = dist ((D.tile j).pts k) ((D.tile j).pts (k + 1))) ∧
      (∑ e ∈ D.lineChain (-f) (-c),
          dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = dist ((D.tile j).pts k) ((D.tile j).pts (k + 1))) := by
  obtain ⟨f, c, hf, hline⟩ := (D.tile j).edge_line k
  have hne : (D.tile j).pts k ≠ (D.tile j).pts (k + 1) := by
    intro hh'
    have h1 : k = k + 1 := (D.tile j).indep.injective hh'
    have h2 : ∀ m : Fin 3, m ≠ m + 1 := by decide
    exact h2 k h1
  have hP : f ((D.tile j).pts k) = c := hline _ (left_mem_segment ℝ _ _)
  have hQ : f ((D.tile j).pts (k + 1)) = c := hline _ (right_mem_segment ℝ _ _)
  obtain ⟨h1, h2⟩ := chord_far_sum D f hf c hne hP hQ g cg hg hgP hgQ h ch hh hhQ hhP hint
    (hwall_of_tile_edge D j k)
  exact ⟨f, c, hf, hline, chain_sum_real D _ _ dist_nonneg h1, chain_sum_real D _ _ dist_nonneg h2⟩

/-- **W3.**  If an edge of the far chain already has the chord's full length, the far chain is
exactly that edge (all other chain edges would have to have length `0`). -/
theorem far_chain_single_of_length_eq {N : ℕ} (D : Dissection N) (S : Finset (Fin N × Fin 3))
    (L : ℝ)
    (hsum : ∑ e ∈ S, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L)
    {e₀ : Fin N × Fin 3} (he₀ : e₀ ∈ S)
    (hlen : dist ((D.tile e₀.1).pts e₀.2) ((D.tile e₀.1).pts (e₀.2 + 1)) = L) :
    S = {e₀} := by
  classical
  have hpos : ∀ e : Fin N × Fin 3,
      0 < dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
    intro e
    apply dist_pos.mpr
    intro hh
    have h1 : e.2 = e.2 + 1 := (D.tile e.1).indep.injective hh
    have h2 : ∀ m : Fin 3, m ≠ m + 1 := by decide
    exact h2 _ h1
  have hsplit := Finset.add_sum_erase S
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) he₀
  have hrest : ∑ e ∈ S.erase e₀, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = 0 := by
    linarith
  have hempty : S.erase e₀ = ∅ := by
    by_contra hne
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have := Finset.sum_pos (fun e _ => hpos e) ⟨e, he⟩
    linarith
  ext e
  simp only [Finset.mem_singleton]
  constructor
  · intro he
    by_contra hne
    have : e ∈ S.erase e₀ := Finset.mem_erase.mpr ⟨hne, he⟩
    rw [hempty] at this; simp at this
  · rintro rfl; exact he₀

/-! ## Witness: the real dissection `wallDissection`

The median `(0,0)–(1,1)` of the right isosceles triangle `(0,0) (2,0) (0,2)` is a chord clamped by
the base (`gBase`) at `(0,0)` and by the hypotenuse (`hHyp`) at `(1,1)`.  It separates the two
tiles `wallTileA` (far, `x₀ - x₁ ≥ 0`) and `wallTileB` (near).  The far chain of `wallF` is the
chain of tile `A`'s own edge, so `chord_far_sum` at this witness is the far-side statement. -/

theorem chord_far_witness :
    (∑ e ∈ wallDissection.lineChain wallF 0,
        ENNReal.ofReal (dist ((wallDissection.tile e.1).pts e.2)
          ((wallDissection.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist wallU wallV)) ∧
    (∑ e ∈ wallDissection.lineChain (-wallF) (-0),
        ENNReal.ofReal (dist ((wallDissection.tile e.1).pts e.2)
          ((wallDissection.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist wallU wallV)) :=
  chord_far_sum wallDissection wallF wallF_ne 0 wallU_ne_wallV wallF_u wallF_v
    gBase 0 gBase_bound_target (by rw [wallU, gBase_pt]; norm_num)
    (by rw [wallV, gBase_pt]; norm_num)
    hHyp 2 hHyp_bound (by rw [wallV, hHyp_pt]; norm_num)
    (by rw [wallU, hHyp_pt]; norm_num) wall_hint wall_hwall

/-- **The same, for a `CongruentDissection`** (the hand proofs' setting): `CongruentDissection.toDissection`
is the underlying dissection, so `chord_far_sum` applies verbatim; the witness is
`EdgeWordConversion.wallCongruentDissection` (two congruent tiles). -/
theorem chord_far_sum_cong {N : ℕ} (D : CongruentDissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) {P Q : Plane} (hPQ : P ≠ Q) (hfP : f P = c) (hfQ : f Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∑ e ∈ D.lineChain (-f) (-c),
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist P Q :=
  chain_sum_real D.toDissection _ _ dist_nonneg
    (chord_far_sum D.toDissection f hf c hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall).2

open Erdos634.EdgeWordConversion in
theorem chord_far_cong_witness :
    ∑ e ∈ wallCongruentDissection.lineChain (-wallF) (-0),
        dist ((wallCongruentDissection.tile e.1).pts e.2)
          ((wallCongruentDissection.tile e.1).pts (e.2 + 1)) = dist wallU wallV :=
  chord_far_sum_cong wallCongruentDissection wallF wallF_ne 0 wallU_ne_wallV wallF_u wallF_v
    gBase 0 gBase_bound_target (by rw [wallU, gBase_pt]; norm_num)
    (by rw [wallV, gBase_pt]; norm_num)
    hHyp 2 hHyp_bound (by rw [wallV, hHyp_pt]; norm_num)
    (by rw [wallU, hHyp_pt]; norm_num) wall_hint wall_hwall

/-- The far chain of the witness is nonempty (an empty chain has sum `0 ≠ √2`), so the far-side
conclusion is not vacuous. -/
theorem far_chain_witness_nonempty :
    (wallDissection.lineChain (-wallF) (-0)).Nonempty := by
  classical
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have h := chord_far_witness.2
  rw [hne, Finset.sum_empty] at h
  have hpos : 0 < dist wallU wallV := dist_pos.mpr wallU_ne_wallV
  have := (ENNReal.ofReal_pos.mpr hpos).ne'
  exact this h.symm

/-! ## Counterexample: the unclamped half chord

`Q' = ½ • (1,1)`: the half chord `(0,0)–Q'` has an end `Q'` in the interior of the target, so no
supporting functional is strict-clamped there, and the whole-edge sum over the chain
(`dist wallU wallV = ‖(1,1)‖`) is NOT `dist wallU Q' = ½ ‖(1,1)‖`.  The conclusion of
`chord_far_sum` fails, so the clamp hypotheses cannot be dropped. -/

theorem wallU_eq_zero : wallU = 0 := by
  ext i; fin_cases i <;> simp [wallU]

theorem half_chord_control :
    (∑ e ∈ wallDissection.lineChain wallF 0,
        ENNReal.ofReal (dist ((wallDissection.tile e.1).pts e.2)
          ((wallDissection.tile e.1).pts (e.2 + 1))))
      ≠ ENNReal.ofReal (dist wallU ((1 / 2 : ℝ) • wallV)) := by
  rw [chord_far_witness.1, wallU_eq_zero]
  intro h
  have hpos : 0 < dist (0 : Plane) wallV := by
    rw [← wallU_eq_zero]; exact dist_pos.mpr wallU_ne_wallV
  have hd : dist (0 : Plane) ((1 / 2 : ℝ) • wallV) = (1 / 2) * dist (0 : Plane) wallV := by
    rw [dist_zero_left, dist_zero_left, norm_smul]; norm_num
  have h' : dist (0 : Plane) wallV = dist (0 : Plane) ((1 / 2 : ℝ) • wallV) := by
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg dist_nonneg).mp h
  rw [hd] at h'
  linarith

end Erdos634.ChordFar

#print axioms Erdos634.ChordFar.chord_far_sum
#print axioms Erdos634.ChordFar.chord_far_sum_tile_edge
#print axioms Erdos634.ChordFar.far_chain_single_of_length_eq
#print axioms Erdos634.ChordFar.chord_far_witness
#print axioms Erdos634.ChordFar.chord_far_cong_witness
#print axioms Erdos634.ChordFar.far_chain_witness_nonempty
#print axioms Erdos634.ChordFar.half_chord_control
