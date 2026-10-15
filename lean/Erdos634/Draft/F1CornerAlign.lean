-- Draft/F1CornerAlign.lean — T₁'s edges at V₁ lie along the target's sides at V₁.
--
-- Proves:
--   `f1_v1_edges_aligned` — at the α-corner V₁ of an F₁ target with a 2π/3 model, the unique
--                            covering tile T₁ has its two edges at V₁ SameRay with the target's
--                            two edges at V₁ (in one order or the other).
--
-- Imported by `All`.  No sorry.

import Erdos634.Draft.F1CornerK
import Erdos634.Draft.F1EdgeAlign
import Erdos634.ApexEdgesReal
import Erdos634.AngleSumDissection
import Erdos634.MarchFlank

open scoped Classical
open Erdos634.Draft.TheoremPConditional

namespace Erdos634.Geometry

open Erdos634.TilePlacement (corner_multiplicities)
open Erdos634.Geometry.Dissection (congruentDissection_localAngle_mem)

private instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp⟩

/-! ## Utility -/

private lemma fin3_succ_ne (k : Fin 3) : k + 1 ≠ k := by fin_cases k <;> decide
private lemma fin3_succ2_ne (k : Fin 3) : k + 2 ≠ k := by fin_cases k <;> decide

/-- Helper: if a finset has card = 0, no element can belong to it. -/
private lemma finset_card_zero_not_mem {α : Type*} {s : Finset α} (h : s.card = 0) (a : α) :
    a ∉ s := by simp [Finset.card_eq_zero.mp h]

/-! ## BLOCKER-K1 -/

/-- **F₁ BLOCKER-K1.** At the α-corner V₁ of an F₁ target with a 2π/3 model, the unique
covering tile T₁ has its two edges at V₁ lying along the target's two sides at V₁ — in one
order or the other. -/
theorem f1_v1_edges_aligned {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) (hF1 : D.target.F1Data α a b c μ)
    (o : Orientation ℝ Plane (Fin 2)) :
    ∃ (k₀ : Fin 3) (i₀ : Fin N) (j : Fin 3),
      D.target.pts k₀ = (D.tile i₀).pts j ∧
      (SameRay ℝ (D.target.pts (k₀ + 1) - D.target.pts k₀)
                 ((D.tile i₀).pts (j + 1) - D.target.pts k₀) ∧
       SameRay ℝ (D.target.pts (k₀ + 2) - D.target.pts k₀)
                 ((D.tile i₀).pts (j + 2) - D.target.pts k₀)) ∨
      (SameRay ℝ (D.target.pts (k₀ + 2) - D.target.pts k₀)
                 ((D.tile i₀).pts (j + 1) - D.target.pts k₀) ∧
       SameRay ℝ (D.target.pts (k₀ + 1) - D.target.pts k₀)
                 ((D.tile i₀).pts (j + 2) - D.target.pts k₀)) := by
  -- Extract σ from F1Data/GridTriData; k₀ = σ 0 is the α-vertex index of the target
  obtain ⟨-, hgrid⟩ := hF1
  obtain ⟨σ, hα_eq, -, -, -, -, -⟩ := hgrid
  set k₀ : Fin 3 := σ 0
  -- Target corner angle at k₀ is α
  have hcorner : cornerAngle (D.target.pts (k₀ + 1)) (D.target.pts k₀)
      (D.target.pts (k₀ + 2)) = α := by
    show D.target.angleAt k₀ = α
    rw [hα_eq]; push_cast; ring
  -- α is positive
  have hα_pos : 0 < α := by
    have := Erdos634.MarchFlank.cornerAngle_pos D.target k₀; rwa [hcorner] at this
  -- IrrPi inequalities
  have hα_ne0  : α ≠ 0            := irrPi_ne_zero hirr
  have hα_neπ  : α ≠ Real.pi      := irrPi_ne_pi hirr
  have hα_ne2π : α ≠ 2 * Real.pi  := fun h => hirr ⟨2, by push_cast; linarith⟩
  -- Target edge directions from k₀ are nonzero
  have htgt_inj := D.target.indep.injective
  have hu_ne0 : D.target.pts (k₀ + 1) - D.target.pts k₀ ≠ 0 :=
    sub_ne_zero.mpr (htgt_inj.ne (fin3_succ_ne k₀))
  have hv_ne0 : D.target.pts (k₀ + 2) - D.target.pts k₀ ≠ 0 :=
    sub_ne_zero.mpr (htgt_inj.ne (fin3_succ2_ne k₀))
  -- Unsigned angle between target edges = α
  have hangle_tgt : InnerProductGeometry.angle
      (D.target.pts (k₀ + 1) - D.target.pts k₀)
      (D.target.pts (k₀ + 2) - D.target.pts k₀) = α := by
    have : InnerProductGeometry.angle
        (D.target.pts (k₀ + 1) - D.target.pts k₀)
        (D.target.pts (k₀ + 2) - D.target.pts k₀)
      = cornerAngle (D.target.pts (k₀ + 1)) (D.target.pts k₀) (D.target.pts (k₀ + 2)) := by
      rw [cornerAngle, EuclideanGeometry.angle]; simp [vsub_eq_sub]
    rw [this, hcorner]
  -- α < π
  have hα_lt_π : α < Real.pi :=
    lt_of_le_of_ne (hangle_tgt ▸ InnerProductGeometry.angle_le_pi _ _) hα_neπ
  -- Corner multiplicities at k₀: n_α = 1, n_β = n_γ = n_π = 0
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k₀) ∈
      ({α, Real.pi / 3 - α, 2 * Real.pi / 3, Real.pi, 0} : Finset ℝ) :=
    fun i => f1_localAngle_mem D hm k₀ i
  have hmeq := corner_multiplicities D.toDissection
    α (Real.pi / 3 - α) (2 * Real.pi / 3)
    (irrPi_ne_beta hirr) (irrPi_ne_twoThirdsPi hirr) (irrPi_ne_pi hirr) (irrPi_ne_zero hirr)
    (irrPi_beta_ne_gamma hirr) (irrPi_beta_ne_pi hirr) (irrPi_beta_ne_zero hirr)
    twoThirdsPi_ne_pi twoThirdsPi_ne_zero Real.pi_ne_zero k₀ hvals
  rw [hcorner] at hmeq
  obtain ⟨h1, h2, h3, h4⟩ := f1_corner_single_tile hirr
    ({i | (D.tile i).localAngle (D.target.pts k₀) = α} : Finset (Fin N)).card
    ({i | (D.tile i).localAngle (D.target.pts k₀) = Real.pi / 3 - α} : Finset (Fin N)).card
    ({i | (D.tile i).localAngle (D.target.pts k₀) = 2 * Real.pi / 3} : Finset (Fin N)).card
    ({i | (D.tile i).localAngle (D.target.pts k₀) = Real.pi} : Finset (Fin N)).card
    (by push_cast at hmeq ⊢; linarith)
  obtain ⟨i₀, hi₀_eq⟩ := Finset.card_eq_one.mp h1
  -- Get covering tile w at k₀; show w = i₀ by local-angle uniqueness
  obtain ⟨w, hw_mem⟩ := D.toDissection.exists_tile_mem
    (subset_convexHull ℝ _ (Set.mem_range_self k₀) : D.target.pts k₀ ∈ D.target.carrier)
  have hw_ne0 := Erdos634.MarchFlank.localAngle_ne_zero_of_mem (D.tile w) hw_mem
  have hw_vals := hvals w
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw_vals
  have hw_α : (D.tile w).localAngle (D.target.pts k₀) = α := by
    rcases hw_vals with h | h | h | h | h
    · exact h
    · exact absurd (by simpa using h : w ∈ ({i | (D.tile i).localAngle (D.target.pts k₀) = Real.pi / 3 - α} : Finset (Fin N)))
        (finset_card_zero_not_mem h2 w)
    · exact absurd (by simpa using h : w ∈ ({i | (D.tile i).localAngle (D.target.pts k₀) = 2 * Real.pi / 3} : Finset (Fin N)))
        (finset_card_zero_not_mem h3 w)
    · exact absurd (by simpa using h : w ∈ ({i | (D.tile i).localAngle (D.target.pts k₀) = Real.pi} : Finset (Fin N)))
        (finset_card_zero_not_mem h4 w)
    · exact absurd h hw_ne0
  have hw_eq_i₀ : w = i₀ := by
    have hmem_set : w ∈ ({i | (D.tile i).localAngle (D.target.pts k₀) = α} : Finset (Fin N)) := by
      simpa using hw_α
    rw [hi₀_eq] at hmem_set; simpa using hmem_set
  -- So i₀ covers D.target.pts k₀
  have hi₀_mem : D.target.pts k₀ ∈ (D.tile i₀).carrier := hw_eq_i₀ ▸ hw_mem
  -- Local angle at i₀ is α
  have hi₀_α : (D.tile i₀).localAngle (D.target.pts k₀) = α := by
    have : i₀ ∈ ({i | (D.tile i).localAngle (D.target.pts k₀) = α} : Finset (Fin N)) := by
      rw [hi₀_eq]; simp
    simpa using this
  -- D.target.pts k₀ is vertex j of tile i₀
  obtain ⟨j, hjV₁⟩ := Erdos634.ApexEdgesReal.isVertex_of_localAngle_ne
      (D.tile i₀) hα_ne2π hα_neπ hα_ne0 hi₀_α
  -- Edge directions
  set u  := D.target.pts (k₀ + 1) - D.target.pts k₀
  set v  := D.target.pts (k₀ + 2) - D.target.pts k₀
  set u' := (D.tile i₀).pts (j + 1) - D.target.pts k₀
  set v' := (D.tile i₀).pts (j + 2) - D.target.pts k₀
  -- Tile edge directions nonzero (using hjV₁ : D.target.pts k₀ = (D.tile i₀).pts j)
  have htile_inj := (D.tile i₀).indep.injective
  have hu'_ne0 : u' ≠ 0 := by
    show (D.tile i₀).pts (j + 1) - D.target.pts k₀ ≠ 0
    rw [hjV₁]; exact sub_ne_zero.mpr (htile_inj.ne (fin3_succ_ne j))
  have hv'_ne0 : v' ≠ 0 := by
    show (D.tile i₀).pts (j + 2) - D.target.pts k₀ ≠ 0
    rw [hjV₁]; exact sub_ne_zero.mpr (htile_inj.ne (fin3_succ2_ne j))
  -- Tile angle at j = α (from local angle = α)
  have hangle_tile : InnerProductGeometry.angle u' v' = α := by
    have hloc : (D.tile i₀).localAngle ((D.tile i₀).pts j) = α := by
      rw [← hjV₁]; exact hi₀_α
    rw [Tri.localAngle_vertex] at hloc
    have heq : InnerProductGeometry.angle u' v' =
        cornerAngle ((D.tile i₀).pts (j + 1)) ((D.tile i₀).pts j) ((D.tile i₀).pts (j + 2)) := by
      show InnerProductGeometry.angle
          ((D.tile i₀).pts (j + 1) - D.target.pts k₀)
          ((D.tile i₀).pts (j + 2) - D.target.pts k₀) =
          cornerAngle ((D.tile i₀).pts (j + 1)) ((D.tile i₀).pts j) ((D.tile i₀).pts (j + 2))
      rw [hjV₁, cornerAngle, EuclideanGeometry.angle]; simp [vsub_eq_sub]
    rw [heq]; exact hloc
  -- T₁'s other vertices lie in D.target.carrier
  have hcar_sub : (D.tile i₀).carrier ⊆ D.target.carrier := tile_subset_target D.toDissection i₀
  have hj1_tgt : (D.tile i₀).pts (j + 1) ∈ D.target.carrier :=
    hcar_sub (subset_convexHull ℝ _ (Set.mem_range_self (j + 1)))
  have hj2_tgt : (D.tile i₀).pts (j + 2) ∈ D.target.carrier :=
    hcar_sub (subset_convexHull ℝ _ (Set.mem_range_self (j + 2)))
  -- Nonneg combinations: T₁'s other vertices = c₁•u + c₂•v from V₁
  obtain ⟨c₁, c₂, hc₁, hc₂, hcomb_u'⟩ :=
    tri_corner_cone_of_mem' D.target k₀ ((D.tile i₀).pts (j + 1)) hj1_tgt
  obtain ⟨d₁, d₂, hd₁, hd₂, hcomb_v'⟩ :=
    tri_corner_cone_of_mem' D.target k₀ ((D.tile i₀).pts (j + 2)) hj2_tgt
  -- Oangle membership
  have hmemu' : (o.oangle u u').toReal ∈ Set.uIcc 0 (o.oangle u v).toReal :=
    nonneg_comb_oangle_mem_uIcc o hu_ne0 hv_ne0 hu'_ne0 hc₁ hc₂ hcomb_u' hα_pos hα_lt_π hangle_tgt
  have hmemv' : (o.oangle u v').toReal ∈ Set.uIcc 0 (o.oangle u v).toReal :=
    nonneg_comb_oangle_mem_uIcc o hu_ne0 hv_ne0 hv'_ne0 hd₁ hd₂ hcomb_v' hα_pos hα_lt_π hangle_tgt
  -- Apply wedge_forces_ray_eq
  rcases wedge_forces_ray_eq o u v u' v' hu_ne0 hv_ne0 hu'_ne0 hv'_ne0
      α hα_pos hα_lt_π hangle_tgt hangle_tile hmemu' hmemv' with
    ⟨huu', hvv'⟩ | ⟨hvu', huv'⟩
  · exact ⟨k₀, i₀, j, Or.inl ⟨hjV₁, huu', hvv'⟩⟩
  · exact ⟨k₀, i₀, j, Or.inr ⟨hvu', huv'⟩⟩

end Erdos634.Geometry
