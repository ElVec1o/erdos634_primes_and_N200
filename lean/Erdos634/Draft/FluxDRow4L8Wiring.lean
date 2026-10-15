-- Draft/FluxDRow4L8Wiring.lean: connects the consumer `FluxDRow4EdgeReading.row4_a_edge_apex_localAngle_beta`
-- to the real leg chain at the two end edges of a leg.
--
-- The consumer's hypothesis `hvert` is needed only in the form "one of the a-edge's two endpoints is the
-- corner", because the consumer exists in two endpoint variants (`row4_a_edge_apex_localAngle_beta` for
-- `pts k`, `..._beta'` for `pts (k+1)`). `WallEndpoints.chain_endpoints` gives `edgeWest (E 0) = a`, and
-- `Placement.edgeWest` is by definition one of the edge's two vertices. So at the end edges no
-- orientation or chirality data is needed: a case split on the `if` in `edgeWest` suffices. The
-- orientation layer would only say which variant applies (`hvert_of_orient`, under an explicit chirality
-- hypothesis).
--
-- The step "`edgeWest` equals the corner, hence the corner is a tile vertex, by unfolding the `if`" is the
-- first move of `TileAt.congruentDissection_endpoints_of_chain` and of
-- `GammaTrap.congruentDissection_gammatrap`. The wall hypotheses for a target side are discharged by
-- `SideWall.wallFun_*`, `WallDir.hker_wallFun`/`hface_wallFun`, `WallThird.hthird_general` and
-- `ApexLegWord.hdirab_dirFun`. The new content is the composition with the consumer.
import Erdos634.Draft.FluxDRow4EdgeReading
import Erdos634.Draft.FluxDOrientation
import Erdos634.Draft.FluxDOrientationChirality
import Erdos634.Draft.ApexLegWord
import Erdos634.WallThird
import Erdos634.WallDir

namespace Erdos634.Draft.FluxDRow4L8Wiring

open Erdos634.Geometry Erdos634.Placement Erdos634.WallEndpoints Erdos634.BaseChain
open Erdos634.SideWall Erdos634.Geometry.Dissection Erdos634.TilePlacement

variable {N : ℕ}

/-! ## §1 Generic: `edgeWest`/`edgeEast` is one of the edge's own vertices -/

theorem vertex_of_edgeWest (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3)
    (x : Plane) (h : edgeWest D dir e = x) :
    (D.tile e.1).pts e.2 = x ∨ (D.tile e.1).pts (e.2 + 1) = x := by
  unfold edgeWest at h
  split at h
  · exact Or.inl h
  · exact Or.inr h

theorem vertex_of_edgeEast (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3)
    (x : Plane) (h : edgeEast D dir e = x) :
    (D.tile e.1).pts e.2 = x ∨ (D.tile e.1).pts (e.2 + 1) = x := by
  unfold edgeEast at h
  split at h
  · exact Or.inr h
  · exact Or.inl h

/-! ## §2 Unconditional: a real target side's chain starts/ends at a tile vertex on the corner

Every wall hypothesis of `chain_endpoints` is discharged from corpus lemmas for side `k` of
`D.target` (wall functional `wallFun`, reading direction `dirFun`). Only `0 < N` remains. -/

theorem side_chain_end_vertices (hN : 0 < N) (D : CongruentDissection N) (k : Fin 3) :
    ∃ E : ℕ → Fin N × Fin 3, ∃ n : ℕ,
      n = (wallList D.toDissection (wallFun D.target k) 0).length ∧ 0 < n ∧
      (∀ m, m < n → E m ∈ wallList D.toDissection (wallFun D.target k) 0) ∧
      edgeWest D.toDissection (dirFun D.target k).linear (E 0) = D.target.pts k ∧
      edgeEast D.toDissection (dirFun D.target k).linear (E (n - 1)) = D.target.pts (k + 1) ∧
      ((D.tile (E 0).1).pts (E 0).2 = D.target.pts k ∨
        (D.tile (E 0).1).pts ((E 0).2 + 1) = D.target.pts k) ∧
      ((D.tile (E (n - 1)).1).pts (E (n - 1)).2 = D.target.pts (k + 1) ∨
        (D.tile (E (n - 1)).1).pts ((E (n - 1)).2 + 1) = D.target.pts (k + 1)) := by
  classical
  set g := wallFun D.target k with hgdef
  have hab : D.target.pts k ≠ D.target.pts (k + 1) := by
    have h : ∀ x : Fin 3, x ≠ x + 1 := by decide
    exact Erdos634.TilePlacement.pts_ne D.target (h k)
  have hwall : ∀ y ∈ D.target.carrier, g y ≤ 0 := fun y hy => wallFun_le D.target k hy
  have hbase : segment ℝ (D.target.pts k) (D.target.pts (k+1)) ⊆ frontier D.target.carrier := by
    intro y hy
    exact edge_subset_frontier D.target k (by rw [Tri.edge]; exact hy)
  have hline : ∀ y ∈ segment ℝ (D.target.pts k) (D.target.pts (k+1)), g y = 0 := by
    intro y hy
    exact wallFun_eq_zero D.target k (by rw [Tri.edge]; exact hy)
  have hface : ∀ y ∈ D.target.carrier, g y = 0 →
      y ∈ segment ℝ (D.target.pts k) (D.target.pts (k+1)) :=
    hface_wallFun D.target k
  have hthird : ∀ p ∈ wallList D.toDissection g 0, g ((D.tile p.1).pts (p.2 + 2)) < 0 :=
    hthird_general D.toDissection g 0 (wallFun_linear_ne_zero D.target k) hwall
  obtain ⟨E, n, hneq, hn0, hwest, heast, -, hmem, -, -, -, -, -⟩ :=
    chain_endpoints hN D.toDissection g 0 (dirFun D.target k).linear (hker_wallFun D.target k)
      hwall (D.target.pts k) (D.target.pts (k+1)) hab
      (Erdos634.Draft.ApexLegWord.hdirab_dirFun D.target k) hbase hline hface hthird
  exact ⟨E, n, hneq, hn0, hmem, hwest, heast,
    vertex_of_edgeWest _ _ _ _ hwest, vertex_of_edgeEast _ _ _ _ heast⟩

/-! ## §3 Row 4: the consumer's `hvert` DISCHARGED at the leg's first and last edges -/

/-- **First edge of side `k`, apex at corner `k`.** If the first edge of the real chain is an
`a`-edge, its tile has `localAngle = β` at the apex. No `hvert`: it is derived. -/
theorem row4_leg_first_edge_beta (hN : 0 < N) (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = α + β) :
    ∃ E : ℕ → Fin N × Fin 3, ∃ n : ℕ,
      n = (wallList D.toDissection (wallFun D.target k) 0).length ∧ 0 < n ∧
      (∀ m, m < n → E m ∈ wallList D.toDissection (wallFun D.target k) 0) ∧
      edgeWest D.toDissection (dirFun D.target k).linear (E 0) = D.target.pts k ∧
      (dist ((D.tile (E 0).1).pts (E 0).2) ((D.tile (E 0).1).pts ((E 0).2 + 1))
          = sideOpp D.model 0 →
        (D.tile (E 0).1).localAngle (D.target.pts k) = β) := by
  obtain ⟨E, n, hneq, hn0, hmem, hwest, -, hv0, -⟩ := side_chain_end_vertices hN D k
  refine ⟨E, n, hneq, hn0, hmem, hwest, fun hlen => ?_⟩
  rcases hv0 with hv | hv
  · exact Erdos634.Row4EdgeReading.row4_a_edge_apex_localAngle_beta D α β γ hαβ hαγ hαπ hα0
      hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' hscalene (E 0).1 (E 0).2 hlen k
      hcorner hv
  · exact Erdos634.Row4EdgeReading.row4_a_edge_apex_localAngle_beta' D α β γ hαβ hαγ hαπ hα0
      hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' hscalene (E 0).1 (E 0).2 hlen k
      hcorner hv

/-- **Last edge of side `k`, apex at corner `k + 1`.** -/
theorem row4_leg_last_edge_beta (hN : 0 < N) (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α) (hrel : 3 * α + β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = α + β) :
    ∃ E : ℕ → Fin N × Fin 3, ∃ n : ℕ,
      n = (wallList D.toDissection (wallFun D.target k) 0).length ∧ 0 < n ∧
      (∀ m, m < n → E m ∈ wallList D.toDissection (wallFun D.target k) 0) ∧
      edgeEast D.toDissection (dirFun D.target k).linear (E (n - 1)) = D.target.pts (k + 1) ∧
      (dist ((D.tile (E (n - 1)).1).pts (E (n - 1)).2)
          ((D.tile (E (n - 1)).1).pts ((E (n - 1)).2 + 1)) = sideOpp D.model 0 →
        (D.tile (E (n - 1)).1).localAngle (D.target.pts (k + 1)) = β) := by
  obtain ⟨E, n, hneq, hn0, hmem, -, heast, -, hv1⟩ := side_chain_end_vertices hN D k
  refine ⟨E, n, hneq, hn0, hmem, heast, fun hlen => ?_⟩
  rcases hv1 with hv | hv
  · exact Erdos634.Row4EdgeReading.row4_a_edge_apex_localAngle_beta D α β γ hαβ hαγ hαπ hα0
      hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' hscalene (E (n - 1)).1 (E (n - 1)).2
      hlen (k + 1) hcorner hv
  · exact Erdos634.Row4EdgeReading.row4_a_edge_apex_localAngle_beta' D α β γ hαβ hαγ hαπ hα0
      hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' hscalene (E (n - 1)).1 (E (n - 1)).2
      hlen (k + 1) hcorner hv

/-! ## §4 The orientation layer's role: which variant fires (explicit chirality, per P126)

Not needed for §3. Under `0 < det` and `0 ≤ dir (leftDir k)` (P125), the west end is `pts k`
exactly, so the unprimed consumer variant is the one that fires. -/

theorem hvert_of_orient (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3) (x : Plane)
    (hw : edgeWest D dir e = x) (hchir : 0 < (D.tile e.1).det)
    (hsign : 0 ≤ dir ((D.tile e.1).leftDir e.2)) :
    (D.tile e.1).pts e.2 = x := by
  have h := (Erdos634.Draft.FluxDOrientation.edgeWest_edgeEast_of_orient_west_k D dir e.1 e.2
    (Or.inl ⟨hchir, hsign⟩)).1
  rw [← hw]; exact h.symm

/-! ## §5 Witnesses

§2's only hypothesis is `0 < N`; it fires on the concrete `N = 1` dissection `CD0` (P126), whose
single tile has `det > 0`, so the chirality hypothesis of §4 is jointly satisfiable with the (fully
discharged) wall setup on the same real dissection. -/

open Erdos634.Draft.FluxDOrientationChirality in
example : ∃ E : ℕ → Fin 1 × Fin 3, ∃ n : ℕ, 0 < n ∧
    ((CD0.tile (E 0).1).pts (E 0).2 = CD0.target.pts 0 ∨
      (CD0.tile (E 0).1).pts ((E 0).2 + 1) = CD0.target.pts 0) ∧
    0 < (CD0.tile (E 0).1).det := by
  obtain ⟨E, n, -, hn0, -, -, -, hv, -⟩ := side_chain_end_vertices (by norm_num) CD0 0
  refine ⟨E, n, hn0, hv, ?_⟩
  have : (E 0).1 = 0 := Subsingleton.elim _ _
  rw [this]; exact CD0_tile_pos

end Erdos634.Draft.FluxDRow4L8Wiring

#print axioms Erdos634.Draft.FluxDRow4L8Wiring.vertex_of_edgeWest
#print axioms Erdos634.Draft.FluxDRow4L8Wiring.vertex_of_edgeEast
#print axioms Erdos634.Draft.FluxDRow4L8Wiring.side_chain_end_vertices
#print axioms Erdos634.Draft.FluxDRow4L8Wiring.row4_leg_first_edge_beta
#print axioms Erdos634.Draft.FluxDRow4L8Wiring.row4_leg_last_edge_beta
#print axioms Erdos634.Draft.FluxDRow4L8Wiring.hvert_of_orient
