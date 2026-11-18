/-
Draft/WGapWedge.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (LF, Lemma 3.2; uses W1-W11 of WEDGE_USES.md).
Not imported by any aggregate.  Module W3a: THE WEDGE API, part A (COUNT: algebra only).

A free wedge of size `θ` at a point `X`: the tiles already known at `X` are the finset `K`; their local angles at `X` sum to `Ω - θ`, where `Ω` is the
total angle at `X` (`2π` at an interior point, `π` at a non-corner boundary point: `Dissection.hasAngleSums`).  Then the tiles NOT in `K` have angles at
`X` summing to `θ`; each is `α`, `β`, `γ` or `0` (a tile with `π` or `2π` would exceed `θ < π`), so by the ledger (`WGapAngles.fill_*`) the multiset is determined.

* `localAngle_vals`   : a tile's local angle at ANY point is one of `α, β, γ, π, 2π, 0`.
* `wedge_count`       : the count theorem (counts `x, y, z` of the `α`-, `β`-, `γ`-tiles outside `K`, `x α + y β + z γ = θ`).
* `wedge_alpha`, `wedge_beta`, `wedge_alpha_beta`, `wedge_2alpha`, `wedge_3alpha`, `wedge_gamma`, `wedge_pi_sub_beta`: the wedge sizes of WEDGE_USES.md.
Geometry (which tile is adjacent to which ray, with which edge on it) is part B (next module).  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapInterior

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

variable {N : ℕ} {D : CongruentDissection N}

section vals

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- a tile's local angle at ANY point of the plane is `α, β, γ, π, 2π` or `0` -/
theorem localAngle_vals (S : SetupG D e f α β γ L ax ay) (i : Fin N) (X : Plane) :
    (D.tile i).localAngle X = α ∨ (D.tile i).localAngle X = β ∨ (D.tile i).localAngle X = γ ∨
      (D.tile i).localAngle X = Real.pi ∨ (D.tile i).localAngle X = 2 * Real.pi ∨
      (D.tile i).localAngle X = 0 := by
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) X with ⟨j, hX, -⟩ | h | h | h
  · subst hX
    have h3 : ∀ j : Fin 3, j ≠ j + 1 ∧ j ≠ j + 2 ∧ j + 1 ≠ j + 2 := by decide
    obtain ⟨h1, h2, h12⟩ := h3 j
    have hang := angle_at_vertexG D S.tile S.hM i h1 h2 h12
    rcases vertex_dist_casesG D S.hM i h12 with d | d | d
    · exact Or.inl (hang.1 d)
    · exact Or.inr (Or.inl (hang.2.1 d))
    · exact Or.inr (Or.inr (Or.inl (hang.2.2 d)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- **THE COUNT THEOREM** (API part A).  `K` = the tiles known at `X`; `Ω` = the total angle at `X`; `θ < π` the free wedge.  The tiles outside
`K` that meet `X` are `x` tiles showing `α`, `y` showing `β`, `z` showing `γ`, with `x α + y β + z γ = θ`. -/
theorem wedge_count (S : SetupG D e f α β γ L ax ay) {X : Plane} {Ω θ : ℝ}
    (hΩ : ∑ i, (D.tile i).localAngle X = Ω) (K : Finset (Fin N))
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - θ) (hθπ : θ < Real.pi) :
    ∃ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = θ ∧
      ((Finset.univ \ K).filter (fun i => (D.tile i).localAngle X = α)).card = x ∧
      ((Finset.univ \ K).filter (fun i => (D.tile i).localAngle X = β)).card = y ∧
      ((Finset.univ \ K).filter (fun i => (D.tile i).localAngle X = γ)).card = z ∧
      ∀ i ∈ Finset.univ \ K, (D.tile i).localAngle X = α ∨ (D.tile i).localAngle X = β ∨
        (D.tile i).localAngle X = γ ∨ (D.tile i).localAngle X = 0 := by
  have hA := S.hA
  obtain ⟨hα0, hβ0, hαγ, hβγ, -, -, hγπ, -⟩ := Erdos634.Draft.WGapAngles.angle_ineqs hA
  have hαβ : α ≠ β := hA.hαβ
  have hpi := Real.pi_pos
  set g : Fin N → ℝ := fun i => (D.tile i).localAngle X with hg
  have hg0 : ∀ i, 0 ≤ g i := fun i => Tri.localAngle_nonneg _ _
  have hsd := Finset.sum_sdiff (Finset.subset_univ K) (f := g)
  have hS : ∑ i ∈ Finset.univ \ K, g i = θ := by
    have h1 : ∑ i, g i = Ω := hΩ
    have h2 : ∑ i ∈ K, g i = Ω - θ := hK
    linarith
  have hvals : ∀ i ∈ Finset.univ \ K, g i = α ∨ g i = β ∨ g i = γ ∨ g i = 0 := by
    intro i hi
    have hle : g i ≤ θ := by
      rw [← hS]
      exact Finset.single_le_sum (f := g) (fun j _ => hg0 j) hi
    rcases localAngle_vals S i X with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exfalso; have : g i = Real.pi := h
      linarith
    · exfalso; have : g i = 2 * Real.pi := h
      linarith
    · exact Or.inr (Or.inr (Or.inr h))
  have hpt : ∀ i ∈ Finset.univ \ K, g i =
      α * (if g i = α then 1 else 0) + β * (if g i = β then 1 else 0) + γ * (if g i = γ then 1 else 0) := by
    intro i hi
    rcases hvals i hi with h | h | h | h
    · rw [h]; simp [hαβ, hαγ.ne]
    · rw [h]; simp [hαβ.symm, hβγ.ne]
    · rw [h]; simp [hαγ.ne', hβγ.ne']
    · rw [h]; simp [hα0.ne, hβ0.ne, (hα0.trans hαγ).ne]
  have hsum : ∑ i ∈ Finset.univ \ K, g i =
      α * ((Finset.univ \ K).filter (fun i => g i = α)).card +
      β * ((Finset.univ \ K).filter (fun i => g i = β)).card +
      γ * ((Finset.univ \ K).filter (fun i => g i = γ)).card := by
    rw [Finset.sum_congr rfl hpt]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
  refine ⟨_, _, _, ?_, rfl, rfl, rfl, hvals⟩
  rw [← hS, hsum]
  ring

end vals

end Erdos634.Draft.WGapStmt
