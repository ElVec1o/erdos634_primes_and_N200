/-
Draft/WGapChord2.lean -- written 15 November 2026 (session 3).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 chord facts (C), "no far-side tile has p'(i,j-i) in the relative interior of an edge").
Not imported by any aggregate.  Module W5d: a far-side tile with an edge ending at `B` on the line prevents any chain edge from straddling `B`.

* `centroid_interior` : the centroid of the three (distinct) vertices of a tile is an interior point of the tile.
* `straddle_excl`     : let `τ` be a tile with the vertices `A`, `B` on the line `F = c` and `W` strictly on the far side `F < c`.  Then no chain edge of the line
  straddles `B` relative to the extension point `A` (any `Q` beyond `B`).  (The straddler has the straight angle `π` at `B` and contains every push into `F < 0`;
  `τ` has the vertex `B`, the push towards its centroid lies in both interiors, so they are one tile, but its angle at `B` is `< π`.)
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapChord1

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

theorem pts_sum_perm (T : Tri) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n) (hmn : m ≠ n) :
    T.pts k + T.pts m + T.pts n = T.pts 0 + T.pts 1 + T.pts 2 := by
  have hperm : ∀ k m n : Fin 3, k ≠ m → k ≠ n → m ≠ n →
      (k = 0 ∧ m = 1 ∧ n = 2) ∨ (k = 0 ∧ m = 2 ∧ n = 1) ∨ (k = 1 ∧ m = 0 ∧ n = 2) ∨
      (k = 1 ∧ m = 2 ∧ n = 0) ∨ (k = 2 ∧ m = 0 ∧ n = 1) ∨ (k = 2 ∧ m = 1 ∧ n = 0) := by decide
  rcases hperm k m n hkm hkn hmn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> abel

/-- the centroid of the three vertices of a tile is interior -/
theorem centroid_interior (T : Tri) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n) (hmn : m ≠ n) :
    (1 / 3 : ℝ) • (T.pts k + T.pts m + T.pts n) ∈ interior T.carrier := by
  apply Erdos634.ChordTraceReal.Tri.mem_interior_of_pos T
  intro i
  have hc := Erdos634.Subdivision.Tri.coord_eq_of_combo T ((1 / 3 : ℝ) • (T.pts k + T.pts m + T.pts n))
    (fun _ => 1 / 3) (by norm_num) (by
      rw [pts_sum_perm T hkm hkn hmn]
      simp only [smul_add]) i
  rw [hc]
  norm_num

theorem lineMap_comb {X A : Plane} (ε : ℝ) :
    X + ε • (A - X) = (1 - ε) • X + ε • A := by
  module

section excl

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **A far-side tile with the edge `[A, B]` on the line excludes every straddler at `B`.** -/
theorem straddle_excl (S : SetupG D e f α β γ L ax ay) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {A B W Q : Plane} {τ : Fin N} (hV : HasV D τ A B W) (hfA : F A = c) (hfB : F B = c) (hW : F W < c)
    (hBQ : B ≠ Q) (hfQ : F Q = c) (hABQ : B ∈ openSegment ℝ A Q) :
    ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) A B Q := by
  intro ed hed hs
  obtain ⟨-, hang, hpush⟩ := straddle_data D.toDissection F hF c hBQ hfB hfQ hfA hABQ hed hs
  obtain ⟨k, m, n, hkm, hkn, hmn, hk, hm, hn⟩ := hV
  set G : Plane := (1 / 3 : ℝ) • (A + B + W) with hG
  have hGint : G ∈ interior (D.tile τ).carrier := by
    have := centroid_interior (D.tile τ) hkm hkn hmn
    rwa [hk, hm, hn] at this
  have hFv : F (G - B) < 0 := by
    have h1 : F G = (F A + F B + F W) / 3 := by
      rw [hG, map_smul, map_add, map_add, smul_eq_mul]; ring
    rw [map_sub, h1, hfA, hfB]; linarith
  obtain ⟨ε₀, hε₀, hε⟩ := hpush (G - B) hFv
  set ε := min (ε₀ / 2) (1 / 2) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεlt : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεlt1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h1 := hε ε hεpos hεlt
  have hBmem : B ∈ (D.tile τ).carrier := by
    rw [← hm]; exact subset_convexHull ℝ _ ⟨m, rfl⟩
  have h2 : B + ε • (G - B) ∈ interior (D.tile τ).carrier := by
    have hsub := (D.tile τ).convex.openSegment_interior_self_subset_interior hGint hBmem
    apply hsub
    refine ⟨ε, 1 - ε, hεpos, by linarith, by ring, ?_⟩
    module
  have heq : ed.1 = τ := by
    by_contra hne
    exact Set.disjoint_left.mp (D.interiors_disjoint hne) h1 h2
  rw [heq] at hang
  have hvc := vertex_angle_cases S τ hkm.symm hmn hkn
  rw [hm] at hvc
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  rcases hvc with h | h | h <;> rw [h] at hang <;> linarith

end excl

#print axioms centroid_interior
#print axioms straddle_excl

end Erdos634.Draft.WGapStmt
