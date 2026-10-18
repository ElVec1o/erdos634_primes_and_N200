import Mathlib.Tactic
import Erdos634.Draft.ThmDSector2
import Erdos634.Draft.ThmDLegPos

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha is ours.

# Theorem D' (ThmDGeo, item (1')): run tiles from tile data  

`dist_of_angle_a/b`: in a `SetupT` frame a tile whose local angle at a vertex is `α` (`β`) has the opposite side `u²` (`b`).
`UTT_of_edge`: a tile with two vertices `lp ξ 0`, `lp (ξ+1) 0` (on the base line, either orientation `ε`) with local angles
`α`, `β` is the lattice tile `U(ξ,0)` (`UTT`): the third vertex is forced by `third_unique_F` (via `row_edge_UT`).
`hrun_of_tiles`: the hypothesis `hrun` of `lemmaK2_final/_corner/_corner_m` from the family of such tiles.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.MarchSlots Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem dist_of_angle_ab (S : SetupT D u v α β γ L ax ay) (i : Fin N) {k m j : Fin 3} (hkm : k ≠ m)
    (hkj : k ≠ j) (hmj : m ≠ j) :
    ((D.tile i).localAngle ((D.tile i).pts k) = α →
      dist ((D.tile i).pts m) ((D.tile i).pts j) = (u : ℝ) ^ 2) ∧
    ((D.tile i).localAngle ((D.tile i).pts k) = β →
      dist ((D.tile i).pts m) ((D.tile i).pts j) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2) := by
  have hd := tile_distinct S.hco S.hu S.huv
  have hab := hd.1
  have hac := hd.2.1
  have hbc := hd.2.2
  have hang := angle_at_vertexT D hab hac hbc S.hM i hkm hkj hmj
  have hαβ := alpha_ne_beta S
  have hαγ := alpha_ne_gamma S
  have hβγ := beta_ne_gamma S
  have hcases := vertex_dist_casesT D S.hM i hmj
  constructor
  · intro h
    rcases hcases with h1 | h1 | h1
    · exact h1
    · exact absurd (h.symm.trans (hang.2.1 h1)) hαβ
    · exact absurd (h.symm.trans (hang.2.2 h1)) hαγ
  · intro h
    rcases hcases with h1 | h1 | h1
    · exact absurd (h.symm.trans (hang.1 h1)) hαβ.symm
    · exact h1
    · exact absurd (h.symm.trans (hang.2.2 h1)) hβγ

theorem UTT_of_edge (S : SetupT D u v α β γ L ax ay) {ε x : ℝ} (hε : ε ^ 2 = 1) {ξ : ℝ} {t : Fin N}
    {k m : Fin 3} (hkm : k ≠ m) (hk : (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x ξ 0)
    (hm : (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) 0)
    (hαk : (D.tile t).localAngle ((D.tile t).pts k) = α)
    (hβm : (D.tile t).localAngle ((D.tile t).pts m) = β) :
    UTT D (u : ℝ) (v : ℝ) ε x ξ 0 := by
  obtain ⟨j, hkj, hmj⟩ := MarchInduction.fin3_third k m hkm
  have hkj' : k ≠ j := fun h => hkj h.symm
  have hmj' : m ≠ j := fun h => hmj h.symm
  have s2 := (dist_of_angle_ab S t hkm hkj' hmj').1 hαk
  have s1 : dist ((D.tile t).pts j) ((D.tile t).pts k) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
    have := (dist_of_angle_ab S t hkm.symm hmj' hkj').2 hβm
    rw [dist_comm]; exact this
  refine ⟨t, ?_⟩
  have hle : ∀ i, GHT (u : ℝ) (v : ℝ) ((D.tile t).pts i) ≤ -(((u : ℝ) * v) * hhT (u : ℝ) (v : ℝ) * 0) := by
    intro i
    rw [GHT_apply]
    have := (S.pts_mem t i).1
    have := S.c_pos
    nlinarith
  have hm' : (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) 0 := hm
  have := row_edge_UT S hε hkm hkj' hmj' hk hm' hle s1 (by rw [dist_comm]; exact s2)
  simpa using this

theorem hrun_of_tiles (S : SetupT D u v α β γ L ax ay) {ε x : ℝ} (hε : ε ^ 2 = 1) {n : ℕ}
    (h : ∀ i : ℕ, i < n → ∃ (t : Fin N) (k m : Fin 3), k ≠ m ∧
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) 0 ∧
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) 0 ∧
      (D.tile t).localAngle ((D.tile t).pts k) = α ∧ (D.tile t).localAngle ((D.tile t).pts m) = β) :
    ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) ε x (i : ℝ) 0 := by
  intro i hi
  obtain ⟨t, k, m, hkm, hk, hm, hα, hβ⟩ := h i hi
  exact UTT_of_edge S hε hkm hk hm hα hβ

#print axioms hrun_of_tiles
end Erdos634.Draft.ThmDRun
