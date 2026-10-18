import Mathlib.Tactic
import Erdos634.Draft.ThmDSector
import Erdos634.Draft.ThmDRowStep

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' (R5 sector step 2): the five tiles at an interior lattice vertex leave exactly one `α`-tile  

At `x = lp ξ η`, interior to the target, let the five tiles `Δ_{ξ-1,η}` (`β`), `Δ_{ξ,η-1}` (`γ`), `∇_{ξ-1,η-1}` (`α`),
`∇_{ξ-1,η}` (`γ`), `∇_{ξ,η-1}` (`β`) be present (Beeson-Rosu Lemma 32/33: with `(ξ,η) = (s-j, j)`).  Their angles add up to `2π - α`;
`residue_alpha` then says every other tile with a vertex at `x` is one tile `G` with angle `α`.  `sector_five_unique` packages this
as: *any tile different from the five whose angle at `x` is nonzero has angle `α`*.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- the vertices of a named triple of one tile are among those of another named triple of the same tile -/
theorem hasV_vertices {t : Fin N} {A B C A' B' C' : Plane} (h : HasV D t A B C) (h' : HasV D t A' B' C') :
    (A = A' ∨ A = B' ∨ A = C') ∧ (B = A' ∨ B = B' ∨ B = C') ∧ (C = A' ∨ C = B' ∨ C = C') := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  obtain ⟨k', m', j', hkm', hkj', hmj', hk', hm', hj'⟩ := h'
  have cov : ∀ i : Fin 3, (D.tile t).pts i = A' ∨ (D.tile t).pts i = B' ∨ (D.tile t).pts i = C' := by
    intro i
    rcases fin3_cover k' m' j' hkm' hkj' hmj' i with h | h | h
    · left; rw [h, hk']
    · right; left; rw [h, hm']
    · right; right; rw [h, hj']
  refine ⟨?_, ?_, ?_⟩
  · rw [← hk]; exact cov k
  · rw [← hm]; exact cov m
  · rw [← hj]; exact cov j

theorem alpha_ne_beta (S : SetupT D u v α β γ L ax ay) : α ≠ β := by
  intro h
  have hirr := S.hirr
  have h5 : α = Real.pi / 4 := by rw [S.hβ] at h; linarith
  apply hirr
  refine ⟨1 / 4, ?_⟩
  rw [h5]; push_cast
  have := Real.pi_ne_zero
  field_simp

theorem alpha_ne_gamma (S : SetupT D u v α β γ L ax ay) : α ≠ γ := by
  intro h
  rw [S.hγ] at h
  have := S.hα
  linarith

theorem beta_ne_gamma (S : SetupT D u v α β γ L ax ay) : β ≠ γ := by
  intro h
  have hirr := S.hirr
  have h5 : α = Real.pi / 5 := by rw [S.hβ, S.hγ] at h; linarith
  apply hirr
  refine ⟨1 / 5, ?_⟩
  rw [h5]; push_cast
  have := Real.pi_ne_zero
  field_simp

theorem lp_ne_of_eta {ε x ξ η ξ' η' : ℝ} (S : SetupT D u v α β γ L ax ay) (h : η ≠ η') :
    lpT (u : ℝ) (v : ℝ) ε x ξ η ≠ lpT (u : ℝ) (v : ℝ) ε x ξ' η' := lpT_ne_eta S.u0 S.uv' S.v2 h

theorem lp_ne_of_xi {ε x ξ η ξ' : ℝ} (S : SetupT D u v α β γ L ax ay) (hε : ε ^ 2 = 1) (h : ξ ≠ ξ') :
    lpT (u : ℝ) (v : ℝ) ε x ξ η ≠ lpT (u : ℝ) (v : ℝ) ε x ξ' η := lpT_ne_xi S.u0 S.uv' S.v2 hε h

/-- **The five tiles at an interior lattice vertex leave one `α`-tile**: any tile different from the five with a nonzero angle at
`x = lp ξ η` has the angle `α` there. -/
theorem sector_five_unique (C : CtxBaseT D u v α β γ L ax ay ε x) {ξ η : ℝ}
    (hx : lpT (u : ℝ) (v : ℝ) ε x ξ η ∈ interior D.target.carrier)
    {t1 t2 t3 t4 t5 : Fin N}
    (h1 : HasV D t1 (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ η)
      (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) (η + 1)))
    (h2 : HasV D t2 (lpT (u : ℝ) (v : ℝ) ε x ξ (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η - 1))
      (lpT (u : ℝ) (v : ℝ) ε x ξ η))
    (h3 : HasV D t3 (lpT (u : ℝ) (v : ℝ) ε x ξ (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) η)
      (lpT (u : ℝ) (v : ℝ) ε x ξ η))
    (h4 : HasV D t4 (lpT (u : ℝ) (v : ℝ) ε x ξ η) (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) (η + 1))
      (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)))
    (h5 : HasV D t5 (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x ξ η)
      (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)) :
    ∀ G : Fin N, G ≠ t1 → G ≠ t2 → G ≠ t3 → G ≠ t4 → G ≠ t5 →
      (D.tile G).localAngle (lpT (u : ℝ) (v : ℝ) ε x ξ η) ≠ 0 →
      (D.tile G).localAngle (lpT (u : ℝ) (v : ℝ) ε x ξ η) = α := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hab := S.tile.hab
  have hac := S.tile.ac
  have hbc := S.tile.bc
  -- the angles at x
  have h1' : HasV D t1 (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) η) (lpT (u : ℝ) (v : ℝ) ε x ((ξ - 1) + 1) η)
      (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) (η + 1)) := hasV_congr h1 rfl (lpT_congr (by ring) rfl) rfl
  have a1 : (D.tile t1).localAngle (lpT (u : ℝ) (v : ℝ) ε x ξ η) = β := by
    have := (U_anglesT hu huv hv2 hε hab hac hbc S.hM h1').2.1
    rwa [show lpT (u : ℝ) (v : ℝ) ε x ((ξ - 1) + 1) η = lpT (u : ℝ) (v : ℝ) ε x ξ η from lpT_congr (by ring) rfl] at this
  have h2' : HasV D t2 (lpT (u : ℝ) (v : ℝ) ε x ξ (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η - 1))
      (lpT (u : ℝ) (v : ℝ) ε x ξ ((η - 1) + 1)) := hasV_congr h2 rfl rfl (lpT_congr rfl (by ring))
  have a2 : (D.tile t2).localAngle (lpT (u : ℝ) (v : ℝ) ε x ξ η) = γ := by
    have := (U_anglesT hu huv hv2 hε hab hac hbc S.hM h2').2.2
    rwa [show lpT (u : ℝ) (v : ℝ) ε x ξ ((η - 1) + 1) = lpT (u : ℝ) (v : ℝ) ε x ξ η from lpT_congr rfl (by ring)] at this
  have h3' : HasV D t3 (lpT (u : ℝ) (v : ℝ) ε x ((ξ - 1) + 1) (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) ((η - 1) + 1))
      (lpT (u : ℝ) (v : ℝ) ε x ((ξ - 1) + 1) ((η - 1) + 1)) :=
    hasV_congr h3 (lpT_congr (by ring) rfl) (lpT_congr rfl (by ring)) (lpT_congr (by ring) (by ring))
  have a3 : (D.tile t3).localAngle (lpT (u : ℝ) (v : ℝ) ε x ξ η) = α := by
    have := (D_anglesT hu huv hv2 hε hab hac hbc S.hM h3').2.2
    rwa [show lpT (u : ℝ) (v : ℝ) ε x ((ξ - 1) + 1) ((η - 1) + 1) = lpT (u : ℝ) (v : ℝ) ε x ξ η from
      lpT_congr (by ring) (by ring)] at this
  have h4' : HasV D t4 (lpT (u : ℝ) (v : ℝ) ε x ((ξ - 1) + 1) η) (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) (η + 1))
      (lpT (u : ℝ) (v : ℝ) ε x ((ξ - 1) + 1) (η + 1)) :=
    hasV_congr h4 (lpT_congr (by ring) rfl) rfl (lpT_congr (by ring) rfl)
  have a4 : (D.tile t4).localAngle (lpT (u : ℝ) (v : ℝ) ε x ξ η) = γ := by
    have := (D_anglesT hu huv hv2 hε hab hac hbc S.hM h4').1
    rwa [show lpT (u : ℝ) (v : ℝ) ε x ((ξ - 1) + 1) η = lpT (u : ℝ) (v : ℝ) ε x ξ η from lpT_congr (by ring) rfl] at this
  have h5' : HasV D t5 (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x ξ ((η - 1) + 1))
      (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) ((η - 1) + 1)) :=
    hasV_congr h5 rfl (lpT_congr rfl (by ring)) (lpT_congr rfl (by ring))
  have a5 : (D.tile t5).localAngle (lpT (u : ℝ) (v : ℝ) ε x ξ η) = β := by
    have := (D_anglesT hu huv hv2 hε hab hac hbc S.hM h5').2.1
    rwa [show lpT (u : ℝ) (v : ℝ) ε x ξ ((η - 1) + 1) = lpT (u : ℝ) (v : ℝ) ε x ξ η from lpT_congr rfl (by ring)] at this
  have hαβ := alpha_ne_beta S
  have hαγ := alpha_ne_gamma S
  have hβγ := beta_ne_gamma S
  -- the five tiles are pairwise distinct
  have n12 : t1 ≠ t2 := ne_of_angle (by rw [a1, a2]; exact hβγ)
  have n13 : t1 ≠ t3 := ne_of_angle (by rw [a1, a3]; exact hαβ.symm)
  have n14 : t1 ≠ t4 := ne_of_angle (by rw [a1, a4]; exact hβγ)
  have n23 : t2 ≠ t3 := ne_of_angle (by rw [a2, a3]; exact hαγ.symm)
  have n24 : t2 ≠ t4 := by
    intro h
    subst h
    have hm := hasV_vertices h2 h4
    -- the vertex `lp ξ (η-1)` of `t2` is not a vertex of `t4`
    rcases hm.1 with e | e | e
    · exact lp_ne_of_eta S (by linarith : η - 1 ≠ η) e
    · exact lp_ne_of_eta S (by linarith : η - 1 ≠ η + 1) e
    · exact lp_ne_of_eta S (by linarith : η - 1 ≠ η + 1) e
  have n25 : t2 ≠ t5 := ne_of_angle (by rw [a2, a5]; exact hβγ.symm)
  have n34 : t3 ≠ t4 := ne_of_angle (by rw [a3, a4]; exact hαγ)
  have n35 : t3 ≠ t5 := ne_of_angle (by rw [a3, a5]; exact hαβ)
  have n45 : t4 ≠ t5 := ne_of_angle (by rw [a4, a5]; exact hβγ.symm)
  have n15 : t1 ≠ t5 := by
    intro h
    subst h
    have hm := hasV_vertices h1 h5
    rcases hm.1 with e | e | e
    · exact lp_ne_of_eta S (by linarith : η ≠ η - 1) e
    · exact lp_ne_of_xi S hε (by linarith : ξ - 1 ≠ ξ) e
    · exact lp_ne_of_xi S hε (by linarith : ξ - 1 ≠ ξ + 1) e
  -- the sum of the five angles is 2π - α
  have hsum : ∑ i ∈ ({t1, t2, t3, t4, t5} : Finset (Fin N)), (D.tile i).localAngle (lpT (u : ℝ) (v : ℝ) ε x ξ η)
      = 2 * Real.pi - α := by
    rw [Finset.sum_insert (by simp [n12, n13, n14, n15]), Finset.sum_insert (by simp [n23, n24, n25]),
      Finset.sum_insert (by simp [n34, n35]), Finset.sum_insert (by simp [n45]), Finset.sum_singleton,
      a1, a2, a3, a4, a5, S.hβ, S.hγ]
    ring
  have hβpos : 0 < β := by
    have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
    have e : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
    rw [e] at h; exact h
  have h3α : 3 * α < Real.pi := by have := S.hβ; linarith
  obtain ⟨G0, hG0S, hG0α, hrest⟩ := residue_alpha D.toDissection D.model (fun i => (D.tiles_congruent i).symm) α S.hirr
    (S.hM.hα') (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α hx {t1, t2, t3, t4, t5} hsum
  intro G g1 g2 g3 g4 g5 hne
  have hGS : G ∉ ({t1, t2, t3, t4, t5} : Finset (Fin N)) := by simp [g1, g2, g3, g4, g5]
  by_cases hG : G = G0
  · rw [hG]; exact hG0α
  · exact absurd (hrest G hGS hG) hne

#print axioms sector_five_unique
end Erdos634.Draft.ThmDRun
