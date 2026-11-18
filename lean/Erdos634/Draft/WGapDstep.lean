/-
Draft/WGapDstep.lean -- written 15 November 2026 (session 4).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 step (D); FINDINGS F10).
Not imported by any aggregate.  Module W7a: `chord_D_step`: at an inner chord point `X = p'(ξ,η)` with the four known tiles `U'(ξ-1,η) [β]`, `U'(ξ,η-1) [γ]`,
`D'(ξ-1,η-1) [α]`, `D'(ξ-1,η) [γ]` (the far tile of the previous a-step), every far-side tile `τ` with vertices `X`, `p'(ξ+1,η-1)`, `W` (`cross (P-X) (W-X) < 0`) is
`D'(ξ,η-1) = (X, p'(ξ+1,η), p'(ξ+1,η-1))`: a fifth tile showing `γ` at `X` would give total angle `π + 2γ = 2π + α > 2π`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapW1d

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

section dstep

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 1000000 in
/-- **(D) step**: the far tile on the next a-step is `D'`. -/
theorem chord_D_step (S : SetupG D e f α β γ L ax ay) (x ξ η : ℝ)
    (hU1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x (ξ - 1) (η + 1)) (mpG (e : ℝ) f 1 x (ξ - 1) η))
    (hU2 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x ξ (η - 1)) (mpG (e : ℝ) f 1 x (ξ + 1) (η - 1)))
    (hD1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x ξ (η - 1)) (mpG (e : ℝ) f 1 x (ξ - 1) η))
    (hD2 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x (ξ - 1) (η + 1)) (mpG (e : ℝ) f 1 x ξ (η + 1)))
    {τ : Fin N} {W : Plane}
    (hτ : HasV D τ (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x (ξ + 1) (η - 1)) W)
    (hW : cross (mpG (e : ℝ) f 1 x (ξ + 1) (η - 1) - mpG (e : ℝ) f 1 x ξ η) (W - mpG (e : ℝ) f 1 x ξ η) < 0) :
    HasV D τ (mpG (e : ℝ) f 1 x ξ η) (mpG (e : ℝ) f 1 x (ξ + 1) η) (mpG (e : ℝ) f 1 x (ξ + 1) (η - 1)) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hef : (e : ℝ) < f := by exact_mod_cast S.hef
  have hf0 : (0 : ℝ) < f := he0.trans hef
  obtain ⟨k1, h1⟩ := hU1
  obtain ⟨k2, h2⟩ := hU2
  obtain ⟨k3, h3⟩ := hD1
  obtain ⟨k4, h4⟩ := hD2
  have hτ' := hτ
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hτ'
  set X := mpG (e : ℝ) f 1 x ξ η with hX
  set P := mpG (e : ℝ) f 1 x (ξ + 1) (η - 1) with hP
  have hA := S.hA
  obtain ⟨hα0, hβ0, hαγ, hβγ, -, -, hγπ, -⟩ := Erdos634.Draft.WGapAngles.angle_ineqs hA
  obtain ⟨hαπ, hβπ, hγπ', -, -, -⟩ := angles_lt_pi S
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hmp : ∀ d : ℝ, 0 ≤ d → ∀ ξ1 η1 ξ2 η2 : ℝ, QfG (e : ℝ) f (ξ1 - ξ2) (η1 - η2) = d ^ 2 →
      dist (mpG (e : ℝ) f 1 x ξ1 η1) (mpG (e : ℝ) f 1 x ξ2 η2) = d :=
    fun d hd ξ1 η1 ξ2 η2 hq => dist_mpG he0 hef x hd hq
  have a1 : (D.tile k1).localAngle X = β :=
    ((h1.anglesG S.tile S.hM).2.1) (hmp _ hb0.le _ _ _ _ (by unfold QfG; ring))
  have a2 : (D.tile k2).localAngle X = γ :=
    ((h2.anglesG S.tile S.hM).2.2) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have a3 : (D.tile k3).localAngle X = α :=
    ((h3.anglesG S.tile S.hM).1) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have a4 : (D.tile k4).localAngle X = γ :=
    ((h4.anglesG S.tile S.hM).2.2) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have nv : ∀ {a b a' b' : ℝ}, (a ≠ a' ∨ b ≠ b') → mpG (e : ℝ) f 1 x a b ≠ mpG (e : ℝ) f 1 x a' b' := by
    intro a b a' b' h hh
    obtain ⟨h1, h2⟩ := mpG_inj he0 hef hh
    rcases h with h | h
    · exact h h1
    · exact h h2
  have hne : ∀ {i j : Fin N} (u v : ℝ), (D.tile i).localAngle X = u → (D.tile j).localAngle X = v → u ≠ v → i ≠ j :=
    fun u v hu hv huv => ne_of_angle (by rw [hu, hv]; exact huv)
  have n24 : k2 ≠ k4 := by
    obtain ⟨i, hi⟩ := hasV_second h2
    exact HasV.ne_of_vertex h4 hi (nv (Or.inr (by linarith))) (nv (Or.inr (by linarith))) (nv (Or.inr (by linarith)))
  -- X is interior
  have hXint : X ∈ interior D.target.carrier := by
    refine interior_of_two_tiles D.toDissection h1.mem₁ n24 a2 a4 ?_
    have hg := hA.hγdef
    have hr := hA.hrel
    linarith
  have hΩ : ∑ i, (D.tile i).localAngle X = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq X
    rw [this, D.target.localAngle_interior hXint]
  have hβγ' : β ≠ γ := hβγ.ne
  have hαβ' : α ≠ β := hA.hαβ
  have hαγ' : α ≠ γ := hαγ.ne
  -- the angle of τ at X
  have hang := angle_at_vertexG D S.tile S.hM τ hkm hkj hmj
  have hXP : dist X P = (e : ℝ) * f := by
    rw [hX, hP]
    have := dist_mp_a (x := x) (ε := 1) he0 hef (by norm_num) ξ (η - 1)
    rw [dist_comm]; simpa using this
  have hXPτ : dist ((D.tile τ).pts k) ((D.tile τ).pts m) = (e : ℝ) * f := by rw [hk, hm]; exact hXP
  have hac : (e : ℝ) * f ≠ (f : ℝ) ^ 2 := by nlinarith
  have hXW_ne : cross (P - X) (W - X) ≠ 0 := hW.ne
  have hτβ : (D.tile τ).localAngle X = β := by
    rcases vertex_dist_casesG D S.hM τ hmj with d | d | d
    · exfalso
      have hα' := hang.1 d
      rw [hk] at hα'
      have hs := sides_of_alpha S τ hkm hkj hmj (by rw [hk]; exact hα')
      rcases hs.2 with ⟨h', -⟩ | ⟨h', -⟩
      · rw [hXPτ] at h'; exact hac h'
      · rw [hXPτ] at h'
        have hb' : dist ((D.tile τ).pts m) ((D.tile τ).pts j) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by rw [d, h']
        have := hang.2.1 hb'
        rw [hk] at this
        rw [hα'] at this; exact hαβ' this
    · have := hang.2.1 d; rw [hk] at this; exact this
    · exfalso
      have hγ' := hang.2.2 d
      rw [hk] at hγ'
      -- five distinct tiles, total > 2 pi
      have hcWne : W ≠ X := by intro h; apply hXW_ne; rw [h]; simp [cross]
      have hcWP : W ≠ P := by intro h; apply hXW_ne; rw [h]; simp [cross]; ring
      have hcWQ : W ≠ mpG (e : ℝ) f 1 x ξ (η - 1) := by
        intro h
        have hc : cross (P - X) (mpG (e : ℝ) f 1 x ξ (η - 1) - X) = kapG (e : ℝ) f := by
          rw [hP, hX, cross_mpG he0 hef]; ring
        rw [h] at hW; have := kapG_pos he0 hef; linarith
      have nτ2 : τ ≠ k2 := by
        have hWv : (D.tile τ).pts j = W := hj
        exact HasV.ne_of_vertex h2 hWv hcWne hcWQ hcWP
      have nτ4 : τ ≠ k4 := by
        have hPv : (D.tile τ).pts m = P := hm
        exact HasV.ne_of_vertex h4 hPv (nv (Or.inl (by linarith))) (nv (Or.inl (by linarith))) (nv (Or.inl (by linarith)))
      set K : Finset (Fin N) := {k1, k2, k3, k4, τ} with hKdef
      have hKsum : ∑ i ∈ K, (D.tile i).localAngle X = 2 * Real.pi + α := by
        rw [hKdef, sum_five _ (hne _ _ a1 a2 hβγ') (hne _ _ a1 a3 hαβ'.symm) (hne _ _ a1 a4 hβγ')
          (hne _ _ a1 hγ' hβγ') (hne _ _ a2 a3 hαγ'.symm) n24 nτ2.symm (hne _ _ a3 a4 hαγ')
          (hne _ _ a3 hγ' hαγ') nτ4.symm, a1, a2, a3, a4, hγ']
        have hr := hA.hrel
        have hg := hA.hγdef
        linarith
      have hle : ∑ i ∈ K, (D.tile i).localAngle X ≤ ∑ i, (D.tile i).localAngle X :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K)
          (fun i _ _ => Tri.localAngle_nonneg _ _)
      rw [hKsum, hΩ] at hle
      linarith
  -- identify the third vertex
  have hs := sides_of_beta S τ hkm hkj hmj (by rw [hk]; exact hτβ)
  obtain ⟨hPW, hsd⟩ := hs
  have hXW : dist X W = (f : ℝ) ^ 2 := by
    rcases hsd with ⟨-, h'⟩ | ⟨h', -⟩
    · rw [← hk, ← hj]; exact h'
    · exfalso; rw [hXPτ] at h'; exact hac h'
  have hZ : mpG (e : ℝ) f 1 x (ξ + 1) η = W := by
    have hXPne : X ≠ P := by
      intro h; rw [← h, dist_self] at hXP
      have : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
      linarith
    have hcrossZ : cross (P - X) (mpG (e : ℝ) f 1 x (ξ + 1) η - X) < 0 := by
      rw [hP, hX, cross_mpG he0 hef]
      have := kapG_pos he0 hef
      nlinarith
    refine same_third hXPne ?_ ?_ hcrossZ hW
    · rw [dist_comm W X, dist_comm, hXW]
      exact hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring)
    · have hb : dist P W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by rw [← hm, ← hj]; exact hPW
      rw [dist_comm W P, hb, dist_comm]
      exact hmp _ hb0.le _ _ _ _ (by unfold QfG; ring)
  rw [hZ]
  exact (hτ.rot.rot).swap

end dstep

#print axioms chord_D_step

end Erdos634.Draft.WGapStmt
