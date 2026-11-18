/-
Draft/WGapW1c.lean -- written 15 November 2026 (session 4).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (Lemma 3.3, use W1; FINDINGS F9).
Not imported by any aggregate.  Module W6d: `w1_clamp` = the start clamp hX of `chord_all` at `X = p'(0,η)` for the run `[X, X + n (Y - X)]`, `Y = p'(1,η-1)`,
from the four known tiles of `w1_fill` (angle count with theta = 2 beta, `no_straddle_gen`).  Same setup as `w1_fill` (copied, no new hypothesis).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapW1b

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

section w1c

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 1000000 in
/-- **the start clamp of the chord at `p'(0,η)`**, from the four known tiles. -/
theorem w1_clamp (S : SetupG D e f α β γ L ax ay) (x η : ℝ)
    (hU0 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (lpG (e : ℝ) f 1 x 1 η) (lpG (e : ℝ) f 1 x 0 (η + 1)))
    (hT : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 1 η) (mpG (e : ℝ) f 1 x 0 (η + 1)))
    (hT1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 1 (η - 1)) (mpG (e : ℝ) f 1 x 0 (η - 1)))
    (hU1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (lpG (e : ℝ) f 1 x 0 (η - 1)) (lpG (e : ℝ) f 1 x 1 (η - 1)))
    {n : ℕ} (hn1 : 1 ≤ n) :
    ∀ ed ∈ D.lineChain (crossL (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (cross (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 0 η)),
      ¬ Straddles ((D.tile ed.1).edge ed.2)
        (mpG (e : ℝ) f 1 x 0 η + (-1 : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (mpG (e : ℝ) f 1 x 0 η)
        (mpG (e : ℝ) f 1 x 0 η + (n : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η)) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hef : (e : ℝ) < f := by exact_mod_cast S.hef
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  obtain ⟨k0, h0⟩ := hU0
  obtain ⟨k1, h1⟩ := hT
  obtain ⟨t0, ht0⟩ := hT1
  obtain ⟨k3, h3⟩ := hU1
  set X := mpG (e : ℝ) f 1 x 0 η with hX
  set Y := mpG (e : ℝ) f 1 x 1 (η - 1) with hY
  have hA := S.hA
  obtain ⟨hα0, hβ0, hαγ, hβγ, -, -, hγπ, -⟩ := Erdos634.Draft.WGapAngles.angle_ineqs hA
  obtain ⟨hαπ, hβπ, hγπ', -, -, -⟩ := angles_lt_pi S
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hsM := sMir_pos he0 hef
  have hmp : ∀ d : ℝ, 0 ≤ d → ∀ ξ1 η1 ξ2 η2 : ℝ, QfG (e : ℝ) f (ξ1 - ξ2) (η1 - η2) = d ^ 2 →
      dist (mpG (e : ℝ) f 1 x ξ1 η1) (mpG (e : ℝ) f 1 x ξ2 η2) = d :=
    fun d hd ξ1 η1 ξ2 η2 hq => dist_mpG he0 hef x hd hq
  have hlp : ∀ d : ℝ, 0 ≤ d → ∀ ξ1 η1 ξ2 η2 : ℝ, QfG (e : ℝ) f (ξ1 - ξ2) (η1 - η2) = d ^ 2 →
      dist (lpG (e : ℝ) f 1 x ξ1 η1) (lpG (e : ℝ) f 1 x ξ2 η2) = d :=
    fun d hd ξ1 η1 ξ2 η2 hq => dist_lpG he0 hef hε hd hq
  have hl0 : ∀ ξ : ℝ, lpG (e : ℝ) f 1 x 0 ξ = mpG (e : ℝ) f 1 x 0 ξ := fun ξ => (mp_zero_eta _ _ _ _ _).symm
  have hXl : lpG (e : ℝ) f 1 x 0 η = X := hl0 η
  -- angles at X
  have a0 : (D.tile k0).localAngle X = α :=
    ((h0.anglesG S.tile S.hM).1) (hlp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have a1 : (D.tile k1).localAngle X = α :=
    ((h1.anglesG S.tile S.hM).1) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have aT : (D.tile t0).localAngle X = γ :=
    ((ht0.anglesG S.tile S.hM).2.2) (hmp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have a3 : (D.tile k3).localAngle X = γ :=
    ((h3.anglesG S.tile S.hM).2.2) (hlp _ (by positivity) _ _ _ _ (by unfold QfG; ring))
  have nv : ∀ {a b a' b' : ℝ}, (a ≠ a' ∨ b ≠ b') → mpG (e : ℝ) f 1 x a b ≠ mpG (e : ℝ) f 1 x a' b' := by
    intro a b a' b' h hh
    obtain ⟨h1, h2⟩ := mpG_inj he0 hef hh
    rcases h with h | h
    · exact h h1
    · exact h h2
  have hne : ∀ {i j : Fin N} (u v : ℝ), (D.tile i).localAngle X = u → (D.tile j).localAngle X = v → u ≠ v → i ≠ j :=
    fun u v hu hv huv => ne_of_angle (by rw [hu, hv]; exact huv)
  have n01 : k0 ≠ k1 := by
    obtain ⟨i, hi⟩ := hasV_second h0
    refine HasV.ne_of_vertex h1 hi ?_ ?_ ?_
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
  have n3T : k3 ≠ t0 := by
    obtain ⟨i, hi⟩ := hasV_third h3
    refine HasV.ne_of_vertex ht0 hi ?_ ?_ ?_
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
    · rw [lp_eq_mp he0 hef]; exact nv (Or.inl (by norm_num))
  have hαγ' : α ≠ γ := hαγ.ne
  set K : Finset (Fin N) := {k0, k1, t0, k3} with hKdef
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle X = 2 * Real.pi - 2 * β := by
    rw [hKdef, sum_four _ n01 (hne _ _ a0 aT hαγ') (hne _ _ a0 a3 hαγ') (hne _ _ a1 aT hαγ')
      (hne _ _ a1 a3 hαγ') n3T.symm, a0, a1, aT, a3]
    have hr := hA.hrel
    have hg := hA.hγdef
    linarith
  have h2b := two_beta_lt_pi S
  have hXt : X ∈ D.target.carrier := h1.mem₁
  have hXint : X ∈ interior D.target.carrier := by
    refine interior_of_sum D.toDissection hXt K ?_
    rw [hKsum]; linarith
  have hΩ : ∑ i, (D.tile i).localAngle X = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq X
    rw [this, D.target.localAngle_interior hXint]
  have hXY : X ≠ Y := by
    intro h
    obtain ⟨h1', -⟩ := mpG_inj he0 hef h
    linarith
  have hKlt : ∀ k ∈ K, (D.tile k).localAngle X < Real.pi := by
    intro k hk
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · rw [a0]; exact hαπ
    · rw [a1]; exact hαπ
    · rw [aT]; exact hγπ'
    · rw [a3]; exact hγπ'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hQ : cross (Y - X) ((X + (n : ℝ) • (Y - X)) - X) = 0 := by
    simp [cross]; ring
  have hXQ : X ≠ X + (n : ℝ) • (Y - X) := by
    intro h
    have h' : (n : ℝ) • (Y - X) = 0 := by
      have : X + (n : ℝ) • (Y - X) - X = 0 := by rw [← h]; simp
      simpa using this
    rcases smul_eq_zero.mp h' with h1 | h1
    · linarith
    · exact hXY (sub_eq_zero.mp h1).symm
  have hP'' : cross (Y - X) ((X + (-1 : ℝ) • (Y - X)) - X) = 0 := by
    simp [cross]; ring
  have hXP' : X ∈ openSegment ℝ (X + (-1 : ℝ) • (Y - X)) (X + (n : ℝ) • (Y - X)) := by
    have := par_mem_open X (Y - X) (t₁ := -1) (t₂ := 0) (t₃ := n) (by norm_num) hnpos
    simpa using this
  exact no_straddle_gen D.toDissection hXY hQ hXQ hP'' hXP' hΩ K (θ := 2 * β) (by rw [hKsum]) h2b hKlt

end w1c

#print axioms w1_clamp

end Erdos634.Draft.WGapStmt
