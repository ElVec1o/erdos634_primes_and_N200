/-
Draft/WGapSide3b.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 [SIDE-3], Corner at p'(j,0), (H4)).
Not imported by any aggregate.  Module P-B2: the BOUNDARY FACTS at `X = p'(j, 0)`, `1 <= j <= f-1`, for `X` in the target (hypotheses `Corner2`, `H4`):
`X` is on the side `QA` (`gA X = 0`), is not a vertex of the target, is not in the interior (the points `p'(j, eta)`, `eta < 0`, are outside: `mp_out`), hence in the frontier and (`hasAngleSums`)
the total of the local angles at `X` is `pi`; moreover `0 < X 1` and `0 < gB X` (the hypotheses of `interior_seg` for the ray from `X` into the target).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapSide3a

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

section bdry

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- a point of the target on the line `QA`, not a vertex `Q`, `A`: positive height and strictly inside the side `BA` -/
theorem onQA_facts (S : SetupG D e f α β γ L ax ay) {X : Plane} (hX : X ∈ D.target.carrier)
    (hgA : gA ax ay X = 0) (hXQ : X ≠ mkPt 0 0) (hXA : X ≠ mkPt ax ay) : 0 < X 1 ∧ 0 < gB L ax ay X := by
  obtain ⟨h1, h2, h3⟩ := S.mem hX
  have hay := S.hay
  have hL := S.hL
  unfold gA at hgA
  have hX1 : 0 < X 1 := by
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exfalso; apply hXQ
      apply plane_ext
      · simp; rw [← h] at hgA; nlinarith
      · simp; exact h.symm
  refine ⟨hX1, ?_⟩
  rcases lt_or_eq_of_le h3 with h | h
  · exact h
  · exfalso; apply hXA
    unfold gB at h
    have e1 : X 1 = ay := by
      have : L * (X 1 - ay) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hL.ne'
      · linarith
    apply plane_ext
    · simp
      have : ay * (X 0 - ax) = 0 := by rw [e1] at hgA; nlinarith
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hay.ne'
      · linarith
    · simp; exact e1

/-- `p'(j,0)` is not in the interior of the target (the points just below are outside) -/
theorem mp_not_interior (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (ξ : ℝ) :
    mpG (e : ℝ) f 1 0 ξ 0 ∉ interior D.target.carrier := by
  intro hint
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
  obtain ⟨r, hr, hball⟩ := hint
  have hb := S.b_pos
  set η : ℝ := -(r / 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) with hη
  have hη0 : η < 0 := by
    rw [hη]; have : 0 < r / 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by positivity
    linarith
  have hd : dist (mpG (e : ℝ) f 1 0 ξ η) (mpG (e : ℝ) f 1 0 ξ 0) = r / 2 := by
    refine dist_mpG S.e0 S.hef' 0 (by positivity) ?_
    unfold QfG
    rw [hη]
    field_simp
    ring
  have hmem : mpG (e : ℝ) f 1 0 ξ η ∈ Metric.ball (mpG (e : ℝ) f 1 0 ξ 0) r := by
    rw [Metric.mem_ball, hd]; linarith
  exact mp_out S h2 hη0 (hball hmem)

/-- **The boundary point `p'(j,0)`**: total local angle `π`, positive height, strictly inside `BA` -/
theorem bdry_total (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) {j : ℕ} (hj1 : 1 ≤ j)
    (hjf : j ≤ f - 1) (hXt : mpG (e : ℝ) f 1 0 (j : ℝ) 0 ∈ D.target.carrier) :
    ∑ i, (D.tile i).localAngle (mpG (e : ℝ) f 1 0 (j : ℝ) 0) = Real.pi ∧ 0 < (mpG (e : ℝ) f 1 0 (j : ℝ) 0) 1 ∧
      0 < gB L ax ay (mpG (e : ℝ) f 1 0 (j : ℝ) 0) := by
  have h2' := h2
  obtain ⟨t, ht, hax, hay'⟩ := h2'
  set X := mpG (e : ℝ) f 1 0 (j : ℝ) 0 with hX
  have hgA : gA ax ay X = 0 := by
    rw [hax, hay', hX, gA_mp S.e0 S.hef' t (j : ℝ) 0]; ring
  have hQ : mkPt 0 0 = mpG (e : ℝ) f 1 0 0 0 := by
    rw [mpG_zero_zero, lpG_zero]
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hXQ : X ≠ mkPt 0 0 := by
    intro h
    rw [hQ] at h
    obtain ⟨h1, -⟩ := mpG_inj S.e0 S.hef' h
    linarith
  have hXA : X ≠ mkPt ax ay := by
    intro h
    have e1 := dist_sq_pts X (mkPt 0 0)
    have e2 := dist_mpG_sq S.e0 S.hef' 0 (j : ℝ) 0 0 0
    rw [← hX, ← hQ] at e2
    have hx0 : X 0 = ax := by rw [h]; simp
    have hx1 : X 1 = ay := by rw [h]; simp
    have e3 := e1.symm.trans e2
    simp only [mkPt_zero, mkPt_one, hx0, hx1] at e3
    unfold QfG at e3
    have hjf' : (j : ℝ) ≤ (f : ℝ) - 1 := by
      have : j + 1 ≤ f := by omega
      have h' : ((j + 1 : ℕ) : ℝ) ≤ f := by exact_mod_cast this
      push_cast at h'; linarith
    have hH := hH4
    unfold H4 at hH
    have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := S.c_pos
    have : (j : ℝ) * (f : ℝ) ^ 2 ≤ ((f : ℝ) - 1) * (f : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hjf' hf2.le
    nlinarith [mul_nonneg hj0.le hf2.le, mul_nonneg hj0.le hj0.le]
  obtain ⟨hy, hgB⟩ := onQA_facts S hXt hgA hXQ hXA
  refine ⟨?_, hy, hgB⟩
  have hfront : X ∈ frontier D.target.carrier := ⟨subset_closure hXt, mp_not_interior S h2 (j : ℝ)⟩
  have hnv : X ∉ Set.range D.target.pts := by
    rintro ⟨k, hk⟩
    rw [S.tgt] at hk
    fin_cases k
    · exact hXQ (by rw [← hk]; rfl)
    · have hk' : mkPt L 0 = X := hk
      have : gA ax ay (mkPt L 0) = 0 := by rw [hk']; exact hgA
      rw [gA_mk] at this
      have := S.hay; have := S.hL; nlinarith
    · exact hXA (by rw [← hk]; rfl)
  exact (D.toDissection.hasAngleSums).2.1 X hfront hnv

end bdry

end Erdos634.Draft.WGapStmt
