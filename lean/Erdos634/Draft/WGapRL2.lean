/-
Draft/WGapRL2.lean -- written 16 November 2026 (session 9).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8, steps (alpha), (beta), and the final overlap "Xi = Z" of Lemma RL).
Not imported by any aggregate.  `EdgeCoverS D X d s`: a tile has `X` with local angle `pi` and covers the open half-disk `{w : 0 < s * cross d w}` at `X`.
`fault_cover` = `fault_straddle` with the cover as conclusion (as `wl_cover` for `wl_straddle`).
`edgecover_clash`: two covers at the same point along NON-parallel directions (`cross d1 d2 != 0`) are impossible (the covering tile is the same and contains `X` in its interior).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapRL1

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

/-- a tile has `X` in the relative interior of an edge and covers the open half-disk `{0 < s * cross d w}` at `X` -/
def EdgeCoverS (D : CongruentDissection N) (X d : Plane) (s : ℝ) : Prop :=
  ∃ φ : Fin N, X ∈ (D.tile φ).carrier ∧ (D.tile φ).localAngle X = Real.pi ∧
    ∀ w : Plane, 0 < s * cross d w → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
      X + ε' • w ∈ interior (D.tile φ).carrier

section rl2

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem fault_cover (S : SetupG D e f α β γ L ax ay) {q : ℕ} (hq1 : 1 ≤ q)
    (P0 d : Plane) (u lam s : ℝ) (hs : s = 1 ∨ s = -1) (hdn : ‖d‖ = u) (hu : 0 < u) (hlam : 0 < lam)
    (hnon : ∀ x y z : ℕ, lam * u + ((x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2) ≠ (q : ℝ) * u)
    (E : Fin N) (A0 : Plane) (hE : HasV D E P0 (P0 + d) A0) (hA0 : s * cross d (A0 - P0) < 0)
    (Fo : Fin N) (R : Plane) (hFo : HasV D Fo P0 (P0 + lam • d) R) (hR : 0 < s * cross d (R - P0))
    (hT : ∀ t : ℕ, t < q → ∃ (T : Fin N) (A : Plane),
      HasV D T (P0 + (t : ℝ) • d) (P0 + ((t : ℝ) + 1) • d) A ∧ s * cross d (A - (P0 + (t : ℝ) • d)) < 0) :
    EdgeCoverS D (P0 + (q : ℝ) • d) d s := by
  obtain ⟨ed, hed, hs'⟩ := fault_straddle S hq1 P0 d u lam s hs hdn hu hlam hnon E A0 hE hA0 Fo R hFo hR hT
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hs0 : s ≠ 0 := by rcases hs with h | h <;> simp [h]
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at hdn; simp at hdn; linarith
  have hF : crossL (-(s • d)) ≠ 0 := crossL_ne_zero (neg_ne_zero.mpr (smul_ne_zero hs0 hd0))
  have hFl : ∀ r : ℝ, crossL (-(s • d)) (P0 + r • d) = crossL (-(s • d)) P0 := by
    intro r
    simp only [crossL_apply, cross, PiLp.neg_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hPQ : P0 + (q : ℝ) • d ≠ P0 := by
    intro h
    have : (q : ℝ) • d = 0 := by simpa using h
    rcases smul_eq_zero.mp this with h0 | h0
    · exact hqpos.ne' h0
    · exact hd0 h0
  have hP' : P0 + (q : ℝ) • d ∈ openSegment ℝ (P0 + ((q : ℝ) + 1) • d) P0 := by
    have := pt_openSeg P0 d (a := 0) (b := (q : ℝ) + 1) (t := (q : ℝ)) hqpos (by linarith)
    rw [openSegment_symm]
    simpa using this
  obtain ⟨hmem, hang, hpush⟩ := straddle_data D.toDissection (crossL (-(s • d))) hF (crossL (-(s • d)) P0)
    (P := P0 + (q : ℝ) • d) (Q := P0) (P' := P0 + ((q : ℝ) + 1) • d) hPQ (hFl _) rfl (hFl _) hP' hed hs'
  refine ⟨ed.1, hmem, hang, fun w hw => ?_⟩
  have hFw : crossL (-(s • d)) w < 0 := by
    simp only [crossL_apply, cross, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [cross] at hw
    linarith
  exact hpush w hFw

/-- two half-disk covers at one point along non-parallel directions are impossible -/
theorem edgecover_clash {X d1 d2 : Plane} {s1 s2 : ℝ} (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1)
    (hK : cross d1 d2 ≠ 0) (h1 : EdgeCoverS D X d1 s1) (h2 : EdgeCoverS D X d2 s2) : False := by
  obtain ⟨φ1, hm1, hang1, hp1⟩ := h1
  obtain ⟨φ2, hm2, hang2, hp2⟩ := h2
  set K : ℝ := cross d1 d2 with hKdef
  have hK2 : 0 < K ^ 2 := by positivity
  have hs1sq : s1 * s1 = 1 := by rcases hs1 with h | h <;> simp [h]
  have hs2sq : s2 * s2 = 1 := by rcases hs2 with h | h <;> simp [h]
  -- common direction w0 = (-s2 K) d1 + (s1 K) d2
  have hcross : ∀ x y : ℝ, cross d1 (x • d1 + y • d2) = y * K ∧ cross d2 (x • d1 + y • d2) = -(x * K) := by
    intro x y
    constructor
    · simp only [hKdef, cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    · simp only [hKdef, cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- step 1: the tiles coincide
  have hsame : φ1 = φ2 := by
    set w0 : Plane := (-(s2 * K)) • d1 + (s1 * K) • d2 with hw0
    have hc := hcross (-(s2 * K)) (s1 * K)
    have hw1 : 0 < s1 * cross d1 w0 := by
      rw [hw0, hc.1]
      have e : s1 * (s1 * K * K) = K ^ 2 := by linear_combination K ^ 2 * hs1sq
      nlinarith [e]
    have hw2 : 0 < s2 * cross d2 w0 := by
      rw [hw0, hc.2]
      have e : s2 * s2 * K * K = K ^ 2 := by linear_combination K ^ 2 * hs2sq
      nlinarith [e]
    obtain ⟨ε₁, hε₁, hq1⟩ := hp1 w0 hw1
    obtain ⟨ε₂, hε₂, hq2⟩ := hp2 w0 hw2
    set ε := min ε₁ ε₂ / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; have := lt_min hε₁ hε₂; linarith
    have hεa : ε < ε₁ := by rw [hε]; have := min_le_left ε₁ ε₂; linarith [lt_min hε₁ hε₂]
    have hεb : ε < ε₂ := by rw [hε]; have := min_le_right ε₁ ε₂; linarith [lt_min hε₁ hε₂]
    by_contra hneq
    exact Set.disjoint_left.mp (D.interiors_disjoint hneq) (hq1 ε hε0 hεa) (hq2 ε hε0 hεb)
  subst hsame
  -- step 2: opposite directions inside one tile => X interior => angle 2 pi
  set w1 : Plane := (s2 * K) • d1 + (s1 * K) • d2 with hw1d
  have hc := hcross (s2 * K) (s1 * K)
  have hpos : 0 < s1 * cross d1 w1 := by
    rw [hw1d, hc.1]
    have e : s1 * (s1 * K * K) = K ^ 2 := by linear_combination K ^ 2 * hs1sq
    nlinarith [e]
  have hneg : 0 < s2 * cross d2 (-w1) := by
    have : cross d2 (-w1) = -(cross d2 w1) := by simp only [cross, PiLp.neg_apply]; ring
    rw [this, hw1d, hc.2]
    have e : s2 * s2 * K * K = K ^ 2 := by linear_combination K ^ 2 * hs2sq
    nlinarith [e]
  obtain ⟨ε₁, hε₁, hq1⟩ := hp1 w1 hpos
  obtain ⟨ε₂, hε₂, hq2⟩ := hp2 (-w1) hneg
  set ε := min ε₁ ε₂ / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; have := lt_min hε₁ hε₂; linarith
  have hεa : ε < ε₁ := by rw [hε]; have := min_le_left ε₁ ε₂; linarith [lt_min hε₁ hε₂]
  have hεb : ε < ε₂ := by rw [hε]; have := min_le_right ε₁ ε₂; linarith [lt_min hε₁ hε₂]
  have hA := hq1 ε hε0 hεa
  have hB := hq2 ε hε0 hεb
  have hXmid : X ∈ openSegment ℝ (X + ε • w1) (X + ε • (-w1)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    ring
  have hconv : Convex ℝ (interior (D.tile φ1).carrier) := (D.tile φ1).convex.interior
  have hXint : X ∈ interior (D.tile φ1).carrier := hconv.openSegment_subset hA hB hXmid
  have := Tri.localAngle_interior (D.tile φ1) hXint
  rw [hang1] at this
  linarith [Real.pi_pos]

end rl2

end Erdos634.Draft.WGapStmt
