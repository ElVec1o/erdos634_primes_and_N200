import Mathlib.Tactic
import Erdos634.Draft.ThmDRunSetup

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' (R5 support): frontier points of the target on the three side lines  

A point of the target on the side line `y = 0` (resp. `gA = 0`, `gB = 0`) is a frontier point of the target.  Used for the ends
`P`, `Q` of the diagonal `PQ` in `ThmDRowStep.row_orient_full`.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Set

theorem frontier_of_dir {K : Set Plane} {f : Plane → ℝ} (hcl : IsClosed K) (hK : ∀ y ∈ K, 0 ≤ f y) {p : Plane}
    (hp : p ∈ K) (hf0 : f p = 0) (d : Plane) (hd : ∀ s : ℝ, 0 < s → f (p + s • d) < 0) :
    p ∈ frontier K := by
  refine ⟨by rw [hcl.closure_eq]; exact hp, fun hint => ?_⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_interior p hint
  set s : ℝ := r / (2 * (‖d‖ + 1)) with hs
  have hpos : 0 < s := by positivity
  have hmem : p + s • d ∈ Metric.ball p r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, hs]
    have h1 : 0 < ‖d‖ + 1 := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg d]
  have := hK _ (interior_subset (hsub hmem))
  linarith [hd s hpos]

namespace SetupT
variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem frontier_y0 (S : SetupT D u v α β γ L ax ay) {p : Plane} (hp : p ∈ D.target.carrier) (h0 : p 1 = 0) :
    p ∈ frontier D.target.carrier := by
  refine frontier_of_dir (f := fun q => q 1) D.target.isCompact.isClosed (fun y hy => (S.mem hy).1) hp h0
    (EuclideanSpace.single 1 (-1)) ?_
  intro s hs
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply]
  simp [h0, hs]

theorem frontier_gA0 (S : SetupT D u v α β γ L ax ay) {p : Plane} (hp : p ∈ D.target.carrier)
    (h0 : gA ax ay p = 0) : p ∈ frontier D.target.carrier := by
  refine frontier_of_dir (f := gA ax ay) D.target.isCompact.isClosed (fun y hy => (S.mem hy).2.1) hp h0
    (mkPt (-ay) ax) ?_
  intro s hs
  have h := S.hay
  have e : gA ax ay (p + s • mkPt (-ay) ax) = gA ax ay p + s * (-(ay ^ 2 + ax ^ 2)) := by
    simp only [gA, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one]; ring
  rw [e, h0]
  nlinarith [sq_nonneg ax, sq_pos_of_pos h]

theorem frontier_gB0 (S : SetupT D u v α β γ L ax ay) {p : Plane} (hp : p ∈ D.target.carrier)
    (h0 : gB L ax ay p = 0) : p ∈ frontier D.target.carrier := by
  refine frontier_of_dir (f := gB L ax ay) D.target.isCompact.isClosed (fun y hy => (S.mem hy).2.2) hp h0
    (mkPt ay (L - ax)) ?_
  intro s hs
  have h := S.hay
  have e : gB L ax ay (p + s • mkPt ay (L - ax)) = gB L ax ay p + s * (-(ay ^ 2 + (L - ax) ^ 2)) := by
    simp only [gB, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one]; ring
  rw [e, h0]
  nlinarith [sq_nonneg (L - ax), sq_pos_of_pos h]

end SetupT

#print axioms SetupT.frontier_y0
#print axioms SetupT.frontier_gA0
#print axioms SetupT.frontier_gB0
end Erdos634.Draft.ThmDRun
