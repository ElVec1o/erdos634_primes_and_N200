-- Side data of the model and target, and controls (p,q) = (1,2),(1,q),(2,3) and non-coprime
-- witnesses for the hypotheses of `s2_family_gen`.
import Erdos634.Draft.S2GAssemble

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.S2G
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF

section sides
variable {p q : ℕ} (hp : 1 ≤ p) (hg : 2 * p ^ 2 < q ^ 2)
include hp hg

/-- Side lengths of the model `Mod`: `(q², q²-p², pq)` on the edges `01, 12, 20`  (the tile `(pq, q²-p², q²)`). -/
theorem model_sides :
    dist ((Mod (hPp hp hg) (hgp hp hg)).pts 0) ((Mod (hPp hp hg) (hgp hp hg)).pts 1) = (q : ℝ) ^ 2 ∧
    dist ((Mod (hPp hp hg) (hgp hp hg)).pts 1) ((Mod (hPp hp hg) (hgp hp hg)).pts 2) = (q : ℝ) ^ 2 - (p : ℝ) ^ 2 ∧
    dist ((Mod (hPp hp hg) (hgp hp hg)).pts 2) ((Mod (hPp hp hg) (hgp hp hg)).pts 0) = (p : ℝ) * q := by
  have hP := hPp hp hg
  have hg' := hgp hp hg
  have hf := hfr hP hg'
  have hc : (q : ℝ) ^ 2 = 2 * Pr p + gr p q := by rw [← hcq hp hg]; push_cast; ring
  have hb : (q : ℝ) ^ 2 - (p : ℝ) ^ 2 = Pr p + gr p q := by rw [hc]; unfold Pr; ring
  have hcp : 0 < 2 * Pr p + gr p q := hcpos hP hg'
  have hbp : 0 < Pr p + gr p q := hbpos hP hg'
  have hpq : 0 ≤ (p : ℝ) * q := by positivity
  simp only [Mod, brickL, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg (by rw [hc]; exact hcp.le)).mp ?_
    rw [sq_Phi' hf, hc]; ring
  · refine (sq_eq_sq₀ dist_nonneg (by rw [hb]; exact hbp.le)).mp ?_
    rw [sq_Phi' hf, hb]; ring
  · refine (sq_eq_sq₀ dist_nonneg hpq).mp ?_
    rw [sq_Phi' hf]
    have h1 := hab_id hP hg'
    have h2 := hapq hp hg
    have h3 : ((p : ℝ) * q) ^ 2 = Pr p * (2 * Pr p + gr p q) := by rw [← h2]; push_cast; ring
    rw [h3, ← h1]; ring

/-- Side lengths of the target `O B' C`: `OB' = (3q²-p²)(q²-p²)`, `OC = q⁴`, `B'C = (2q²-p²) q²`. -/
theorem tgt_sides :
    dist ((tgt hp hg).pts 0) ((tgt hp hg).pts 1) = (3 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2) * ((q : ℝ) ^ 2 - (p : ℝ) ^ 2) ∧
    dist ((tgt hp hg).pts 0) ((tgt hp hg).pts 2) = (q : ℝ) ^ 4 ∧
    dist ((tgt hp hg).pts 1) ((tgt hp hg).pts 2) = (2 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2) * (q : ℝ) ^ 2 := by
  have hP := hPp hp hg
  have hg' := hgp hp hg
  have hf := hfr hP hg'
  have hc : (q : ℝ) ^ 2 = 2 * Pr p + gr p q := by rw [← hcq hp hg]; push_cast; ring
  have hpP : (p : ℝ) ^ 2 = Pr p := rfl
  have h1 : (2 * Pr p + gr p q) ≠ 0 := (hcpos hP hg').ne'
  simp only [tgt, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg (by rw [hc, hpP]; have := hbpos hP hg'; nlinarith [mul_pos hP hg'])).mp ?_
    rw [sq_Phi' hf, hc, hpP]; simp only [pO, pB]; ring
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi' hf]
    have e : (q : ℝ) ^ 4 = ((2 * Pr p + gr p q) ^ 2) := by rw [← hc]; ring
    rw [e]; simp only [pO, pC, ff]; field_simp; ring
  · refine (sq_eq_sq₀ dist_nonneg (by rw [hc, hpP]; have := hbpos hP hg'; nlinarith [mul_pos hP hg'])).mp ?_
    rw [sq_Phi' hf, hc, hpP]; simp only [pB, pC]; ring

end sides

/-- Control p = 1: the general theorem specialises to the existing S2L statement. -/
theorem p1_control (q : ℕ) (hq : 2 ≤ q) : Nonempty (CongruentDissection ((2 * q ^ 2 - 1) * (3 * q ^ 2 - 1))) := by
  have h := s2_family_gen 1 q le_rfl (by nlinarith)
  simpa using h

example : Nonempty (CongruentDissection 77) := by simpa using s2_family_gen 1 2 le_rfl (by norm_num)
example : Nonempty (CongruentDissection 442) := by simpa using s2_family_gen 1 3 le_rfl (by norm_num)
/-- (p,q) = (2,3): N = 322, tile (6,5,9), target (126,81,115): the `S2RTilingBridge` instance. -/
example : Nonempty (CongruentDissection 322) := by simpa using s2_family_gen 2 3 (by norm_num) (by norm_num)
example : Nonempty (CongruentDissection 2706) := by simpa using s2_family_gen 3 5 (by norm_num) (by norm_num)
example : Nonempty (CongruentDissection 3266) := by simpa using s2_family_gen 2 5 (by norm_num) (by norm_num)
/-- non-coprime pairs (coprimality is not used): (2,4): 1232, (3,6): 6237, (4,6): 5152. -/
example : Nonempty (CongruentDissection 1232) := by simpa using s2_family_gen 2 4 (by norm_num) (by norm_num)
example : Nonempty (CongruentDissection 6237) := by simpa using s2_family_gen 3 6 (by norm_num) (by norm_num)
example : Nonempty (CongruentDissection 5152) := by simpa using s2_family_gen 4 6 (by norm_num) (by norm_num)
/-- the hypotheses are satisfiable (witness) and the boundary g = 0 is excluded: (p,q) = (1,1) has 2 < 1 false. -/
example : 1 ≤ 2 ∧ 2 * 2 ^ 2 < 3 ^ 2 := by norm_num

end Erdos634.Draft.S2G

#print axioms Erdos634.Draft.S2G.model_sides
#print axioms Erdos634.Draft.S2G.tgt_sides
#print axioms Erdos634.Draft.S2G.p1_control
