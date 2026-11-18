-- Draft/ThetaUnitPieces.lean -- containment, separation and SSS facts for the pieces of the UNIT THETA STEP.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
Continuation of `ThetaUnitCore` (points `tY tO tU2 tU1 tA1 tA2 tAs tB`, pieces `T = Preg Y O U2 (G/(f+G))`,
`R = Preg A* A2 U1 ((G-e)/G)`, `G = (f-e) n`).  Here:

* both pieces lie in the target `theta_{n+1}` (`InTgt`: `0 <= y`, `0 <= x`, `e x + f y <= e f b (n+1)`);
* the old block `theta_n` lies in `e x + f y <= e f b n`, both pieces in `e x + f y >= e f b n`;
* `T` lies in `f x + e y >= e f b n`, `R` in `f x + e y <= e f b n`   (this is where `(f-e) n >= e` is used for `B`);
* the base tiles of `T` and `R` are congruent to the model brick `(0,0),(b,0),(b,a)` (SSS; `T` through the relabelling `(0 1)`).

CREDIT: see `ThetaUnitCore`.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaUnitCore

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaUnit
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam
open Erdos634.Draft.S2L (baseTri)

/-- the three linear inequalities of the target `theta_{n+1}` (triangle `(0,0), (f b N, 0), (0, e b N)`) -/
def InTgt (E F n : ℝ) (p : ℝ × ℝ) : Prop :=
  0 ≤ p.2 ∧ 0 ≤ p.1 ∧ E * p.1 + F * p.2 ≤ E * F * (F ^ 2 - E ^ 2) * (n + 1)

section pieces
variable {E F n : ℝ} (hE : 0 < E) (hEF : E < F) (hn : 0 ≤ n) (hg : E ≤ (F - E) * n)
include hE hEF hn hg

/-- positive and nonnegative products used as linear hints -/
theorem hints : 0 < E * F * (F ^ 2 - E ^ 2) ∧ 0 ≤ F * (F ^ 2 - E ^ 2) * n * (F - E) ∧
    0 ≤ F * (F ^ 2 - E ^ 2) * (F + (F - E) * n) ∧ 0 ≤ E * (F ^ 2 - E ^ 2) * ((F - E) * n - E) ∧
    0 ≤ F * E * ((F - E) * n - E) ∧ 0 ≤ E * F * (F + (F - E) * n) ∧ 0 ≤ E * F * ((F - E) * n) ∧
    0 ≤ E * (F ^ 2 - E ^ 2) * n ∧ 0 ≤ F * (F ^ 2 - E ^ 2) * n ∧ 0 ≤ E * (F ^ 2 - E ^ 2) * (n + 1) ∧
    0 ≤ F * (F ^ 2 - E ^ 2) * (n + 1) ∧ 0 ≤ E * (F ^ 2 - E ^ 2) * n * (F - E) ∧ 0 ≤ E * F * (F ^ 2 - E ^ 2) * n := by
  obtain ⟨hF, hb, hG0, hGE, hk, hGp⟩ := facts hE hEF hn hg
  have hG : 0 ≤ (F - E) * n := hG0
  have hGE' : E ≤ (F - E) * n := hGE
  have hFE : 0 ≤ F - E := by linarith
  have hk' : 0 ≤ F + (F - E) * n := by linarith
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg hF.le hb.le) hn) hFE
  · exact mul_nonneg (mul_nonneg hF.le hb.le) hk'
  · exact mul_nonneg (mul_nonneg hE.le hb.le) (by linarith)
  · exact mul_nonneg (mul_nonneg hF.le hE.le) (by linarith)
  · exact mul_nonneg (mul_nonneg hE.le hF.le) hk'
  · exact mul_nonneg (mul_nonneg hE.le hF.le) hG
  · exact mul_nonneg (mul_nonneg hE.le hb.le) hn
  · exact mul_nonneg (mul_nonneg hF.le hb.le) hn
  · exact mul_nonneg (mul_nonneg hE.le hb.le) (by linarith)
  · exact mul_nonneg (mul_nonneg hF.le hb.le) (by linarith)
  · exact mul_nonneg (mul_nonneg (mul_nonneg hE.le hb.le) hn) hFE
  · exact mul_nonneg (mul_nonneg (mul_nonneg hE.le hF.le) hb.le) hn

/-! ### `T` -/

theorem T_inTgt : ∀ p ∈ Preg (tY E F n) (tO E F n) (tU2 E F n) (gg E F n / (F + gg E F n)), InTgt E F n p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hints hE hEF hn hg
  intro p hp
  refine ⟨?_, ?_, ?_⟩
  · refine (T_ge hE hEF hn hg 0 1 0 ?_ ?_ ?_ ?_ p hp).trans_eq (by ring) <;> dsimp only [tA1, tU1, tO, tU2, gg] at * <;> linarith
  · refine (T_ge hE hEF hn hg 1 0 0 ?_ ?_ ?_ ?_ p hp).trans_eq (by ring) <;> dsimp only [tA1, tU1, tO, tU2, gg] at * <;> linarith
  · refine T_le hE hEF hn hg E F _ ?_ ?_ ?_ ?_ p hp <;> dsimp only [tA1, tU1, tO, tU2, gg] at * <;> linarith

theorem T_old : ∀ p ∈ Preg (tY E F n) (tO E F n) (tU2 E F n) (gg E F n / (F + gg E F n)),
    E * F * (F ^ 2 - E ^ 2) * n ≤ E * p.1 + F * p.2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hints hE hEF hn hg
  intro p hp
  refine T_ge hE hEF hn hg E F _ ?_ ?_ ?_ ?_ p hp <;> dsimp only [tA1, tU1, tO, tU2, gg] at * <;> linarith

theorem T_sepR : ∀ p ∈ Preg (tY E F n) (tO E F n) (tU2 E F n) (gg E F n / (F + gg E F n)),
    E * F * (F ^ 2 - E ^ 2) * n ≤ F * p.1 + E * p.2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hints hE hEF hn hg
  intro p hp
  refine T_ge hE hEF hn hg F E _ ?_ ?_ ?_ ?_ p hp <;> dsimp only [tA1, tU1, tO, tU2, gg] at * <;> linarith

/-! ### `R` -/

theorem R_inTgt : ∀ p ∈ Preg (tAs E F n) (tA2 E F n) (tU1 E F n) ((gg E F n - E) / gg E F n), InTgt E F n p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hints hE hEF hn hg
  intro p hp
  refine ⟨?_, ?_, ?_⟩
  · refine (R_ge hE hEF hn hg 0 1 0 ?_ ?_ ?_ ?_ p hp).trans_eq (by ring) <;> dsimp only [tB, tU2, tA2, tU1, gg] at * <;> linarith
  · refine (R_ge hE hEF hn hg 1 0 0 ?_ ?_ ?_ ?_ p hp).trans_eq (by ring) <;> dsimp only [tB, tU2, tA2, tU1, gg] at * <;> linarith
  · refine R_le hE hEF hn hg E F _ ?_ ?_ ?_ ?_ p hp <;> dsimp only [tB, tU2, tA2, tU1, gg] at * <;> linarith

theorem R_old : ∀ p ∈ Preg (tAs E F n) (tA2 E F n) (tU1 E F n) ((gg E F n - E) / gg E F n),
    E * F * (F ^ 2 - E ^ 2) * n ≤ E * p.1 + F * p.2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hints hE hEF hn hg
  intro p hp
  refine R_ge hE hEF hn hg E F _ ?_ ?_ ?_ ?_ p hp <;> dsimp only [tB, tU2, tA2, tU1, gg] at * <;> linarith

theorem R_sepT : ∀ p ∈ Preg (tAs E F n) (tA2 E F n) (tU1 E F n) ((gg E F n - E) / gg E F n),
    F * p.1 + E * p.2 ≤ E * F * (F ^ 2 - E ^ 2) * n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hints hE hEF hn hg
  intro p hp
  refine R_le hE hEF hn hg F E _ ?_ ?_ ?_ ?_ p hp <;> dsimp only [tB, tU2, tA2, tU1, gg] at * <;> linarith

/-! ### the old block `theta_n = (0,0), A1, A2` -/

theorem old_le : ∀ p ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), tA1 E F n, tA2 E F n} : Set (ℝ × ℝ)),
    E * p.1 + F * p.2 ≤ E * F * (F ^ 2 - E ^ 2) * n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hints hE hEF hn hg
  intro p hp
  refine Erdos634.Draft.S2L.hull_le E F _ ?_ p hp
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl <;> dsimp only [tA1, tA2] <;> linarith

theorem old_inTgt : ∀ p ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), tA1 E F n, tA2 E F n} : Set (ℝ × ℝ)),
    InTgt E F n p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hints hE hEF hn hg
  intro p hp
  have hS : ∀ v ∈ ({((0 : ℝ), (0 : ℝ)), tA1 E F n, tA2 E F n} : Set (ℝ × ℝ)), 0 ≤ v.1 ∧ 0 ≤ v.2 := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> dsimp only [tA1, tA2] <;> constructor <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (Erdos634.Draft.S2L.hull_ge (S := ({((0 : ℝ), (0 : ℝ)), tA1 E F n, tA2 E F n} : Set (ℝ × ℝ))) 0 1 0 (fun v hv => by linarith [(hS v hv).2]) p hp).trans_eq (by ring)
  · exact (Erdos634.Draft.S2L.hull_ge (S := ({((0 : ℝ), (0 : ℝ)), tA1 E F n, tA2 E F n} : Set (ℝ × ℝ))) 1 0 0 (fun v hv => by linarith [(hS v hv).1]) p hp).trans_eq (by ring)
  · have := old_le hE hEF hn hg p hp
    linarith [h1, h2]

/-! ### determinants and SSS congruences -/

theorem det_T : ((tO E F n).1 - (tY E F n).1) * ((tU2 E F n).2 - (tY E F n).2) -
    ((tU2 E F n).1 - (tY E F n).1) * ((tO E F n).2 - (tY E F n).2) ≠ 0 := by
  obtain ⟨hF, hb, hG0, hGE, hk, hGp⟩ := facts hE hEF hn hg
  have : ((tO E F n).1 - (tY E F n).1) * ((tU2 E F n).2 - (tY E F n).2) -
      ((tU2 E F n).1 - (tY E F n).1) * ((tO E F n).2 - (tY E F n).2)
      = (F ^ 2 - E ^ 2) * (E * F) * (F + gg E F n) ^ 2 := by
    dsimp only [tO, tY, tU2, gg]; ring
  rw [this]
  exact (mul_pos (mul_pos hb (mul_pos hE hF)) (pow_pos hk 2)).ne'

theorem det_R : ((tA2 E F n).1 - (tAs E F n).1) * ((tU1 E F n).2 - (tAs E F n).2) -
    ((tU1 E F n).1 - (tAs E F n).1) * ((tA2 E F n).2 - (tAs E F n).2) ≠ 0 := by
  obtain ⟨hF, hb, hG0, hGE, hk, hGp⟩ := facts hE hEF hn hg
  have : ((tA2 E F n).1 - (tAs E F n).1) * ((tU1 E F n).2 - (tAs E F n).2) -
      ((tU1 E F n).1 - (tAs E F n).1) * ((tA2 E F n).2 - (tAs E F n).2)
      = (F * E) * (F ^ 2 - E ^ 2) * gg E F n ^ 2 := by
    dsimp only [tA2, tAs, tU1, gg]; ring
  rw [this]
  exact (mul_pos (mul_pos (mul_pos hF hE) hb) (pow_pos hGp 2)).ne'

theorem cong_T {φ : ℝ} (hφ : 1 < φ) (hφE : φ = F / E) {k : ℕ} (hk : 0 < k) (hkR : (k : ℝ) = F + gg E F n)
    (hA : 0 < F ^ 2 - E ^ 2) (hB : 0 < E * F) :
    (baseTri φ hφ (tY E F n) (tO E F n) (tU2 E F n) k hk (det_T hE hEF hn hg)).Congruent
      (brickL φ hφ (F ^ 2 - E ^ 2) (E * F) hA hB) := by
  obtain ⟨hF, hb, hG0, hGE, hkk, hGp⟩ := facts hE hEF hn hg
  have hE0 := hE.ne'
  have hF0 := hF.ne'
  have hK0 : (k : ℝ) ≠ 0 := by rw [hkR]; exact hkk.ne'
  subst hφE
  refine (Erdos634.SssCongruent.congruent_of_dist_three
    (U := (brickL (F / E) hφ (F ^ 2 - E ^ 2) (E * F) hA hB).relabel (Equiv.swap (0 : Fin 3) 1)) ?_ ?_ ?_).trans
    ((brickL (F / E) hφ (F ^ 2 - E ^ 2) (E * F) hA hB).congruent_relabel (Equiv.swap (0 : Fin 3) 1)).symm <;>
    simp only [baseTri, Tri.relabel, brickL, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi hφ, sq_Phi hφ];
     simp only [tY, tO, tU2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub,
       Prod.snd_sub, gg, Function.comp]
     field_simp; rw [hkR]; simp only [gg]; ring)

theorem cong_R {φ : ℝ} (hφ : 1 < φ) (hφE : φ = F / E) {k : ℕ} (hk : 0 < k) (hkR : (k : ℝ) = gg E F n)
    (hA : 0 < F ^ 2 - E ^ 2) (hB : 0 < E * F) :
    (baseTri φ hφ (tAs E F n) (tA2 E F n) (tU1 E F n) k hk (det_R hE hEF hn hg)).Congruent
      (brickL φ hφ (F ^ 2 - E ^ 2) (E * F) hA hB) := by
  obtain ⟨hF, hb, hG0, hGE, hkk, hGp⟩ := facts hE hEF hn hg
  have hE0 := hE.ne'
  have hF0 := hF.ne'
  have hK0 : (k : ℝ) ≠ 0 := by rw [hkR]; exact hGp.ne'
  subst hφE
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [baseTri, brickL, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi hφ, sq_Phi hφ];
     simp only [tAs, tA2, tU1, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub,
       Prod.snd_sub, gg]
     field_simp; rw [hkR]; simp only [gg]; ring)

end pieces

end

end Erdos634.Draft.ThetaUnit
