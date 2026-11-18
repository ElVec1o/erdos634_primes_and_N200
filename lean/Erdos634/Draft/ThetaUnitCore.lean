-- Draft/ThetaUnitCore.lean -- real-level core of the UNIT THETA STEP (theta_n tiled and (f-e) n >= e  ==>  theta_{n+1} tiled).
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
**Unit theta step, geometry in the skew frame.**  Tile `(a,b,c) = (e f, f^2-e^2, f^2)`, frame `Phi_phi`, `phi = f/e`
(the frame of `CollarLayer`, `ThetaCompose.alpha_exists`).  In skew coordinates `(x,y)` (`u1` along a leg, `u2` along the base):

* target `theta_{n+1}`:  `P = (0,0)`, `O = (f b N, 0)`, `B = (0, e b N)`, `N = n+1`;
* old block `theta_n`:   `P`, `A1 = (f b n, 0)`, `A2 = (0, e b n)`  (homothetic corner block at the base vertex `P`);
* with `G = (f-e) n` (the hypothesis is `G >= e`):
    `Y = (e b n, 0)`, `U1 = (e f G, e f G)`, `U2 = (f e (G-e), e f (f+G))`, `A* = (0, f b n)`;
* strip piece `T = Delta_Y(f+G) \ Delta_Y(G)`  = Preg Y O U2 (G/(f+G))   [the cap `f tau` plus the `a`-`c` parallelogram in ONE ladder trapezoid],
* strip piece `R = Delta_{A*}(G) \ Delta_{A*}(G-e)` = Preg A* A2 U1 ((G-e)/G).
Counts: `(f+G)^2 - G^2 + G^2 - (G-e)^2 = f^2 + 2 f G + 2 e G - e^2 = b (2n+1)`.

This file: points, the linear inequalities (containment in the target, pairwise separation), the SSS congruences
of the base tiles of `T` and `R` with the model brick.  The assembly is `ThetaUnitStep`.

CREDIT: the theta family and the up-set method on a seed (annulus/band steps): D. Paliy (2026-10-08, prior art for the
method); the families: Y. Zhang; skew frame: Beeson-Rosu; ladder trapezoid machinery: this project (`LadderFam`,
`CollarLayer`).  The unit step itself: internal working notes (T1), audited by exact arithmetic in
internal working notes  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.CollarLayer
import Erdos634.Draft.CollarFam

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaUnit
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam
open Erdos634.Draft.S2L (baseTri)

/-- `G = (f-e) n`. -/
def gg (E F n : ℝ) : ℝ := (F - E) * n

def tO (E F n : ℝ) : ℝ × ℝ := (F * (F ^ 2 - E ^ 2) * (n + 1), 0)
def tB (E F n : ℝ) : ℝ × ℝ := (0, E * (F ^ 2 - E ^ 2) * (n + 1))
def tA1 (E F n : ℝ) : ℝ × ℝ := (F * (F ^ 2 - E ^ 2) * n, 0)
def tA2 (E F n : ℝ) : ℝ × ℝ := (0, E * (F ^ 2 - E ^ 2) * n)
def tY (E F n : ℝ) : ℝ × ℝ := (E * (F ^ 2 - E ^ 2) * n, 0)
def tU1 (E F n : ℝ) : ℝ × ℝ := (E * F * gg E F n, E * F * gg E F n)
def tU2 (E F n : ℝ) : ℝ × ℝ := (F * E * (gg E F n - E), E * F * (F + gg E F n))
def tAs (E F n : ℝ) : ℝ × ℝ := (0, F * (F ^ 2 - E ^ 2) * n)

section pieces
variable {E F n : ℝ} (hE : 0 < E) (hEF : E < F) (hn : 0 ≤ n) (hg : E ≤ (F - E) * n)
include hE hEF hn hg

theorem facts : 0 < F ∧ 0 < F ^ 2 - E ^ 2 ∧ 0 ≤ gg E F n ∧ E ≤ gg E F n ∧ 0 < F + gg E F n ∧ 0 < gg E F n := by
  have hF : 0 < F := by linarith
  have hb : 0 < F ^ 2 - E ^ 2 := by nlinarith
  have hG : E ≤ gg E F n := hg
  refine ⟨hF, hb, by linarith, hG, by linarith, by linarith⟩

/-! ### Cut-point equations -/

theorem T_cut :
    (tA1 E F n).1 = (tY E F n).1 + (gg E F n / (F + gg E F n)) * ((tO E F n).1 - (tY E F n).1) ∧
    (tA1 E F n).2 = (tY E F n).2 + (gg E F n / (F + gg E F n)) * ((tO E F n).2 - (tY E F n).2) ∧
    (tU1 E F n).1 = (tY E F n).1 + (gg E F n / (F + gg E F n)) * ((tU2 E F n).1 - (tY E F n).1) ∧
    (tU1 E F n).2 = (tY E F n).2 + (gg E F n / (F + gg E F n)) * ((tU2 E F n).2 - (tY E F n).2) := by
  obtain ⟨hF, hb, hG0, hGE, hk, hGp⟩ := facts hE hEF hn hg
  have hk0 := hk.ne'
  obtain ⟨G, hG⟩ : ∃ G, gg E F n = G := ⟨_, rfl⟩
  have hGd : G = (F - E) * n := hG.symm
  rw [hG] at hk
  have hk0 : F + G ≠ 0 := hk.ne'
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [tA1, tY, tO, tU1, tU2] <;> simp only [hG] <;> field_simp <;>
    (rw [hGd]; ring)

theorem R_cut :
    (tB E F n).1 = (tAs E F n).1 + ((gg E F n - E) / gg E F n) * ((tA2 E F n).1 - (tAs E F n).1) ∧
    (tB E F n).2 = (tAs E F n).2 + ((gg E F n - E) / gg E F n) * ((tA2 E F n).2 - (tAs E F n).2) ∧
    (tU2 E F n).1 = (tAs E F n).1 + ((gg E F n - E) / gg E F n) * ((tU1 E F n).1 - (tAs E F n).1) ∧
    (tU2 E F n).2 = (tAs E F n).2 + ((gg E F n - E) / gg E F n) * ((tU1 E F n).2 - (tAs E F n).2) := by
  obtain ⟨hF, hb, hG0, hGE, hk, hGp⟩ := facts hE hEF hn hg
  have hk0 : gg E F n ≠ 0 := hGp.ne'
  obtain ⟨G, hG⟩ : ∃ G, gg E F n = G := ⟨_, rfl⟩
  have hGd : G = (F - E) * n := hG.symm
  rw [hG] at hGp
  have hk0 : G ≠ 0 := hGp.ne'
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [tB, tAs, tA2, tU1, tU2] <;> simp only [hG] <;> field_simp <;>
    (rw [hGd]; ring)

theorem T_sig0 : 0 ≤ gg E F n / (F + gg E F n) := by
  obtain ⟨hF, hb, hG0, hGE, hk, hGp⟩ := facts hE hEF hn hg
  positivity

theorem T_sig1 : gg E F n / (F + gg E F n) ≤ 1 := by
  obtain ⟨hF, hb, hG0, hGE, hk, hGp⟩ := facts hE hEF hn hg
  rw [div_le_one hk]; linarith

theorem R_sig0 : 0 ≤ (gg E F n - E) / gg E F n := by
  obtain ⟨hF, hb, hG0, hGE, hk, hGp⟩ := facts hE hEF hn hg
  exact div_nonneg (by linarith) hGp.le

theorem R_sig1 : (gg E F n - E) / gg E F n ≤ 1 := by
  obtain ⟨hF, hb, hG0, hGE, hk, hGp⟩ := facts hE hEF hn hg
  rw [div_le_one hGp]; linarith

/-- the linear bounds on `T`, from its four corner points -/
theorem T_ge (u w c : ℝ)
    (h1 : c ≤ u * (tA1 E F n).1 + w * (tA1 E F n).2) (h2 : c ≤ u * (tU1 E F n).1 + w * (tU1 E F n).2)
    (h3 : c ≤ u * (tO E F n).1 + w * (tO E F n).2) (h4 : c ≤ u * (tU2 E F n).1 + w * (tU2 E F n).2) :
    ∀ p ∈ Preg (tY E F n) (tO E F n) (tU2 E F n) (gg E F n / (F + gg E F n)), c ≤ u * p.1 + w * p.2 := by
  obtain ⟨c1, c2, c3, c4⟩ := T_cut hE hEF hn hg
  exact preg_ge4 _ _ _ (tA1 E F n) (tU1 E F n) _ u w c (T_sig0 hE hEF hn hg) (T_sig1 hE hEF hn hg) c1 c2 c3 c4 h1 h2 h3 h4

theorem T_le (u w c : ℝ)
    (h1 : u * (tA1 E F n).1 + w * (tA1 E F n).2 ≤ c) (h2 : u * (tU1 E F n).1 + w * (tU1 E F n).2 ≤ c)
    (h3 : u * (tO E F n).1 + w * (tO E F n).2 ≤ c) (h4 : u * (tU2 E F n).1 + w * (tU2 E F n).2 ≤ c) :
    ∀ p ∈ Preg (tY E F n) (tO E F n) (tU2 E F n) (gg E F n / (F + gg E F n)), u * p.1 + w * p.2 ≤ c := by
  obtain ⟨c1, c2, c3, c4⟩ := T_cut hE hEF hn hg
  exact preg_le4 _ _ _ (tA1 E F n) (tU1 E F n) _ u w c (T_sig0 hE hEF hn hg) (T_sig1 hE hEF hn hg) c1 c2 c3 c4 h1 h2 h3 h4

theorem R_ge (u w c : ℝ)
    (h1 : c ≤ u * (tB E F n).1 + w * (tB E F n).2) (h2 : c ≤ u * (tU2 E F n).1 + w * (tU2 E F n).2)
    (h3 : c ≤ u * (tA2 E F n).1 + w * (tA2 E F n).2) (h4 : c ≤ u * (tU1 E F n).1 + w * (tU1 E F n).2) :
    ∀ p ∈ Preg (tAs E F n) (tA2 E F n) (tU1 E F n) ((gg E F n - E) / gg E F n), c ≤ u * p.1 + w * p.2 := by
  obtain ⟨c1, c2, c3, c4⟩ := R_cut hE hEF hn hg
  exact preg_ge4 _ _ _ (tB E F n) (tU2 E F n) _ u w c (R_sig0 hE hEF hn hg) (R_sig1 hE hEF hn hg) c1 c2 c3 c4 h1 h2 h3 h4

theorem R_le (u w c : ℝ)
    (h1 : u * (tB E F n).1 + w * (tB E F n).2 ≤ c) (h2 : u * (tU2 E F n).1 + w * (tU2 E F n).2 ≤ c)
    (h3 : u * (tA2 E F n).1 + w * (tA2 E F n).2 ≤ c) (h4 : u * (tU1 E F n).1 + w * (tU1 E F n).2 ≤ c) :
    ∀ p ∈ Preg (tAs E F n) (tA2 E F n) (tU1 E F n) ((gg E F n - E) / gg E F n), u * p.1 + w * p.2 ≤ c := by
  obtain ⟨c1, c2, c3, c4⟩ := R_cut hE hEF hn hg
  exact preg_le4 _ _ _ (tB E F n) (tU2 E F n) _ u w c (R_sig0 hE hEF hn hg) (R_sig1 hE hEF hn hg) c1 c2 c3 c4 h1 h2 h3 h4

end pieces

end

end Erdos634.Draft.ThetaUnit
