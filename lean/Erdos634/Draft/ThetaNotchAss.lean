-- Draft/ThetaNotchAss.lean -- the Rh group (C1 + C2 + C3) and its region rReg, case rho = 0 (target membership and the assembly are in ThetaNotchMain).
-- INTERNAL BUILD ONLY, UNAUDITED (reading audit 2026-11-14, SOUND WITH GAPS, internal audit).  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchL2

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam

def rReg (E F m j s : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 * ax E F p + (-1) * ay E F s p ≤ 0 ∧ 0 * ax E F p + 1 * ay E F s p ≤ j * F ∧
    (-1) * ax E F p + (-1) * ay E F s p ≤ -s ∧ 1 * ax E F p + 1 * ay E F s p ≤ F * m + j * F ∧
    F ^ 2 * ax E F p + (2 * F ^ 2 - E ^ 2) * ay E F s p ≤ (F * ((F ^ 2 - E ^ 2) * m)) + (2 * F ^ 2 - E ^ 2) * (j * F)}

namespace NP
variable (P : NP)

section rg
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- **the Rh group**: `C1 + C2 + C3` tile the pentagon `Rh minus (en)tau` -/
def rFam : TFam (Phi φ '' rReg (P.e : ℝ) P.f P.m P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef)
    (2 * P.pp * (P.qq - P.en) + 2 * (P.pp - P.en) * P.en + P.en * P.en) := by
  have H := P.rh
  have hE := H.hE
  have hEF := H.hEF
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := c1_facts H
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := c2_facts H
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := c3_facts H
  refine TFam.join3 (c1Fam P hφ hφE) (c2Fam P hφ hφE) (c3Fam P hφ hφE) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Set.image_mono (fun p hp => ⟨a1 p hp, a2 p hp, a3 p hp, a4 p hp, a5 p hp⟩)
  · exact Set.image_mono (fun p hp => ⟨b1 p hp, b2 p hp, b3 p hp, b4 p hp, b5 p hp⟩)
  · exact Set.image_mono (fun p hp => ⟨c1 p hp, c2 p hp, c3 p hp, c4 p hp, c5 p hp⟩)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inr one_ne_zero) (by norm_num) (by norm_num) rfl a6 b6)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inr one_ne_zero) (by norm_num) (by norm_num) rfl a6 c6)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl one_ne_zero) (by norm_num) (by norm_num) (by norm_num) b7 c7)

end rg

end NP

end

end Erdos634.Draft.ThetaNotch
