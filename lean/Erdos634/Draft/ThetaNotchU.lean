-- Draft/ThetaNotchU.lean -- the U group of the notch seed: `theta_M(D)` minus the mirrored `theta_n'` = v-tau + pi5 + pi4.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  Case rho = 0 of T2 (`internal notes`), as `t2_region` of
`rust/audit_notch_20261114`.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchGroups

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam

/-- two regions with opposite facts (`al2 = -al`, ...) have disjoint interiors -/
theorem disjLF {E F : ℝ} (s : ℝ) (hE : 0 < E) (hEF : E < F) {S1 S2 : Set (ℝ × ℝ)} {al be ga al2 be2 ga2 : ℝ}
    (hnd : al ≠ 0 ∨ be ≠ 0) (ha : al2 = -al) (hb : be2 = -be) (hg : ga2 = -ga)
    (h1 : LF E F s S1 al be ga) (h2 : LF E F s S2 al2 be2 ga2) : Disjoint (interior S1) (interior S2) := by
  subst ha hb hg
  exact disj_of_facts s hE hEF al be ga hnd h1 h2

def suReg (E F m j s : ℝ) : Set (ℝ × ℝ) :=
  {p | (-1) * ax E F p + 0 * ay E F s p ≤ 0 ∧ 0 * ax E F p + (-1) * ay E F s p ≤ -(j * F) ∧
    F ^ 2 * ax E F p + (F ^ 2 - E ^ 2) * ay E F s p ≤ (F ^ 2 - E ^ 2) * (F * m + j * F)}

namespace NP
variable (P : NP)

section ug
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- **the U group**: `v-tau + pi5 + pi4` tile the triangle `(D, P2', V2)` -/
def uFam : TFam (Phi φ '' suReg (P.e : ℝ) P.f P.m P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef)
    (P.v * P.v + (P.gn * P.gn - (P.gn - P.e) * (P.gn - P.e)) + 2 * P.f * P.gn) := by
  have H := P.rh
  have hE := H.hE
  have hEF := H.hEF
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  obtain ⟨v1, v2, v3, v4⟩ := vt_facts H
  obtain ⟨q1, q2, q3, q4, q5⟩ := p5_facts H
  obtain ⟨r1, r2, r3, r4, r5⟩ := p4_facts H
  refine TFam.join3 (vtFam P hφ hφE) (p5Fam P hφ hφE) (p4Fam P hφ hφE) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Set.image_mono (fun p hp => ⟨v1 p hp, v2 p hp, v3 p hp⟩)
  · exact Set.image_mono (fun p hp => ⟨q1 p hp, q2 p hp, q3 p hp⟩)
  · exact Set.image_mono (fun p hp => ⟨r1 p hp, r2 p hp, r3 p hp⟩)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by positivity)) rfl rfl rfl v4 q4)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by positivity)) rfl rfl rfl v4 r4)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by norm_num)) (by norm_num) (by norm_num) (by norm_num) q5 r5)

end ug

end NP

end

end Erdos634.Draft.ThetaNotch
