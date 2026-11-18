-- Draft/ThetaNotchGroups.lean -- joins of 2 and 3 tile families; the U group family (v-tau + pi5 + pi4).
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchFamU

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam

def TFam.join2 {M : Erdos634.Geometry.Tri} {S S1 S2 : Set Plane} {n1 n2 : ℕ} (R1 : TFam S1 M n1) (R2 : TFam S2 M n2)
    (h1 : S1 ⊆ S) (h2 : S2 ⊆ S) (d : Disjoint (interior S1) (interior S2)) : TFam S M (n1 + n2) :=
  castTF rfl (by simp [Fin.sum_univ_two]) (TFam.join (m := 2) S ![S1, S2] ![n1, n2]
    (fun a => match a with | ⟨0, _⟩ => R1 | ⟨1, _⟩ => R2 | ⟨k + 2, h⟩ => absurd h (by omega))
    (fun a => by fin_cases a <;> assumption)
    (fun a b hab => by
      fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | exact d | exact d.symm))

def TFam.join3 {M : Erdos634.Geometry.Tri} {S S1 S2 S3 : Set Plane} {n1 n2 n3 : ℕ} (R1 : TFam S1 M n1) (R2 : TFam S2 M n2)
    (R3 : TFam S3 M n3) (h1 : S1 ⊆ S) (h2 : S2 ⊆ S) (h3 : S3 ⊆ S) (d12 : Disjoint (interior S1) (interior S2))
    (d13 : Disjoint (interior S1) (interior S3)) (d23 : Disjoint (interior S2) (interior S3)) :
    TFam S M (n1 + n2 + n3) :=
  castTF rfl (by simp [Fin.sum_univ_three]) (TFam.join (m := 3) S ![S1, S2, S3] ![n1, n2, n3]
    (fun a => match a with | ⟨0, _⟩ => R1 | ⟨1, _⟩ => R2 | ⟨2, _⟩ => R3 | ⟨k + 3, h⟩ => absurd h (by omega))
    (fun a => by fin_cases a <;> assumption)
    (fun a b hab => by
      fin_cases a <;> fin_cases b <;>
        first | exact absurd rfl hab | exact d12 | exact d12.symm | exact d13 | exact d13.symm | exact d23 | exact d23.symm))

end

end Erdos634.Draft.ThetaNotch
