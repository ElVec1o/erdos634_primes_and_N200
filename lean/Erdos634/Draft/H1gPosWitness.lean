-- Draft/H1gPosWitness.lean — non-vacuity control for H1gPos: the theorems apply to a real
-- `CongruentDissection` (the N = 2 witness `dissection'` of H1Witnesses), with the minimal field.
--  Standard axioms, no sorry.
import Erdos634.Draft.H1gPosGlue
import Erdos634.Draft.H1Witnesses

open scoped Classical

namespace Erdos634.H1gPos

open Erdos634.Geometry Erdos634.CertCoord Erdos634.AngleThreshold
open Erdos634.Draft.FluxGRow3AngleWitnessDissection Erdos634.Draft.FluxGRow3WitnessBridge
open Erdos634.Draft.FluxGRow3SharedGrid Erdos634.Draft.FluxGRow3Step3N2Final
open Erdos634.Draft.FluxRow4Witness Erdos634.Geometry.Row3 Erdos634.Draft.FluxGRow3RPWitness

/-- `L1_modelField` instantiated on the real 2-tile dissection. -/
theorem L1_witness : ∃ (g : Plane ≃ᵢ Plane) (D' : CongruentDissection 2),
    D'.target.pts 0 = 0 ∧ D'.target.pts 1 1 = 0 ∧
    (∀ i k v, (D'.tile i).pts k v ∈ modelField dissection') :=
  let ⟨g, D', _, _, _, h0, h1, hA, _⟩ := L1_modelField dissection'
  ⟨g, D', h0, h1, hA⟩

/-- `L1_pos` on the real witness (any base tile and corner). -/
theorem L1_pos_witness : ∀ i k, (dissection'.tile i).pts k - (dissection'.tile 0).pts 0 ∈
    edgeGroup dissection'.toDissection :=
  L1_pos dissection'.toDissection 0 0

end Erdos634.H1gPos

#print axioms Erdos634.H1gPos.L1_witness
#print axioms Erdos634.H1gPos.L1_pos_witness
