import Erdos634.LemmaPTree
namespace Erdos634.Draft.LemmaPTreeWrap
open Erdos634.LemmaPTree
open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertNode Erdos634.CertGeom Erdos634.PlacementCompleteness

theorem wrap_hD32 : (0 : ℝ) < 32 :=
  hD32

theorem wrap_sr32_lt : sr 32 < 6 :=
  sr32_lt

theorem wrap_sr32_gt1 : 1 < sr 32 :=
  sr32_gt1

theorem wrap_MODEL_sides : dist (MODEL.pts 0) (MODEL.pts 1) = 6 ∧
    dist (MODEL.pts 1) (MODEL.pts 2) = 5 ∧
    dist (MODEL.pts 0) (MODEL.pts 2) = 9 :=
  MODEL_sides

theorem wrap_T0_pts : T0.pts 0 = rp 32 0 0 ∧ T0.pts 1 = rp 32 6 0 ∧
    T0.pts 2 = rp 32 (23/3) (5/6) :=
  T0_pts

theorem wrap_T1_pts : T1.pts 0 = rp 32 6 0 ∧ T1.pts 1 = rp 32 15 0 ∧
    T1.pts 2 = rp 32 (100/9) (5/9) :=
  T1_pts

theorem wrap_T5_pts : T5.pts 0 = rp 32 15 0 ∧ T5.pts 1 = rp 32 20 0 ∧
    T5.pts 2 = rp 32 22 1 :=
  T5_pts

example : True := trivial
#print axioms wrap_MODEL_sides
end Erdos634.Draft.LemmaPTreeWrap
