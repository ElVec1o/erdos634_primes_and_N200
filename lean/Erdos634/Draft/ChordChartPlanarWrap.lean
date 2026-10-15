import Erdos634.ChordChartPlanar
namespace Erdos634.Draft.ChordChartPlanarWrap
open Erdos634.ChordChartPlanar Erdos634.CertCoord Erdos634.Geometry

theorem wrap_interiors_meet_at_shared_foot
    (p₁ qx₁ qy₁ p₂ qx₂ qy₂ : ℝ)
    (hp₁ : p₁ < 0) (hqx₁ : 0 < qx₁) (hqy₁ : 0 < qy₁)
    (hp₂ : 0 < p₂) (hqx₂ : qx₂ < 0) (hqy₂ : 0 < qy₂)
    (hD₁ : 0 < det3 0 0 qx₁ qy₁ p₁ 0) (hD₂ : 0 < det3 0 0 p₂ 0 qx₂ qy₂) :
    ∃ z : Plane,
      z ∈ interior (mkTri 0 0 qx₁ qy₁ p₁ 0 hD₁.ne').carrier ∧
      z ∈ interior (mkTri 0 0 p₂ 0 qx₂ qy₂ hD₂.ne').carrier :=
  interiors_meet_at_shared_foot p₁ qx₁ qy₁ p₂ qx₂ qy₂ hp₁ hqx₁ hqy₁ hp₂ hqx₂ hqy₂ hD₁ hD₂

theorem wrap_member_configuration_interiors_meet
    (e f xu xr c₁ c₂ : ℝ) (he : 0 < e) (hef : e < f)
    (hu : e * f < xu) (hr : xr < 0) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hD₁ : 0 < det3 0 0 (-(e * f) + xu) c₁ (-(e * f)) 0)
    (hD₂ : 0 < det3 0 0 (e * f) 0 xr c₂) :
    ∃ z : Plane,
      z ∈ interior (mkTri 0 0 (-(e * f) + xu) c₁ (-(e * f)) 0 hD₁.ne').carrier ∧
      z ∈ interior (mkTri 0 0 (e * f) 0 xr c₂ hD₂.ne').carrier :=
  member_configuration_interiors_meet e f xu xr c₁ c₂ he hef hu hr hc₁ hc₂ hD₁ hD₂

theorem wrap_member_hypotheses_inhabited :
    (0:ℝ) < 1 ∧ (1:ℝ) < 2 ∧ ((1:ℝ) * 2) < 11/4 ∧ (-1:ℝ) < 0 ∧
      0 < det3 0 0 (-((1:ℝ) * 2) + 11/4) 1 (-((1:ℝ) * 2)) 0 ∧
      0 < det3 0 0 ((1:ℝ) * 2) 0 (-1) 1 :=
  member_hypotheses_inhabited

example : True := trivial
#print axioms wrap_member_configuration_interiors_meet
end Erdos634.Draft.ChordChartPlanarWrap
