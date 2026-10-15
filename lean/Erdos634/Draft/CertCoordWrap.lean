import Erdos634.CertCoord

namespace Erdos634.Draft.CertCoordWrap

open Erdos634.CertCoord Erdos634.Geometry

theorem cc_dist_sq_mkPt (x₁ y₁ x₂ y₂ : ℝ) :
    dist (mkPt x₁ y₁) (mkPt x₂ y₂) ^ 2 = (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 :=
  dist_sq_mkPt x₁ y₁ x₂ y₂

theorem cc_not_collinear_of_det {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ} (hdet : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    ¬ Collinear ℝ ({mkPt x₀ y₀, mkPt x₁ y₁, mkPt x₂ y₂} : Set Plane) :=
  not_collinear_of_det hdet

theorem cc_detTri_mkTri (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (hdet : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    Erdos634.AreaDet.detTri (mkTri x₀ y₀ x₁ y₁ x₂ y₂ hdet) = det3 x₀ y₀ x₁ y₁ x₂ y₂ :=
  detTri_mkTri x₀ y₀ x₁ y₁ x₂ y₂ hdet

theorem cc_det3_split (x₀ y₀ x₁ y₁ x₂ y₂ a b : ℝ) :
    det3 a b x₁ y₁ x₂ y₂ + det3 x₀ y₀ a b x₂ y₂ + det3 x₀ y₀ x₁ y₁ a b
      = det3 x₀ y₀ x₁ y₁ x₂ y₂ :=
  det3_split x₀ y₀ x₁ y₁ x₂ y₂ a b

example : cc_det3_split 0 0 1 0 0 1 (1/3) (1/3) = det3_split 0 0 1 0 0 1 (1/3) (1/3) := rfl

#print axioms cc_detTri_mkTri

end Erdos634.Draft.CertCoordWrap
