/-
Draft/ZhangRot.lean — third layer: lattice isometries of the skew frame `Φ_1` (rotations by `2π/3`) as `Plane ≃ᵢ Plane`,
and the transport `Pc.map` of a piece along such a map.

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.ZhangTrap

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.ZhangRot
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G
open Erdos634.Draft.F4All (hf1 f4_eq_of_sq)
open Erdos634.Draft.ZhangBase
open Erdos634.Draft.CollarParam (RTiling.cast)

/-- the skew quadratic form is preserved. -/
def QPres (φ : ℝ × ℝ → ℝ × ℝ) : Prop :=
  ∀ z w : ℝ × ℝ, ((φ z).1 - (φ w).1) ^ 2 + ((φ z).2 - (φ w).2) ^ 2 + ((φ z).1 - (φ w).1) * ((φ z).2 - (φ w).2) / 1
    = (z.1 - w.1) ^ 2 + (z.2 - w.2) ^ 2 + (z.1 - w.1) * (z.2 - w.2) / 1

theorem skew_dist (φ : ℝ × ℝ → ℝ × ℝ) (hq : QPres φ) (x y : Plane) :
    dist (Phi 1 (φ (Psi 1 x))) (Phi 1 (φ (Psi 1 y))) = dist x y := by
  refine f4_eq_of_sq dist_nonneg dist_nonneg ?_
  have ex : dist x y ^ 2 = ((Psi 1 x).1 - (Psi 1 y).1) ^ 2 + ((Psi 1 x).2 - (Psi 1 y).2) ^ 2
      + ((Psi 1 x).1 - (Psi 1 y).1) * ((Psi 1 x).2 - (Psi 1 y).2) / 1 := by
    have := sq_Phi' hf1 (Psi 1 x) (Psi 1 y)
    rwa [Phi_Psi' hf1, Phi_Psi' hf1] at this
  rw [ex, sq_Phi' hf1]
  exact hq _ _

/-- the isometry of the plane induced by a lattice map `φ` with inverse `ψ` preserving the form. -/
noncomputable def skewIso (φ ψ : ℝ × ℝ → ℝ × ℝ) (h1 : ∀ z, ψ (φ z) = z) (h2 : ∀ z, φ (ψ z) = z)
    (hq : QPres φ) : Plane ≃ᵢ Plane where
  toFun x := Phi 1 (φ (Psi 1 x))
  invFun y := Phi 1 (ψ (Psi 1 y))
  left_inv x := by simp only [Psi_Phi' hf1, h1, Phi_Psi' hf1]
  right_inv y := by simp only [Psi_Phi' hf1, h2, Phi_Psi' hf1]
  isometry_toFun := Isometry.of_dist_eq (skew_dist φ hq)

theorem skewIso_apply (φ ψ : ℝ × ℝ → ℝ × ℝ) (h1 : ∀ z, ψ (φ z) = z) (h2 : ∀ z, φ (ψ z) = z)
    (hq : QPres φ) (z : ℝ × ℝ) : skewIso φ ψ h1 h2 hq (Phi 1 z) = Phi 1 (φ z) := by
  show Phi 1 (φ (Psi 1 (Phi 1 z))) = _
  rw [Psi_Phi' hf1]

theorem Pc.map {M : TriG} {B : Set (ℝ × ℝ)} {N : ℕ} (h : Pc M B N) (φ ψ : ℝ × ℝ → ℝ × ℝ)
    (h1 : ∀ z, ψ (φ z) = z) (h2 : ∀ z, φ (ψ z) = z) (hq : QPres φ) : Pc M (φ '' B) N := by
  obtain ⟨S, hS, ⟨R⟩⟩ := h
  refine ⟨φ '' S, Set.image_mono hS, ⟨?_⟩⟩
  have e : skewIso φ ψ h1 h2 hq '' (Phi 1 '' S) = Phi 1 '' (φ '' S) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr (fun z _ => skewIso_apply φ ψ h1 h2 hq z)
  exact RTiling.cast e (RegionTiling.map R (skewIso φ ψ h1 h2 hq))

/-- the rotations of the triangle `(0,0), (L,0), (0,L)`. -/
def rotB (L : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (L - z.1 - z.2, z.1)
def rotC (L : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.2, L - z.1 - z.2)

theorem rotC_rotB (L : ℝ) (z : ℝ × ℝ) : rotC L (rotB L z) = z := by
  simp only [rotB, rotC]; ext <;> simp <;> ring
theorem rotB_rotC (L : ℝ) (z : ℝ × ℝ) : rotB L (rotC L z) = z := by
  simp only [rotB, rotC]; ext <;> simp

theorem rotB_q (L : ℝ) : QPres (rotB L) := by
  intro z w; simp only [rotB]; ring
theorem rotC_q (L : ℝ) : QPres (rotC L) := by
  intro z w; simp only [rotC]; ring

end Erdos634.Draft.ZhangRot
