/-
Draft/DirCosetApps.lean: the γ-grading of edge directions and the coset clause of the direction group statement, from
`DirCoset.edge_dir_pair`.

* `dir_coset_general`: in any congruent dissection, the difference of two tile edge directions is
  `x α + y β + z π` with integers `x, y, z`, where `α`, `β` are the model's angles at its vertices 0 and 1.
* `gamma_grading`: if the model's angles are `α, β, γ` with `3α + 2β = π` and `γ = 2α + β`, the difference of two
  tile edge directions is `m γ + l π` with integers `m, l`.  No sorry, no native_decide.
-/
import Erdos634.Draft.DirCoset

open scoped Classical

namespace Erdos634.Draft.DirCoset

open Erdos634.Geometry

variable {N : ℕ}

/-- `(x, y, z) ↦ x a + y b + z π` -/
noncomputable def dirHom (a b : Real.Angle) : ℤ × ℤ × ℤ →+ Real.Angle :=
  (zmultiplesHom Real.Angle a).coprod
    ((zmultiplesHom Real.Angle b).coprod (zmultiplesHom Real.Angle ((Real.pi : ℝ) : Real.Angle)))

theorem dirHom_apply (a b : Real.Angle) (x y z : ℤ) :
    dirHom a b (x, y, z) = x • a + (y • b + z • ((Real.pi : ℝ) : Real.Angle)) := by
  simp only [dirHom, AddMonoidHom.coprod_apply, zmultiplesHom_apply]

/-- `(m, l) ↦ m g + l π` -/
noncomputable def gHom (g : Real.Angle) : ℤ × ℤ →+ Real.Angle :=
  (zmultiplesHom Real.Angle g).coprod (zmultiplesHom Real.Angle ((Real.pi : ℝ) : Real.Angle))

theorem gHom_apply (g : Real.Angle) (m l : ℤ) :
    gHom g (m, l) = m • g + l • ((Real.pi : ℝ) : Real.Angle) := by
  simp only [gHom, AddMonoidHom.coprod_apply, zmultiplesHom_apply]

theorem angle_sum (T : Tri) : T.angleAt 0 + T.angleAt 1 + T.angleAt 2 = Real.pi := by
  unfold Tri.angleAt
  exact cornerAngle_sum T

/-- **`prop:dirgroup`, coset clause.**  In any tiling by congruent copies of a triangle with angles `α`, `β`
(and `π − α − β`), two edge directions differ by `x α + y β + z π`. -/
theorem dir_coset_general (D : CongruentDissection N) (i i' : Fin N) (k k' : Fin 3) :
    ∃ x y z : ℤ, ((D.tile i).leftUnit k).angle - ((D.tile i').leftUnit k').angle
      = x • ((D.model.angleAt 0 : ℝ) : Real.Angle) + y • ((D.model.angleAt 1 : ℝ) : Real.Angle)
        + z • ((Real.pi : ℝ) : Real.Angle) := by
  have hπ : ((Real.pi : ℝ) : Real.Angle) ∈
      (dirHom ((D.model.angleAt 0 : ℝ) : Real.Angle) ((D.model.angleAt 1 : ℝ) : Real.Angle)).range :=
    ⟨(0, 0, 1), by rw [dirHom_apply]; simp⟩
  have hM : ∀ j, ((D.model.angleAt j : ℝ) : Real.Angle) ∈
      (dirHom ((D.model.angleAt 0 : ℝ) : Real.Angle) ((D.model.angleAt 1 : ℝ) : Real.Angle)).range := by
    intro j
    have hj : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    rcases hj j with rfl | rfl | rfl
    · exact ⟨(1, 0, 0), by rw [dirHom_apply]; simp⟩
    · exact ⟨(0, 1, 0), by rw [dirHom_apply]; simp⟩
    · refine ⟨(-1, -1, 1), ?_⟩
      have hs := angle_sum D.model
      have h2 : D.model.angleAt 2 = Real.pi - D.model.angleAt 0 - D.model.angleAt 1 := by linarith
      rw [h2, dirHom_apply, Real.Angle.coe_sub, Real.Angle.coe_sub]
      simp only [neg_smul, one_smul]
      abel
  obtain ⟨⟨x, y, z⟩, hxyz⟩ := edge_dir_pair _ hπ D hM i i' k k'
  exact ⟨x, y, z, by rw [← hxyz, dirHom_apply]; abel⟩

/-- **`prop:gammagrading`.**  For a tile with `3α + 2β = π`, `γ = 2α + β`, two edge directions of any tiling
differ by an integer multiple of `γ` modulo `π`. -/
theorem gamma_grading (D : CongruentDissection N) {α β γ : ℝ}
    (hα : D.model.angleAt 0 = α) (hβ : D.model.angleAt 1 = β) (hγ : D.model.angleAt 2 = γ)
    (hrel : 3 * α + 2 * β = Real.pi) (hγdef : γ = 2 * α + β) (i i' : Fin N) (k k' : Fin 3) :
    ∃ m l : ℤ, ((D.tile i).leftUnit k).angle - ((D.tile i').leftUnit k').angle
      = m • ((γ : ℝ) : Real.Angle) + l • ((Real.pi : ℝ) : Real.Angle) := by
  have hπ : ((Real.pi : ℝ) : Real.Angle) ∈ (gHom ((γ : ℝ) : Real.Angle)).range :=
    ⟨(0, 1), by rw [gHom_apply]; simp⟩
  have hM : ∀ j, ((D.model.angleAt j : ℝ) : Real.Angle) ∈ (gHom ((γ : ℝ) : Real.Angle)).range := by
    intro j
    have hj : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    rcases hj j with rfl | rfl | rfl
    · refine ⟨(2, -1), ?_⟩
      have h : α = ((2 : ℤ) : ℝ) * γ - Real.pi := by push_cast; linarith
      rw [hα, h, gHom_apply, Real.Angle.coe_sub, Real.Angle.intCast_mul_eq_zsmul]
      simp only [neg_smul, one_smul]
      abel
    · refine ⟨(-3, 2), ?_⟩
      have h : β = ((-3 : ℤ) : ℝ) * γ + ((2 : ℤ) : ℝ) * Real.pi := by push_cast; linarith
      rw [hβ, h, gHom_apply, Real.Angle.coe_add, Real.Angle.intCast_mul_eq_zsmul,
        Real.Angle.intCast_mul_eq_zsmul]
    · exact ⟨(1, 0), by rw [gHom_apply, hγ]; simp⟩
  obtain ⟨⟨m, l⟩, hml⟩ := edge_dir_pair _ hπ D hM i i' k k'
  exact ⟨m, l, by rw [← hml, gHom_apply]⟩

end Erdos634.Draft.DirCoset

#print axioms Erdos634.Draft.DirCoset.dir_coset_general
#print axioms Erdos634.Draft.DirCoset.gamma_grading
