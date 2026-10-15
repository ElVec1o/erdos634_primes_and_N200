import Erdos634.ReflS.MT30Inst
import Erdos634.ReflS.Sound
import Erdos634.NormalPosition

/-! ReflS/MT30Setup.lean -- the instance `T30` in real coordinates (hand-written; the certificate is generated).

Target: the equilateral triangle of side 60, `(0,0), (60,0), (30, 30√3)`.
Model: the tile with sides `9+√21, 9−√21, 12` (angle `π/3` opposite the side 12),
`(0,0), (9+√21, 0), ((9+3√21)/2, ((9−√21)/2)·√3)`.
This is the `π/3` pair `(30,6)` of `N = 60` (`GapE60 60`). -/

open Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord

namespace ReflS

theorem cast_zi (a : ℤ) : ((zi a : R) : ℝ) = (a : ℝ) := by
  show φ ⟨a, 0⟩ = _
  rw [φ_apply]; simp

theorem cast_zr (a b : ℤ) : ((zr a b : R) : ℝ) = (a : ℝ) + (b : ℝ) * Real.sqrt 21 := by
  show φ ⟨a, b⟩ = _
  rw [φ_apply]; simp

namespace MT30

theorem s21 : Real.sqrt 21 * Real.sqrt 21 = 21 := Real.mul_self_sqrt (by norm_num)
theorem s21_pos : 0 < Real.sqrt 21 := Real.sqrt_pos.mpr (by norm_num)
theorem s21_lt : Real.sqrt 21 < 5 := by
  have := s21
  by_contra h
  push_neg at h
  nlinarith

theorem hDn : (0:ℝ) < 3 := by norm_num

theorem TGT_pos : 0 < ef 0 0 60 0 30 30 := by unfold ef; norm_num
/-- the equilateral target of side 60 -/
noncomputable def TGT : Erdos634.Geometry.Tri := rtri 3 hDn 0 0 60 0 30 30 TGT_pos
theorem TGT_sides : dist (TGT.pts 0) (TGT.pts 1) = 60 ∧ dist (TGT.pts 1) (TGT.pts 2) = 60 ∧
    dist (TGT.pts 0) (TGT.pts 2) = 60 :=
  model_sides_rp hDn TGT_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem MODEL_pos : 0 < ef 0 0 (9 + Real.sqrt 21) 0 ((9 + 3 * Real.sqrt 21) / 2) ((9 - Real.sqrt 21) / 2) := by
  unfold ef
  have := s21
  nlinarith
/-- the tile `(9+√21, 9−√21, 12)` -/
noncomputable def MODEL : Erdos634.Geometry.Tri :=
  rtri 3 hDn 0 0 (9 + Real.sqrt 21) 0 ((9 + 3 * Real.sqrt 21) / 2) ((9 - Real.sqrt 21) / 2) MODEL_pos
theorem MODEL_sides : dist (MODEL.pts 0) (MODEL.pts 1) = 9 + Real.sqrt 21 ∧
    dist (MODEL.pts 1) (MODEL.pts 2) = 9 - Real.sqrt 21 ∧ dist (MODEL.pts 0) (MODEL.pts 2) = 12 := by
  have h := s21
  have hp := s21_pos
  have hl := s21_lt
  exact model_sides_rp hDn MODEL_pos (by linarith) (by linarith) (by norm_num)
    (by ring) (by ring) (by nlinarith)

theorem tgt_ok : inst.tgt.ok = true := by decide +kernel

theorem tgt_carr : inst.tgt.carr 3 = TGT.carrier := by
  obtain ⟨hp, h⟩ := Tri.ok_sem 3 hDn inst.tgt tgt_ok
  rw [h]
  have e1 : inst.tgt.a.X = 0 := by simp [inst, pt, Pt.X, cast_zi]
  have e2 : inst.tgt.a.Y = 0 := by simp [inst, pt, Pt.Y, cast_zi]
  have e3 : inst.tgt.b.X = 60 := by simp [inst, pt, Pt.X, cast_zi]
  have e4 : inst.tgt.b.Y = 0 := by simp [inst, pt, Pt.Y, cast_zi]
  have e5 : inst.tgt.c.X = 30 := by simp [inst, pt, Pt.X, cast_zi]
  have e6 : inst.tgt.c.Y = 30 := by simp [inst, pt, Pt.Y, cast_zi]
  unfold TGT
  simp only [e1, e2, e3, e4, e5, e6]

theorem hMa : dist (MODEL.pts 0) (MODEL.pts 1) = ((inst.sides.1 : R) : ℝ) := by
  rw [(MODEL_sides).1]; simp [inst, cast_zr]
theorem hMb : dist (MODEL.pts 1) (MODEL.pts 2) = ((inst.sides.2.1 : R) : ℝ) := by
  rw [(MODEL_sides).2.1]; simp [inst, cast_zr]; ring
theorem hMc : dist (MODEL.pts 0) (MODEL.pts 2) = ((inst.sides.2.2 : R) : ℝ) := by
  rw [(MODEL_sides).2.2]; simp [inst, cast_zi]
theorem hDnI : ((inst.Dn : R) : ℝ) = 3 := by simp [inst, cast_zi]

end MT30
end ReflS
