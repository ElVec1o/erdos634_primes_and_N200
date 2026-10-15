import Erdos634.Refl.DataA
import Erdos634.Refl.SoundStage13
import Erdos634.N15IsoA
import Erdos634.NormalPosition

/-! Reflective reproduction of `Erdos634.N15IsoA.not_dissection`: `Refl.checkAll_sound` on the real
    `DataA` instance, with the same NormalPosition lift as `N15IsoALift`. -/

open Erdos634.CertNode Erdos634.Geometry

namespace Refl.BridgeA

theorem hD7 : (0:ℝ) < 7 := by norm_num

theorem wA_ok : inst.ok = true := by decide +kernel
theorem wA_base : inst.baseY = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem wA_check : inst.checkAll 100 tree = true := by decide +kernel

theorem tgt_ok : inst.tgt.ok = true := by decide +kernel

/-- the reflective instance target is the unrolled `TGT`. -/
theorem tgt_carr : inst.tgt.carr 7 = Erdos634.N15IsoA.TGT.carrier := by
  obtain ⟨hp, h⟩ := Tri.ok_sem 7 hD7 inst.tgt tgt_ok
  rw [h]
  have e1 : inst.tgt.a.X = 0 := by simp [inst, pt, Pt.X]
  have e2 : inst.tgt.a.Y = 0 := by simp [inst, pt, Pt.Y]
  have e3 : inst.tgt.b.X = 15 := by simp [inst, pt, Pt.X]
  have e4 : inst.tgt.b.Y = 0 := by simp [inst, pt, Pt.Y]
  have e5 : inst.tgt.c.X = 15/2 := by simp [inst, pt, Pt.X]
  have e6 : inst.tgt.c.Y = 45/2 := by simp [inst, pt, Pt.Y]
  unfold Erdos634.N15IsoA.TGT
  simp only [e1, e2, e3, e4, e5, e6]

theorem not_dissection_refl {N : ℕ} (D : CongruentDissection N)
    (hT : D.target.Congruent Erdos634.N15IsoA.TGT) (hM : D.model.Congruent Erdos634.N15IsoA.MODEL) : False := by
  obtain ⟨g, D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hT
  obtain ⟨hMa, hMb, hMc⟩ := Erdos634.N15IsoA.MODEL_sides
  have S : Sound 7 inst Erdos634.N15IsoA.MODEL [] := checkAll_sound 7 hD7 inst (by norm_num [inst]) Erdos634.N15IsoA.MODEL
    (by simpa [inst] using hMa) (by simpa [inst] using hMb) (by simpa [inst] using hMc)
    wA_base 100 tree wA_check
  exact S (N := N) D' (by rw [hD'T, tgt_carr]) (by rw [hD'M]; exact hM) (by simp)

end Refl.BridgeA
#print axioms Refl.BridgeA.not_dissection_refl
#print axioms Refl.BridgeA.wA_check
