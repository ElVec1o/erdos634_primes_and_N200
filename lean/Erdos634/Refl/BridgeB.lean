import Erdos634.Refl.DataB
import Erdos634.Refl.SoundStage13
import Erdos634.NormalPosition

/-! Reflective refutation for N=15 isoB: target `(0,0),(105,0),(105/2, 45/2 √23)`, tile sides `(56,15,64)`.
    `Refl.checkAll_sound` on the real `DataB` instance (526 nodes) with the NormalPosition lift, mirroring
    `Refl.BridgeA`. `TGT`/`MODEL` restored from a script (INST isoB). -/

open Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord

namespace Refl.BridgeB

theorem hD23 : (0:ℝ) < 23 := by norm_num

theorem TGT_pos : 0 < ef 0 0 105 0 (105/2) (45/2) := by unfold ef; norm_num
/-- The target `(0, 0)`, `(105, 0)`, `(105/2, 45/2·r)`. -/
noncomputable def TGT : Erdos634.Geometry.Tri := rtri 23 hD23 0 0 105 0 (105/2) (45/2) TGT_pos
theorem MODEL_pos : 0 < ef 0 0 56 0 (1001/16) (45/16) := by unfold ef; norm_num
/-- The model tile `(0, 0)`, `(56, 0)`, `(1001/16, 45/16·r)`: sides `56, 15, 64`. -/
noncomputable def MODEL : Erdos634.Geometry.Tri := rtri 23 hD23 0 0 56 0 (1001/16) (45/16) MODEL_pos
theorem MODEL_sides : dist (MODEL.pts 0) (MODEL.pts 1) = 56 ∧ dist (MODEL.pts 1) (MODEL.pts 2) = 15 ∧
    dist (MODEL.pts 0) (MODEL.pts 2) = 64 :=
  model_sides_rp hD23 MODEL_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem wB_ok : instB.ok = true := by decide +kernel
theorem wB_base : instB.baseY = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem wB_check : instB.checkAll 200 treeB = true := by decide +kernel

theorem tgt_ok : instB.tgt.ok = true := by decide +kernel

theorem tgt_carr : instB.tgt.carr 23 = TGT.carrier := by
  obtain ⟨hp, h⟩ := Tri.ok_sem 23 hD23 instB.tgt tgt_ok
  rw [h]
  have e1 : instB.tgt.a.X = 0 := by simp [instB, pt, Pt.X]
  have e2 : instB.tgt.a.Y = 0 := by simp [instB, pt, Pt.Y]
  have e3 : instB.tgt.b.X = 105 := by simp [instB, pt, Pt.X]
  have e4 : instB.tgt.b.Y = 0 := by simp [instB, pt, Pt.Y]
  have e5 : instB.tgt.c.X = 105/2 := by simp [instB, pt, Pt.X]
  have e6 : instB.tgt.c.Y = 45/2 := by simp [instB, pt, Pt.Y]
  unfold TGT
  simp only [e1, e2, e3, e4, e5, e6]

theorem not_dissection_refl {N : ℕ} (D : CongruentDissection N)
    (hT : D.target.Congruent TGT) (hM : D.model.Congruent MODEL) : False := by
  obtain ⟨g, D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hT
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have S : Sound 23 instB MODEL [] := checkAll_sound 23 hD23 instB (by norm_num [instB]) MODEL
    (by simpa [instB] using hMa) (by simpa [instB] using hMb) (by simpa [instB] using hMc)
    wB_base 200 treeB wB_check
  exact S (N := N) D' (by rw [hD'T, tgt_carr]) (by rw [hD'M]; exact hM) (by simp)

end Refl.BridgeB
#print axioms Refl.BridgeB.not_dissection_refl
#print axioms Refl.BridgeB.wB_check
