import Erdos634.Draft.SIXRunS21
import Erdos634.Refl.SoundE4
import Erdos634.NormalPosition
import Erdos634.Draft.SIXCong

/-! Draft/SIXBridgeS21.lean.  `Refl.checkAllR_sound` on the chunked `SIXDataS21` certificate
    (pattern of `Refl.BridgeE120`).  Result `not_dissection_sides`: no `CongruentDissection` (any `N`) whose target has opposite sides
    (12,12,21) (vertex-labelled as in `TGT`) and whose model has the sides (2,3,4) in some order. -/

open Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord

namespace Refl.SIXBridgeS21

set_option maxRecDepth 100000

theorem hD : (0:ℝ) < 15 := by norm_num

theorem TGT_pos : 0 < ef 0 0 12 0 (147/8) (21/8) := by unfold ef; norm_num
noncomputable def TGT : Erdos634.Geometry.Tri := rtri 15 hD 0 0 12 0 (147/8) (21/8) TGT_pos
theorem MODEL_pos : 0 < ef 0 0 2 0 (11/4) (3/4) := by unfold ef; norm_num
noncomputable def MODEL : Erdos634.Geometry.Tri := rtri 15 hD 0 0 2 0 (11/4) (3/4) MODEL_pos
theorem MODEL_sides : dist (MODEL.pts 0) (MODEL.pts 1) = 2 ∧ dist (MODEL.pts 1) (MODEL.pts 2) = 3 ∧
    dist (MODEL.pts 0) (MODEL.pts 2) = 4 :=
  model_sides_rp hD MODEL_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem TGT_sides : dist (TGT.pts 0) (TGT.pts 1) = 12 ∧ dist (TGT.pts 1) (TGT.pts 2) = 12 ∧
    dist (TGT.pts 0) (TGT.pts 2) = 21 :=
  model_sides_rp hD TGT_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem wBase : sixInstS21.baseY = true := by decide +kernel
theorem tgt_ok : sixInstS21.tgt.ok = true := by decide +kernel

theorem tgt_carr : sixInstS21.tgt.carr 15 = TGT.carrier := by
  obtain ⟨hp, h⟩ := Tri.ok_sem 15 hD sixInstS21.tgt tgt_ok
  rw [h]
  have e1 : sixInstS21.tgt.a.X = 0 := by simp [sixInstS21, pt, Pt.X]
  have e2 : sixInstS21.tgt.a.Y = 0 := by simp [sixInstS21, pt, Pt.Y]
  have e3 : sixInstS21.tgt.b.X = 12 := by simp [sixInstS21, pt, Pt.X]
  have e4 : sixInstS21.tgt.b.Y = 0 := by simp [sixInstS21, pt, Pt.Y]
  have e5 : sixInstS21.tgt.c.X = (147/8) := by simp [sixInstS21, pt, Pt.X]
  have e6 : sixInstS21.tgt.c.Y = (21/8) := by simp [sixInstS21, pt, Pt.Y]
  unfold TGT
  simp only [e1, e2, e3, e4, e5, e6]

theorem hMa' : dist (MODEL.pts 0) (MODEL.pts 1) = (sixInstS21.sides.1 : ℝ) := by simpa [sixInstS21] using MODEL_sides.1
theorem hMb' : dist (MODEL.pts 1) (MODEL.pts 2) = (sixInstS21.sides.2.1 : ℝ) := by simpa [sixInstS21] using MODEL_sides.2.1
theorem hMc' : dist (MODEL.pts 0) (MODEL.pts 2) = (sixInstS21.sides.2.2 : ℝ) := by simpa [sixInstS21] using MODEL_sides.2.2

theorem sound_0 : Sound 15 sixInstS21 MODEL sixCfgS0 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS0 sixChunkS0
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk0 t ht) sixS21_chunk0

theorem sound_1 : Sound 15 sixInstS21 MODEL sixCfgS1 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS1 sixChunkS1
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk1 t ht) sixS21_chunk1

theorem sound_2 : Sound 15 sixInstS21 MODEL sixCfgS2 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS2 sixChunkS2
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk2 t ht) sixS21_chunk2

theorem sound_3 : Sound 15 sixInstS21 MODEL sixCfgS3 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS3 sixChunkS3
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk3 t ht) sixS21_chunk3

theorem sound_4 : Sound 15 sixInstS21 MODEL sixCfgS4 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS4 sixChunkS4
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk4 t ht) sixS21_chunk4

theorem sound_5 : Sound 15 sixInstS21 MODEL sixCfgS5 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS5 sixChunkS5
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk5 t ht) sixS21_chunk5

theorem sound_6 : Sound 15 sixInstS21 MODEL sixCfgS6 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS6 sixChunkS6
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk6 t ht) sixS21_chunk6

theorem sound_7 : Sound 15 sixInstS21 MODEL sixCfgS7 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS7 sixChunkS7
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk7 t ht) sixS21_chunk7

theorem sound_8 : Sound 15 sixInstS21 MODEL sixCfgS8 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS8 sixChunkS8
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk8 t ht) sixS21_chunk8

theorem sound_9 : Sound 15 sixInstS21 MODEL sixCfgS9 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS9 sixChunkS9
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk9 t ht) sixS21_chunk9

theorem sound_10 : Sound 15 sixInstS21 MODEL sixCfgS10 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS10 sixChunkS10
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk10 t ht) sixS21_chunk10

theorem sound_11 : Sound 15 sixInstS21 MODEL sixCfgS11 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS11 sixChunkS11
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk11 t ht) sixS21_chunk11

theorem sound_12 : Sound 15 sixInstS21 MODEL sixCfgS12 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS12 sixChunkS12
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk12 t ht) sixS21_chunk12

theorem sound_13 : Sound 15 sixInstS21 MODEL sixCfgS13 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS13 sixChunkS13
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk13 t ht) sixS21_chunk13

theorem sound_14 : Sound 15 sixInstS21 MODEL sixCfgS14 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS14 sixChunkS14
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk14 t ht) sixS21_chunk14

theorem sound_15 : Sound 15 sixInstS21 MODEL sixCfgS15 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS15 sixChunkS15
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk15 t ht) sixS21_chunk15

theorem sound_16 : Sound 15 sixInstS21 MODEL sixCfgS16 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS16 sixChunkS16
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk16 t ht) sixS21_chunk16

theorem sound_17 : Sound 15 sixInstS21 MODEL sixCfgS17 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS17 sixChunkS17
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk17 t ht) sixS21_chunk17

theorem sound_18 : Sound 15 sixInstS21 MODEL sixCfgS18 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS18 sixChunkS18
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk18 t ht) sixS21_chunk18

theorem sound_19 : Sound 15 sixInstS21 MODEL sixCfgS19 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS19 sixChunkS19
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk19 t ht) sixS21_chunk19

theorem sound_20 : Sound 15 sixInstS21 MODEL sixCfgS20 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS20 sixChunkS20
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk20 t ht) sixS21_chunk20

theorem sound_21 : Sound 15 sixInstS21 MODEL sixCfgS21 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS21 sixChunkS21
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk21 t ht) sixS21_chunk21

theorem sound_22 : Sound 15 sixInstS21 MODEL sixCfgS22 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS22 sixChunkS22
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk22 t ht) sixS21_chunk22

theorem sound_23 : Sound 15 sixInstS21 MODEL sixCfgS23 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS23 sixChunkS23
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk23 t ht) sixS21_chunk23

theorem sound_24 : Sound 15 sixInstS21 MODEL sixCfgS24 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS24 sixChunkS24
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk24 t ht) sixS21_chunk24

theorem sound_25 : Sound 15 sixInstS21 MODEL sixCfgS25 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS25 sixChunkS25
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk25 t ht) sixS21_chunk25

theorem sound_26 : Sound 15 sixInstS21 MODEL sixCfgS26 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS26 sixChunkS26
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk26 t ht) sixS21_chunk26

theorem sound_27 : Sound 15 sixInstS21 MODEL sixCfgS27 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS27 sixChunkS27
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk27 t ht) sixS21_chunk27

theorem sound_28 : Sound 15 sixInstS21 MODEL sixCfgS28 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS28 sixChunkS28
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk28 t ht) sixS21_chunk28

theorem sound_29 : Sound 15 sixInstS21 MODEL sixCfgS29 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS29 sixChunkS29
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk29 t ht) sixS21_chunk29

theorem sound_30 : Sound 15 sixInstS21 MODEL sixCfgS30 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS30 sixChunkS30
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk30 t ht) sixS21_chunk30

theorem sound_31 : Sound 15 sixInstS21 MODEL sixCfgS31 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS31 sixChunkS31
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk31 t ht) sixS21_chunk31

theorem sound_32 : Sound 15 sixInstS21 MODEL sixCfgS32 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS32 sixChunkS32
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk32 t ht) sixS21_chunk32

theorem sound_33 : Sound 15 sixInstS21 MODEL sixCfgS33 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS33 sixChunkS33
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk33 t ht) sixS21_chunk33

theorem sound_34 : Sound 15 sixInstS21 MODEL sixCfgS34 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS34 sixChunkS34
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk34 t ht) sixS21_chunk34

theorem sound_35 : Sound 15 sixInstS21 MODEL sixCfgS35 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS35 sixChunkS35
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk35 t ht) sixS21_chunk35

theorem sound_36 : Sound 15 sixInstS21 MODEL sixCfgS36 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS36 sixChunkS36
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk36 t ht) sixS21_chunk36

theorem sound_37 : Sound 15 sixInstS21 MODEL sixCfgS37 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS37 sixChunkS37
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk37 t ht) sixS21_chunk37

theorem sound_38 : Sound 15 sixInstS21 MODEL sixCfgS38 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS38 sixChunkS38
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk38 t ht) sixS21_chunk38

theorem sound_39 : Sound 15 sixInstS21 MODEL sixCfgS39 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS39 sixChunkS39
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk39 t ht) sixS21_chunk39

theorem sound_40 : Sound 15 sixInstS21 MODEL sixCfgS40 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS40 sixChunkS40
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk40 t ht) sixS21_chunk40

theorem sound_41 : Sound 15 sixInstS21 MODEL sixCfgS41 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS41 sixChunkS41
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk41 t ht) sixS21_chunk41

theorem sound_42 : Sound 15 sixInstS21 MODEL sixCfgS42 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS42 sixChunkS42
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk42 t ht) sixS21_chunk42

theorem sound_43 : Sound 15 sixInstS21 MODEL sixCfgS43 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS43 sixChunkS43
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk43 t ht) sixS21_chunk43

theorem sound_44 : Sound 15 sixInstS21 MODEL sixCfgS44 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS44 sixChunkS44
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk44 t ht) sixS21_chunk44

theorem sound_45 : Sound 15 sixInstS21 MODEL sixCfgS45 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS45 sixChunkS45
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk45 t ht) sixS21_chunk45

theorem sound_46 : Sound 15 sixInstS21 MODEL sixCfgS46 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS46 sixChunkS46
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk46 t ht) sixS21_chunk46

theorem sound_47 : Sound 15 sixInstS21 MODEL sixCfgS47 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS47 sixChunkS47
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk47 t ht) sixS21_chunk47

theorem sound_48 : Sound 15 sixInstS21 MODEL sixCfgS48 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS48 sixChunkS48
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk48 t ht) sixS21_chunk48

theorem sound_49 : Sound 15 sixInstS21 MODEL sixCfgS49 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS49 sixChunkS49
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk49 t ht) sixS21_chunk49

theorem sound_50 : Sound 15 sixInstS21 MODEL sixCfgS50 :=
  checkNodeE_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL hMa' hMb' hMc' sixS21_ok wBase 400 sixCfgS50 sixChunkS50
    (fun t ht => List.all_eq_true.mp sixS21_cfgOk50 t ht) sixS21_chunk50

theorem known_sound : ∀ c ∈ sixKnownS21, Sound 15 sixInstS21 MODEL c := by
  intro c hc
  simp only [sixKnownS21, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_0
  · exact sound_1
  · exact sound_2
  · exact sound_3
  · exact sound_4
  · exact sound_5
  · exact sound_6
  · exact sound_7
  · exact sound_8
  · exact sound_9
  · exact sound_10
  · exact sound_11
  · exact sound_12
  · exact sound_13
  · exact sound_14
  · exact sound_15
  · exact sound_16
  · exact sound_17
  · exact sound_18
  · exact sound_19
  · exact sound_20
  · exact sound_21
  · exact sound_22
  · exact sound_23
  · exact sound_24
  · exact sound_25
  · exact sound_26
  · exact sound_27
  · exact sound_28
  · exact sound_29
  · exact sound_30
  · exact sound_31
  · exact sound_32
  · exact sound_33
  · exact sound_34
  · exact sound_35
  · exact sound_36
  · exact sound_37
  · exact sound_38
  · exact sound_39
  · exact sound_40
  · exact sound_41
  · exact sound_42
  · exact sound_43
  · exact sound_44
  · exact sound_45
  · exact sound_46
  · exact sound_47
  · exact sound_48
  · exact sound_49
  · exact sound_50

theorem not_dissection_refl {N : ℕ} (D : CongruentDissection N)
    (hT : D.target.Congruent TGT) (hM : D.model.Congruent MODEL) : False := by
  obtain ⟨g, D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hT
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have S : Sound 15 sixInstS21 MODEL [] := checkAllR_sound 15 hD sixInstS21 (by norm_num [sixInstS21]) MODEL
    (by simpa [sixInstS21] using hMa) (by simpa [sixInstS21] using hMb) (by simpa [sixInstS21] using hMc)
    wBase sixKnownS21 known_sound 400 sixTreeS21 sixS21_top
  exact S (N := N) D' (by rw [hD'T, tgt_carr]) (by rw [hD'M]; exact hM) (by simp)

theorem TGT_opp0 : TGT.oppLen 0 = 12 := by unfold Tri.oppLen; exact TGT_sides.2.1
theorem TGT_opp1 : TGT.oppLen 1 = 21 := by unfold Tri.oppLen; rw [dist_comm]; exact TGT_sides.2.2
theorem TGT_opp2 : TGT.oppLen 2 = 12 := by unfold Tri.oppLen; exact TGT_sides.1
theorem MODEL_opp0 : MODEL.oppLen 0 = 3 := by unfold Tri.oppLen; exact MODEL_sides.2.1
theorem MODEL_opp1 : MODEL.oppLen 1 = 4 := by unfold Tri.oppLen; rw [dist_comm]; exact MODEL_sides.2.2
theorem MODEL_opp2 : MODEL.oppLen 2 = 2 := by unfold Tri.oppLen; exact MODEL_sides.1

/-- **No dissection**: target opposite-side lengths `12 , 12 , 21` (read through `σt`) and model opposite-side lengths
`2 , 3 , 4` (read through `σm`).  -/
theorem not_dissection_sides {N : ℕ} (D : CongruentDissection N) (σt σm : Equiv.Perm (Fin 3))
    (h0 : D.target.oppLen (σt 0) = 12) (h1 : D.target.oppLen (σt 1) = 12) (h2 : D.target.oppLen (σt 2) = 21)
    (m0 : D.model.oppLen (σm 0) = 2) (m1 : D.model.oppLen (σm 1) = 3) (m2 : D.model.oppLen (σm 2) = 4) :
    False := by
  have s0 : (Equiv.swap (1:Fin 3) 2) 0 = 0 := by decide
  have s1 : (Equiv.swap (1:Fin 3) 2) 1 = 2 := by decide
  have s2 : (Equiv.swap (1:Fin 3) 2) 2 = 1 := by decide
  have r0 : (finRotate 3).symm (0:Fin 3) = 2 := by decide
  have r1 : (finRotate 3).symm (1:Fin 3) = 0 := by decide
  have r2 : (finRotate 3).symm (2:Fin 3) = 1 := by decide
  refine not_dissection_refl D ?_ ?_
  · refine Erdos634.Geometry.SIX.cong_of_oppLens_sigma _ _ σt (Equiv.swap 1 2) (fun j => ?_)
    fin_cases j
    · show D.target.oppLen (σt 0) = TGT.oppLen ((Equiv.swap (1:Fin 3) 2) 0)
      rw [s0, h0, TGT_opp0]
    · show D.target.oppLen (σt 1) = TGT.oppLen ((Equiv.swap (1:Fin 3) 2) 1)
      rw [s1, h1, TGT_opp2]
    · show D.target.oppLen (σt 2) = TGT.oppLen ((Equiv.swap (1:Fin 3) 2) 2)
      rw [s2, h2, TGT_opp1]
  · refine Erdos634.Geometry.SIX.cong_of_oppLens_sigma _ _ σm ((finRotate 3).symm) (fun j => ?_)
    fin_cases j
    · show D.model.oppLen (σm 0) = MODEL.oppLen ((finRotate 3).symm 0)
      rw [r0, m0, MODEL_opp2]
    · show D.model.oppLen (σm 1) = MODEL.oppLen ((finRotate 3).symm 1)
      rw [r1, m1, MODEL_opp0]
    · show D.model.oppLen (σm 2) = MODEL.oppLen ((finRotate 3).symm 2)
      rw [r2, m2, MODEL_opp1]

end Refl.SIXBridgeS21
#print axioms Refl.SIXBridgeS21.not_dissection_sides
