import Erdos634.Draft.SIXRunI33
import Erdos634.Refl.SoundE4
import Erdos634.NormalPosition
import Erdos634.Draft.SIXCong

/-! Draft/SIXBridgeI33.lean.  `Refl.checkAllR_sound` on the chunked `SIXDataI33` certificate.  Result `not_dissection_sides`: no `CongruentDissection` (any `N`)
    whose target has opposite sides (21,21,33) and whose model has the sides (5,3,7) in some order.  The coordinates are over Q(sqrt 3),
    Dn = 3 (angle 2pi/3 tile). -/

open Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord

namespace Refl.SIXBridgeI33

set_option maxRecDepth 100000

theorem hD : (0:ℝ) < 3 := by norm_num

theorem TGT_pos : 0 < ef 0 0 (39/2) (9/2) (33/2) (33/2) := by unfold ef; norm_num
noncomputable def TGT : Erdos634.Geometry.Tri := rtri 3 hD 0 0 (39/2) (9/2) (33/2) (33/2) TGT_pos
theorem MODEL_pos : 0 < ef 0 0 5 0 (13/2) (3/2) := by unfold ef; norm_num
noncomputable def MODEL : Erdos634.Geometry.Tri := rtri 3 hD 0 0 5 0 (13/2) (3/2) MODEL_pos
theorem MODEL_sides : dist (MODEL.pts 0) (MODEL.pts 1) = 5 ∧ dist (MODEL.pts 1) (MODEL.pts 2) = 3 ∧
    dist (MODEL.pts 0) (MODEL.pts 2) = 7 :=
  model_sides_rp hD MODEL_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem TGT_sides : dist (TGT.pts 0) (TGT.pts 1) = 21 ∧ dist (TGT.pts 1) (TGT.pts 2) = 21 ∧
    dist (TGT.pts 0) (TGT.pts 2) = 33 :=
  model_sides_rp hD TGT_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem wBase : sixInstI33.baseY = true := by decide +kernel
theorem tgt_ok : sixInstI33.tgt.ok = true := by decide +kernel

theorem tgt_carr : sixInstI33.tgt.carr 3 = TGT.carrier := by
  obtain ⟨hp, h⟩ := Tri.ok_sem 3 hD sixInstI33.tgt tgt_ok
  rw [h]
  have e1 : sixInstI33.tgt.a.X = 0 := by simp [sixInstI33, pt, Pt.X]
  have e2 : sixInstI33.tgt.a.Y = 0 := by simp [sixInstI33, pt, Pt.Y]
  have e3 : sixInstI33.tgt.b.X = (39/2) := by simp [sixInstI33, pt, Pt.X]
  have e4 : sixInstI33.tgt.b.Y = (9/2) := by simp [sixInstI33, pt, Pt.Y]
  have e5 : sixInstI33.tgt.c.X = (33/2) := by simp [sixInstI33, pt, Pt.X]
  have e6 : sixInstI33.tgt.c.Y = (33/2) := by simp [sixInstI33, pt, Pt.Y]
  unfold TGT
  simp only [e1, e2, e3, e4, e5, e6]

theorem hMa' : dist (MODEL.pts 0) (MODEL.pts 1) = (sixInstI33.sides.1 : ℝ) := by simpa [sixInstI33] using MODEL_sides.1
theorem hMb' : dist (MODEL.pts 1) (MODEL.pts 2) = (sixInstI33.sides.2.1 : ℝ) := by simpa [sixInstI33] using MODEL_sides.2.1
theorem hMc' : dist (MODEL.pts 0) (MODEL.pts 2) = (sixInstI33.sides.2.2 : ℝ) := by simpa [sixInstI33] using MODEL_sides.2.2

theorem sound_0 : Sound 3 sixInstI33 MODEL sixCfgI0 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI0 sixChunkI0
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk0 t ht) sixI33_chunk0

theorem sound_1 : Sound 3 sixInstI33 MODEL sixCfgI1 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI1 sixChunkI1
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk1 t ht) sixI33_chunk1

theorem sound_2 : Sound 3 sixInstI33 MODEL sixCfgI2 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI2 sixChunkI2
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk2 t ht) sixI33_chunk2

theorem sound_3 : Sound 3 sixInstI33 MODEL sixCfgI3 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI3 sixChunkI3
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk3 t ht) sixI33_chunk3

theorem sound_4 : Sound 3 sixInstI33 MODEL sixCfgI4 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI4 sixChunkI4
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk4 t ht) sixI33_chunk4

theorem sound_5 : Sound 3 sixInstI33 MODEL sixCfgI5 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI5 sixChunkI5
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk5 t ht) sixI33_chunk5

theorem sound_6 : Sound 3 sixInstI33 MODEL sixCfgI6 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI6 sixChunkI6
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk6 t ht) sixI33_chunk6

theorem sound_7 : Sound 3 sixInstI33 MODEL sixCfgI7 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI7 sixChunkI7
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk7 t ht) sixI33_chunk7

theorem sound_8 : Sound 3 sixInstI33 MODEL sixCfgI8 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI8 sixChunkI8
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk8 t ht) sixI33_chunk8

theorem sound_9 : Sound 3 sixInstI33 MODEL sixCfgI9 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI9 sixChunkI9
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk9 t ht) sixI33_chunk9

theorem sound_10 : Sound 3 sixInstI33 MODEL sixCfgI10 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI10 sixChunkI10
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk10 t ht) sixI33_chunk10

theorem sound_11 : Sound 3 sixInstI33 MODEL sixCfgI11 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI11 sixChunkI11
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk11 t ht) sixI33_chunk11

theorem sound_12 : Sound 3 sixInstI33 MODEL sixCfgI12 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI12 sixChunkI12
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk12 t ht) sixI33_chunk12

theorem sound_13 : Sound 3 sixInstI33 MODEL sixCfgI13 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI13 sixChunkI13
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk13 t ht) sixI33_chunk13

theorem sound_14 : Sound 3 sixInstI33 MODEL sixCfgI14 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI14 sixChunkI14
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk14 t ht) sixI33_chunk14

theorem sound_15 : Sound 3 sixInstI33 MODEL sixCfgI15 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI15 sixChunkI15
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk15 t ht) sixI33_chunk15

theorem sound_16 : Sound 3 sixInstI33 MODEL sixCfgI16 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI16 sixChunkI16
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk16 t ht) sixI33_chunk16

theorem sound_17 : Sound 3 sixInstI33 MODEL sixCfgI17 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI17 sixChunkI17
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk17 t ht) sixI33_chunk17

theorem sound_18 : Sound 3 sixInstI33 MODEL sixCfgI18 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI18 sixChunkI18
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk18 t ht) sixI33_chunk18

theorem sound_19 : Sound 3 sixInstI33 MODEL sixCfgI19 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI19 sixChunkI19
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk19 t ht) sixI33_chunk19

theorem sound_20 : Sound 3 sixInstI33 MODEL sixCfgI20 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI20 sixChunkI20
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk20 t ht) sixI33_chunk20

theorem sound_21 : Sound 3 sixInstI33 MODEL sixCfgI21 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI21 sixChunkI21
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk21 t ht) sixI33_chunk21

theorem sound_22 : Sound 3 sixInstI33 MODEL sixCfgI22 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI22 sixChunkI22
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk22 t ht) sixI33_chunk22

theorem sound_23 : Sound 3 sixInstI33 MODEL sixCfgI23 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI23 sixChunkI23
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk23 t ht) sixI33_chunk23

theorem sound_24 : Sound 3 sixInstI33 MODEL sixCfgI24 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI24 sixChunkI24
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk24 t ht) sixI33_chunk24

theorem sound_25 : Sound 3 sixInstI33 MODEL sixCfgI25 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI25 sixChunkI25
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk25 t ht) sixI33_chunk25

theorem sound_26 : Sound 3 sixInstI33 MODEL sixCfgI26 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI26 sixChunkI26
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk26 t ht) sixI33_chunk26

theorem sound_27 : Sound 3 sixInstI33 MODEL sixCfgI27 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI27 sixChunkI27
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk27 t ht) sixI33_chunk27

theorem sound_28 : Sound 3 sixInstI33 MODEL sixCfgI28 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI28 sixChunkI28
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk28 t ht) sixI33_chunk28

theorem sound_29 : Sound 3 sixInstI33 MODEL sixCfgI29 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI29 sixChunkI29
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk29 t ht) sixI33_chunk29

theorem sound_30 : Sound 3 sixInstI33 MODEL sixCfgI30 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI30 sixChunkI30
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk30 t ht) sixI33_chunk30

theorem sound_31 : Sound 3 sixInstI33 MODEL sixCfgI31 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI31 sixChunkI31
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk31 t ht) sixI33_chunk31

theorem sound_32 : Sound 3 sixInstI33 MODEL sixCfgI32 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI32 sixChunkI32
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk32 t ht) sixI33_chunk32

theorem sound_33 : Sound 3 sixInstI33 MODEL sixCfgI33 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI33 sixChunkI33
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk33 t ht) sixI33_chunk33

theorem sound_34 : Sound 3 sixInstI33 MODEL sixCfgI34 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI34 sixChunkI34
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk34 t ht) sixI33_chunk34

theorem sound_35 : Sound 3 sixInstI33 MODEL sixCfgI35 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI35 sixChunkI35
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk35 t ht) sixI33_chunk35

theorem sound_36 : Sound 3 sixInstI33 MODEL sixCfgI36 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI36 sixChunkI36
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk36 t ht) sixI33_chunk36

theorem sound_37 : Sound 3 sixInstI33 MODEL sixCfgI37 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI37 sixChunkI37
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk37 t ht) sixI33_chunk37

theorem sound_38 : Sound 3 sixInstI33 MODEL sixCfgI38 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI38 sixChunkI38
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk38 t ht) sixI33_chunk38

theorem sound_39 : Sound 3 sixInstI33 MODEL sixCfgI39 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI39 sixChunkI39
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk39 t ht) sixI33_chunk39

theorem sound_40 : Sound 3 sixInstI33 MODEL sixCfgI40 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI40 sixChunkI40
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk40 t ht) sixI33_chunk40

theorem sound_41 : Sound 3 sixInstI33 MODEL sixCfgI41 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI41 sixChunkI41
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk41 t ht) sixI33_chunk41

theorem sound_42 : Sound 3 sixInstI33 MODEL sixCfgI42 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI42 sixChunkI42
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk42 t ht) sixI33_chunk42

theorem sound_43 : Sound 3 sixInstI33 MODEL sixCfgI43 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI43 sixChunkI43
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk43 t ht) sixI33_chunk43

theorem sound_44 : Sound 3 sixInstI33 MODEL sixCfgI44 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI44 sixChunkI44
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk44 t ht) sixI33_chunk44

theorem sound_45 : Sound 3 sixInstI33 MODEL sixCfgI45 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI45 sixChunkI45
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk45 t ht) sixI33_chunk45

theorem sound_46 : Sound 3 sixInstI33 MODEL sixCfgI46 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI46 sixChunkI46
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk46 t ht) sixI33_chunk46

theorem sound_47 : Sound 3 sixInstI33 MODEL sixCfgI47 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI47 sixChunkI47
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk47 t ht) sixI33_chunk47

theorem sound_48 : Sound 3 sixInstI33 MODEL sixCfgI48 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI48 sixChunkI48
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk48 t ht) sixI33_chunk48

theorem sound_49 : Sound 3 sixInstI33 MODEL sixCfgI49 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI49 sixChunkI49
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk49 t ht) sixI33_chunk49

theorem sound_50 : Sound 3 sixInstI33 MODEL sixCfgI50 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI50 sixChunkI50
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk50 t ht) sixI33_chunk50

theorem sound_51 : Sound 3 sixInstI33 MODEL sixCfgI51 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI51 sixChunkI51
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk51 t ht) sixI33_chunk51

theorem sound_52 : Sound 3 sixInstI33 MODEL sixCfgI52 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI52 sixChunkI52
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk52 t ht) sixI33_chunk52

theorem sound_53 : Sound 3 sixInstI33 MODEL sixCfgI53 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI53 sixChunkI53
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk53 t ht) sixI33_chunk53

theorem sound_54 : Sound 3 sixInstI33 MODEL sixCfgI54 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI54 sixChunkI54
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk54 t ht) sixI33_chunk54

theorem sound_55 : Sound 3 sixInstI33 MODEL sixCfgI55 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI55 sixChunkI55
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk55 t ht) sixI33_chunk55

theorem sound_56 : Sound 3 sixInstI33 MODEL sixCfgI56 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI56 sixChunkI56
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk56 t ht) sixI33_chunk56

theorem sound_57 : Sound 3 sixInstI33 MODEL sixCfgI57 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI57 sixChunkI57
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk57 t ht) sixI33_chunk57

theorem sound_58 : Sound 3 sixInstI33 MODEL sixCfgI58 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI58 sixChunkI58
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk58 t ht) sixI33_chunk58

theorem sound_59 : Sound 3 sixInstI33 MODEL sixCfgI59 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI59 sixChunkI59
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk59 t ht) sixI33_chunk59

theorem sound_60 : Sound 3 sixInstI33 MODEL sixCfgI60 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI60 sixChunkI60
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk60 t ht) sixI33_chunk60

theorem sound_61 : Sound 3 sixInstI33 MODEL sixCfgI61 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI61 sixChunkI61
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk61 t ht) sixI33_chunk61

theorem sound_62 : Sound 3 sixInstI33 MODEL sixCfgI62 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI62 sixChunkI62
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk62 t ht) sixI33_chunk62

theorem sound_63 : Sound 3 sixInstI33 MODEL sixCfgI63 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI63 sixChunkI63
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk63 t ht) sixI33_chunk63

theorem sound_64 : Sound 3 sixInstI33 MODEL sixCfgI64 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI64 sixChunkI64
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk64 t ht) sixI33_chunk64

theorem sound_65 : Sound 3 sixInstI33 MODEL sixCfgI65 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI65 sixChunkI65
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk65 t ht) sixI33_chunk65

theorem sound_66 : Sound 3 sixInstI33 MODEL sixCfgI66 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI66 sixChunkI66
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk66 t ht) sixI33_chunk66

theorem sound_67 : Sound 3 sixInstI33 MODEL sixCfgI67 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI67 sixChunkI67
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk67 t ht) sixI33_chunk67

theorem sound_68 : Sound 3 sixInstI33 MODEL sixCfgI68 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI68 sixChunkI68
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk68 t ht) sixI33_chunk68

theorem sound_69 : Sound 3 sixInstI33 MODEL sixCfgI69 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI69 sixChunkI69
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk69 t ht) sixI33_chunk69

theorem sound_70 : Sound 3 sixInstI33 MODEL sixCfgI70 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI70 sixChunkI70
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk70 t ht) sixI33_chunk70

theorem sound_71 : Sound 3 sixInstI33 MODEL sixCfgI71 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI71 sixChunkI71
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk71 t ht) sixI33_chunk71

theorem sound_72 : Sound 3 sixInstI33 MODEL sixCfgI72 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI72 sixChunkI72
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk72 t ht) sixI33_chunk72

theorem sound_73 : Sound 3 sixInstI33 MODEL sixCfgI73 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI73 sixChunkI73
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk73 t ht) sixI33_chunk73

theorem sound_74 : Sound 3 sixInstI33 MODEL sixCfgI74 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI74 sixChunkI74
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk74 t ht) sixI33_chunk74

theorem sound_75 : Sound 3 sixInstI33 MODEL sixCfgI75 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI75 sixChunkI75
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk75 t ht) sixI33_chunk75

theorem sound_76 : Sound 3 sixInstI33 MODEL sixCfgI76 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI76 sixChunkI76
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk76 t ht) sixI33_chunk76

theorem sound_77 : Sound 3 sixInstI33 MODEL sixCfgI77 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI77 sixChunkI77
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk77 t ht) sixI33_chunk77

theorem sound_78 : Sound 3 sixInstI33 MODEL sixCfgI78 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI78 sixChunkI78
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk78 t ht) sixI33_chunk78

theorem sound_79 : Sound 3 sixInstI33 MODEL sixCfgI79 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI79 sixChunkI79
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk79 t ht) sixI33_chunk79

theorem sound_80 : Sound 3 sixInstI33 MODEL sixCfgI80 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI80 sixChunkI80
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk80 t ht) sixI33_chunk80

theorem sound_81 : Sound 3 sixInstI33 MODEL sixCfgI81 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI81 sixChunkI81
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk81 t ht) sixI33_chunk81

theorem sound_82 : Sound 3 sixInstI33 MODEL sixCfgI82 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI82 sixChunkI82
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk82 t ht) sixI33_chunk82

theorem sound_83 : Sound 3 sixInstI33 MODEL sixCfgI83 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI83 sixChunkI83
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk83 t ht) sixI33_chunk83

theorem sound_84 : Sound 3 sixInstI33 MODEL sixCfgI84 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI84 sixChunkI84
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk84 t ht) sixI33_chunk84

theorem sound_85 : Sound 3 sixInstI33 MODEL sixCfgI85 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI85 sixChunkI85
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk85 t ht) sixI33_chunk85

theorem sound_86 : Sound 3 sixInstI33 MODEL sixCfgI86 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI86 sixChunkI86
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk86 t ht) sixI33_chunk86

theorem sound_87 : Sound 3 sixInstI33 MODEL sixCfgI87 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI87 sixChunkI87
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk87 t ht) sixI33_chunk87

theorem sound_88 : Sound 3 sixInstI33 MODEL sixCfgI88 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI88 sixChunkI88
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk88 t ht) sixI33_chunk88

theorem sound_89 : Sound 3 sixInstI33 MODEL sixCfgI89 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI89 sixChunkI89
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk89 t ht) sixI33_chunk89

theorem sound_90 : Sound 3 sixInstI33 MODEL sixCfgI90 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI90 sixChunkI90
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk90 t ht) sixI33_chunk90

theorem sound_91 : Sound 3 sixInstI33 MODEL sixCfgI91 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI91 sixChunkI91
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk91 t ht) sixI33_chunk91

theorem sound_92 : Sound 3 sixInstI33 MODEL sixCfgI92 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI92 sixChunkI92
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk92 t ht) sixI33_chunk92

theorem sound_93 : Sound 3 sixInstI33 MODEL sixCfgI93 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI93 sixChunkI93
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk93 t ht) sixI33_chunk93

theorem sound_94 : Sound 3 sixInstI33 MODEL sixCfgI94 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI94 sixChunkI94
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk94 t ht) sixI33_chunk94

theorem sound_95 : Sound 3 sixInstI33 MODEL sixCfgI95 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI95 sixChunkI95
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk95 t ht) sixI33_chunk95

theorem sound_96 : Sound 3 sixInstI33 MODEL sixCfgI96 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI96 sixChunkI96
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk96 t ht) sixI33_chunk96

theorem sound_97 : Sound 3 sixInstI33 MODEL sixCfgI97 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI97 sixChunkI97
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk97 t ht) sixI33_chunk97

theorem sound_98 : Sound 3 sixInstI33 MODEL sixCfgI98 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI98 sixChunkI98
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk98 t ht) sixI33_chunk98

theorem sound_99 : Sound 3 sixInstI33 MODEL sixCfgI99 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI99 sixChunkI99
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk99 t ht) sixI33_chunk99

theorem sound_100 : Sound 3 sixInstI33 MODEL sixCfgI100 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI100 sixChunkI100
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk100 t ht) sixI33_chunk100

theorem sound_101 : Sound 3 sixInstI33 MODEL sixCfgI101 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI101 sixChunkI101
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk101 t ht) sixI33_chunk101

theorem sound_102 : Sound 3 sixInstI33 MODEL sixCfgI102 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI102 sixChunkI102
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk102 t ht) sixI33_chunk102

theorem sound_103 : Sound 3 sixInstI33 MODEL sixCfgI103 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI103 sixChunkI103
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk103 t ht) sixI33_chunk103

theorem sound_104 : Sound 3 sixInstI33 MODEL sixCfgI104 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI104 sixChunkI104
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk104 t ht) sixI33_chunk104

theorem sound_105 : Sound 3 sixInstI33 MODEL sixCfgI105 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI105 sixChunkI105
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk105 t ht) sixI33_chunk105

theorem sound_106 : Sound 3 sixInstI33 MODEL sixCfgI106 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI106 sixChunkI106
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk106 t ht) sixI33_chunk106

theorem sound_107 : Sound 3 sixInstI33 MODEL sixCfgI107 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI107 sixChunkI107
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk107 t ht) sixI33_chunk107

theorem sound_108 : Sound 3 sixInstI33 MODEL sixCfgI108 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI108 sixChunkI108
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk108 t ht) sixI33_chunk108

theorem sound_109 : Sound 3 sixInstI33 MODEL sixCfgI109 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI109 sixChunkI109
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk109 t ht) sixI33_chunk109

theorem sound_110 : Sound 3 sixInstI33 MODEL sixCfgI110 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI110 sixChunkI110
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk110 t ht) sixI33_chunk110

theorem sound_111 : Sound 3 sixInstI33 MODEL sixCfgI111 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI111 sixChunkI111
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk111 t ht) sixI33_chunk111

theorem sound_112 : Sound 3 sixInstI33 MODEL sixCfgI112 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI112 sixChunkI112
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk112 t ht) sixI33_chunk112

theorem sound_113 : Sound 3 sixInstI33 MODEL sixCfgI113 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI113 sixChunkI113
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk113 t ht) sixI33_chunk113

theorem sound_114 : Sound 3 sixInstI33 MODEL sixCfgI114 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI114 sixChunkI114
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk114 t ht) sixI33_chunk114

theorem sound_115 : Sound 3 sixInstI33 MODEL sixCfgI115 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI115 sixChunkI115
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk115 t ht) sixI33_chunk115

theorem sound_116 : Sound 3 sixInstI33 MODEL sixCfgI116 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI116 sixChunkI116
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk116 t ht) sixI33_chunk116

theorem sound_117 : Sound 3 sixInstI33 MODEL sixCfgI117 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI117 sixChunkI117
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk117 t ht) sixI33_chunk117

theorem sound_118 : Sound 3 sixInstI33 MODEL sixCfgI118 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI118 sixChunkI118
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk118 t ht) sixI33_chunk118

theorem sound_119 : Sound 3 sixInstI33 MODEL sixCfgI119 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI119 sixChunkI119
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk119 t ht) sixI33_chunk119

theorem sound_120 : Sound 3 sixInstI33 MODEL sixCfgI120 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI120 sixChunkI120
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk120 t ht) sixI33_chunk120

theorem sound_121 : Sound 3 sixInstI33 MODEL sixCfgI121 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI121 sixChunkI121
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk121 t ht) sixI33_chunk121

theorem sound_122 : Sound 3 sixInstI33 MODEL sixCfgI122 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI122 sixChunkI122
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk122 t ht) sixI33_chunk122

theorem sound_123 : Sound 3 sixInstI33 MODEL sixCfgI123 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI123 sixChunkI123
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk123 t ht) sixI33_chunk123

theorem sound_124 : Sound 3 sixInstI33 MODEL sixCfgI124 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI124 sixChunkI124
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk124 t ht) sixI33_chunk124

theorem sound_125 : Sound 3 sixInstI33 MODEL sixCfgI125 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI125 sixChunkI125
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk125 t ht) sixI33_chunk125

theorem sound_126 : Sound 3 sixInstI33 MODEL sixCfgI126 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI126 sixChunkI126
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk126 t ht) sixI33_chunk126

theorem sound_127 : Sound 3 sixInstI33 MODEL sixCfgI127 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI127 sixChunkI127
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk127 t ht) sixI33_chunk127

theorem sound_128 : Sound 3 sixInstI33 MODEL sixCfgI128 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI128 sixChunkI128
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk128 t ht) sixI33_chunk128

theorem sound_129 : Sound 3 sixInstI33 MODEL sixCfgI129 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI129 sixChunkI129
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk129 t ht) sixI33_chunk129

theorem sound_130 : Sound 3 sixInstI33 MODEL sixCfgI130 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI130 sixChunkI130
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk130 t ht) sixI33_chunk130

theorem sound_131 : Sound 3 sixInstI33 MODEL sixCfgI131 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI131 sixChunkI131
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk131 t ht) sixI33_chunk131

theorem sound_132 : Sound 3 sixInstI33 MODEL sixCfgI132 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI132 sixChunkI132
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk132 t ht) sixI33_chunk132

theorem sound_133 : Sound 3 sixInstI33 MODEL sixCfgI133 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI133 sixChunkI133
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk133 t ht) sixI33_chunk133

theorem sound_134 : Sound 3 sixInstI33 MODEL sixCfgI134 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI134 sixChunkI134
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk134 t ht) sixI33_chunk134

theorem sound_135 : Sound 3 sixInstI33 MODEL sixCfgI135 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI135 sixChunkI135
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk135 t ht) sixI33_chunk135

theorem sound_136 : Sound 3 sixInstI33 MODEL sixCfgI136 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI136 sixChunkI136
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk136 t ht) sixI33_chunk136

theorem sound_137 : Sound 3 sixInstI33 MODEL sixCfgI137 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI137 sixChunkI137
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk137 t ht) sixI33_chunk137

theorem sound_138 : Sound 3 sixInstI33 MODEL sixCfgI138 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI138 sixChunkI138
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk138 t ht) sixI33_chunk138

theorem sound_139 : Sound 3 sixInstI33 MODEL sixCfgI139 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI139 sixChunkI139
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk139 t ht) sixI33_chunk139

theorem sound_140 : Sound 3 sixInstI33 MODEL sixCfgI140 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI140 sixChunkI140
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk140 t ht) sixI33_chunk140

theorem sound_141 : Sound 3 sixInstI33 MODEL sixCfgI141 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI141 sixChunkI141
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk141 t ht) sixI33_chunk141

theorem sound_142 : Sound 3 sixInstI33 MODEL sixCfgI142 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI142 sixChunkI142
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk142 t ht) sixI33_chunk142

theorem sound_143 : Sound 3 sixInstI33 MODEL sixCfgI143 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI143 sixChunkI143
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk143 t ht) sixI33_chunk143

theorem sound_144 : Sound 3 sixInstI33 MODEL sixCfgI144 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI144 sixChunkI144
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk144 t ht) sixI33_chunk144

theorem sound_145 : Sound 3 sixInstI33 MODEL sixCfgI145 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI145 sixChunkI145
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk145 t ht) sixI33_chunk145

theorem sound_146 : Sound 3 sixInstI33 MODEL sixCfgI146 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI146 sixChunkI146
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk146 t ht) sixI33_chunk146

theorem sound_147 : Sound 3 sixInstI33 MODEL sixCfgI147 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI147 sixChunkI147
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk147 t ht) sixI33_chunk147

theorem sound_148 : Sound 3 sixInstI33 MODEL sixCfgI148 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI148 sixChunkI148
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk148 t ht) sixI33_chunk148

theorem sound_149 : Sound 3 sixInstI33 MODEL sixCfgI149 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI149 sixChunkI149
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk149 t ht) sixI33_chunk149

theorem sound_150 : Sound 3 sixInstI33 MODEL sixCfgI150 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI150 sixChunkI150
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk150 t ht) sixI33_chunk150

theorem sound_151 : Sound 3 sixInstI33 MODEL sixCfgI151 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI151 sixChunkI151
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk151 t ht) sixI33_chunk151

theorem sound_152 : Sound 3 sixInstI33 MODEL sixCfgI152 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI152 sixChunkI152
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk152 t ht) sixI33_chunk152

theorem sound_153 : Sound 3 sixInstI33 MODEL sixCfgI153 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI153 sixChunkI153
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk153 t ht) sixI33_chunk153

theorem sound_154 : Sound 3 sixInstI33 MODEL sixCfgI154 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI154 sixChunkI154
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk154 t ht) sixI33_chunk154

theorem sound_155 : Sound 3 sixInstI33 MODEL sixCfgI155 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI155 sixChunkI155
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk155 t ht) sixI33_chunk155

theorem sound_156 : Sound 3 sixInstI33 MODEL sixCfgI156 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI156 sixChunkI156
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk156 t ht) sixI33_chunk156

theorem sound_157 : Sound 3 sixInstI33 MODEL sixCfgI157 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI157 sixChunkI157
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk157 t ht) sixI33_chunk157

theorem sound_158 : Sound 3 sixInstI33 MODEL sixCfgI158 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI158 sixChunkI158
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk158 t ht) sixI33_chunk158

theorem sound_159 : Sound 3 sixInstI33 MODEL sixCfgI159 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI159 sixChunkI159
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk159 t ht) sixI33_chunk159

theorem sound_160 : Sound 3 sixInstI33 MODEL sixCfgI160 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI160 sixChunkI160
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk160 t ht) sixI33_chunk160

theorem sound_161 : Sound 3 sixInstI33 MODEL sixCfgI161 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI161 sixChunkI161
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk161 t ht) sixI33_chunk161

theorem sound_162 : Sound 3 sixInstI33 MODEL sixCfgI162 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI162 sixChunkI162
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk162 t ht) sixI33_chunk162

theorem sound_163 : Sound 3 sixInstI33 MODEL sixCfgI163 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI163 sixChunkI163
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk163 t ht) sixI33_chunk163

theorem sound_164 : Sound 3 sixInstI33 MODEL sixCfgI164 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI164 sixChunkI164
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk164 t ht) sixI33_chunk164

theorem sound_165 : Sound 3 sixInstI33 MODEL sixCfgI165 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI165 sixChunkI165
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk165 t ht) sixI33_chunk165

theorem sound_166 : Sound 3 sixInstI33 MODEL sixCfgI166 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI166 sixChunkI166
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk166 t ht) sixI33_chunk166

theorem sound_167 : Sound 3 sixInstI33 MODEL sixCfgI167 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI167 sixChunkI167
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk167 t ht) sixI33_chunk167

theorem sound_168 : Sound 3 sixInstI33 MODEL sixCfgI168 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI168 sixChunkI168
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk168 t ht) sixI33_chunk168

theorem sound_169 : Sound 3 sixInstI33 MODEL sixCfgI169 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI169 sixChunkI169
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk169 t ht) sixI33_chunk169

theorem sound_170 : Sound 3 sixInstI33 MODEL sixCfgI170 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI170 sixChunkI170
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk170 t ht) sixI33_chunk170

theorem sound_171 : Sound 3 sixInstI33 MODEL sixCfgI171 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI171 sixChunkI171
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk171 t ht) sixI33_chunk171

theorem sound_172 : Sound 3 sixInstI33 MODEL sixCfgI172 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI172 sixChunkI172
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk172 t ht) sixI33_chunk172

theorem sound_173 : Sound 3 sixInstI33 MODEL sixCfgI173 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI173 sixChunkI173
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk173 t ht) sixI33_chunk173

theorem sound_174 : Sound 3 sixInstI33 MODEL sixCfgI174 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI174 sixChunkI174
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk174 t ht) sixI33_chunk174

theorem sound_175 : Sound 3 sixInstI33 MODEL sixCfgI175 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI175 sixChunkI175
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk175 t ht) sixI33_chunk175

theorem sound_176 : Sound 3 sixInstI33 MODEL sixCfgI176 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI176 sixChunkI176
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk176 t ht) sixI33_chunk176

theorem sound_177 : Sound 3 sixInstI33 MODEL sixCfgI177 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI177 sixChunkI177
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk177 t ht) sixI33_chunk177

theorem sound_178 : Sound 3 sixInstI33 MODEL sixCfgI178 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI178 sixChunkI178
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk178 t ht) sixI33_chunk178

theorem sound_179 : Sound 3 sixInstI33 MODEL sixCfgI179 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI179 sixChunkI179
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk179 t ht) sixI33_chunk179

theorem sound_180 : Sound 3 sixInstI33 MODEL sixCfgI180 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI180 sixChunkI180
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk180 t ht) sixI33_chunk180

theorem sound_181 : Sound 3 sixInstI33 MODEL sixCfgI181 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI181 sixChunkI181
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk181 t ht) sixI33_chunk181

theorem sound_182 : Sound 3 sixInstI33 MODEL sixCfgI182 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI182 sixChunkI182
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk182 t ht) sixI33_chunk182

theorem sound_183 : Sound 3 sixInstI33 MODEL sixCfgI183 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI183 sixChunkI183
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk183 t ht) sixI33_chunk183

theorem sound_184 : Sound 3 sixInstI33 MODEL sixCfgI184 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI184 sixChunkI184
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk184 t ht) sixI33_chunk184

theorem sound_185 : Sound 3 sixInstI33 MODEL sixCfgI185 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI185 sixChunkI185
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk185 t ht) sixI33_chunk185

theorem sound_186 : Sound 3 sixInstI33 MODEL sixCfgI186 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI186 sixChunkI186
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk186 t ht) sixI33_chunk186

theorem sound_187 : Sound 3 sixInstI33 MODEL sixCfgI187 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI187 sixChunkI187
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk187 t ht) sixI33_chunk187

theorem sound_188 : Sound 3 sixInstI33 MODEL sixCfgI188 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI188 sixChunkI188
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk188 t ht) sixI33_chunk188

theorem sound_189 : Sound 3 sixInstI33 MODEL sixCfgI189 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI189 sixChunkI189
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk189 t ht) sixI33_chunk189

theorem sound_190 : Sound 3 sixInstI33 MODEL sixCfgI190 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI190 sixChunkI190
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk190 t ht) sixI33_chunk190

theorem sound_191 : Sound 3 sixInstI33 MODEL sixCfgI191 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI191 sixChunkI191
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk191 t ht) sixI33_chunk191

theorem sound_192 : Sound 3 sixInstI33 MODEL sixCfgI192 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI192 sixChunkI192
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk192 t ht) sixI33_chunk192

theorem sound_193 : Sound 3 sixInstI33 MODEL sixCfgI193 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI193 sixChunkI193
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk193 t ht) sixI33_chunk193

theorem sound_194 : Sound 3 sixInstI33 MODEL sixCfgI194 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI194 sixChunkI194
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk194 t ht) sixI33_chunk194

theorem sound_195 : Sound 3 sixInstI33 MODEL sixCfgI195 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI195 sixChunkI195
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk195 t ht) sixI33_chunk195

theorem sound_196 : Sound 3 sixInstI33 MODEL sixCfgI196 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI196 sixChunkI196
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk196 t ht) sixI33_chunk196

theorem sound_197 : Sound 3 sixInstI33 MODEL sixCfgI197 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI197 sixChunkI197
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk197 t ht) sixI33_chunk197

theorem sound_198 : Sound 3 sixInstI33 MODEL sixCfgI198 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI198 sixChunkI198
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk198 t ht) sixI33_chunk198

theorem sound_199 : Sound 3 sixInstI33 MODEL sixCfgI199 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI199 sixChunkI199
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk199 t ht) sixI33_chunk199

theorem sound_200 : Sound 3 sixInstI33 MODEL sixCfgI200 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI200 sixChunkI200
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk200 t ht) sixI33_chunk200

theorem sound_201 : Sound 3 sixInstI33 MODEL sixCfgI201 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI201 sixChunkI201
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk201 t ht) sixI33_chunk201

theorem sound_202 : Sound 3 sixInstI33 MODEL sixCfgI202 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI202 sixChunkI202
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk202 t ht) sixI33_chunk202

theorem sound_203 : Sound 3 sixInstI33 MODEL sixCfgI203 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI203 sixChunkI203
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk203 t ht) sixI33_chunk203

theorem sound_204 : Sound 3 sixInstI33 MODEL sixCfgI204 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI204 sixChunkI204
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk204 t ht) sixI33_chunk204

theorem sound_205 : Sound 3 sixInstI33 MODEL sixCfgI205 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI205 sixChunkI205
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk205 t ht) sixI33_chunk205

theorem sound_206 : Sound 3 sixInstI33 MODEL sixCfgI206 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI206 sixChunkI206
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk206 t ht) sixI33_chunk206

theorem sound_207 : Sound 3 sixInstI33 MODEL sixCfgI207 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI207 sixChunkI207
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk207 t ht) sixI33_chunk207

theorem sound_208 : Sound 3 sixInstI33 MODEL sixCfgI208 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI208 sixChunkI208
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk208 t ht) sixI33_chunk208

theorem sound_209 : Sound 3 sixInstI33 MODEL sixCfgI209 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI209 sixChunkI209
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk209 t ht) sixI33_chunk209

theorem sound_210 : Sound 3 sixInstI33 MODEL sixCfgI210 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI210 sixChunkI210
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk210 t ht) sixI33_chunk210

theorem sound_211 : Sound 3 sixInstI33 MODEL sixCfgI211 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI211 sixChunkI211
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk211 t ht) sixI33_chunk211

theorem sound_212 : Sound 3 sixInstI33 MODEL sixCfgI212 :=
  checkNodeE_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL hMa' hMb' hMc' sixI33_ok wBase 400 sixCfgI212 sixChunkI212
    (fun t ht => List.all_eq_true.mp sixI33_cfgOk212 t ht) sixI33_chunk212

theorem known_sound : ∀ c ∈ sixKnownI33, Sound 3 sixInstI33 MODEL c := by
  intro c hc
  simp only [sixKnownI33, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact sound_51
  · exact sound_52
  · exact sound_53
  · exact sound_54
  · exact sound_55
  · exact sound_56
  · exact sound_57
  · exact sound_58
  · exact sound_59
  · exact sound_60
  · exact sound_61
  · exact sound_62
  · exact sound_63
  · exact sound_64
  · exact sound_65
  · exact sound_66
  · exact sound_67
  · exact sound_68
  · exact sound_69
  · exact sound_70
  · exact sound_71
  · exact sound_72
  · exact sound_73
  · exact sound_74
  · exact sound_75
  · exact sound_76
  · exact sound_77
  · exact sound_78
  · exact sound_79
  · exact sound_80
  · exact sound_81
  · exact sound_82
  · exact sound_83
  · exact sound_84
  · exact sound_85
  · exact sound_86
  · exact sound_87
  · exact sound_88
  · exact sound_89
  · exact sound_90
  · exact sound_91
  · exact sound_92
  · exact sound_93
  · exact sound_94
  · exact sound_95
  · exact sound_96
  · exact sound_97
  · exact sound_98
  · exact sound_99
  · exact sound_100
  · exact sound_101
  · exact sound_102
  · exact sound_103
  · exact sound_104
  · exact sound_105
  · exact sound_106
  · exact sound_107
  · exact sound_108
  · exact sound_109
  · exact sound_110
  · exact sound_111
  · exact sound_112
  · exact sound_113
  · exact sound_114
  · exact sound_115
  · exact sound_116
  · exact sound_117
  · exact sound_118
  · exact sound_119
  · exact sound_120
  · exact sound_121
  · exact sound_122
  · exact sound_123
  · exact sound_124
  · exact sound_125
  · exact sound_126
  · exact sound_127
  · exact sound_128
  · exact sound_129
  · exact sound_130
  · exact sound_131
  · exact sound_132
  · exact sound_133
  · exact sound_134
  · exact sound_135
  · exact sound_136
  · exact sound_137
  · exact sound_138
  · exact sound_139
  · exact sound_140
  · exact sound_141
  · exact sound_142
  · exact sound_143
  · exact sound_144
  · exact sound_145
  · exact sound_146
  · exact sound_147
  · exact sound_148
  · exact sound_149
  · exact sound_150
  · exact sound_151
  · exact sound_152
  · exact sound_153
  · exact sound_154
  · exact sound_155
  · exact sound_156
  · exact sound_157
  · exact sound_158
  · exact sound_159
  · exact sound_160
  · exact sound_161
  · exact sound_162
  · exact sound_163
  · exact sound_164
  · exact sound_165
  · exact sound_166
  · exact sound_167
  · exact sound_168
  · exact sound_169
  · exact sound_170
  · exact sound_171
  · exact sound_172
  · exact sound_173
  · exact sound_174
  · exact sound_175
  · exact sound_176
  · exact sound_177
  · exact sound_178
  · exact sound_179
  · exact sound_180
  · exact sound_181
  · exact sound_182
  · exact sound_183
  · exact sound_184
  · exact sound_185
  · exact sound_186
  · exact sound_187
  · exact sound_188
  · exact sound_189
  · exact sound_190
  · exact sound_191
  · exact sound_192
  · exact sound_193
  · exact sound_194
  · exact sound_195
  · exact sound_196
  · exact sound_197
  · exact sound_198
  · exact sound_199
  · exact sound_200
  · exact sound_201
  · exact sound_202
  · exact sound_203
  · exact sound_204
  · exact sound_205
  · exact sound_206
  · exact sound_207
  · exact sound_208
  · exact sound_209
  · exact sound_210
  · exact sound_211
  · exact sound_212

theorem not_dissection_refl {N : ℕ} (D : CongruentDissection N)
    (hT : D.target.Congruent TGT) (hM : D.model.Congruent MODEL) : False := by
  obtain ⟨g, D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hT
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have S : Sound 3 sixInstI33 MODEL [] := checkAllR_sound 3 hD sixInstI33 (by norm_num [sixInstI33]) MODEL
    (by simpa [sixInstI33] using hMa) (by simpa [sixInstI33] using hMb) (by simpa [sixInstI33] using hMc)
    wBase sixKnownI33 known_sound 400 sixTreeI33 sixI33_top
  exact S (N := N) D' (by rw [hD'T, tgt_carr]) (by rw [hD'M]; exact hM) (by simp)

theorem TGT_opp0 : TGT.oppLen 0 = 21 := by unfold Tri.oppLen; exact TGT_sides.2.1
theorem TGT_opp1 : TGT.oppLen 1 = 33 := by unfold Tri.oppLen; rw [dist_comm]; exact TGT_sides.2.2
theorem TGT_opp2 : TGT.oppLen 2 = 21 := by unfold Tri.oppLen; exact TGT_sides.1
theorem MODEL_opp0 : MODEL.oppLen 0 = 3 := by unfold Tri.oppLen; exact MODEL_sides.2.1
theorem MODEL_opp1 : MODEL.oppLen 1 = 7 := by unfold Tri.oppLen; rw [dist_comm]; exact MODEL_sides.2.2
theorem MODEL_opp2 : MODEL.oppLen 2 = 5 := by unfold Tri.oppLen; exact MODEL_sides.1

/-- **No dissection**: target opposite-side lengths `21 , 21 , 33` (read through `σt`) and model opposite-side lengths
`5 , 3 , 7` (read through `σm`).  -/
theorem not_dissection_sides {N : ℕ} (D : CongruentDissection N) (σt σm : Equiv.Perm (Fin 3))
    (h0 : D.target.oppLen (σt 0) = 21) (h1 : D.target.oppLen (σt 1) = 21) (h2 : D.target.oppLen (σt 2) = 33)
    (m0 : D.model.oppLen (σm 0) = 5) (m1 : D.model.oppLen (σm 1) = 3) (m2 : D.model.oppLen (σm 2) = 7) :
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

end Refl.SIXBridgeI33
#print axioms Refl.SIXBridgeI33.not_dissection_sides
