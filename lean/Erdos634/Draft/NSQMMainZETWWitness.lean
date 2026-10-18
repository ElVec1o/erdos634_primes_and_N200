/-
Draft/NSQMMainZETWWitness.lean — non-vacuity of the S5 word leaf `S5wChk` and of `NSQM.CN'zETW`, with negative controls.
* `s5wChk_459`, `not_s5pChk_459`: 459 = 3^3 · 17 has the S5 instances (3,7,10) and (3,25,26); the old leaf `S5pChk` fails, the word leaf holds
  (no word: `wordN` false for both).  Leaf-level witness (459 itself still fails the G leaf).
* Negative controls, the real tilings of θ_t(e,f): `¬ S5wChk N` for N = 48 = θ_4(1,2), 108 = θ_6(1,2), 300 = θ_10(1,2), 320 = θ_8(2,3)
  (each has an instance with a word, as it must: the tilings exist).
* `cnzETW_168`: `CN'zETW 168` holds (168 has no S5 instance); `cnzETW_not_72`: 72 is a tile count and `CN'zETW 72` fails.
Census: no non-squarefree N ≤ 10^6 is excluded by the new chain and not by `CN'zET` (every value where the word leaf is the
difference also fails the formal G leaf); see PAPER_MAP, batch 2026-10-18 (S5 word leaf).
    No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMMainZETW

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM

open Erdos634.Geometry

theorem s5wChk_459 : S5wChk 459 := by decide +kernel
theorem not_s5pChk_459 : ¬ S5pChk 459 := by decide +kernel
theorem not_s5wChk_48 : ¬ S5wChk 48 := by decide +kernel
theorem not_s5wChk_108 : ¬ S5wChk 108 := by decide +kernel
theorem not_s5wChk_300 : ¬ S5wChk 300 := by decide +kernel
theorem not_s5wChk_320 : ¬ S5wChk 320 := by decide +kernel
theorem wordN_8_2_3 : WordN 8 2 3 := by decide +kernel
theorem not_wordN_3_7_10 : ¬ WordN 3 7 10 := by decide +kernel

theorem cnzETW_168 : CN'zETW 168 := by decide +kernel
theorem cnzETW_not_72 : ¬ CN'zETW 72 := by decide +kernel

/-- the word-leaf chain applied: no congruent dissection with 168 tiles -/
theorem no_dissection_168_w (D : CongruentDissection 168) : False := not_tile_of_conditionsNSQzETW 168 cnzETW_168 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.s5wChk_459
#print axioms Erdos634.Draft.NSQM.cnzETW_168
#print axioms Erdos634.Draft.NSQM.no_dissection_168_w
