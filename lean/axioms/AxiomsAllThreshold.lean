/-
Axioms of the declarations of the Lean map table of the paper (and of the tilings with 330, 897 and 990
tiles) whose module lies in the import closure of `Erdos634.AllThreshold`. After building `Erdos634.AllThreshold`, run
from the directory `lean/`:
  lake env lean axioms/AxiomsAllThreshold.lean
Every line of the output should read: depends on axioms: [propext, Classical.choice, Quot.sound].
-/
import Erdos634.Draft.E1ScaleTwo
import Erdos634.Draft.LayerE1
import Erdos634.Draft.LayerG
import Erdos634.Draft.LayerGChord
import Erdos634.Draft.ResidueSeed
import Erdos634.Draft.SideRun
import Erdos634.Draft.SideRunGAngles
import Erdos634.Draft.SideRunGCornerMainB
import Erdos634.Draft.SideRunGMain
import Erdos634.Draft.SideRunGThick
import Erdos634.Draft.SideRunHalf
import Erdos634.Draft.SideRunRules
import Erdos634.Draft.SignedDecompW
import Erdos634.Draft.ThresholdBlind
import Erdos634.Draft.UniformThreshold
import Erdos634.Draft.WSeedGAssemble
import Erdos634.Draft.WSeedGW
import Erdos634.Draft.WStrip
import Erdos634.Draft.WStripChord
import Erdos634.Draft.NSQMMainZETWitness
import Erdos634.Draft.NSQMS5W
import Erdos634.Draft.NSQMMainZETW
import Erdos634.Draft.NSQMMainZETWWitness
import Erdos634.Draft.ThmDStatementGeo
import Erdos634.Draft.ThmDChain
import Erdos634.Draft.ThmDChainW
import Erdos634.Draft.ThmDChainWitnessC
import Erdos634.Draft.ThmDChainWitnessW
import Erdos634.Draft.SideRunGThetaMain

#print axioms Erdos634.Draft.UniformThreshold.not_betaTilable_one
#print axioms Erdos634.Draft.Residue.betaTilable_ge
#print axioms Erdos634.Draft.Residue.wTilable_ge
#print axioms Erdos634.Draft.SideRun.Setup.side_theorem'
#print axioms Erdos634.Draft.SideRun.wTilable_e1_iff
#print axioms Erdos634.Draft.SideRun.not_betaTilable_e1_le_half
#print axioms Erdos634.Draft.SideRunG.thm_siderunall_angles_T
#print axioms Erdos634.Draft.SideRunG.thm_siderunall_angles_W
#print axioms Erdos634.Draft.SideRunG.ebelow_a
#print axioms Erdos634.Draft.SideRunG.ebelow_b
#print axioms Erdos634.Draft.SideRunGA.thickw_a
#print axioms Erdos634.Draft.SideRunGA.thickw_b
#print axioms Erdos634.Draft.SideRunGA.thickw_c
#print axioms Erdos634.Draft.LayerE1.betaTilable_succ
#print axioms Erdos634.Draft.LayerE1.exists_min_scale
#print axioms Erdos634.Draft.LayerE1.threshold_e1_iff_top
#print axioms Erdos634.Draft.WSeedG.beta_seed
#print axioms Erdos634.Draft.WSeedG.w_seed
#print axioms Erdos634.Draft.SideRunGA.thm_cornerrun
#print axioms Erdos634.Draft.SideRunGA.thm_cornerrun_addendum
#print axioms Erdos634.Draft.SignedDecompW.signed_decomposition_member_W
#print axioms Erdos634.Draft.LayerG.layer_real
#print axioms Erdos634.Draft.LayerG.layer_c_i
#print axioms Erdos634.Draft.LayerG.layer_c_ii
#print axioms Erdos634.Draft.WStripG.wstrip_step
#print axioms Erdos634.Draft.WStripChord.wstrip_c
#print axioms Erdos634.Draft.WStripChord.wstrip_d
#print axioms Erdos634.Draft.Residue.threshold_iff_small
#print axioms Erdos634.Draft.UniformThreshold.threshold_1_2
#print axioms Erdos634.Draft.E1ScaleTwo.thresholdAt_e1_of
#print axioms Erdos634.Draft.SideRun.thresholdAt_e1_le_half
#print axioms Erdos634.Draft.Blind.invariant_blind
#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzET
#print axioms Erdos634.Draft.NSQM.no_dissection_168
#print axioms Erdos634.Draft.NSQM.no_dissection_248
#print axioms Erdos634.Draft.ThmD.thmD_standalone
#print axioms Erdos634.Draft.ThmD.thmDStatement_geo
#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETD
#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETWD
#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETW
#print axioms Erdos634.Draft.NSQM.raStatement_of_s5w
#print axioms Erdos634.Draft.SideRunGT.theta_word_hasSides
#print axioms Erdos634.Draft.NSQM.no_dissection_276
#print axioms Erdos634.Draft.NSQM.cnzETWD_204
#print axioms Erdos634.Draft.NSQM.cnzETWD_268
#print axioms Erdos634.Draft.NSQM.cnzETWD_279
#print axioms Erdos634.Draft.NSQM.not_cnzETWD_72
#print axioms Erdos634.Draft.NSQM.not_cnzETWD_143
#print axioms Erdos634.Draft.NSQM.not_cnzETWD_320
