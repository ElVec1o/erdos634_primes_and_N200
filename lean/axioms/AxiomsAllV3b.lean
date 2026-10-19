/-
Axioms of the results added after `AllV3` in release v3.0 (chain lemma, thick regime, Theorem R2 arithmetic half and conditional
corollary, collar families 966 g^2 and 2485 g^2, exclusions of 412 and 270).  After building `Erdos634.AllV3b`, from `lean/`:
  lake env lean axioms/AxiomsAllV3b.lean
Every line should read: depends on axioms: [propext, Classical.choice, Quot.sound] (theorems with hypotheses print the same).
NOTE: `SplusR2.wTilable_not_of_small_M2_of_R2` is CONDITIONAL on the hypothesis `R2Count e f`, which is not proved in Lean.
-/
import Erdos634.AllV3b

#print axioms Erdos634.Draft.Chain.chain_tri
#print axioms Erdos634.Draft.Chain.W.w_placement
#print axioms Erdos634.Draft.Chain.W.w_placement_threshold
#print axioms Erdos634.Draft.SplusThick.cornerrun_counts_thick
#print axioms Erdos634.Draft.SplusThick.thickw_count_tiling_thick
#print axioms Erdos634.Draft.SplusThick.wTilable_not_of_small_M
#print axioms Erdos634.Draft.SplusThick.not_W_5_8_2
#print axioms Erdos634.Draft.SplusThick.not_W_5_7_3
#print axioms Erdos634.Draft.SplusThick.not_W_7_11_2
#print axioms Erdos634.Draft.SplusThick.not_W_8_11_3
#print axioms Erdos634.Draft.SplusThick.not_W_3_5_2
#print axioms Erdos634.Draft.SplusR2.A5'
#print axioms Erdos634.Draft.SplusR2.Aa'
#print axioms Erdos634.Draft.SplusR2.c_single_rep
#print axioms Erdos634.Draft.SplusR2.r2_arith
#print axioms Erdos634.Draft.SplusR2.count_tiling_r2
#print axioms Erdos634.Draft.SplusR2.wTilable_not_of_small_M2_of_R2
#print axioms Erdos634.Draft.CollarFam2.tileCount_966_sq_ge2
#print axioms Erdos634.Draft.CollarFam2.tileCount_2485_sq_ge2
#print axioms Erdos634.Draft.CollarFam2.tileCount_279174'
#print axioms Erdos634.Draft.CollarFam2.tileCount_718165'
#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETWD3
#print axioms Erdos634.Draft.NSQM.no_dissection_412
#print axioms Erdos634.Draft.NSQM.no_dissection_270
