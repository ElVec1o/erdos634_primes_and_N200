import Erdos634.Draft.HerdtFamily
import Erdos634.Draft.LaczFamily
import Erdos634.Draft.ZhangProps
import Erdos634.Draft.Iso357Semigroup
import Erdos634.Draft.EqSemigroup
import Erdos634.Draft.F3All
import Erdos634.Draft.F4All
import Erdos634.Draft.S2All
/-
Axioms of the declarations of the Lean map table of the paper (and of the tilings with 330, 897 and 990
tiles) whose module lies in the import closure of `Erdos634.All`. After building `Erdos634.All`, run
from the directory `lean/`:
  lake env lean axioms/AxiomsAll.lean
Every line of the output should read: depends on axioms: [propext, Classical.choice, Quot.sound].
-/
import Erdos634.AngleSumDissection
import Erdos634.BaseBetaCorners
import Erdos634.BaseBetaWalks
import Erdos634.Dissection
import Erdos634.Draft.AtomShape
import Erdos634.Draft.B3Prime
import Erdos634.Draft.BaseBetaFullUnc
import Erdos634.Draft.E120Count
import Erdos634.Draft.E60Count
import Erdos634.Draft.FDBMod12Converse
import Erdos634.Draft.FDDSpectrumPaper
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxPaperCorIntAnchored
import Erdos634.Draft.FluxPaperLemCancel
import Erdos634.Draft.GAUFinal
import Erdos634.Draft.ISUMain
import Erdos634.Draft.LemmaCFinal
import Erdos634.Draft.LemmaPProof
import Erdos634.Draft.N330
import Erdos634.Draft.N897
import Erdos634.Draft.N990
import Erdos634.Draft.OtherSpectraFull
import Erdos634.Draft.PierceScale
import Erdos634.Draft.PrimeCharacterization
import Erdos634.Draft.S5Family
import Erdos634.Draft.SporadicCounts
import Erdos634.Draft.TheoremP6
import Erdos634.Draft.TileCountFamilies
import Erdos634.Draft.TileCountSpectrum
import Erdos634.Ladder
import Erdos634.NonIntegrality
import Erdos634.Rationality
import Erdos634.RunPartition
import Erdos634.WallEndpoints
import Erdos634.R126TilingBridge
import Erdos634.R189TilingBridge
import Erdos634.R84TilingBridge
import Erdos634.R88TilingBridge

#print axioms Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff
#print axioms Erdos634.Draft.TheoremP6.theoremP_6
#print axioms Erdos634.Draft.BaseBetaFullUnc.basebeta_full_unc
#print axioms Erdos634.Draft.ISUMain.thmIso_unrestricted
#print axioms Erdos634.Geometry.Dissection.volume_target
#print axioms Erdos634.Geometry.Dissection.hasAngleSums
#print axioms Erdos634.WallEndpoints.chain_endpoints
#print axioms Erdos634.RunPartition.run_partition
#print axioms Erdos634.Ladder.ladder
#print axioms Erdos634.Draft.TileCountFamilies.tileCount_scale
#print axioms Erdos634.Draft.TileCountFamilies.tileCount_two_squares
#print axioms Erdos634.Draft.TileCountFamilies.tileCount_three_sq
#print axioms Erdos634.Draft.TileCountFamilies.tileCount_six_sq
#print axioms Erdos634.Draft.LemmaCFinal.lemmaC_general
#print axioms Erdos634.Draft.LemmaPProof.lemmaP_general
#print axioms Erdos634.Geometry.vertex_multiplicities
#print axioms Erdos634.BaseBetaCorners.corner_beta_unique
#print axioms Erdos634.BaseBetaCorners.corner_apex_unique
#print axioms Erdos634.Geometry.Paper.lem_cancel
#print axioms Erdos634.Geometry.Paper.lem_value_alpha
#print axioms Erdos634.Geometry.Paper.lem_value_beta
#print axioms Erdos634.Geometry.Paper.cor_int_anchored
#print axioms Erdos634.NonIntegrality.k_not_dvd
#print axioms Erdos634.Rationality.tile_rational
#print axioms Erdos634.Draft.OtherSpectraFull.otherspectra
#print axioms Erdos634.Draft.FDDSpectrumPaper.spectrum_paper
#print axioms Erdos634.Draft.FDBMod12Converse.thm_mod12
#print axioms Erdos634.Draft.PierceScale.thm_pierce_scale
#print axioms Erdos634.BaseBetaWalks.apex_leftover_nonrepresentable
#print axioms Erdos634.Geometry.Row5.theoremE_sixty
#print axioms Erdos634.Geometry.Row5.theoremE_twoPiThree
#print axioms Erdos634.Draft.E60Graph.sixty_has_a_relation
#print axioms Erdos634.Draft.E120Graph.twoPiThree_has_a_relation
#print axioms Erdos634.Draft.TileCountSpectrum.tileCount_seven_sq_iff
#print axioms Erdos634.Draft.TileCountSpectrum.tileCount_eleven_sq_iff
#print axioms Erdos634.Draft.SporadicCounts.tc77
#print axioms Erdos634.R84TilingBridge.r84_nonempty_congruentDissection
#print axioms Erdos634.R88TilingBridge.r88_nonempty_congruentDissection
#print axioms Erdos634.R126TilingBridge.r126_nonempty_congruentDissection
#print axioms Erdos634.R189TilingBridge.r189_nonempty_congruentDissection
#print axioms Erdos634.Draft.NSQM.s5_base_word2_hasSides
#print axioms Erdos634.Draft.NSQM.s5_family_2k_hasSides
#print axioms Erdos634.Draft.NSQM.atom_shape_te
#print axioms Erdos634.Draft.NSQM.atom_not_squarefree
#print axioms Erdos634.Draft.NSQM.b3prime
#print axioms Erdos634.Draft.GAU.gapA_sq
#print axioms Erdos634.Draft.N330.tileCount_330
#print axioms Erdos634.Draft.N897.tileCount_897
#print axioms Erdos634.Draft.N990.tileCount_990
#print axioms Erdos634.Draft.S2All.s2_family_all
#print axioms Erdos634.Draft.F4All.f4_family
#print axioms Erdos634.Draft.F3All.f3_family
#print axioms Erdos634.Draft.EqSemigroup.eq357_semigroup
#print axioms Erdos634.Draft.Iso357Semigroup.iso357_semigroup
#print axioms Erdos634.Draft.ZhangEqui.zhang_equi_m
#print axioms Erdos634.Draft.ZhangProps.zhang_five
#print axioms Erdos634.Draft.LaczFamily.lacz_family_uncond
#print axioms Erdos634.Draft.HerdtFamily.herdt_family
#print axioms Erdos634.Draft.HerdtFamily.herdt_uniform
#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzE
