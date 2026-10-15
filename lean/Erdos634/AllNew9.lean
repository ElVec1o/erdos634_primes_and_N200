/- AllNew9: umbrella import module for the CornerPara*, CornerStep* and wrapper modules. -/
import Erdos634.Draft.CornerParaBase
import Erdos634.Draft.CornerParaClamp
import Erdos634.Draft.CornerParaCorner
import Erdos634.Draft.CornerParaCornerAux
import Erdos634.Draft.CornerParaPartner
import Erdos634.Draft.CornerParaHalfTurn
import Erdos634.Draft.CornerParaForwardAux
import Erdos634.Draft.CornerParaForward
import Erdos634.Draft.CornerParaChain
import Erdos634.Draft.CornerParaMaster
import Erdos634.Draft.CornerParaWitnessAux
import Erdos634.Draft.CornerParaWitness
import Erdos634.Draft.CornerStepFormal
import Erdos634.Draft.CornerStepWitness
-- NogoCensusWrap: prop:nogocensus abstract wrapper;
import Erdos634.Draft.NogoCensusWrap
-- OffsetForcingWrap: lem:offsets arithmetic kernel;
import Erdos634.Draft.OffsetForcingWrap
-- StraddleGenWrap: prop:straddlegen area arithmetic kernel;
import Erdos634.Draft.StraddleGenWrap
-- PierceRungWrap: thm:pierce + prop:rung2 arithmetic kernels;
import Erdos634.Draft.PierceRungWrap
-- L2SlotEllTwoWrap: thm:l2slot + thm:elltwo arithmetic kernels;
import Erdos634.Draft.L2SlotEllTwoWrap
-- RayWrap: thm:ray arithmetic kernel;
import Erdos634.Draft.RayWrap
-- LastJunctionWrap: thm:lastjunction combinatorial kernel;
import Erdos634.Draft.LastJunctionWrap
-- ForkKillWrap: thm:forkkill + prop:a2branch arithmetic kernels;
import Erdos634.Draft.ForkKillWrap
-- ApexWrap: lem:apex arithmetic cores;
import Erdos634.Draft.ApexWrap
-- SlotDichotomyWrap: prop:slotdichotomy arithmetic kernels;
import Erdos634.Draft.SlotDichotomyWrap
-- NilpotentTowerWrap: rem:nilptower group theory kernel;
import Erdos634.Draft.NilpotentTowerWrap
-- PBoundWrap: cor:pbound arithmetic kernel;
import Erdos634.Draft.PBoundWrap
-- StradleWrap: prop:straddle arithmetic kernel;
import Erdos634.Draft.StradleWrap
-- FigurePWrap: cor:figureP + prop:figurePprime arithmetic kernels;
import Erdos634.Draft.FigurePWrap
-- PrimitivesWrap: prop:cevianatom + thm:addlaw arithmetic kernels;
import Erdos634.Draft.PrimitivesWrap
-- OtherSpectraWrap: prop:otherspectra equilateral clause;
import Erdos634.Draft.OtherSpectraWrap
-- PinBufferWrap: rem:pinbuffer arithmetic cores;
import Erdos634.Draft.PinBufferWrap
-- ChordDecompWrap: prop:chorddecomp flush classification;
import Erdos634.Draft.ChordDecompWrap
-- NoTPWrap: cor:noTP arithmetic cores;
import Erdos634.Draft.NoTPWrap
-- MirrorUWrap: thm:nobothmirror + prop:Uplacements arithmetic kernels;
import Erdos634.Draft.MirrorUWrap
-- AForcesTWrap: thm:aforcesT arithmetic cores;
import Erdos634.Draft.AForcesTWrap
-- WideColWrap: prop:widecol one-member certificate;
import Erdos634.Draft.WideColWrap
-- UnifyWrap: prop:unify fill + angle + partition arithmetic kernels;
import Erdos634.Draft.UnifyWrap
-- Eq105Wrap: thm:eq105 rational-angle branch (partial);
import Erdos634.Draft.Eq105Wrap
-- DoubleCWrap: prop:doublec assembly — double-c kill uniform in j;
import Erdos634.Draft.DoubleCWrap
-- SpectralWrap: rem:spectral dual-graph numeric corrections;
import Erdos634.Draft.SpectralWrap
-- DirGroupWrap: prop:gammagrading + prop:dirgroup direction-group algebraic kernels;
import Erdos634.Draft.DirGroupWrap
-- PentagonWrap: lem:pentagon both-stub arithmetic core (pentagon_region_dies);
import Erdos634.Draft.PentagonWrap
-- LadderTermWrap: lem:termination consecutive_gap ladder termination arithmetic;
import Erdos634.Draft.LadderTermWrap
import Erdos634.Draft.LemChargeWrap
-- InflationSideWrap: prop:inflbdy + cor:inflcrux + prop:inflparity side-rigidity arithmetic;
import Erdos634.Draft.InflationSideWrap
-- OrientMonoWrap: prop:orientmono orientation-sequence arithmetic kernel;
import Erdos634.Draft.OrientMonoWrap
-- EastFanWrap: lem:eastfan straight-junction arithmetic kernel;
import Erdos634.Draft.EastFanWrap
-- NoGoldenWrap: prop:nogolden golden-ratio removability arithmetic;
import Erdos634.Draft.NoGoldenWrap
-- OneBlocWrap: cor:onebloc one-end-blocked chord dichotomy arithmetic;
import Erdos634.Draft.OneBlocWrap
-- DepthWindowWrap: thm:depthwindow pincer window arithmetic kernel;
import Erdos634.Draft.DepthWindowWrap
-- AlignWrap: thm:align alignment arithmetic (far_near_disjoint, b_not_dvd_fsq, far_is_bpow);
import Erdos634.Draft.AlignWrap
-- KbRepWrap: thm:kbrep + thm:halfangle arithmetic kernels;
import Erdos634.Draft.KbRepWrap
-- TopJunctionWrap: lem:topjunction filler discriminant + p ≤ f−3 arithmetic;
import Erdos634.Draft.TopJunctionWrap
-- TightSideWrap: prop:tightside p=2 side arithmetic (p_two_single_c, pi_vertex_with_gamma);
import Erdos634.Draft.TightSideWrap
-- JbLineWrap: lem:jbline jb-line partition arithmetic;
import Erdos634.Draft.JbLineWrap
-- ClosePairColWrap: prop:closepaircolumns close-pair column arithmetic kernels;
import Erdos634.Draft.ClosePairColWrap
-- SharpColumnWrap: prop:sharpcolumn column criterion identity + sharp criterion + residue step;
import Erdos634.Draft.SharpColumnWrap
-- BaseBetaE1Wrap: thm:basebeta-e1 vertex-figure classification + α-irrationality;
import Erdos634.Draft.BaseBetaE1Wrap
-- CollarWrap: lem:collar collar cell/tile count arithmetic kernels;
import Erdos634.Draft.CollarWrap
-- BUnsplitWrap: prop:bunsplit b-chord unsplittability arithmetic;
import Erdos634.Draft.BUnsplitWrap
-- PTwoDeadWrap: thm:ptwodead filler-angle overflow arithmetic;
import Erdos634.Draft.PTwoDeadWrap
-- InflBdyWrap: prop:inflbdy inflated boundary word arithmetic at (1,3);
import Erdos634.Draft.InflBdyWrap
-- LemTerminationWrap: lem:termination consecutive-gap arithmetic;
import Erdos634.Draft.LemTerminationWrap
-- Walls16Wrap: cor:walls16 reach-4 pincer window at f≤6;
import Erdos634.Draft.Walls16Wrap
-- RowQ0Wrap: lem:rowq0 parallelogram closure + remainder anchor arithmetic;
import Erdos634.Draft.RowQ0Wrap
-- LemTermWedgeWrap: lem:termwedge terminal-wedge vertex-figure arithmetic;
import Erdos634.Draft.LemTermWedgeWrap
-- LemFillerWrap: lem:filler filler-mesh identity + sum forcing arithmetic kernels;
import Erdos634.Draft.LemFillerWrap
-- EpredWrap: thm:efminus1 + prop:n1fromwalls e=f−1 side-walk arithmetic kernels;
import Erdos634.Draft.EpredWrap
-- SecondCWrap: thm:secondc admissible angular orders + second-edge arithmetic;
import Erdos634.Draft.SecondCWrap
-- SolitaryWrap: lem:solitary crossing-tangency ring identity + shadow arithmetic;
import Erdos634.Draft.SolitaryWrap
import Erdos634.Draft.NoapexWrap
-- SeedDegenerateWrap: thm:seeddegenerate five interface-relation ring identities;
import Erdos634.Draft.SeedDegenerateWrap
-- MarchRunWrap: rem:marchobl(i) junction dichotomy + combinatorial kernel;
import Erdos634.Draft.MarchRunWrap
-- V1GapsWrap: O-v1repair three arithmetic kills (N1/N2/N3 Diophantine);
import Erdos634.Draft.V1GapsWrap
-- ColumnReductionWrap: rem:columnreduction six extra-column arithmetic kernels;
import Erdos634.Draft.ColumnReductionWrap
-- MirrorKillWrap: rem:reversal/rem:walls14 seven combinatorial kernels;
import Erdos634.Draft.MirrorKillWrap
-- ZhangTargetsWrap: rem:zhangsmall/rem:zhangsharp Heron+Frobenius kernels;
import Erdos634.Draft.ZhangTargetsWrap
-- WalkEquationWrap: thm:walks walk_equation + sum_lengths measure kernels;
import Erdos634.Draft.WalkEquationWrap
-- FanPruneSoundWrap: prop:fanprune soundness + residue arithmetic kernels;
import Erdos634.Draft.FanPruneSoundWrap
-- CChordWrap: lem:basedi + cor:onebloc c-chord and base walk dichotomy arithmetic kernels;
import Erdos634.Draft.CChordWrap
-- BaseBetaWalkArithWrap: thm:walks/walkstruct equal_side_no_b + base_b_count walk arithmetic kernels;
import Erdos634.Draft.BaseBetaWalkArithWrap
-- SideNoBWrap: cor:wallsf2e equal-side no-b-edge arithmetic kernels;
import Erdos634.Draft.SideNoBWrap
-- ScaleBreakWrap: scale-break m=2 side_no_b_fails arithmetic kernel;
import Erdos634.Draft.ScaleBreakWrap
-- BaseBetaCornersWrap: vertex figures + b-unsplittability arithmetic kernels;
import Erdos634.Draft.BaseBetaCornersWrap
-- BaseBetaMod12Wrap: thm:mod12 prime≡11(mod12) arithmetic kernel;
import Erdos634.Draft.BaseBetaMod12Wrap
-- AngleArithmeticWrap: vertex figure + β-π/3 arithmetic kernels;
import Erdos634.Draft.AngleArithmeticWrap
-- BaseAlphaBetaPrimeWrap: base α+β prime obstruction arithmetic kernels;
import Erdos634.Draft.BaseAlphaBetaPrimeWrap
-- AdmissibleSpectrumWrap: sqfree-scale + admissible spectrum arithmetic kernels;
import Erdos634.Draft.AdmissibleSpectrumWrap
-- AngleThresholdWrap: law-of-cosines for (f,f²-1,f²) tile angles;
import Erdos634.Draft.AngleThresholdWrap
-- BaseBetaWalksWrap: walk-equation Diophantine classification kernels;
import Erdos634.Draft.BaseBetaWalksWrap
-- BaseCountsE1Wrap: e=1 base-walk classification (base_counts, base_counts_corner);
import Erdos634.Draft.BaseCountsE1Wrap
-- IsoAlphaPrimeWrap: isosceles α-tile prime obstruction arithmetic;
import Erdos634.Draft.IsoAlphaPrimeWrap
-- InvariantCoreWrap: flux/charge invariant core algebra (sum_antisym, cancellation_core);
import Erdos634.Draft.InvariantCoreWrap
-- InvariantProductWrap: F1 invariant product algebra (F1_product, disc_not_square);
import Erdos634.Draft.InvariantProductWrap
-- Mod12Wrap: sq_odd_mod_four, sq_mod_three, base_beta_prime_mod12 arithmetic;
import Erdos634.Draft.Mod12Wrap
-- RationalityWrap: prod_eq, sum_eq, ratios_rational, tile_rational (tile rationality);
import Erdos634.Draft.RationalityWrap
-- E1BaseWordWrap: thm:e1family f≥3 — e1_family_f_ge_3_congruent + of_sides;
import Erdos634.Draft.E1BaseWordWrap
-- E1NormalFormWrap: congruent_modelTri_of_sides + self-congruence witnesses;
import Erdos634.Draft.E1NormalFormWrap
-- VertexFigureRealWrap: prop:vertexfigures interior/boundary figure cases;
import Erdos634.Draft.VertexFigureRealWrap
-- ComposeWrap: thm:ladder compose dissections (M·N pieces from M outer + N inner);
import Erdos634.Draft.ComposeWrap
-- WalkStructureWrap: thm:walkstruct base/side walk structure (P residue, no-b, level);
import Erdos634.Draft.WalkStructureWrap
-- ApexEdgesRealWrap: corner tile base edge theorem (apex_edges_real);
import Erdos634.Draft.ApexEdgesRealWrap
-- DissectionWrap: vertex_multiplicities + apex/pi/beta figure cases + volume_pos;
import Erdos634.Draft.DissectionWrap
-- LadderWrap: thm:ladder k²·N dissection by scaling (Ladder.ladder);
import Erdos634.Draft.LadderWrap
-- BaseWordWrap: base walk word arithmetic (b_count_is_e, param_word, N=83 words);
import Erdos634.Draft.BaseWordWrap
-- CornerBaseEdgesRealWrap: corner tile base-edge (congruentDissection_base_corner_edges);
import Erdos634.Draft.CornerBaseEdgesRealWrap
-- SubDissectionWrap: restrict/restrictCongruent sub-region extraction;
import Erdos634.Draft.SubDissectionWrap
-- InterfaceWrap: Interface tile-placement arithmetic (side_no_b, partner_unique, no_two_gamma);
import Erdos634.Draft.InterfaceWrap
-- BaseBetaTargetCoordWrap: explicit base-β target triangle (cornerAngles, htarget, modelBeta);
import Erdos634.Draft.BaseBetaTargetCoordWrap
-- MarchComposeWrap: modelTri sides/angles + base_word_dies;
import Erdos634.Draft.MarchComposeWrap
-- MarchSlotsWrap: no_two_gamma + third_of_gamma_beta junction slot analysis;
import Erdos634.Draft.MarchSlotsWrap
-- MarchInductionWrap: march_step + run_rigid march induction;
import Erdos634.Draft.MarchInductionWrap
-- RunPartitionWrap: bOverM_dies + cSplit_dies run partition eliminations;
import Erdos634.Draft.RunPartitionWrap
-- BaseDecompositionWrap: base walk (a,b,c)-word classification (base_decomposition_general);
import Erdos634.Draft.BaseDecompositionWrap
-- CongruenceWrap: Tri.Congruent refl/symm/trans + corner angles + volume;
import Erdos634.Draft.CongruenceWrap
-- BaseIdentityWrap: area identity algebraic kernels (equilateral + general + base-β);
import Erdos634.Draft.BaseIdentityWrap
-- BaseWordBlockWrap: no_f_plus_one_a + no_a_block + row_three_closes counting;
import Erdos634.Draft.BaseWordBlockWrap
-- BaseSelectionWrap: tile containment + boundary_point_on_edge + coord_zero_mem_segment;
import Erdos634.Draft.BaseSelectionWrap
-- BaseWalkGeneralWrap: hiso_wallFun' + base_walk_pos_general (γ-trap, any real dissection);
import Erdos634.Draft.BaseWalkGeneralWrap
-- E1AssemblyWrap: e=1 base walk arithmetic kernels (sum_eps_mod, integral_forces_p_eq_q, etc.);
import Erdos634.Draft.E1AssemblyWrap
-- MarchAssemblyWrap: march run orientation + junction dichotomy (orient_west_beta, run_west_flank_gamma);
import Erdos634.Draft.MarchAssemblyWrap
-- BaseChainWrap: wall chain enumeration (wallList_nodup, mem_wallList, base_chain_consecutive_meet);
import Erdos634.Draft.BaseChainWrap
-- GammaTrapWrap: prop:gammatrap — every side of a base-beta target carries >=1 c-edge;
import Erdos634.Draft.GammaTrapWrap
-- AnchoredChainWrap: chain anchoring at gamma-corners (no_second_through, chain_endpoint_pinned);
import Erdos634.Draft.AnchoredChainWrap
-- AngleSumAssembledWrap: angle_sum_interior + angle_sum_boundary measure-theory kernels;
import Erdos634.Draft.AngleSumAssembledWrap
-- AngleSumDissectionWrap: G2 theorem (hasAngleSums) + sum_localAngle_eq;
import Erdos634.Draft.AngleSumDissectionWrap
-- ApexRigidityWrap: two_gamma + figure_at_P/P' + V_interior + side bounds;
import Erdos634.Draft.ApexRigidityWrap
-- ApexRayWrap: c_eq_f_a + angle_is_alpha + Q_f + apex_tile_flanks;
import Erdos634.Draft.ApexRayWrap
-- TheoremP6Wrap: theoremP_6 (prime exclusion, N ≡ 3 mod 4)
import Erdos634.Draft.TheoremP6Wrap
-- AreaDetWrap: volume=det*stdCarrier + area identity + stdCarrier geometry;
import Erdos634.Draft.AreaDetWrap
-- MarchKillsWrap: apex heights + overshoot + far_corner_kill;
import Erdos634.Draft.MarchKillsWrap
-- MarchKillsFanWrap: fan angle lemmas + modelAlpha irrationality;
import Erdos634.Draft.MarchKillsFanWrap
-- PrimeArithmeticWrap: prime exclusion arithmetic (F1–F4 counts, mod 4);
import Erdos634.Draft.PrimeArithmeticWrap
-- EpredColumnKillWrap: e=f-1 column kill + survivors_23/59/83;
import Erdos634.Draft.EpredColumnKillWrap
-- RationalityFreeWrap: rationality exclusion arithmetic;
import Erdos634.Draft.RationalityFreeWrap
-- RealizableWrap: scaleTri composition + Cut scaling + realizableSet;
import Erdos634.Draft.RealizableWrap
-- Route1Wrap: Route 1 word count lemmas (run_le, starvation, rigidity);
import Erdos634.Draft.Route1Wrap
-- CrossingCountWrap: crossing count + area identity + base point;
import Erdos634.Draft.CrossingCountWrap
-- ScaleMapWrap: sin² values for base-beta angles;
import Erdos634.Draft.ScaleMapWrap
-- Crux1Wrap: ladder crux arithmetic (4,2 cleared, column fits bound);
import Erdos634.Draft.Crux1Wrap
-- MasterLemmasWrap: inter-apex uniqueness + equal footprints per member;
import Erdos634.Draft.MasterLemmasWrap
-- CrossingCharacterisedWrap: crossing iff block reaches + residue range;
import Erdos634.Draft.CrossingCharacterisedWrap
-- CrossingHypothesisWrap: e=1 reduction chain + partition of line;
import Erdos634.Draft.CrossingHypothesisWrap
-- LadderCeilingWrap: L4 gap identity + thick-mixed impossibility;
import Erdos634.Draft.LadderCeilingWrap
-- LadderInvariantWrap: flush overrun + step identity + march bounds + terminal kill;
import Erdos634.Draft.LadderInvariantWrap
-- ScaleRigidityWrap: scale-sensitivity no-go + instance arithmetic;
import Erdos634.Draft.ScaleRigidityWrap
-- GlobalSystemWrap: corner count system reduction + solution counts;
import Erdos634.Draft.GlobalSystemWrap
-- FanKillWrap: fan kill + semigroup gap one_is_gap + two_gap_contract;
import Erdos634.Draft.FanKillWrap
-- PincerLadderWrap: pincer ladder reach + mirror symmetry + (4,2) escape;
import Erdos634.Draft.PincerLadderWrap
-- HeightLadderWrap: target height + chord width + rung width;
import Erdos634.Draft.HeightLadderWrap
-- OrderForcingWrap: key partition/gap/junction/window theorems from OrderForcing;
import Erdos634.Draft.OrderForcingWrap
-- DissectionMapWrap: affine transport of dissections + interior disjointness;
import Erdos634.Draft.DissectionMapWrap
-- PlacementWrap: edge placement contiguity + no-double-wall;
import Erdos634.Draft.PlacementWrap
-- ChordDecompWrap: chord trace + area non-integrality;
import Erdos634.Draft.ChordDecompWrap
-- B3PrimeBlockerWrap: recorded blocker for prop:b3prime hypothesis;
import Erdos634.Draft.B3PrimeBlockerWrap
-- BeesonBoundaryWrap: Beeson Def.13 boundary orientation + dichotomy;
import Erdos634.Draft.BeesonBoundaryWrap
-- BeesonThm2HypWrap: Beeson Thm 2 hypotheses discharged for our target;
import Erdos634.Draft.BeesonThm2HypWrap
-- AdmissibleSpectrumWrap: squarefree-scale lemma + valuation parity;
import Erdos634.Draft.AdmissibleSpectrumWrap
-- AnchoredChainWrap: chain anchored at γ-corner;
import Erdos634.Draft.AnchoredChainWrap
-- AngleArithmeticWrap: angle figure combinatorics (apex/beta/pi/alpha-beta forced);
import Erdos634.Draft.AngleArithmeticWrap
-- Beeson3NotPrimeWrap: Beeson Thm 3 arithmetic exclusions;
import Erdos634.Draft.Beeson3NotPrimeWrap
-- BeesonOmegaWrap: Beeson Ω region reflexivity/transitivity/symmetry;
import Erdos634.Draft.BeesonOmegaWrap
-- BlockNeverCompletesWrap: corner block never completes (run bound);
import Erdos634.Draft.BlockNeverCompletesWrap
-- BlockedPartnerWrap: blocked partner analysis (residue, end slots);
import Erdos634.Draft.BlockedPartnerWrap
-- CLayerRigidWrap: C-layer rigidity (three gap types excluded);
import Erdos634.Draft.CLayerRigidWrap
-- BoundaryRigidInsufficientWrap: boundary rigidity iff 2e ≤ f;
import Erdos634.Draft.BoundaryRigidInsufficientWrap
import Erdos634.Draft.CensusSideRelationWrap
-- BentWallCouplingWrap: bent coupling vs straight edge sums;
import Erdos634.Draft.BentWallCouplingWrap
-- AngleSumScopeWrap: three/four ray telescope (mod 2π half of angle sum);
import Erdos634.Draft.AngleSumScopeWrap
-- ApexChordCriterionWrap: apex exclusion iff 2e²≤f + fan criterion;
import Erdos634.Draft.ApexChordCriterionWrap
-- A36ReductionWrap: 3α+2β row reduction via layer rigidity;
import Erdos634.Draft.A36ReductionWrap
import Erdos634.Draft.BAdjacencyWrap
-- BeesonDef5Wrap: Beeson Def.5 Type I/II placements;
import Erdos634.Draft.BeesonDef5Wrap
-- BeesonDeltaWrap: Beeson Δ traversal + strictly advancing contradiction;
import Erdos634.Draft.BeesonDeltaWrap
-- BeesonDirectionsWrap: Type I/II edge directions + Par equivalence;
import Erdos634.Draft.BeesonDirectionsWrap
-- BeesonGraphHWrap: HAdj/HConn graph connectivity (Beeson Def.3);
import Erdos634.Draft.BeesonGraphHWrap
-- R1FinalWrap: thick line e=f-1 exclusion r1_no_tiling (core of prime exclusion);
import Erdos634.Draft.R1FinalWrap
-- FCStep2Wrap: prime forces N=2 chain (chain_unconditional + split_of_raw);
import Erdos634.Draft.FCStep2Wrap
-- BeesonThm2GraphWrap: degree balance + Thm2 skeleton (beeson_thm2_skeleton);
import Erdos634.Draft.BeesonThm2GraphWrap
-- CongruentAreaWrap: isometry preserves measure, congruent dissection area eq;
import Erdos634.Draft.CongruentAreaWrap
-- FourCompCongruenceWrap: B_never_square + fourcomp_no_odd_prime;
import Erdos634.Draft.FourCompCongruenceWrap
-- FCStep1Wrap: gcd_A_B coprimality + fourcomp_AB_prime_eq_two;
import Erdos634.Draft.FCStep1Wrap
-- RouteOneWallOnlyWrap: flank_from_wall_only + alpha_tile_witness;
import Erdos634.Draft.RouteOneWallOnlyWrap
-- CornerBlockWrap: block footprint/far-side/counts + m=1 iff;
import Erdos634.Draft.CornerBlockWrap
-- CornerRuleWrap: corner figure + walls_forces_a_ends + e_one_words;
import Erdos634.Draft.CornerRuleWrap
-- CongruentTileEdgesWrap: lem:ccornerside for real CongruentDissection tiles;
import Erdos634.Draft.CongruentTileEdgesWrap
-- ConeScalingWrap: angle_sum_of_cones;
import Erdos634.Draft.ConeScalingWrap
-- CongruentAnglesWrap: congruent_corner_angles + angle_of_sss;
import Erdos634.Draft.CongruentAnglesWrap
-- CornerAnglePermWrap: cornerAngle_perm + congruentDissection_corner_total;
import Erdos634.Draft.CornerAnglePermWrap
-- ClearanceLemmaWrap: clearance ratio bounds;
import Erdos634.Draft.ClearanceLemmaWrap
-- ContiguityWrap: gap/contiguity lemmas for wall ordering;
import Erdos634.Draft.ContiguityWrap
-- CorridorLowStopWrap: corridor eq classification below e (squeeze_Y_zero, classification);
import Erdos634.Draft.CorridorLowStopWrap
-- ExclusionCriterionWrap: leg_exclusion_iff + all_three_excluded_iff;
import Erdos634.Draft.ExclusionCriterionWrap
-- DualGraph44Wrap: dual graph degree distribution + paper correction;
import Erdos634.Draft.DualGraph44Wrap
-- CornerCascadeWrap: beta_flanks + residue_is_one_beta + e_one_contradiction;
import Erdos634.Draft.CornerCascadeWrap
-- CornerParaLinkWrap: wedge_forces_ray_eq + endpoints_of_uIcc;
import Erdos634.Draft.CornerParaLinkWrap
-- CrossingChiralityWrap: chirality propagation lemmas;
import Erdos634.Draft.CrossingChiralityWrap
-- ConvexCoverWrap: aedisjoint + volume lemmas for cover proofs;
import Erdos634.Draft.ConvexCoverWrap
-- CosetPropagationWrap: sub_mem_of_reach + image_subset_coset;
import Erdos634.Draft.CosetPropagationWrap
-- CoversGeneralWrap: covers_of_volume_general + covers_of_volume_tri;
import Erdos634.Draft.CoversGeneralWrap
-- DescentUniformWrap: progression_inj + step_is_a (apex edge uniformity);
import Erdos634.Draft.DescentUniformWrap
-- DirectionGroupWrap: L_relation + basebeta_coprime (edge-direction coset);
import Erdos634.Draft.DirectionGroupWrap
-- E2JoinWrap: sector_agree + volume_wedge (e≥2 join geometry);
import Erdos634.Draft.E2JoinWrap
-- EdgeChainWrap: no_second_tile_same_side + side_partition;
import Erdos634.Draft.EdgeChainWrap
-- EdgeDisjointWrap: exists_pos_dir + no_same_side_contact;
import Erdos634.Draft.EdgeDisjointWrap
-- EdgeTypeWrap: exists_matching_side (tile-edge type assignment);
import Erdos634.Draft.EdgeTypeWrap
-- EdgeWordConversionWrap: len_eq + chain_edge_length_mem_model;
import Erdos634.Draft.EdgeWordConversionWrap
-- EpredBaseColumnsWrap: epred_first/last_is_solution + epred_k_injective;
import Erdos634.Draft.EpredBaseColumnsWrap
-- FanStepWrap: gamma_never_fits + step_exhaustion (fan step analysis);
import Erdos634.Draft.FanStepWrap
-- GammaCascadeWrap: cascade (pigeonhole on junction placement);
import Erdos634.Draft.GammaCascadeWrap
-- GammaCountWrap: c_edge_exists + survivors (two base words above f=2e);
import Erdos634.Draft.GammaCountWrap
-- GeneralPillarsWrap: b_lattice lemmas + c_minus_a_undec constraints;
import Erdos634.Draft.GeneralPillarsWrap
-- GoldenFormWrap: quartic_eq_golden + golden_fails_at_3_7;
import Erdos634.Draft.GoldenFormWrap
-- InflationWrap: sum_zero_or_three + middle_three + c_side_words;
import Erdos634.Draft.InflationWrap
-- InterfaceFloorWrap: interface_floor + floor_attained;
import Erdos634.Draft.InterfaceFloorWrap
-- InteriorCoordWrap: Tri.interior_iff_pos_coord;
import Erdos634.Draft.InteriorCoordWrap
-- IntervalChainWrap: no_straddle + chain_of_cover;
import Erdos634.Draft.IntervalChainWrap
-- IrregularWrap: base_beta_irregular + which_corner_kills;
import Erdos634.Draft.IrregularWrap
-- IsoTriWrap: dist01 + not_collinear;
import Erdos634.Draft.IsoTriWrap
-- JunctionAutomatonWrap: only_forbidden_pair_is_gg + gg_inadmissible;
import Erdos634.Draft.JunctionAutomatonWrap
-- CollarAreaM4Wrap: edgeMap_mapTri + apex/column_area_sum;
import Erdos634.Draft.CollarAreaM4Wrap
-- CollarAssembleM4Wrap: delta4Pieces_subset + delta4Dissection;
import Erdos634.Draft.CollarAssembleM4Wrap
-- CollarCongruentM4Wrap: delta4CongruentDissection;
import Erdos634.Draft.CollarCongruentM4Wrap
-- CollarContainM4Wrap: apex/corner_subset_delta4;
import Erdos634.Draft.CollarContainM4Wrap
-- CollarDisjointColM4Wrap: columnPieceAt_disjoint;
import Erdos634.Draft.CollarDisjointColM4Wrap
-- CollarDisjointM4Wrap: apex_corner_disjoint + translated_tiling44_interiors_disjoint;
import Erdos634.Draft.CollarDisjointM4Wrap
-- CollarGeometryM4Wrap: pgram_scaled_corners + apex/corner_copy_pts;
import Erdos634.Draft.CollarGeometryM4Wrap
-- CollarPieceContainM4Wrap: apexPieceAt/cornerPieceAt/columnPieceAt_subset_delta4;
import Erdos634.Draft.CollarPieceContainM4Wrap
-- CollarPiecesM4Wrap: delta4_area_sum;
import Erdos634.Draft.CollarPiecesM4Wrap
-- CornerAnglePermCensusWrap: congruentDissection_vertex_census + climber_mandatory;
import Erdos634.Draft.CornerAnglePermCensusWrap
-- FlushContainWrap: exists_counts_of_side (wall contact → nonneg combination);
import Erdos634.Draft.FlushContainWrap
-- FlushCountsWrap: sideLen_eq_or + exists_counts_of_wall;
import Erdos634.Draft.FlushCountsWrap
-- FlushJoinWrap: sum_sideLen_eq_dist + lineChain_nonempty_of_join;
import Erdos634.Draft.FlushJoinWrap
-- FlushSideWrap: endpoints_eq_of_two_level + whole_side_of_two_level;
import Erdos634.Draft.FlushSideWrap
-- ForcedRowWrap: row_count + slot_residual_beta + base_letter_distinct;
import Erdos634.Draft.ForcedRowWrap
-- ForcedSecondRowWrap: type5_bound + all_junctions_type3 + walk_spans;
import Erdos634.Draft.ForcedSecondRowWrap
-- FrontierWrap: gap_south_straddle + base_column_reduction + one_column_per_k;
import Erdos634.Draft.FrontierWrap
-- GaloisMirrorWrap: galoisStable_iff_mirrorInvariant + norm_qconj;
import Erdos634.Draft.GaloisMirrorWrap
-- Gamma2AlphaWrap: gamma2alpha_param (γ=2α family parameterization);
import Erdos634.Draft.Gamma2AlphaWrap
-- GammaCWrap: gammac_witness + gammac_classification;
import Erdos634.Draft.GammaCWrap
-- EpredWedgeClearanceWrap: clearNum_b + a_lt_c (wedge clearance for e=f-1);
import Erdos634.Draft.EpredWedgeClearanceWrap
-- EscapeNoLandingWrap: admissible_no_landing + span_hypotheses_satisfiable;
import Erdos634.Draft.EscapeNoLandingWrap
-- FCAuditWrap: B_never_square_nonvacuous + A_square_forces_mod8;
import Erdos634.Draft.FCAuditWrap
-- FCTwoTilesWrap: three_alpha_two_beta_no_right_angle + N_ne_two;
import Erdos634.Draft.FCTwoTilesWrap
-- FibExtremalWrap: two_le_gap + fib_gap (Fibonacci extremality);
import Erdos634.Draft.FibExtremalWrap
-- FibonacciFamiliesWrap: M_sq_lt_N_iff + fib_extremal_iff;
import Erdos634.Draft.FibonacciFamiliesWrap
-- MarchCoordsWrap: gb_left + offsets_complementary;
import Erdos634.Draft.MarchCoordsWrap
-- MarchFlankWrap: beta_or_gamma + flank_is_beta_or_gamma;
import Erdos634.Draft.MarchFlankWrap
-- MarchFrontierWrap: frontier_induction + frontier_grows;
import Erdos634.Draft.MarchFrontierWrap
-- MarchJunctionsWrap: gamma_gamma_impossible + march_orientation_propagates;
import Erdos634.Draft.MarchJunctionsWrap
-- MarchKillWrap: bg_gb_dies;
import Erdos634.Draft.MarchKillWrap
-- MarchMonotoneWrap: mono_of_no_step + transitions_card_le_one;
import Erdos634.Draft.MarchMonotoneWrap
-- MarchOverlapWrap: wedge_disjoint_at_vertex + coord_pos_of_combo;
import Erdos634.Draft.MarchOverlapWrap
-- MarchRecurrenceWrap: golden_ratio_growth + second_family_shift;
import Erdos634.Draft.MarchRecurrenceWrap
-- MarchRunObjectWrap: aRun_nodup + run_exceptional_le_one;
import Erdos634.Draft.MarchRunObjectWrap
-- MarchRunStepWrap: bg_abscissa + run_step_bg_gb_dies;
import Erdos634.Draft.MarchRunStepWrap
-- LabelCalculusWrap: label_shift + label_tile_angles + alpha_is_two_gamma;
import Erdos634.Draft.LabelCalculusWrap
-- LambdaFactorWrap: P_factor + Q_factor + b_in_ideal;
import Erdos634.Draft.LambdaFactorWrap
-- LayerLinkWrap: layer_rigid_of_exclusions + c_layer_rigid_link;
import Erdos634.Draft.LayerLinkWrap
-- LayerWordWrap: word_classification + no_mixed_word + c_layer_offset;
import Erdos634.Draft.LayerWordWrap
-- LemmaPNode2Wrap: node2_configuration_exists + node2_jam;
import Erdos634.Draft.LemmaPNode2Wrap
-- LemmaPTheoremWrap: lemmaP_no_dissection;
import Erdos634.Draft.LemmaPTheoremWrap
-- LemmaPTreeWrap: hD32 + sr32_lt + MODEL_sides;
import Erdos634.Draft.LemmaPTreeWrap
-- LineParamWrap: dist_lineMap_lineMap + lineChain_param_sum;
import Erdos634.Draft.LineParamWrap
-- LocalCriterionBoundWrap: local_criterion_powerless + witness_23;
import Erdos634.Draft.LocalCriterionBoundWrap
-- MarchStepWrap: march_dies + overshoot_le_one + offset_terminal_dies;
import Erdos634.Draft.MarchStepWrap
-- MemberUniformWrap: fill_iff_counts + gap_one_uniform;
import Erdos634.Draft.MemberUniformWrap
-- MidTriangleWrap: corner_decomp_alphabeta + base_walk_forced;
import Erdos634.Draft.MidTriangleWrap
-- MidTriangleComposedWrap: midTriangle_untileable_composed + prime_case_covered;
import Erdos634.Draft.MidTriangleComposedWrap
-- MidTriangleE1Wrap: midTriangle_untileable;
import Erdos634.Draft.MidTriangleE1Wrap
-- MidTriangleGeneralWrap: midTriangle_untileable_general;
import Erdos634.Draft.MidTriangleGeneralWrap
-- MirrorGaugeWrap: mirrorPt_injective + no_global_orientation_count;
import Erdos634.Draft.MirrorGaugeWrap
-- N1GapWrap: c_overrun + no_cheaper_repair;
import Erdos634.Draft.N1GapWrap
-- N1GapCRangeWrap: c_range_dichotomy + two_vertices_iff;
import Erdos634.Draft.N1GapCRangeWrap
-- N1GapMastGapWrap: card_adm_ge_six + mast_vacuous_at_crossing;
import Erdos634.Draft.N1GapMastGapWrap
-- N1GapSubGoldenWrap: epred_subGolden + epred_prime_mod_twelve;
import Erdos634.Draft.N1GapSubGoldenWrap
-- N1GapSubcasesWrap: adm_iff + card_adm + member_witness;
import Erdos634.Draft.N1GapSubcasesWrap
-- NoCompleteCutWrap: base_to_leg_cut_impossible + apex_cut_impossible;
import Erdos634.Draft.NoCompleteCutWrap
-- NoRightAngleWrap: angles_ne_pi_div_two + no_piece_has_right_angle;
import Erdos634.Draft.NoRightAngleWrap
-- A2BranchRow3Wrap: gamma_wedge_cases + endpoints_exceed_supply;
import Erdos634.Draft.A2BranchRow3Wrap
-- AEdgeReadingWrap: a_edge_west_east (real a-edge reads);
import Erdos634.Draft.AEdgeReadingWrap
-- ARAFormWrap: model_heron + theoremA_N_form_full;
import Erdos634.Draft.ARAFormWrap
-- ARAGeomWrap: area_heron + four_det_sq;
import Erdos634.Draft.ARAGeomWrap
-- ARAWitWrap: nform_at_84 + atom_nform_A4;
import Erdos634.Draft.ARAWitWrap
-- ATDAlgWrap: Ba_eq + atomdiv_of_poly;
import Erdos634.Draft.ATDAlgWrap
-- ATDFinalWrap: atomDiv_L2_full + atom_count;
import Erdos634.Draft.ATDFinalWrap
-- ATDL2Wrap: target_flux_atom + L2atom;
import Erdos634.Draft.ATDL2Wrap
-- ATDWitWrap: apply_atom + witness_A4;
import Erdos634.Draft.ATDWitWrap
-- B84FinalWrap: witness84 + theoremA_at_84;
import Erdos634.Draft.B84FinalWrap
-- B84GeomWrap: b84_exists;
import Erdos634.Draft.B84GeomWrap
-- BADAlgebraWrap: tsum_eq + basealpha_div_of_poly;
import Erdos634.Draft.BADAlgebraWrap
-- BADAnglesWrap: ang_bounds + tile_angles;
import Erdos634.Draft.BADAnglesWrap
-- BADFinalWrap: theoremA_L2;
import Erdos634.Draft.BADFinalWrap
-- BADFinal2Wrap: theoremA_L2_full;
import Erdos634.Draft.BADFinal2Wrap
-- BADFluxTileWrap: mp_injective + flux_pos_R;
import Erdos634.Draft.BADFluxTileWrap
-- BADFluxTile2Wrap: phi_apply + tile_flux_form;
import Erdos634.Draft.BADFluxTile2Wrap
-- BADGridCharWrap: ofAddChar_chi + psi0_apply + psi0_ker;
import Erdos634.Draft.BADGridCharWrap
-- BADInstancesWrap: witness_84 + N_form + seven_rows;
import Erdos634.Draft.BADInstancesWrap
-- BaseBetaQuadCoordWrap: qmul_comm + xiQ_sq_zetaQ_cube;
import Erdos634.Draft.BaseBetaQuadCoordWrap
-- BaseBetaQuadFieldWrap: emb_qmul + V_mul;
import Erdos634.Draft.BaseBetaQuadFieldWrap
-- CellCoordWrap: coord_eq_of_combo + cellUp_cellDown_disjoint;
import Erdos634.Draft.CellCoordWrap
-- CertCoordWrap: detTri_mkTri + det3_split;
import Erdos634.Draft.CertCoordWrap
-- CertGeomWrap: interiors_disjoint_of_separating;
import Erdos634.Draft.CertGeomWrap
-- CertNodeWrap: sr_sq + exists_rp;
import Erdos634.Draft.CertNodeWrap
-- CevianCutWrap: four_AD_sq + cut_triangle_is_scaled_tile;
import Erdos634.Draft.CevianCutWrap
-- CevianRealizationWrap: isoceles_cevian_sq;
import Erdos634.Draft.CevianRealizationWrap
-- CevianSplitWrap: split_count + scaled_piece_sides;
import Erdos634.Draft.CevianSplitWrap
-- ChainEnumWrap: exists_sorted_enum;
import Erdos634.Draft.ChainEnumWrap
-- ChainOrderWrap: no_gap_in_sorted_cover + reach_next;
import Erdos634.Draft.ChainOrderWrap
-- ChainWalkWrap: chain_walk + count_pos;
import Erdos634.Draft.ChainWalkWrap
-- ChordChartWrap: reflected_apex_left_of_mast;
import Erdos634.Draft.ChordChartWrap
-- BADL2Wrap: L2 + Bdry_eq_Bd;
import Erdos634.Draft.BADL2Wrap
-- BADL2WitWrap: alpha_witness_12 + poly_witness_and_control;
import Erdos634.Draft.BADL2WitWrap
-- BADPlacementWrap: kk_period + p_form;
import Erdos634.Draft.BADPlacementWrap
-- BADPlacementGeoWrap: rot_sides + mir_sides;
import Erdos634.Draft.BADPlacementGeoWrap
-- BADPlacementWitWrap: placed_rot + placed_mir;
import Erdos634.Draft.BADPlacementWitWrap
-- BADTargetWrap: w0_neg + target_flux;
import Erdos634.Draft.BADTargetWrap
-- BEdgeReadingWrap: b_edge_west_east + tile_orient;
import Erdos634.Draft.BEdgeReadingWrap
-- BridgeCWrap: g_ends + chain_edge_readings;
import Erdos634.Draft.BridgeCWrap
-- CertBridgeWrap: ofCert_target + ofCert_volume;
import Erdos634.Draft.CertBridgeWrap
-- CevianTiling28Wrap: ceviantiling28_certificate;
import Erdos634.Draft.CevianTiling28Wrap
-- CevianTiling28BridgeWrap: all_pieces_pos + pieces_interiors_disjoint;
import Erdos634.Draft.CevianTiling28BridgeWrap
-- CevianTiling63Wrap: congOK + insideOK;
import Erdos634.Draft.CevianTiling63Wrap
-- CevianTiling63BridgeWrap: all_pieces_pos + pieces_interiors_disjoint;
import Erdos634.Draft.CevianTiling63BridgeWrap
-- CevianUniqueWrap: rival_absent_by_length + rival_present_at_83;
import Erdos634.Draft.CevianUniqueWrap
-- ChainInstanceWrap: edge_image_eq_uIcc + consecutive_edges_meet;
import Erdos634.Draft.ChainInstanceWrap
-- ChordAssemblyWrap: chord_isSegment;
import Erdos634.Draft.ChordAssemblyWrap
-- ChordBetweennessDisjointWrap: openSegment_disjoint_segment_of_wbtw;
import Erdos634.Draft.ChordBetweennessDisjointWrap
-- ChordBetweennessDisjointFarWrap: openSegment_disjoint_segment_of_wbtw_far;
import Erdos634.Draft.ChordBetweennessDisjointFarWrap
-- ChordChartPlanarWrap: member_hypotheses_inhabited;
import Erdos634.Draft.ChordChartPlanarWrap
-- ChordDecompositionChainWrap: chord_decomposition_of_chain;
import Erdos634.Draft.ChordDecompositionChainWrap
-- ChordDecompositionGapGeneralWrap: chord_decomposition_of_gap';
import Erdos634.Draft.ChordDecompositionGapGeneralWrap
-- ChordDecompositionNoStraddleWrap: chord_decomposition_of_no_straddlers;
import Erdos634.Draft.ChordDecompositionNoStraddleWrap
-- ChordDecompositionOneStraddlerWrap: chord_decomposition_one_straddler;
import Erdos634.Draft.ChordDecompositionOneStraddlerWrap
-- ChordDecompositionOneStraddlerFinalWrap: chord_decomposition_one_straddler';
import Erdos634.Draft.ChordDecompositionOneStraddlerFinalWrap
-- ChordDecompositionThreeStraddlersWrap: chord_decomposition_three_straddlers;
import Erdos634.Draft.ChordDecompositionThreeStraddlersWrap
-- ChordDecompositionThreeStraddlersFinalWrap: chord_decomposition_three_straddlers';
import Erdos634.Draft.ChordDecompositionThreeStraddlersFinalWrap
-- ChordEndpointFrontierWrap: chord_endpoint_not_interior;
import Erdos634.Draft.ChordEndpointFrontierWrap
-- ChordEndpointsDistinctWrap: straddle_two_distinct_points;
import Erdos634.Draft.ChordEndpointsDistinctWrap
-- ChordFinsetBaseCaseWrap: not_mem_gap_of_far_precedes;
import Erdos634.Draft.ChordFinsetBaseCaseWrap
-- ChordFlushCoverWrap: upperFlush_edge_endpoints_eq_c;
import Erdos634.Draft.ChordFlushCoverWrap
-- ChordInteriorStraddleWrap: interior_on_line_straddles;
import Erdos634.Draft.ChordInteriorStraddleWrap
-- ChordLengthAdditivityWrap: hausdorff_segment_split;
import Erdos634.Draft.ChordLengthAdditivityWrap
-- ChordOpenSegmentInteriorWrap: straddle_openSegment_interior;
import Erdos634.Draft.ChordOpenSegmentInteriorWrap
-- ChordStraddlerSegmentWrap: straddle_trace_isSegment;
import Erdos634.Draft.ChordStraddlerSegmentWrap
-- ChordTraceRealWrap: isSegment_of_convex_inter_hyperplane;
import Erdos634.Draft.ChordTraceRealWrap
-- CornerAnglePermTargetWrap: cornerAngle_sum_indexed + htarget_of_isosceles;
import Erdos634.Draft.CornerAnglePermTargetWrap
-- ChordDecompositionConsWrap: chord_decomposition_cons;
import Erdos634.Draft.ChordDecompositionConsWrap
-- ChordDecompositionConsGeneralWrap: chord_decomposition_cons';
import Erdos634.Draft.ChordDecompositionConsGeneralWrap
-- ChordDecompositionGapWrap: chord_decomposition_of_gap;
import Erdos634.Draft.ChordDecompositionGapWrap
-- ChordDecompositionTwoStraddlersWrap: chord_decomposition_two_straddlers;
import Erdos634.Draft.ChordDecompositionTwoStraddlersWrap
-- ChordDecompositionTwoStraddlersFinalWrap: chord_decomposition_two_straddlers';
import Erdos634.Draft.ChordDecompositionTwoStraddlersFinalWrap
-- ChordEndpointFrontierGeneralWrap: chord_endpoint_not_interior';
import Erdos634.Draft.ChordEndpointFrontierGeneralWrap
-- ChordFinsetBaseCaseGapWrap: gap_free_of_all_excluded;
import Erdos634.Draft.ChordFinsetBaseCaseGapWrap
-- ChordFinsetChainInjWrap: exists_injective_chain;
import Erdos634.Draft.ChordFinsetChainInjWrap
-- ChordFinsetDegenerateWrap: hausdorff_segment_self + chord_decomposition_of_trivial_gap;
import Erdos634.Draft.ChordFinsetDegenerateWrap
-- ChordFinsetGeometricChainWrap: exists_geometric_chain;
import Erdos634.Draft.ChordFinsetGeometricChainWrap
-- ChordFinsetGeometricChainBaseWrap: not_interior_of_all_excluded;
import Erdos634.Draft.ChordFinsetGeometricChainBaseWrap
-- ChordFinsetInvariantWrap: excl_new_self + excl_carries_forward;
import Erdos634.Draft.ChordFinsetInvariantWrap
-- ChordFinsetPrependInjWrap: injective_prepend_two;
import Erdos634.Draft.ChordFinsetPrependInjWrap
-- ChordFinsetReachLemmaWrap: reach_of_le_all;
import Erdos634.Draft.ChordFinsetReachLemmaWrap
-- ChordFinsetStepCombinedWrap: gap_free_of_finset_step';
import Erdos634.Draft.ChordFinsetStepCombinedWrap
-- ChordFinsetStepGapWrap: gap_free_of_finset_step;
import Erdos634.Draft.ChordFinsetStepGapWrap
-- ChordFinsetWrapperWrap: exists_geometric_chain_of_finset;
import Erdos634.Draft.ChordFinsetWrapperWrap
-- ChordInterfaceWrap: no_interior_vertex + prefix_hit_or_straddle;
import Erdos634.Draft.ChordInterfaceWrap
-- ChordStraddleTotalWrap: straddle_total_eq_sum;
import Erdos634.Draft.ChordStraddleTotalWrap
import Erdos634.Draft.AllWrap
import Erdos634.Draft.CrossingHoldsInBlockWrap
import Erdos634.Draft.ElevenMBridgeWrap
import Erdos634.Draft.Eq105RationalWrap
import Erdos634.Draft.EqSpecAlgebraWrap
import Erdos634.Draft.EqSpecIntWrap
import Erdos634.Draft.EquilateralConicWrap
import Erdos634.Draft.EquilateralScalingWrap
import Erdos634.Draft.EquilateralSpectrumWrap
import Erdos634.Draft.FillerGeneralWrap
import Erdos634.Draft.FinsetSortedListWrap
import Erdos634.Draft.FloorDependsOnJPosWrap
import Erdos634.Draft.PrimeBranchRepairWrap
import Erdos634.Draft.PrimeRegimesWrap
import Erdos634.Draft.R126CBridgeWrap
import Erdos634.Draft.R126CDefsWrap
import Erdos634.Draft.R126CS0Wrap
import Erdos634.Draft.R126CS1Wrap
import Erdos634.Draft.R126CS2Wrap
import Erdos634.Draft.R126CS3Wrap
import Erdos634.Draft.R126CS4Wrap
import Erdos634.Draft.R126CS5Wrap
import Erdos634.Draft.R126TilingWrap
import Erdos634.Draft.R126TilingBridgeWrap
import Erdos634.Draft.R4bSeparationWrap
import Erdos634.Draft.R84TilingWrap
import Erdos634.Draft.R84TilingBridgeWrap
import Erdos634.Draft.R88TilingWrap
import Erdos634.Draft.R88TilingBridgeWrap
import Erdos634.Draft.ReflectBrickWrap
import Erdos634.Draft.ReflectBrickTranslateWrap
import Erdos634.Draft.ResidueRunZ1Wrap
import Erdos634.Draft.RigidityWrap
import Erdos634.Draft.RigidityGeneralWrap
import Erdos634.Draft.RogueAreaWrap
import Erdos634.Draft.RogueChordWrap
import Erdos634.Draft.RogueContainmentWrap
import Erdos634.Draft.RogueFanWrap
import Erdos634.Draft.RunForcingWrap
import Erdos634.Draft.RunOrientationWrap
import Erdos634.Draft.S2RPairs0Wrap
import Erdos634.Draft.S2RPairs1Wrap
import Erdos634.Draft.S2RPairs10Wrap
import Erdos634.Draft.S2RPairs11Wrap
import Erdos634.Draft.S2RPairs12Wrap
import Erdos634.Draft.S2RPairs13Wrap
import Erdos634.Draft.S2RPairs2Wrap
import Erdos634.Draft.S2RPairs3Wrap
import Erdos634.Draft.S2RPairs4Wrap
import Erdos634.Draft.S2RPairs5Wrap
import Erdos634.Draft.S2RPairs6Wrap
import Erdos634.Draft.S2RPairs7Wrap
import Erdos634.Draft.S2RPairs8Wrap
import Erdos634.Draft.S2RPairs9Wrap
import Erdos634.Draft.S2RPairsDefsWrap
import Erdos634.Draft.S2RTilingWrap
import Erdos634.Draft.S2RTilingBridgeWrap
import Erdos634.Draft.SecondEdgeWrap
import Erdos634.Draft.SectorAreaWrap
import Erdos634.Draft.SideForcingWrap
import Erdos634.Draft.SidePRangeWrap
import Erdos634.Draft.SideWalkWrap
import Erdos634.Draft.SideWallWrap
import Erdos634.Draft.SixPlacementsWrap
import Erdos634.Draft.SixtyInvariantWrap
import Erdos634.Draft.SixtyStructureWrap
import Erdos634.Draft.SolvCoreWrap
import Erdos634.Draft.SpectrumLatticeWrap
import Erdos634.Draft.SpectrumZhangWrap
import Erdos634.Draft.TargetShapeWrap
import Erdos634.Draft.TileArithmeticWrap
import Erdos634.Draft.TileAtWrap
import Erdos634.Draft.TilePlacementWrap
import Erdos634.Draft.AllWrap
import Erdos634.Draft.CrossingHoldsInBlockWrap
import Erdos634.Draft.ElevenMBridgeWrap
import Erdos634.Draft.Eq105RationalWrap
import Erdos634.Draft.EqSpecAlgebraWrap
import Erdos634.Draft.EqSpecIntWrap
import Erdos634.Draft.EquilateralConicWrap
import Erdos634.Draft.EquilateralScalingWrap
import Erdos634.Draft.EquilateralSpectrumWrap
import Erdos634.Draft.FillerGeneralWrap
import Erdos634.Draft.FinsetSortedListWrap
import Erdos634.Draft.FloorDependsOnJPosWrap
import Erdos634.Draft.FloorPropagationWrap
import Erdos634.Draft.JunctionWedgeWrap
import Erdos634.Draft.LocalMarchRunWrap
import Erdos634.Draft.LocalMarchRunWitnessWrap
import Erdos634.Draft.N15IsoAWrap
import Erdos634.Draft.N15IsoALiftWrap
import Erdos634.Draft.NoRightAngleTileWrap
import Erdos634.Draft.NonIntegralityWrap
import Erdos634.Draft.NormFormWrap
import Erdos634.Draft.NormalPositionWrap
import Erdos634.Draft.OffsetInteriorWrap
import Erdos634.Draft.OrientBridgeWrap
import Erdos634.Draft.OrientMonoWitnessWrap
import Erdos634.Draft.OrientWordWrap
import Erdos634.Draft.OrientationGaugeWrap
import Erdos634.Draft.OverlapAsymmetryWrap
import Erdos634.Draft.OvershootBlockingWrap
import Erdos634.Draft.PentagonLemmaWrap
import Erdos634.Draft.PgramTiling22Wrap
import Erdos634.Draft.PgramTiling22BridgeWrap
import Erdos634.Draft.PgramTiling22RegionWrap
import Erdos634.Draft.PgramTiling52Wrap
import Erdos634.Draft.PgramTiling52BridgeWrap
-- f=3 analogue of PgramTiling22Region;
import Erdos634.Draft.PgramTiling52RegionWrap
import Erdos634.Draft.PickPointNode2Wrap
import Erdos634.Draft.PinLemmaWrap
import Erdos634.Draft.PinPlumbingWrap
import Erdos634.Draft.PrimeBranchRepairWrap
import Erdos634.Draft.PrimeRegimesWrap
import Erdos634.Draft.R126CBridgeWrap
import Erdos634.Draft.R126CDefsWrap
import Erdos634.Draft.R126CS0Wrap
import Erdos634.Draft.R126CS1Wrap
import Erdos634.Draft.R126CS2Wrap
import Erdos634.Draft.R126CS3Wrap
import Erdos634.Draft.R126CS4Wrap
import Erdos634.Draft.R126CS5Wrap
import Erdos634.Draft.R126TilingWrap
import Erdos634.Draft.R126TilingBridgeWrap
import Erdos634.Draft.R4bSeparationWrap
import Erdos634.Draft.R84TilingWrap
import Erdos634.Draft.R84TilingBridgeWrap
import Erdos634.Draft.R88TilingWrap
import Erdos634.Draft.R88TilingBridgeWrap
import Erdos634.Draft.ReflectBrickWrap
import Erdos634.Draft.ReflectBrickTranslateWrap
import Erdos634.Draft.RegimeSplitWrap
import Erdos634.Draft.RegionDissectionWrap
import Erdos634.Draft.RegionWitnessWrap
import Erdos634.Draft.ResidueRunZ1Wrap
import Erdos634.Draft.RigidityWrap
import Erdos634.Draft.RigidityGeneralWrap
import Erdos634.Draft.RogueAreaWrap
import Erdos634.Draft.RogueChordWrap
import Erdos634.Draft.RogueContainmentWrap
import Erdos634.Draft.RogueFanWrap
import Erdos634.Draft.RogueMirrorWrap
import Erdos634.Draft.Route1FillerWrap
import Erdos634.Draft.RouteOneWrap
import Erdos634.Draft.RouteOneAboveLocalWrap
import Erdos634.Draft.RouteOneApproachWrap
import Erdos634.Draft.RouteOneBoundaryAWrap
import Erdos634.Draft.RouteOneCrossingWrap
import Erdos634.Draft.RouteOneFlankTransferWrap
import Erdos634.Draft.RouteOneStepBridgeWrap
import Erdos634.Draft.RouteOneThroughEdgeWrap
import Erdos634.Draft.RouteOneVEWrap
import Erdos634.Draft.RouteOneVertexKillWrap
import Erdos634.Draft.RunForcingWrap
import Erdos634.Draft.RunOrientationWrap
import Erdos634.Draft.S2RPairs0Wrap
import Erdos634.Draft.S2RPairs1Wrap
import Erdos634.Draft.S2RPairs10Wrap
import Erdos634.Draft.S2RPairs11Wrap
import Erdos634.Draft.S2RPairs12Wrap
import Erdos634.Draft.S2RPairs13Wrap
import Erdos634.Draft.S2RPairs2Wrap
import Erdos634.Draft.S2RPairs3Wrap
import Erdos634.Draft.S2RPairs4Wrap
import Erdos634.Draft.S2RPairs5Wrap
import Erdos634.Draft.S2RPairs6Wrap
import Erdos634.Draft.S2RPairs7Wrap
import Erdos634.Draft.S2RPairs8Wrap
import Erdos634.Draft.S2RPairs9Wrap
import Erdos634.Draft.S2RPairsDefsWrap
import Erdos634.Draft.S2RTilingWrap
import Erdos634.Draft.S2RTilingBridgeWrap
import Erdos634.Draft.SecondEdgeWrap
import Erdos634.Draft.SectorAreaWrap
import Erdos634.Draft.SegmentDenseWrap
import Erdos634.Draft.ShadowCoverWrap
import Erdos634.Draft.SideForcingWrap
import Erdos634.Draft.SidePRangeWrap
import Erdos634.Draft.SideWalkWrap
import Erdos634.Draft.SideWallWrap
import Erdos634.Draft.SixPlacementsWrap
import Erdos634.Draft.SixtyInvariantWrap
import Erdos634.Draft.SixtyStructureWrap
import Erdos634.Draft.SixtyUnsplittableWrap
import Erdos634.Draft.SolvCoreWrap
import Erdos634.Draft.SpectrumLatticeWrap
import Erdos634.Draft.SpectrumZhangWrap
import Erdos634.Draft.SssCongruentWrap
import Erdos634.Draft.SssTriWrap
import Erdos634.Draft.StraddleBoundWrap
import Erdos634.Draft.StraddlerApexWrap
import Erdos634.Draft.StraightEdgeSumsWrap
import Erdos634.Draft.StripIterationWrap
import Erdos634.Draft.StripRigidWrap
import Erdos634.Draft.StubGapWrap
import Erdos634.Draft.SubdivisionWrap
import Erdos634.Draft.SupportFaceWrap
import Erdos634.Draft.SurplusLatticeWrap
import Erdos634.Draft.TPTwoTilesWrap
import Erdos634.Draft.TP_erdosWrap
import Erdos634.Draft.TP_gonthierWrap
import Erdos634.Draft.TP_halesWrap
import Erdos634.Draft.TP_hilbertWrap
import Erdos634.Draft.TP_ramanujanWrap
import Erdos634.Draft.TP_taoWrap
import Erdos634.Draft.TangentConeWrap
import Erdos634.Draft.TargetShapeWrap
import Erdos634.Draft.TargetShapeDissectionWrap
import Erdos634.Draft.ThickAngleIrrationalWrap
import Erdos634.Draft.ThickBlockingLemmasWrap
import Erdos634.Draft.ThickEFminus1ProbeWrap
import Erdos634.Draft.ThickJunctionCoordsWrap
import Erdos634.Draft.ThickJunctionEscapeWrap
import Erdos634.Draft.ThickOffsetFillerWrap
import Erdos634.Draft.ThickPrefixACBWrap
import Erdos634.Draft.ThickWedgeGramWrap
import Erdos634.Draft.ThinCaseAnalysisWrap
import Erdos634.Draft.ThinClosedWrap
import Erdos634.Draft.ThinFamilyWrap
import Erdos634.Draft.ThinHoleWrap
import Erdos634.Draft.ThinPrimesWrap
import Erdos634.Draft.ThreeWordsWrap
import Erdos634.Draft.TileAdjacencyWrap
import Erdos634.Draft.TileArithmeticWrap
import Erdos634.Draft.TileAtWrap
import Erdos634.Draft.TilePlacementWrap
import Erdos634.Draft.Tiling28Wrap
import Erdos634.Draft.Tiling44Wrap
import Erdos634.Draft.Tiling44BridgeWrap
import Erdos634.Draft.Tiling44ControlWrap
import Erdos634.Draft.Tiling44CornerTileWrap
import Erdos634.Draft.Tiling44EqualSideWalkWrap
import Erdos634.Draft.Tiling44EqualSideWalkPosWrap
import Erdos634.Draft.Tiling44NodesWrap
import Erdos634.Draft.Tiling44NodesControlWrap
import Erdos634.Draft.Tiling44ScaleneWrap
import Erdos634.Draft.Tiling44WallFinalWrap
import Erdos634.Draft.Tiling44WallSetupWrap
import Erdos634.Draft.Tiling77Wrap
import Erdos634.Draft.Tiling99Wrap
import Erdos634.Draft.Tiling99BridgeWrap
import Erdos634.Draft.TranslateDissectionWrap
import Erdos634.Draft.TransverseChainWrap
import Erdos634.Draft.TriLawSinWrap
import Erdos634.Draft.TrichotomyCutWrap
import Erdos634.Draft.TwoPiThirdCornersWrap
import Erdos634.Draft.UniformFillWrap
import Erdos634.Draft.UnionDissectionWrap
import Erdos634.Draft.UnsplittableWrap
import Erdos634.Draft.V1AssemblyWrap
import Erdos634.Draft.VacCheckWrap
import Erdos634.Draft.VertexSectorWrap
import Erdos634.Draft.W2CoreWrap
import Erdos634.Draft.WallChainWrap
import Erdos634.Draft.WallDirWrap
import Erdos634.Draft.WallEdgesWrap
import Erdos634.Draft.WallEndpointsWrap
import Erdos634.Draft.WallFaceWrap
import Erdos634.Draft.WallInjectiveWrap
import Erdos634.Draft.WallNeighbourWrap
import Erdos634.Draft.WallSideWrap
import Erdos634.Draft.WallStraddleWrap
import Erdos634.Draft.WallThirdWrap
import Erdos634.Draft.Walls13Wrap
import Erdos634.Draft.WallsCircularWrap
import Erdos634.Draft.WallsClosedWrap
import Erdos634.Draft.WallsWordWrap
import Erdos634.Draft.WbtwChainWrap
import Erdos634.Draft.WbtwDistCoordWrap
import Erdos634.Draft.WbtwGapFreeOfMinimalWrap
import Erdos634.Draft.WbtwGlobalBoundHelpersWrap
import Erdos634.Draft.WbtwMinimalPrecedesRestWrap
import Erdos634.Draft.WbtwOrientedTraceWrap
import Erdos634.Draft.WbtwTraceInTargetWrap
import Erdos634.Draft.WbtwTracesSeparatedWrap
import Erdos634.Draft.WedgeWrap
import Erdos634.Draft.WedgeBoundWrap
import Erdos634.Draft.WedgeExtremalWrap
import Erdos634.Draft.WindowLeverWrap
import Erdos634.Draft.WindowNoGeneralTheoryWrap
import Erdos634.Draft.WindowUnboundedWrap
import Erdos634.Draft.WordCountWrap
import Erdos634.Draft.Z15RealWrap
import Erdos634.Draft.Z2RealWrap
import Erdos634.Draft.Z35RealWrap
import Erdos634.Draft.Z3RealWrap
import Erdos634.Draft.ZZVacuityProbeWrap
import Erdos634.Draft.AllWrap
import Erdos634.Draft.CrossingHoldsInBlockWrap
import Erdos634.Draft.ElevenMBridgeWrap
import Erdos634.Draft.Eq105RationalWrap
import Erdos634.Draft.EqSpecAlgebraWrap
import Erdos634.Draft.EqSpecIntWrap
import Erdos634.Draft.EquilateralConicWrap
import Erdos634.Draft.EquilateralScalingWrap
import Erdos634.Draft.EquilateralSpectrumWrap
import Erdos634.Draft.FillerGeneralWrap
import Erdos634.Draft.FinsetSortedListWrap
import Erdos634.Draft.FloorDependsOnJPosWrap
import Erdos634.Draft.FloorPropagationWrap
import Erdos634.Draft.JunctionWedgeWrap
import Erdos634.Draft.LocalMarchRunWrap
import Erdos634.Draft.LocalMarchRunWitnessWrap
import Erdos634.Draft.N15IsoAWrap
import Erdos634.Draft.N15IsoALiftWrap
import Erdos634.Draft.NoRightAngleTileWrap
import Erdos634.Draft.NonIntegralityWrap
import Erdos634.Draft.NormFormWrap
import Erdos634.Draft.NormalPositionWrap
import Erdos634.Draft.OffsetInteriorWrap
import Erdos634.Draft.OrientBridgeWrap
import Erdos634.Draft.OrientMonoWitnessWrap
import Erdos634.Draft.OrientWordWrap
import Erdos634.Draft.OrientationGaugeWrap
import Erdos634.Draft.OverlapAsymmetryWrap
import Erdos634.Draft.OvershootBlockingWrap
import Erdos634.Draft.PentagonLemmaWrap
import Erdos634.Draft.PgramTiling22Wrap
import Erdos634.Draft.PgramTiling22BridgeWrap
import Erdos634.Draft.PgramTiling22RegionWrap
import Erdos634.Draft.PgramTiling52Wrap
import Erdos634.Draft.PgramTiling52BridgeWrap
import Erdos634.Draft.PickPointNode2Wrap
import Erdos634.Draft.PinLemmaWrap
import Erdos634.Draft.PinPlumbingWrap
import Erdos634.Draft.PinRayWrap
import Erdos634.Draft.PrimeBranchRepairWrap
import Erdos634.Draft.PrimeRegimesWrap
import Erdos634.Draft.R126CBridgeWrap
import Erdos634.Draft.R126CDefsWrap
import Erdos634.Draft.R126CS0Wrap
import Erdos634.Draft.R126CS1Wrap
import Erdos634.Draft.R126CS2Wrap
import Erdos634.Draft.R126CS3Wrap
import Erdos634.Draft.R126CS4Wrap
import Erdos634.Draft.R126CS5Wrap
import Erdos634.Draft.R126TilingWrap
import Erdos634.Draft.R126TilingBridgeWrap
import Erdos634.Draft.R4bSeparationWrap
import Erdos634.Draft.R84TilingWrap
import Erdos634.Draft.R84TilingBridgeWrap
import Erdos634.Draft.R88TilingWrap
import Erdos634.Draft.R88TilingBridgeWrap
import Erdos634.Draft.ReflectBrickWrap
import Erdos634.Draft.ReflectBrickTranslateWrap
import Erdos634.Draft.RegimeSplitWrap
import Erdos634.Draft.RegionDissectionWrap
import Erdos634.Draft.RegionWitnessWrap
import Erdos634.Draft.ResidueRunZ1Wrap
import Erdos634.Draft.RigidityWrap
import Erdos634.Draft.RigidityGeneralWrap
import Erdos634.Draft.RogueAreaWrap
import Erdos634.Draft.RogueChordWrap
import Erdos634.Draft.RogueContainmentWrap
import Erdos634.Draft.RogueFanWrap
import Erdos634.Draft.RogueMirrorWrap
import Erdos634.Draft.Route1FillerWrap
import Erdos634.Draft.RouteOneWrap
import Erdos634.Draft.RouteOneAboveLocalWrap
import Erdos634.Draft.RouteOneApproachWrap
import Erdos634.Draft.RouteOneBoundaryAWrap
import Erdos634.Draft.RouteOneCrossingWrap
import Erdos634.Draft.RouteOneFlankTransferWrap
import Erdos634.Draft.RouteOneStepBridgeWrap
import Erdos634.Draft.RouteOneThroughEdgeWrap
import Erdos634.Draft.RouteOneVEWrap
import Erdos634.Draft.RouteOneVertexKillWrap
import Erdos634.Draft.RunForcingWrap
import Erdos634.Draft.RunOrientationWrap
import Erdos634.Draft.S2RPairs0Wrap
import Erdos634.Draft.S2RPairs1Wrap
import Erdos634.Draft.S2RPairs10Wrap
import Erdos634.Draft.S2RPairs11Wrap
import Erdos634.Draft.S2RPairs12Wrap
import Erdos634.Draft.S2RPairs13Wrap
import Erdos634.Draft.S2RPairs2Wrap
import Erdos634.Draft.S2RPairs3Wrap
import Erdos634.Draft.S2RPairs4Wrap
import Erdos634.Draft.S2RPairs5Wrap
import Erdos634.Draft.S2RPairs6Wrap
import Erdos634.Draft.S2RPairs7Wrap
import Erdos634.Draft.S2RPairs8Wrap
import Erdos634.Draft.S2RPairs9Wrap
import Erdos634.Draft.S2RPairsDefsWrap
import Erdos634.Draft.S2RTilingWrap
import Erdos634.Draft.S2RTilingBridgeWrap
import Erdos634.Draft.SecondEdgeWrap
import Erdos634.Draft.SectorAreaWrap
import Erdos634.Draft.SegmentDenseWrap
import Erdos634.Draft.ShadowCoverWrap
import Erdos634.Draft.SideForcingWrap
import Erdos634.Draft.SidePRangeWrap
import Erdos634.Draft.SideWalkWrap
import Erdos634.Draft.SideWallWrap
import Erdos634.Draft.SixPlacementsWrap
import Erdos634.Draft.SixtyInvariantWrap
import Erdos634.Draft.SixtyStructureWrap
import Erdos634.Draft.SixtyUnsplittableWrap
import Erdos634.Draft.SolvCoreWrap
import Erdos634.Draft.SpectrumLatticeWrap
import Erdos634.Draft.SpectrumZhangWrap
import Erdos634.Draft.SssCongruentWrap
import Erdos634.Draft.SssTriWrap
import Erdos634.Draft.StraddleBoundWrap
import Erdos634.Draft.StraddlerApexWrap
import Erdos634.Draft.StraightEdgeSumsWrap
import Erdos634.Draft.StripIterationWrap
import Erdos634.Draft.StripRigidWrap
import Erdos634.Draft.StubGapWrap
import Erdos634.Draft.SubdivisionWrap
import Erdos634.Draft.SupportFaceWrap
import Erdos634.Draft.SurplusLatticeWrap
import Erdos634.Draft.TPTwoTilesWrap
import Erdos634.Draft.TP_erdosWrap
import Erdos634.Draft.TP_gonthierWrap
import Erdos634.Draft.TP_halesWrap
import Erdos634.Draft.TP_hilbertWrap
import Erdos634.Draft.TP_ramanujanWrap
import Erdos634.Draft.TP_taoWrap
import Erdos634.Draft.TangentConeWrap
import Erdos634.Draft.TargetShapeWrap
import Erdos634.Draft.TargetShapeDissectionWrap
import Erdos634.Draft.ThickAngleIrrationalWrap
import Erdos634.Draft.ThickBlockingLemmasWrap
import Erdos634.Draft.ThickEFminus1ProbeWrap
import Erdos634.Draft.ThickJunctionCoordsWrap
import Erdos634.Draft.ThickJunctionEscapeWrap
import Erdos634.Draft.ThickOffsetFillerWrap
import Erdos634.Draft.ThickPrefixACBWrap
import Erdos634.Draft.ThickWedgeGramWrap
import Erdos634.Draft.ThinCaseAnalysisWrap
import Erdos634.Draft.ThinClosedWrap
import Erdos634.Draft.ThinFamilyWrap
import Erdos634.Draft.ThinHoleWrap
import Erdos634.Draft.ThinPrimesWrap
import Erdos634.Draft.ThreeWordsWrap
import Erdos634.Draft.TileAdjacencyWrap
import Erdos634.Draft.TileArithmeticWrap
import Erdos634.Draft.TileAtWrap
import Erdos634.Draft.TilePlacementWrap
import Erdos634.Draft.Tiling28Wrap
import Erdos634.Draft.Tiling44Wrap
import Erdos634.Draft.Tiling44BridgeWrap
import Erdos634.Draft.Tiling44ControlWrap
import Erdos634.Draft.Tiling44CornerTileWrap
import Erdos634.Draft.Tiling44EqualSideWalkWrap
import Erdos634.Draft.Tiling44EqualSideWalkPosWrap
import Erdos634.Draft.Tiling44NodesWrap
import Erdos634.Draft.Tiling44NodesControlWrap
import Erdos634.Draft.Tiling44ScaleneWrap
import Erdos634.Draft.Tiling44WallFinalWrap
import Erdos634.Draft.Tiling44WallSetupWrap
import Erdos634.Draft.Tiling77Wrap
import Erdos634.Draft.Tiling99Wrap
import Erdos634.Draft.Tiling99BridgeWrap
import Erdos634.Draft.TranslateDissectionWrap
import Erdos634.Draft.TransverseChainWrap
import Erdos634.Draft.TriLawSinWrap
import Erdos634.Draft.TrichotomyCutWrap
import Erdos634.Draft.TwoPiThirdCornersWrap
import Erdos634.Draft.UniformFillWrap
import Erdos634.Draft.UnionDissectionWrap
import Erdos634.Draft.UnsplittableWrap
import Erdos634.Draft.V1AssemblyWrap
import Erdos634.Draft.VacCheckWrap
import Erdos634.Draft.VertexSectorWrap
import Erdos634.Draft.W2CoreWrap
import Erdos634.Draft.WallChainWrap
import Erdos634.Draft.WallDirWrap
import Erdos634.Draft.WallEdgesWrap
import Erdos634.Draft.WallEndpointsWrap
import Erdos634.Draft.WallFaceWrap
import Erdos634.Draft.WallInjectiveWrap
import Erdos634.Draft.WallNeighbourWrap
import Erdos634.Draft.WallSideWrap
import Erdos634.Draft.WallStraddleWrap
import Erdos634.Draft.WallThirdWrap
import Erdos634.Draft.Walls13Wrap
import Erdos634.Draft.WallsCircularWrap
import Erdos634.Draft.WallsClosedWrap
import Erdos634.Draft.WallsWordWrap
import Erdos634.Draft.WbtwChainWrap
import Erdos634.Draft.WbtwDistCoordWrap
import Erdos634.Draft.WbtwGapFreeOfMinimalWrap
import Erdos634.Draft.WbtwGlobalBoundHelpersWrap
import Erdos634.Draft.WbtwMinimalPrecedesRestWrap
import Erdos634.Draft.WbtwOrientedTraceWrap
import Erdos634.Draft.WbtwTraceInTargetWrap
import Erdos634.Draft.WbtwTracesSeparatedWrap
import Erdos634.Draft.WedgeWrap
import Erdos634.Draft.WedgeBoundWrap
import Erdos634.Draft.WedgeExtremalWrap
import Erdos634.Draft.WindowLeverWrap
import Erdos634.Draft.WindowNoGeneralTheoryWrap
import Erdos634.Draft.WindowUnboundedWrap
import Erdos634.Draft.WordCountWrap
import Erdos634.Draft.Z15RealWrap
import Erdos634.Draft.Z2RealWrap
import Erdos634.Draft.Z35RealWrap
import Erdos634.Draft.Z3RealWrap
import Erdos634.Draft.ZZVacuityProbeWrap
import Erdos634.Draft.AnchorClearFormal
-- RowP0Wrap: lem:rowp0 corner-tile uniqueness + vertex identification;
import Erdos634.Draft.RowP0Wrap
-- AvgenWrap: lem:avgen arithmetic exclusions + foot offset;
import Erdos634.Draft.AvgenWrap
-- ClimberDetectWrap: lem:climberdetect brickmate figure + mandatory + escape charge;
import Erdos634.Draft.ClimberDetectWrap
-- RowWordsWrap: lem:rowwords boundary words b^k/a^k/no-b, all three branches;
import Erdos634.Draft.RowWordsWrap
-- RowP1Wrap: lem:rowp1 row-advance arithmetic (junction_ledger, base_distinct, residual);
import Erdos634.Draft.RowP1Wrap
-- RowInductionWrap: cor:rowinduction row count + remainder coords + rogue overrun;
import Erdos634.Draft.RowInductionWrap
-- ChordWrap: lem:chord chord-length identity + tile_contact_face + contact_is_edge;
import Erdos634.Draft.ChordWrap
-- SelfsimWrap: prop:selfsim drop-uniformity arithmetic (selfsim_drop + selfsim_uniform);
import Erdos634.Draft.SelfsimWrap
-- PgramE1Wrap: thm:pgram-e1 three-piece count arithmetic f²+2b+3f²=2N₁;
import Erdos634.Draft.PgramE1Wrap
-- ClosePairsWrap: rem:closepairs y-form + cornerpara filter arithmetic;
import Erdos634.Draft.ClosePairsWrap
-- ThreeCostumesWrap: prop:threecostumes e=1 reduction (span_all_a + row_three_dies_of_span);
import Erdos634.Draft.ThreeCostumesWrap
-- NineToolsWrap: prop:ninetools two tool classes formalized (metric_class_never_fires + no_similarity_invariant_proof);
import Erdos634.Draft.NineToolsWrap
-- LegCornerWrap: prop:legcorner G1+G2 re-exports of GLCG1.corner_G1 + GLCG2k.corner_G2_k;
import Erdos634.Draft.LegCornerWrap
-- InflRigidWrap: thm:inflrigid arithmetic kernel (middle_nine, residual_75/105/200/245, a_b_sides_rigid, c_side_words from Inflation.lean);
import Erdos634.Draft.InflRigidWrap
-- E1ReduceWrap: thm:e1reduce equal-side nb=0/shape + base nb=1/nc=1 arithmetic kernels;
import Erdos634.Draft.E1ReduceWrap
-- LemLadderWrap: lem:ladder descent/sinb/no-base identities + consecutive_gap + step identity;
import Erdos634.Draft.LemLadderWrap
-- CensusScopeWrap: rem:censusscope vertex_census identity + climber_mandatory;
import Erdos634.Draft.CensusScopeWrap
-- InflCruxWrap: cor:inflcrux c-side quantization at k=f + p=0/p=1 words exhibited;
import Erdos634.Draft.InflCruxWrap
-- ShadowWrap: lem:shadow shadow_footage_e1 arithmetic kernel (3f²>1 kills c-corners at e=1);
import Erdos634.Draft.ShadowWrap
-- WallsF2EWrap: cor:wallsf2e base_dichotomy_2e at e=1 + three-letter walls form conclusion;
import Erdos634.Draft.WallsF2EWrap
-- ColumnLinesWrap: lem:columnlines angle_is_alpha + apex identities + distance formula;
import Erdos634.Draft.ColumnLinesWrap
-- WallClimbWrap: lem:wallclimb wedge_is_alpha + wedge_fill_unique + cos_alpha_not_niven;
import Erdos634.Draft.WallClimbWrap
-- Eq105Wrap: thm:eq105 rational-angle branch (d·k²≠105 for d|6);
import Erdos634.Draft.Eq105Wrap
-- DecidableWrap: thm:decidable prime case (prime_tile_count_iff gives Decidable);
import Erdos634.Draft.DecidableWrap
import Erdos634.Draft.VacuousCompanionWrap
-- E2StripArith: rem:e2strip arithmetic kernel — ef∤f(f²−e²) and ef∤e³ for IsCoprime e f, e≥2, f≥3;
import Erdos634.Draft.E2StripArith
-- F1N3: prop:reduction N=3 F1-shape gap — f1_N3_free (0 sorry, standard axioms); closes (P=3,R=0)
import Erdos634.Draft.F1N3
-- PropReductionN3: prop:reduction for prime N≥3, all shapes — tp_prime_excluded_ge3
-- (0 sorry, standard axioms); assembles N=3 case (N3EqCase+ISUCore+F1N3+r8_prime_free_any)
import Erdos634.Draft.PropReductionN3
-- CheckPWrap: registers Refl.CheckP (4-vertex/parallelogram reflective checker) in AllNew9→All;
import Erdos634.Draft.CheckPWrap
-- PropReductionFull: prop:reduction for ALL prime N≥2 (incl. N=2 via two_piece_cut_of_twoPiThree);
-- N≥3 zero extra axioms; N=2 one named plane-topology axiom; axioms: [propext, Classical.choice,
import Erdos634.Draft.PropReductionFull
