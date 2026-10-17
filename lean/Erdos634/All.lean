-- Memory split.  `Erdos634.All` does not import any module whose import closure contains a search
-- certificate (`Refl.M*`): those 84 modules are aggregated in `Erdos634.AllSpectrum`, and the threshold program of the
-- base-beta row in `Erdos634.AllThreshold`.  Importing everything in one process needs about 9.5 GB of oleans.
-- Build `All`, `AllSpectrum` and `AllThreshold` one at a time, plus the `AllCert*` aggregates for files that use the large certificates.
-- Certificate-free modules of the former aggregates are imported directly below.
import Erdos634.LadderCeiling
import Erdos634.PrimeBranchRepair
import Erdos634.R4bSeparation
import Erdos634.WindowUnbounded
import Erdos634.NoRightAngleTile
import Erdos634.WindowNoGeneralTheory
import Erdos634.WindowLever
import Erdos634.FloorDependsOnJPos
import Erdos634.BoundaryRigidInsufficient
import Erdos634.CevianUnique
import Erdos634.B3PrimeBlocker
import Erdos634.ApexChordCriterion
import Erdos634.BeesonDelta
import Erdos634.ClearanceLemma
import Erdos634.NoCompleteCut
import Erdos634.ExclusionCriterion
import Erdos634.RegimeSplit
import Erdos634.MidTriangleComposed
import Erdos634.RunForcing
import Erdos634.MidTriangleGeneral
import Erdos634.BeesonBoundary
import Erdos634.BeesonOmega
import Erdos634.TargetShapeDissection
import Erdos634.TargetShape
import Erdos634.CevianRealization
import Erdos634.ScaleMap
import Erdos634.BeesonGraphH
import Erdos634.BeesonDef5
import Erdos634.BeesonDirections
import Erdos634.BeesonThm2Hyp
import Erdos634.FlushContain
import Erdos634.FlushCounts
import Erdos634.FlushJoin
import Erdos634.FlushSide
import Erdos634.MidTriangleE1
import Erdos634.BeesonThm2Graph
import Erdos634.CevianCut
import Erdos634.LineParam
import Erdos634.PgramTiling22Region
import Erdos634.PgramTiling52Region
import Erdos634.OrientMonoWitness
import Erdos634.CornerAnglePermTarget
import Erdos634.CornerAnglePermCensus
import Erdos634.RouteOneAboveLocal
import Erdos634.RouteOneFlankTransfer
import Erdos634.RouteOneVE
import Erdos634.RegionWitness
import Erdos634.RegionDissection
import Erdos634.EqSpecInt
import Erdos634.VacCheck
import Erdos634.AnchoredChain
import Erdos634.AngleArithmetic
import Erdos634.AngleSumAssembled
import Erdos634.AngleSumDissection
import Erdos634.AngleSumScope
import Erdos634.ApexRigidity
import Erdos634.BAdjacency
import Erdos634.BaseAlphaBetaPrime
import Erdos634.BaseBetaCorners
import Erdos634.BaseBetaE1
import Erdos634.BaseBetaMod12
import Erdos634.BaseBetaQuadCoord
import Erdos634.BaseBetaQuadField
import Erdos634.BaseBetaWalkArith
import Erdos634.BaseBetaWalks
import Erdos634.Beeson3NotPrime
import Erdos634.FourCompCongruence
import Erdos634.LocalCriterionBound
import Erdos634.LocalMarchRun
import Erdos634.LocalMarchRunWitness
import Erdos634.RouteOneStepBridge
import Erdos634.OvershootBlocking
import Erdos634.SpectrumZhang
import Erdos634.AdmissibleSpectrum
import Erdos634.Eq105Rational
import Erdos634.CornerParaLink
import Erdos634.EdgeWordConversion
import Erdos634.NilpotentTower
import Erdos634.JunctionAutomaton
import Erdos634.DualGraph44
import Erdos634.FCStep1
import Erdos634.FCStep2
import Erdos634.FCAudit
import Erdos634.CChord
import Erdos634.CevianSplit
import Erdos634.CevianTiling28
import Erdos634.CevianTiling63
import Erdos634.ChordDecomp
import Erdos634.ChordInterface
import Erdos634.Collar
import Erdos634.ConeScaling
import Erdos634.CongruentAngles
import Erdos634.Contiguity
import Erdos634.CorridorLowStop
import Erdos634.CosetPropagation
import Erdos634.DirectionGroup
import Erdos634.Dissection
import Erdos634.TileAt
import Erdos634.CongruentTileEdges
import Erdos634.CornerBaseEdgesReal
import Erdos634.ApexEdgesReal
import Erdos634.WallDir
import Erdos634.WallThird
import Erdos634.BaseWalkGeneral
import Erdos634.BaseDecomposition
import Erdos634.EdgeType
import Erdos634.AEdgeReading
import Erdos634.SideWalk
import Erdos634.IsoTri
import Erdos634.SssTri
import Erdos634.BEdgeReading
import Erdos634.SubDissection
import Erdos634.E2Join
import Erdos634.EdgeChain
import Erdos634.EquilateralConic
import Erdos634.FanKill
import Erdos634.FanPruneSound
import Erdos634.FanStep
import Erdos634.FibonacciFamilies
import Erdos634.ForcedRow
import Erdos634.Frontier
import Erdos634.Gamma2Alpha
import Erdos634.GammaC
import Erdos634.GeneralPillars
import Erdos634.Inflation
import Erdos634.Interface
import Erdos634.IntervalChain
import Erdos634.InvariantCore
import Erdos634.InvariantProduct
import Erdos634.IsoAlphaPrime
import Erdos634.LabelCalculus
import Erdos634.LadderInvariant
import Erdos634.LambdaFactor
import Erdos634.MarchAssembly
import Erdos634.MarchJunctions
import Erdos634.MarchRecurrence
import Erdos634.MasterLemmas
import Erdos634.MidTriangle
import Erdos634.Mod12
import Erdos634.OffsetForcing
import Erdos634.OrderForcing
import Erdos634.OrientBridge
import Erdos634.Pentagon
import Erdos634.PentagonLemma
import Erdos634.PgramTiling22
import Erdos634.PgramTiling52
import Erdos634.PinBuffer
import Erdos634.PinLemma
import Erdos634.PinPlumbing
import Erdos634.PinRay
import Erdos634.Primitives
import Erdos634.Rationality
import Erdos634.RationalityFree
import Erdos634.Rigidity
import Erdos634.RogueChord
import Erdos634.RogueContainment
import Erdos634.RogueFan
import Erdos634.RogueMirror
import Erdos634.RunOrientation
import Erdos634.ScaleBreak
import Erdos634.ScaleRigidity
import Erdos634.SecondEdge
import Erdos634.SectorArea
import Erdos634.SeedDegenerate
import Erdos634.SegmentDense
import Erdos634.SideNoB
import Erdos634.SidePRange
import Erdos634.Tiling44Scalene
import Erdos634.Tiling44WallSetup
import Erdos634.Tiling44WallFinal
import Erdos634.Tiling44EqualSideWalk
import Erdos634.Tiling44CornerTile
import Erdos634.Tiling44EqualSideWalkPos
import Erdos634.ReflectBrick
import Erdos634.CoversGeneral
import Erdos634.ReflectBrickTranslate
import Erdos634.SupportFace
import Erdos634.SurplusLattice
import Erdos634.TangentCone
import Erdos634.Tiling28
import Erdos634.Tiling44
import Erdos634.Tiling77
import Erdos634.Tiling99
import Erdos634.TransverseChain
import Erdos634.TwoPiThirdCorners
import Erdos634.V1Assembly
import Erdos634.V1Gaps
import Erdos634.VertexSector
import Erdos634.W2Core
import Erdos634.WalkEquation
import Erdos634.WallChain
import Erdos634.Walls13
import Erdos634.Wedge
import Erdos634.ZhangTargets
-- All.lean — aggregator. Importing this module pulls in the entire corpus, so compiling it is a
-- single end-to-end check that every module elaborates and that their olean interfaces agree.
--
-- WHY THIS EXISTS. The library root `Erdos634.lean` is not an index: it is a substantive module (the
-- arithmetic layer of the prime case) that imports only Mathlib. Consequently `lake build`, whose
-- default target is that root, compiles one file and not the corpus. Modules here are otherwise
-- largely standalone — only `Dissection`, `E2Join`, `SecondEdge` and `Frontier` import a sibling —
-- so nothing forced them to be checked together until now.
--
-- To verify the whole corpus:
--     lean --root=. lean/All.lean
--
--   `Dissection.hasAngleSums` is a theorem) added.
import Erdos634.MarchStep
import Erdos634.WedgeExtremal
import Erdos634.JunctionWedge
import Erdos634.EdgeDisjoint
import Erdos634.ChainOrder
import Erdos634.ChainInstance
import Erdos634.BaseSelection
import Erdos634.WallEdges
import Erdos634.ShadowCover
import Erdos634.ChainEnum
import Erdos634.BaseChain
import Erdos634.WallEndpoints
import Erdos634.WallFace
import Erdos634.OrientWord
import Erdos634.Placement
import Erdos634.WallSide
import Erdos634.WallInjective
import Erdos634.BridgeC
import Erdos634.BaseCountsE1
import Erdos634.GammaCascade
import Erdos634.VertexFigureReal
import Erdos634.NonIntegrality
import Erdos634.StubGap
import Erdos634.Unsplittable
import Erdos634.NormForm
import Erdos634.FibExtremal
import Erdos634.SolvCore
import Erdos634.TilePlacement
import Erdos634.TriLawSin
import Erdos634.SideWall
import Erdos634.DissectionMap
import Erdos634.Subdivision
import Erdos634.ChainWalk
import Erdos634.EqSpecAlgebra
import Erdos634.MemberUniform
import Erdos634.AngleThreshold
import Erdos634.FillerGeneral
import Erdos634.RigidityGeneral
import Erdos634.InterfaceFloor
import Erdos634.NoRightAngle
import Erdos634.SpectrumLattice
import Erdos634.MarchRun
import Erdos634.MarchCoords
import Erdos634.MarchOverlap
import Erdos634.MarchKill
import Erdos634.MarchRunStep
import Erdos634.MarchFrontier
import Erdos634.MarchMonotone
import Erdos634.MarchFlank
import Erdos634.MarchRunObject
import Erdos634.RouteOne
import Erdos634.RouteOneVertexKill
import Erdos634.RouteOneApproach
import Erdos634.RouteOneWallOnly
import Erdos634.N1Gap
import Erdos634.ConvexCover
import Erdos634.CongruentArea
import Erdos634.InteriorCoord
import Erdos634.CellCoord
import Erdos634.Compose
import Erdos634.Ladder
import Erdos634.Realizable
import Erdos634.AreaDet
import Erdos634.SssCongruent
import Erdos634.CertBridge
import Erdos634.CertGeom
import Erdos634.CertCoord
import Erdos634.Z15Real
import Erdos634.Z35Real
import Erdos634.Tiling44Bridge
import Erdos634.CevianTiling63Bridge
import Erdos634.Tiling99Bridge
import Erdos634.ElevenMBridge
import Erdos634.PgramTiling22Bridge
import Erdos634.PgramTiling52Bridge
import Erdos634.UnionDissection
import Erdos634.TranslateDissection
import Erdos634.CollarGeometryM4
import Erdos634.CollarDisjointM4
import Erdos634.CollarContainM4
import Erdos634.CollarAreaM4
import Erdos634.CollarPiecesM4
import Erdos634.CollarPieceContainM4
import Erdos634.CollarDisjointColM4
import Erdos634.CollarAssembleM4
import Erdos634.CollarCongruentM4
import Erdos634.TileAdjacency
import Erdos634.ChordTraceReal
import Erdos634.ChordStraddleTotal
import Erdos634.ChordFlushCover
import Erdos634.ChordAssembly
import Erdos634.ChordInteriorStraddle
import Erdos634.ChordStraddlerSegment
import Erdos634.ChordEndpointFrontier
import Erdos634.ChordOpenSegmentInterior
import Erdos634.ChordDecompositionNoStraddle
import Erdos634.ChordEndpointsDistinct
import Erdos634.ChordDecompositionGap
import Erdos634.ChordLengthAdditivity
import Erdos634.ChordDecompositionOneStraddler
import Erdos634.ChordBetweennessDisjoint
import Erdos634.ChordDecompositionOneStraddlerFinal
import Erdos634.ChordDecompositionTwoStraddlers
import Erdos634.ChordBetweennessDisjointFar
import Erdos634.ChordDecompositionTwoStraddlersFinal
import Erdos634.ChordDecompositionThreeStraddlers
import Erdos634.ChordDecompositionThreeStraddlersFinal
import Erdos634.WbtwChain
import Erdos634.WbtwOrientedTrace
import Erdos634.WbtwTracesSeparated
import Erdos634.WbtwDistCoord
import Erdos634.ChordDecompositionCons
import Erdos634.WbtwGapFreeOfMinimal
import Erdos634.WbtwMinimalPrecedesRest
import Erdos634.ChordDecompositionChain
import Erdos634.WbtwTraceInTarget
import Erdos634.ChordFinsetBaseCase
import Erdos634.ChordFinsetBaseCaseGap
import Erdos634.ChordFinsetStepGap
import Erdos634.ChordFinsetInvariant
import Erdos634.ChordFinsetDegenerate
import Erdos634.ChordFinsetStepCombined
import Erdos634.ChordDecompositionGapGeneral
import Erdos634.ChordDecompositionConsGeneral
import Erdos634.ChordFinsetPrependInj
import Erdos634.ChordFinsetChainInj
import Erdos634.ChordEndpointFrontierGeneral
import Erdos634.ChordFinsetGeometricChainBase
import Erdos634.WbtwGlobalBoundHelpers
import Erdos634.ChordFinsetReachLemma
import Erdos634.ChordFinsetGeometricChain
import Erdos634.FinsetSortedList
import Erdos634.ChordFinsetWrapper
import Erdos634.RouteOneThroughEdge
import Erdos634.CornerAnglePerm
import Erdos634.CensusSideRelation
import Erdos634.GlobalSystem
import Erdos634.FCTwoTiles
import Erdos634.TPTwoTiles
import Erdos634.OrientationGauge
import Erdos634.OverlapAsymmetry
import Erdos634.MirrorGauge
import Erdos634.GaloisMirror
import Erdos634.BentWallCoupling
import Erdos634.Crux1
import Erdos634.ZZVacuityProbe
import Erdos634.PincerLadder
import Erdos634.SixtyInvariant
import Erdos634.ThinHole
import Erdos634.TP_hales
import Erdos634.MirrorKill
import Erdos634.EscapeNoLanding
import Erdos634.N1GapSubcases
import Erdos634.N1GapMastGap
import Erdos634.N1GapCRange
import Erdos634.N1GapSubGolden
import Erdos634.EpredBaseColumns
import Erdos634.EpredWedgeClearance
import Erdos634.BaseBetaTargetCoord
import Erdos634.RouteOneBoundaryA
import Erdos634.NormalPosition
import Erdos634.RouteOneCrossing
import Erdos634.EpredColumnKill
import Erdos634.MarchKills
import Erdos634.MarchKillsFan
import Erdos634.ThickBlockingLemmas
import Erdos634.ThickPrefixACB
import Erdos634.ThickJunctionEscape
import Erdos634.ResidueRunZ1
import Erdos634.ThickJunctionCoords
import Erdos634.ThickAngleIrrational
import Erdos634.ThickWedgeGram
import Erdos634.ThickOffsetFiller
import Erdos634.ThickEFminus1Probe
import Erdos634.MarchInduction
import Erdos634.MarchSlots
import Erdos634.RunPartition
import Erdos634.MarchCompose
import Erdos634.E1NormalForm
import Erdos634.E1BaseWord
import Erdos634.PlacementCompleteness
import Erdos634.SixPlacements
import Erdos634.LemmaPNode2
import Erdos634.PickPointNode2
import Erdos634.Tiling44Control
import Erdos634.CertNode
import Erdos634.LemmaPTree
import Erdos634.LemmaPTheorem
import Erdos634.Tiling44Nodes
import Erdos634.Tiling44NodesControl
import Erdos634.Draft.ApexPlacement
import Erdos634.Draft.ApexLegWord
import Erdos634.Draft.ApexFrameReal
import Erdos634.Draft.ApexNormal
import Erdos634.Draft.ApexR2Frame
import Erdos634.Draft.ApexWitness44
import Erdos634.Draft.CornerAdjacency
import Erdos634.Draft.NearBaseVertex
import Erdos634.Draft.NearBase
import Erdos634.Draft.NearBaseKill
import Erdos634.Draft.NearBaseBridge
import Erdos634.Draft.HalfTurnR3R4
import Erdos634.Draft.HalfTurnR3R4Glue
import Erdos634.Draft.HalfTurnR3R4Order
import Erdos634.Draft.TileIdent
import Erdos634.Draft.TraceCovering
import Erdos634.Draft.MaximalStretch
import Erdos634.Draft.InterfaceMultiset
import Erdos634.Draft.MirrorStripR2
import Erdos634.Draft.MirrorStripR2Glue
import Erdos634.Draft.MirrorStripR2Real
import Erdos634.Draft.RowWallReal
import Erdos634.Draft.RowWallLocal
import Erdos634.Draft.RowWallInduction
import Erdos634.Draft.MirrorLevelQReal
import Erdos634.Draft.LemmaGRowReal
import Erdos634.Draft.LemmaGADReal
import Erdos634.Draft.LemmaGCornerReal
import Erdos634.Draft.ConvergingWallsLocal
import Erdos634.Draft.ConvergingWallsReal
import Erdos634.Draft.RowLineP2Real
import Erdos634.Draft.PatchCompleteReal
import Erdos634.Draft.LcPhaseReal
import Erdos634.Draft.L3MReal
import Erdos634.Draft.Level2LemmaGReal
import Erdos634.Draft.HalfTurnR4Real
import Erdos634.Draft.RowWallWitness44
import Erdos634.Draft.ConvergingWallsWitness44
import Erdos634.Draft.ModelWitnessE
import Erdos634.Draft.TheoremHCongruent
import Erdos634.Draft.R1Frame
import Erdos634.Draft.R1Pierce
import Erdos634.Draft.R1Kill
import Erdos634.Draft.R1Final
import Erdos634.Draft.R1TileWitness
import Erdos634.Draft.ThickEFminus1Steps
import Erdos634.Draft.FluxBoundary
import Erdos634.Draft.FluxCBoundary
import Erdos634.Draft.FluxCBoundaryWitness
import Erdos634.Draft.FluxCRow12
import Erdos634.Draft.FluxCRow12Witness
import Erdos634.Draft.FluxCRow2
import Erdos634.Draft.FluxCRow2Witness
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.FluxCRow5Complete
import Erdos634.Draft.FluxCRow5Witness
import Erdos634.Draft.FluxCSimilar
import Erdos634.Draft.FluxCSimilarWitness
import Erdos634.Draft.FluxCWitness99
import Erdos634.Draft.FluxCancel
import Erdos634.Draft.FluxCore
import Erdos634.Draft.FluxDRem45
import Erdos634.Draft.FluxDRow11
import Erdos634.Draft.FluxDRow11Prime
import Erdos634.Draft.FluxDRow11PrimeWitness
import Erdos634.Draft.FluxDRow11Witness
import Erdos634.Draft.FluxDRow12a
import Erdos634.Draft.FluxDRow12b
import Erdos634.Draft.FluxDRow12bWitness
import Erdos634.Draft.FluxDRow13
import Erdos634.Draft.FluxDRow13Witness
import Erdos634.Draft.FluxDRow2D
import Erdos634.Draft.FluxDRow2DWitness
import Erdos634.Draft.FluxDRow2K
import Erdos634.Draft.FluxDRow2KWitness
import Erdos634.Draft.FluxDRow2S1
import Erdos634.Draft.FluxDRow2S1Witness
import Erdos634.Draft.FluxDRow4
import Erdos634.Draft.FluxDRow4Bk
import Erdos634.Draft.FluxDRow4L8
import Erdos634.Draft.FluxDRow4L8Witness
import Erdos634.Draft.FluxDRow4Witness
import Erdos634.Draft.FluxDSideWord
import Erdos634.Draft.FluxE2Pi3Boundary
import Erdos634.Draft.FluxE2Pi3Row7
import Erdos634.Draft.FluxE2Pi3Row9
import Erdos634.Draft.FluxERow2C
import Erdos634.Draft.FluxERow2E
import Erdos634.Draft.FluxERow2Q
import Erdos634.Draft.FluxERow2R
import Erdos634.Draft.FluxERow2S
import Erdos634.Draft.FluxERow9Arith
import Erdos634.Draft.FluxGridWitness
import Erdos634.Draft.FluxGrids
import Erdos634.Draft.FluxInterior
import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxPaperWitness
import Erdos634.Draft.FluxRow11
import Erdos634.Draft.FluxRow11Witness
import Erdos634.Draft.FluxRow2
import Erdos634.Draft.FluxRow2Witness
import Erdos634.Draft.FluxRow4
import Erdos634.Draft.FluxRow4Witness
import Erdos634.Draft.FluxTurn
import Erdos634.Draft.FluxValue
import Erdos634.Draft.FluxWeight
import Erdos634.Draft.FluxWitness
import Erdos634.Draft.FluxGRow3
import Erdos634.Draft.FluxGRow3Weight
import Erdos634.Draft.FluxFRow14
import Erdos634.Draft.FluxFRow15
import Erdos634.Draft.FluxFRow15Cases
import Erdos634.Draft.FluxFRow14Bridge
import Erdos634.Draft.FluxDRow4Bridge
import Erdos634.Draft.FluxFRow15Bridge
import Erdos634.Draft.FluxFRow14Derive
import Erdos634.Draft.FluxHBreakpointsInjectivity
import Erdos634.Draft.FluxHBreakpointsPoint
import Erdos634.Draft.FluxHBreakpointsFrontier
import Erdos634.Draft.FluxGRow3Cancel
import Erdos634.Draft.FluxGRow3Placement
import Erdos634.Draft.FluxGRow3Witness
import Erdos634.Draft.FluxFRow15Cases2
import Erdos634.Draft.FluxCRow5Bridge
import Erdos634.Draft.FluxFRow15Calculus
import Erdos634.Draft.FluxGRow3LemmaA
import Erdos634.Draft.FluxGRow3Step1
import Erdos634.Draft.FluxHBreakpointsCounting
-- integration-tested as Draft/IntegrationTest5.lean.
import Erdos634.Draft.FluxDRow4Boundary
-- integration-tested as Draft/IntegrationTest7.lean.
import Erdos634.Draft.FluxDRow4L8AC
-- integration-tested as Draft/IntegrationTest8.lean.
import Erdos634.Draft.FluxDRow4EdgeReading
import Erdos634.Draft.FluxGRow3TargetCoords
import Erdos634.Draft.FluxGRow3TargetDirs
import Erdos634.Draft.FluxGRow3Step5
import Erdos634.Draft.FluxGRow3AngleWitness
-- P106, P107, P108); integration-tested as Draft/IntegrationTest13.lean.
import Erdos634.Draft.FluxGRow3AngleWitnessDissection
import Erdos634.Draft.FluxGRow3WitnessBridge
import Erdos634.Draft.FluxGRow3WitnessFinal
-- flux instantiation, and the row3 N=2 Step 3/6 splice capstone `row3_N2_full_identity`),
-- Draft/IntegrationTest14.lean.
import Erdos634.Draft.FluxGRow3DirAngle
import Erdos634.Draft.FluxGRow3SharedGrid
import Erdos634.Draft.FluxGRow3ConcreteFlux
import Erdos634.Draft.FluxGRow3Step3N2Final
-- Draft/IntegrationTest15.lean.
import Erdos634.Draft.FluxGRow3Step6N2
-- integration-tested as Draft/IntegrationTest16.lean.
import Erdos634.Draft.FluxCRow5SideBridge
-- integration-tested as Draft/IntegrationTest17.lean.
import Erdos634.Draft.FluxCRow5EdgeDirection
import Erdos634.Draft.FluxCRow5E7bFinal
-- P125, P126, P127); integration-tested as Draft/IntegrationTest19.lean.
import Erdos634.Draft.FluxDOrientation
import Erdos634.Draft.FluxDOrientationChirality
import Erdos634.Draft.FluxDOrientationWall
-- the e = 1 family theorem for every f >= 2 (f=2 via r1_n11, f>=3 via E1BaseWord)
import Erdos634.Draft.E1FamilyFull
-- prime corollary: for f>=2, if 3f²-1 is prime it is not a tile count.
import Erdos634.Draft.E1FamilyPrimeClause
-- the base-β theorem as one statement (union of three clauses)
import Erdos634.Draft.BaseBetaFullUnc
-- lem:cancel at the paper's weights
import Erdos634.Draft.FluxPaperLemCancel
-- cor:int as written (anchored frame, quotient form)
import Erdos634.Draft.FluxPaperCorIntAnchored
import Erdos634.Draft.FluxDRow4AnyLabel
import Erdos634.Draft.FluxCRow5Hr0
import Erdos634.Draft.FluxCRow5TwoPiThreeFull
import Erdos634.Draft.FluxFRow14F4
import Erdos634.Draft.FluxFRow14Close
import Erdos634.Draft.FluxGRow3Step6Alg
import Erdos634.Draft.FluxGRow3Relabel
import Erdos634.Draft.FluxGRow3RP
import Erdos634.Draft.FluxGRow3RPWitness
import Erdos634.Draft.FluxFRow14AnyLabel
import Erdos634.Draft.FluxGRow3RPAnyLabel
import Erdos634.Draft.FluxGRow3RPAnyLabelWitness
import Erdos634.Draft.FluxFRow15Conj
import Erdos634.Draft.FluxFRow15Setup
import Erdos634.Draft.FluxFRow15Close
import Erdos634.Draft.FluxFRow15AnyLabel
import Erdos634.Draft.CaseACorF
import Erdos634.Draft.Rows11_13AnyLabel
import Erdos634.Draft.Tiling77Bridge
import Erdos634.Draft.Row14JointWitness
import Erdos634.Draft.Row15JointWitness
import Erdos634.Draft.CaseACorFIntUnits
import Erdos634.Draft.CaseALemmaH
import Erdos634.Draft.CaseALemmaHWitness
import Erdos634.Draft.CaseALemmaHDegree
import Erdos634.Draft.CaseALemmaHExc
import Erdos634.Draft.CaseALemmaHGlue
import Erdos634.Draft.CaseALemmaHExc2
import Erdos634.Draft.CaseALemmaHPiFour
import Erdos634.Draft.LemmaSB1
import Erdos634.Draft.LemmaSB1Hurwitz
import Erdos634.Draft.LemmaSG
import Erdos634.Draft.CaseALemmaVCore
import Erdos634.Draft.CaseALemmaVSines
import Erdos634.Draft.CaseALemmaVDissection
import Erdos634.Draft.CaseALemmaVWitness
import Erdos634.Draft.CaseALemmaKStar
import Erdos634.Draft.A1EdgeDirections
import Erdos634.Draft.CaseALemmaF
import Erdos634.Draft.CaseALemmaFWritten
import Erdos634.Draft.A1ChainClass1D
import Erdos634.Draft.A1SharedClass
import Erdos634.Draft.A1CornerLattice
import Erdos634.Draft.LemmaSCDist
import Erdos634.Draft.LemmaSC
import Erdos634.Draft.LemmaSCCrit
import Erdos634.Draft.LemmaSN
import Erdos634.Draft.LemmaSG2
import Erdos634.Draft.LemmaSR
import Erdos634.Draft.LemmaSHalving
import Erdos634.Draft.LemmaSG2Avoid
import Erdos634.Draft.A1FieldClause
import Erdos634.Draft.DirichletCRT
import Erdos634.Draft.CaseALemmaK1
import Erdos634.Draft.CaseALemmaK1Witness
import Erdos634.Draft.KMomentStd
import Erdos634.Draft.KMomentTri
import Erdos634.Draft.KMomentDet
import Erdos634.Draft.KConjField
import Erdos634.Draft.KConjAe
import Erdos634.Draft.KConjAngle
import Erdos634.Draft.KConjNormal
import Erdos634.Draft.KConjLemmaK
import Erdos634.Draft.KConjLemmaKWitness
import Erdos634.Draft.CaseAR0c
import Erdos634.Draft.LemmaSGpp -- Lemma S odd branch
import Erdos634.Draft.LemmaSGprime -- Lemma S odd branch
import Erdos634.Draft.LemmaSPhi -- Lemma S odd branch
import Erdos634.Draft.LemmaSIso -- Lemma S odd branch
import Erdos634.Draft.LemmaSElim -- Lemma S odd branch
import Erdos634.Draft.LemmaSParity -- Lemma S odd branch
import Erdos634.Draft.LemmaSFC -- Lemma S odd branch
import Erdos634.Draft.LemmaSFCPair -- Lemma S odd branch
import Erdos634.Draft.LemmaSL -- Lemma S odd branch
import Erdos634.Draft.LemmaSR3 -- Lemma S odd branch
import Erdos634.Draft.LemmaSR2a -- Lemma S odd branch
import Erdos634.Draft.LemmaSR1p -- Lemma S odd branch
import Erdos634.Draft.LemmaSF3 -- Lemma S odd branch
import Erdos634.Draft.LemmaSR2b12 -- Lemma S odd branch
import Erdos634.Draft.LemmaSR1F2 -- Lemma S odd branch
import Erdos634.Draft.LemmaSFCOdd -- Lemma S odd branch
import Erdos634.Draft.LemmaSOdd -- Lemma S odd branch
import Erdos634.Draft.LemmaSOddAll -- Lemma S odd branch
import Erdos634.Draft.LemmaSEvenT -- Lemma S even branch + R0c
import Erdos634.Draft.LemmaSEvenComp -- Lemma S even branch + R0c
import Erdos634.Draft.LemmaSEvenTop -- Lemma S even branch + R0c
import Erdos634.Draft.LemmaSEvenD -- Lemma S even branch + R0c
import Erdos634.Draft.LemmaSEven -- Lemma S even branch + R0c
import Erdos634.Draft.LemmaSAll -- Lemma S even branch + R0c
import Erdos634.Draft.TheoremPConditional -- V-COMP, conditional on 9 Case C Props
import Erdos634.Draft.ThmIsoShBridge -- C10 bridge: TwoPiThreeData → BaseAlphaData (cos_alpha_of_TwoPiThree, base_alpha_of_isoTP)
import Erdos634.Draft.ThmIso -- C10 partial: model_four_det_sq, target_four_det_sq, base_alpha_area_identity (N·b=μ²(a+2b))
import Erdos634.Draft.ThmIsoFull
import Erdos634.Draft.RMinus4Full
import Erdos634.Draft.ScaleBaseBetaFull
import Erdos634.Draft.LemmaPProof
import Erdos634.Draft.TheoremP6 -- theoremP_6 (no hypotheses)
import Erdos634.Refl.BridgeA -- reflective checker

-- H1 chain, composites, AllN exclusion, R84 tiling, Refl (previously un-imported tracked files)
import Erdos634.Draft.AllNExclusion
import Erdos634.Draft.AllNExclusionArith
import Erdos634.Draft.AllNExclusionArith2
import Erdos634.Draft.AllNExclusionCheck
import Erdos634.Draft.CaseAComposite
import Erdos634.Draft.CaseACompositeE
import Erdos634.Draft.CaseALemmaHN
import Erdos634.Draft.Chain38
import Erdos634.Draft.Chain86
import Erdos634.Draft.ChainComposite
import Erdos634.Draft.ChainCompositeR8
import Erdos634.Draft.ChainCompositeR8b
import Erdos634.Draft.CompositeArith
import Erdos634.Draft.CompositeE5Gen
import Erdos634.Draft.CompositeF1Gen
import Erdos634.Draft.CompositeFinal
import Erdos634.Draft.CompositeFinal10
import Erdos634.Draft.CompositeFinal11
import Erdos634.Draft.CompositeFinal12
import Erdos634.Draft.CompositeFinal13
import Erdos634.Draft.CompositeFinal2
import Erdos634.Draft.CompositeFinal3
import Erdos634.Draft.CompositeFinal4
import Erdos634.Draft.CompositeFinal5
import Erdos634.Draft.CompositeFinal6
import Erdos634.Draft.CompositeFinal7
import Erdos634.Draft.CompositeFinal8
import Erdos634.Draft.CompositeFinal9
import Erdos634.Draft.CompositeIsoB
import Erdos634.Draft.CompositeNine
import Erdos634.Draft.CompositeS1Arith
import Erdos634.Draft.CompositeS2Arith
import Erdos634.Draft.CompositeS2Global
import Erdos634.Draft.CompositeS2Mod27
import Erdos634.Draft.CompositeS3Refined
import Erdos634.Draft.E60Mod9A
import Erdos634.Draft.E60Mod9B
import Erdos634.Draft.E60Mod9C
import Erdos634.Draft.F1KappaSide
import Erdos634.Draft.F1KappaSide2
import Erdos634.Draft.F1KappaSide3
import Erdos634.Draft.FluxERow2Sqfree17
import Erdos634.Draft.FluxERow2SqfreeEven
import Erdos634.Draft.G2AAssembly
import Erdos634.Draft.G2AChain
import Erdos634.Draft.G2AFinal
import Erdos634.Draft.G2AGeo1
import Erdos634.Draft.G2AGeo2
import Erdos634.Draft.G2AGeo3
import Erdos634.Draft.H1Witnesses
import Erdos634.Draft.H1aSetup
import Erdos634.Draft.H1bCaseAB
import Erdos634.Draft.H1cCaseC
import Erdos634.Draft.H1dCaseD
import Erdos634.Draft.H1eCLAlign
import Erdos634.Draft.H1eCLCaseD
import Erdos634.Draft.H1eCLCount
import Erdos634.Draft.H1eCLFacts
import Erdos634.Draft.H1eCLWitness
import Erdos634.Draft.H1fNG
import Erdos634.Draft.H1fNGEdge
import Erdos634.Draft.H1gDir
import Erdos634.Draft.H1gPos1D
import Erdos634.Draft.H1gPosCover
import Erdos634.Draft.H1gPosGlue
import Erdos634.Draft.H1gPosLine
import Erdos634.Draft.H1gPosStep
import Erdos634.Draft.H1gPosWitness
import Erdos634.Draft.H1hCT
import Erdos634.Draft.H1hCTCong
import Erdos634.Draft.H1iSLChar
import Erdos634.Draft.H1iSLMain
import Erdos634.Draft.H1iSLWitness
import Erdos634.Draft.H1jGlue
import Erdos634.Draft.H1kAssembly
import Erdos634.Draft.H1kFinal
import Erdos634.Draft.ThmIsoH9b
import Erdos634.R84Tiling
import Erdos634.R84TilingBridge
import Erdos634.Refl.BridgeB
import Erdos634.Refl.BridgeE120
import Erdos634.Refl.Check
import Erdos634.Refl.CheckE
import Erdos634.Refl.CheckR
import Erdos634.Refl.CheckP -- 4-vertex/parallelogram reflective checker
import Erdos634.Refl.DataA
import Erdos634.Refl.DataB
import Erdos634.Refl.DataE120
import Erdos634.Refl.NegE120
import Erdos634.Refl.RunA
import Erdos634.Refl.RunB
import Erdos634.Refl.RunE120
import Erdos634.Refl.Sound
import Erdos634.Refl.SoundE1
import Erdos634.Refl.SoundE2
import Erdos634.Refl.SoundE3
import Erdos634.Refl.SoundE4
import Erdos634.Refl.SoundStage1
import Erdos634.Refl.SoundStage10
import Erdos634.Refl.SoundStage11
import Erdos634.Refl.SoundStage12
import Erdos634.Refl.SoundStage13
import Erdos634.Refl.SoundStage2
import Erdos634.Refl.SoundStage3
import Erdos634.Refl.SoundStage4
import Erdos634.Refl.SoundStage5
import Erdos634.Refl.SoundStage6
import Erdos634.Refl.SoundStage7
import Erdos634.Refl.SoundStage8
import Erdos634.Refl.SoundStage8b
import Erdos634.Refl.SoundStage9
import Erdos634.Refl.SoundWitness
import Erdos634.Draft.AllN2Cond
import Erdos634.Draft.AllN2Check
import Erdos634.Draft.AllN2Check2
import Erdos634.Draft.AllN2Check3
import Erdos634.Draft.AllN2Check4
import Erdos634.Draft.AllN2Check5
import Erdos634.Draft.AllN2Check6
import Erdos634.Draft.AllN2Check8
import Erdos634.Draft.AllN2Check9
import Erdos634.Draft.AllN2Check10
import Erdos634.Draft.AllN2Check11
import Erdos634.Draft.AllN2Check12
import Erdos634.Draft.AllN2Check13
import Erdos634.Draft.AllN2Check14 -- 267–355
import Erdos634.Draft.AllN2Check15 -- 357–453
import Erdos634.Draft.AllN2Check16 -- 469–537
import Erdos634.Draft.AllN2Check17  -- 543–581
import Erdos634.Draft.AllN2Check17b -- 591–633
import Erdos634.Draft.AllN2Check18  -- 635–679
import Erdos634.Draft.AllN2Check18b -- 681–707
import Erdos634.Draft.AllN2Check19  -- 715–749
import Erdos634.Draft.AllN2Check19b -- 753–771
import Erdos634.Draft.AllN2Check20  -- 789–815
import Erdos634.Draft.AllN2Check20b -- 831–879
import Erdos634.Draft.AllN2Check21  -- 889–933
import Erdos634.Draft.AllN2Check21b -- 939–959
import Erdos634.Draft.AllN2Check22  -- 973–995
import Erdos634.Draft.AllN2Check23  -- N ∈ {1001,1011,1015,1023,1041}
import Erdos634.Draft.AllN2Check24  -- N ∈ {1043,1045,1047,1055,1057}
import Erdos634.Draft.AllN2Check25  -- N ∈ {1059,1077,1085,1099,1101}
import Erdos634.Draft.AllN2Check26  -- N ∈ {1111,1115,1119,1131,1133}
import Erdos634.Draft.AllN2Check27  -- N ∈ {1135,1137,1141,1149,1167}
import Erdos634.Draft.AllN2Check28  -- N ∈ {1169,1191,1195,1199,1203}
import Erdos634.Draft.AllN2Check29  -- 1209,1211,1227,1235,1243
import Erdos634.Draft.AllN2Check30  -- 1253,1255,1257,1263,1265
import Erdos634.Draft.AllN2Check31  -- 1267,1293,1295,1299,1309
import Erdos634.Draft.AllN2Check32  -- 1315,1317,1329,1337,1347
import Erdos634.Draft.AllN2Check33  -- 1351,1355,1371,1379,1383
import Erdos634.Draft.AllN2Check34  -- 1389,1393,1397,1401,1415
import Erdos634.Draft.AllN2Check35  -- 1435,1437,1441,1443,1461
import Erdos634.Draft.AllN2Check36  -- 1463,1473,1477,1495,1497
import Erdos634.Draft.AllN2Check37  -- 1505,1507,1509,1527,1529
import Erdos634.Draft.AllN2Check38  -- 1535,1547,1555,1561,1563
import Erdos634.Draft.AllN2Check39  -- 1569,1589,1595,1603,1615
import Erdos634.Draft.AllN2Check40  -- 1623,1639,1641,1645,1651
import Erdos634.Draft.AllN2Check41  -- 1655,1661,1671,1673,1687
import Erdos634.Draft.AllN2Check42  -- 1689,1703,1705,1707,1713
import Erdos634.Draft.AllN2Check43  -- 1727,1731,1735,1757,1761
import Erdos634.Draft.AllN2Check44  -- 1771,1779,1793,1795,1797
import Erdos634.Draft.AllN2Check45  -- 1799,1803,1807,1821,1835
import Erdos634.Draft.AllN2Check46  -- 1837,1839,1841,1851,1855
import Erdos634.Draft.AllN2Check47  -- 1857,1883,1887,1893,1895
import Erdos634.Draft.AllN2Check48  -- 1897,1903,1915,1923,1929
import Erdos634.Draft.AllN2Check49  -- 1939,1941,1955,1959,1963
import Erdos634.Draft.AllN2Check50  -- 1967,1969,1977,1981,1983
import Erdos634.Draft.AllN2Check51  -- 1991
import Erdos634.Draft.AllN2Check52  -- 1999,2002,2003,2010,2011
import Erdos634.Draft.AllN2Check53  -- 2014,2015,2019,2021,2022
import Erdos634.Draft.AllN2Check54  -- 2027,2030,2031,2033,2035
import Erdos634.Draft.AllN2Check55  -- 2038,2039,2047,2049,2051
import Erdos634.Draft.AllN2Check56  -- 2054,2059,2062,2063,2071
import Erdos634.Draft.AllN2Check57  -- 2073,2077,2078,2082,2083
import Erdos634.Draft.AllN2Check58  -- 2086,2087,2090,2091,2093
import Erdos634.Draft.AllN2Check59  -- 2094,2095,2099,2101,2102
import Erdos634.Draft.AllN2Check60  -- 2103,2110,2111,2114,2118
import Erdos634.Draft.AllN2Check61  -- 2119,2123,2126,2127,2130
import Erdos634.Draft.AllN2Check62  -- 2131,2134,2135,2143,2147
import Erdos634.Draft.AllN2Check63  -- 2149,2154,2155,2157,2158
import Erdos634.Draft.AllN2Check64  -- 2159,2162,2167,2170,2171
import Erdos634.Draft.AllN2Check65  -- 2174,2177,2179,2181,2182
import Erdos634.Draft.AllN2Check66  -- 2183,2185,2190,2191,2193
import Erdos634.Draft.AllN2Check67  -- 2195,2198,2199,2201,2202
import Erdos634.Draft.AllN2Check68  -- 2203,2206,2207,2215,2217
import Erdos634.Draft.AllN2Check69  -- 2219,2222,2226,2227,2229
import Erdos634.Draft.AllN2Check70  -- 2230,2231,2233,2238,2239
import Erdos634.Draft.AllN2Check71  -- 2243,2246,2251,2253,2255
import Erdos634.Draft.AllN2Check72  -- 2263,2266,2267,2270,2271
import Erdos634.Draft.AllN2Check73  -- 2274,2278,2279,2282,2283
import Erdos634.Draft.AllN2Check74  -- 2287,2291,2294,2298,2302
import Erdos634.Draft.AllN2Check75  -- 2307,2311,2315,2317,2318
import Erdos634.Draft.AllN2Check76  -- 2319,2321,2323,2326,2327
import Erdos634.Draft.AllN2Check77  -- 2334,2335,2337,2338,2339
import Erdos634.Draft.AllN2Check78  -- 2342,2345,2347,2351,2354
import Erdos634.Draft.AllN2Check79  -- 2359,2361,2363,2365,2369
import Erdos634.Draft.AllN2Check80  -- 2370,2371,2374,2382,2383
import Erdos634.Draft.AllN2Check81  -- 2387,2390,2391,2395,2397
import Erdos634.Draft.AllN2Check82  -- 2398,2399
import Erdos634.Draft.AllN2Check83  -- 2406,2407,2411,2413,2414
import Erdos634.Draft.AllN2Check84  -- 2419,2422,2423,2427,2429
import Erdos634.Draft.AllN2Check85  -- 2431,2433,2435,2438,2443
import Erdos634.Draft.AllN2Check86  -- 2446,2447,2449,2451,2453
import Erdos634.Draft.AllN2Check87  -- 2454,2455,2459,2461,2462
import Erdos634.Draft.AllN2Check88  -- 2463,2467,2469,2470,2471
import Erdos634.Draft.AllN2Check89  -- 2478,2479,2481,2483,2486
import Erdos634.Draft.AllN2Check90  -- 2487,2489,2490,2491,2494
import Erdos634.Draft.AllN2Check91  -- 2495,2497,2503,2506,2507
import Erdos634.Draft.AllN2Check92  -- 2510,2513,2514,2515,2517
import Erdos634.Draft.AllN2Check93  -- 2518,2519,2526,2530,2531
import Erdos634.Draft.AllN2Check94  -- 2534,2537,2539,2542,2543
import Erdos634.Draft.AllN2Check95  -- 2546,2551,2555,2558,2559
import Erdos634.Draft.AllN2Check96  -- 2562,2563,2566,2567,2569
import Erdos634.Draft.AllN2Check97  -- 2571,2573,2577,2579,2582
import Erdos634.Draft.AllN2Check98  -- 2585,2586,2587,2589,2590
import Erdos634.Draft.AllN2Check99  -- 2591,2598,2599,2603,2606
import Erdos634.Draft.AllN2Check100  -- 2611,2614,2615,2618,2623
import Erdos634.Draft.AllN2Check101  -- 2627,2629,2630,2631,2634
import Erdos634.Draft.AllN2Check102  -- 2635,2638,2639,2641,2643
import Erdos634.Draft.AllN2Check103  -- 2647,2649,2651,2653,2654
import Erdos634.Draft.AllN2Check104  -- 2658,2659,2661,2663,2666
import Erdos634.Draft.AllN2Check105  -- 2670,2671,2674,2678,2679
import Erdos634.Draft.AllN2Check106  -- 2681,2683,2686,2687,2694
import Erdos634.Draft.AllN2Check107  -- 2698,2699,2702,2707,2710
import Erdos634.Draft.AllN2Check108  -- 2711,2717,2719,2721,2723
import Erdos634.Draft.AllN2Check109  -- 2726,2731,2733,2734,2735
import Erdos634.Draft.AllN2Check110  -- 2737,2742,2743,2747,2755
import Erdos634.Draft.AllN2Check111  -- 2757,2758,2759,2761,2765
import Erdos634.Draft.AllN2Check112  -- 2766,2767,2771,2773,2774
import Erdos634.Draft.AllN2Check113  -- 2778,2779,2782,2786,2787
import Erdos634.Draft.AllN2Check114  -- 2791,2794,2795,2798,2802
import Erdos634.Draft.AllN2Check115  -- 2803,2806,2807,2811,2814
import Erdos634.Draft.AllN2Check116  -- 2815,2819,2821,2822,2823
import Erdos634.Draft.AllN2Check117  -- 2827,2830,2831,2839,2841
import Erdos634.Draft.AllN2Check118  -- 2843,2846,2849,2851,2854
import Erdos634.Draft.AllN2Check119  -- 2855,2859,2863,2867,2869
import Erdos634.Draft.AllN2Check120  -- 2870,2874,2878,2879,2881
import Erdos634.Draft.AllN2Check121  -- 2882,2887,2893,2894,2899
import Erdos634.Draft.AllN2Check122  -- 2901,2902,2903,2910,2911
import Erdos634.Draft.AllN2Check123  -- 2913,2914,2915,2918,2921
import Erdos634.Draft.AllN2Check124  -- 2922,2923,2926,2927,2931
import Erdos634.Draft.AllN2Check125  -- 2933,2935,2939,2942,2945
import Erdos634.Draft.AllN2Check126  -- 2946,2947,2949,2951,2954
import Erdos634.Draft.AllN2Check127  -- 2959,2963,2966,2971,2973
import Erdos634.Draft.AllN2Check128  -- 2974,2981,2983,2987,2990
import Erdos634.Draft.AllN2Check129  -- 2991,2994,2995,2998,2999
import Erdos634.Draft.AllN2Check130  -- 3002,3007,3010,3011,3013
import Erdos634.Draft.AllN2Check131  -- 3014,3017,3018,3019,3021
import Erdos634.Draft.AllN2Check132  -- 3022,3023,3027,3030,3031
import Erdos634.Draft.AllN2Check133  -- 3035,3039,3043,3046,3047
import Erdos634.Draft.AllN2Check134  -- 3053,3054,3055,3057,3058
import Erdos634.Draft.AllN2Check135  -- 3059,3062,3063,3066,3067
import Erdos634.Draft.AllN2Check136  -- 3070,3071,3073,3079,3082
import Erdos634.Draft.AllN2Check137  -- 3083,3086,3090,3091,3093
import Erdos634.Draft.AllN2Check138  -- 3095,3097,3099,3101,3102
import Erdos634.Draft.AllN2Check139  -- 3103,3107,3110,3113,3115
import Erdos634.Draft.AllN2Check140  -- 3117,3118,3119,3122,3126
import Erdos634.Draft.AllN2Check141  -- 3127,3131,3134,3138,3139
import Erdos634.Draft.AllN2Check142  -- 3142,3143,3147,3149,3151
import Erdos634.Draft.AllN2Check143  -- 3153,3154,3155,3157,3158
import Erdos634.Draft.AllN2Check144  -- 3163,3166,3167,3173,3182
import Erdos634.Draft.AllN2Check145  -- 3183,3187,3189,3190,3191
import Erdos634.Draft.AllN2Check146  -- 3193,3197,3199,3203,3206
import Erdos634.Draft.AllN2Check147  -- 3207,3210,3214,3215,3223
import Erdos634.Draft.AllN2Check148  -- 3227,3230,3235,3238,3239
import Erdos634.Draft.AllN2Check149  -- 3241,3243,3245,3246,3247
import Erdos634.Draft.AllN2Check150  -- 3251,3254,3259,3261,3262
import Erdos634.Draft.AllN2Check151  -- 3263,3269,3270,3271,3273
import Erdos634.Draft.AllN2Check152  -- 3278,3279,3282,3286,3287
import Erdos634.Draft.AllN2Check153  -- 3290,3291,3295,3299,3302
import Erdos634.Draft.AllN2Check154  -- 3307,3309,3310,3311,3317
import Erdos634.Draft.AllN2Check155  -- 3318,3319,3322,3323,3326
import Erdos634.Draft.AllN2Check156  -- 3327,3331,3334,3335,3337
import Erdos634.Draft.AllN2Check157  -- 3342,3343,3346,3347,3351
import Erdos634.Draft.AllN2Check158  -- 3353,3355,3358,3359,3367
import Erdos634.Draft.AllN2Check159  -- 3369,3371,3374,3377,3378
import Erdos634.Draft.AllN2Check160  -- 3379,3382,3383,3387,3390
import Erdos634.Draft.AllN2Check161  -- 3391,3395,3397,3398,3401
import Erdos634.Draft.AllN2Check162  -- 3403,3406,3407,3409,3410
import Erdos634.Draft.AllN2Check163  -- 3414,3415,3419,3421,3422
import Erdos634.Draft.AllN2Check164  -- 3426,3427,3437,3439,3443
import Erdos634.Draft.AllN2Check165  -- 3446,3451,3453,3454,3455
import Erdos634.Draft.AllN2Check166  -- 3458,3459,3462,3463,3467
import Erdos634.Draft.AllN2Check167  -- 3470,3473,3478,3486,3487
import Erdos634.Draft.AllN2Check168  -- 3489,3491,3493,3494,3498
import Erdos634.Draft.AllN2Check169  -- 3499,3502,3503,3511,3513
import Erdos634.Draft.AllN2Check170  -- 3514,3515,3518,3521,3522
import Erdos634.Draft.AllN2Check171  -- 3523,3526,3527,3535,3539
import Erdos634.Draft.AllN2Check172  -- 3542,3543,3547,3551,3553
import Erdos634.Draft.AllN2Check173  -- 3558,3559,3561,3563,3565
import Erdos634.Draft.AllN2Check174  -- 3566,3569,3571,3574,3579
import Erdos634.Draft.AllN2Check175  -- 3583,3586,3587,3590,3594
import Erdos634.Draft.AllN2Check176  -- 3595,3598,3599,3603,3605
import Erdos634.Draft.AllN2Check177  -- 3606,3607,3611,3614,3619
import Erdos634.Draft.AllN2Check178  -- 3622,3623,3629,3631,3634
import Erdos634.Draft.AllN2Check179  -- 3635,3638,3639,3641,3642
import Erdos634.Draft.AllN2Check180  -- 3643,3646,3647,3651,3655
import Erdos634.Draft.AllN2Check181  -- 3657,3658,3659,3661,3662
import Erdos634.Draft.AllN2Check182  -- 3667,3669,3670,3671,3674
import Erdos634.Draft.AllN2Check183  -- 3678,3679,3682,3683,3685
import Erdos634.Draft.AllN2Check184  -- 3686,3687,3689,3691,3693
import Erdos634.Draft.AllN2Check185  -- 3694,3695,3702,3707,3710
import Erdos634.Draft.AllN2Check186  -- 3711,3713,3714,3715,3719
import Erdos634.Draft.AllN2Check187  -- 3727,3731,3734,3738,3739
import Erdos634.Draft.AllN2Check188  -- 3742,3743,3745,3747,3749
import Erdos634.Draft.AllN2Check189  -- 3755,3758,3763,3766,3767
import Erdos634.Draft.AllN2Check190  -- 3777,3779,3781,3782,3786
import Erdos634.Draft.AllN2Check191  -- 3787,3790,3791,3794,3799
import Erdos634.Draft.AllN2Check192  -- 3803,3806,3810,3811,3814
import Erdos634.Draft.AllN2Check193  -- 3815,3817,3823,3827,3829
import Erdos634.Draft.AllN2Check194  -- 3830,3831,3835,3837,3838
import Erdos634.Draft.AllN2Check195  -- 3839,3846,3847,3849,3851
import Erdos634.Draft.AllN2Check196  -- 3854,3857,3858,3859,3862
import Erdos634.Draft.AllN2Check197  -- 3863,3867,3873,3878,3882
import Erdos634.Draft.AllN2Check198  -- 3883,3886,3891,3894,3895
import Erdos634.Draft.AllN2Check199  -- 3899,3902,3903,3907,3909
import Erdos634.Draft.AllN2Check200  -- 3910,3911,3913,3914,3918
import Erdos634.Draft.AllN2Check201  -- 3919,3921,3923,3926,3930
import Erdos634.Draft.AllN2Check202  -- 3931,3935,3937,3938,3941
import Erdos634.Draft.AllN2Check203  -- 3943,3947,3949,3953,3954
import Erdos634.Draft.AllN2Check204  -- 3955,3957,3958,3959,3962
import Erdos634.Draft.AllN2Check205  -- 3963,3966,3967,3974,3979
import Erdos634.Draft.AllN2Check206  -- 3981,3982,3983,3991,3995
import Erdos634.Draft.AllN2Check207  -- 3997,3998,4003,4006,4007
import Erdos634.Draft.AllN2Check208  -- 4009,4015,4019,4022,4026
import Erdos634.Draft.AllN2Check209  -- 4027,4030,4031,4037,4038
import Erdos634.Draft.AllN2Check210  -- 4039,4042,4043,4051,4054
import Erdos634.Draft.AllN2Check211  -- 4055,4061,4062,4063,4066
import Erdos634.Draft.AllN2Check212  -- 4070,4071,4074,4078,4079
import Erdos634.Draft.AllN2Check213  -- 4081,4083,4085,4087,4091
import Erdos634.Draft.AllN2Check214  -- 4094,4098,4099,4101,4102
import Erdos634.Draft.AllN2Check215  -- 4103,4109,4110,4111,4115
import Erdos634.Draft.AllN2Check216  -- 4117,4118,4119,4123,4126
import Erdos634.Draft.AllN2Check217  -- 4127,4130,4134,4135,4139
import Erdos634.Draft.AllN2Check218  -- 4142,4143,4146,4147,4151
import Erdos634.Draft.AllN2Check219  -- 4154,4159,4163,4166,4169
import Erdos634.Draft.AllN2Check220  -- 4170,4171,4174,4183,4186
import Erdos634.Draft.AllN2Check221  -- 4187,4189,4190,4193,4195
import Erdos634.Draft.AllN2Check222  -- 4197,4198,4199,4202,4206
import Erdos634.Draft.AllN2Check223  -- 4207,4209,4211,4213,4219
import Erdos634.Draft.AllN2Check224  -- 4222,4223,4227,4231,4237
import Erdos634.Draft.AllN2Check225  -- 4238,4242,4243,4246,4247
import Erdos634.Draft.AllN2Check226  -- 4249,4254,4255,4259,4262
import Erdos634.Draft.AllN2Check227  -- 4267,4269,4270,4271,4277
import Erdos634.Draft.AllN2Check228  -- 4279,4281,4283,4286,4287
import Erdos634.Draft.AllN2Check229  -- 4290,4291,4294,4295,4298
import Erdos634.Draft.AllN2Check230  -- 4299,4301,4303,4307,4309
import Erdos634.Draft.AllN2Check231  -- 4310,4313,4314,4315,4317
import Erdos634.Draft.AllN2Check232  -- 4318,4319,4326,4327,4331
import Erdos634.Draft.AllN2Check233  -- 4333,4334,4339,4341,4342
import Erdos634.Draft.AllN2Check234  -- 4343,4345,4351,4353,4354
import Erdos634.Draft.AllN2Check235  -- 4355,4358,4359,4362,4363
import Erdos634.Draft.AllN2Check236  -- 4366,4367,4370,4377,4378
import Erdos634.Draft.AllN2Check237  -- 4379,4382,4387,4390,4391
import Erdos634.Draft.AllN2Check238  -- 4393,4398,4399,4402,4403
import Erdos634.Draft.AllN2Check239  -- 4406,4413,4414,4415,4417
import Erdos634.Draft.AllN2Check240  -- 4422,4423,4427,4429,4430
import Erdos634.Draft.AllN2Check241  -- 4433,4434,4435,4438,4439
import Erdos634.Draft.AllN2Check242  -- 4443,4445,4447,4449,4451
import Erdos634.Draft.AllN2Check243  -- 4454,4458,4461,4462,4463
import Erdos634.Draft.AllN2Check244  -- 4465,4466,4467,4470,4471
import Erdos634.Draft.AllN2Check245  -- 4478,4479,4483,4486,4487
import Erdos634.Draft.AllN2Check246  -- 4494,4495,4497,4499,4501
import Erdos634.Draft.AllN2Check247  -- 4502,4506,4507,4510,4511
import Erdos634.Draft.AllN2Check248  -- 4519,4522,4523,4526,4529
import Erdos634.Draft.AllN2Check249  -- 4530,4531,4533,4534,4535
import Erdos634.Draft.AllN2Check250  -- 4541,4542,4543,4547,4555
import Erdos634.Draft.AllN2Check251  -- 4558,4559,4565,4566,4567
import Erdos634.Draft.AllN2Check252  -- 4569,4571,4574,4577,4578
import Erdos634.Draft.AllN2Check253  -- 4579,4582,4583,4585,4591
import Erdos634.Draft.AllN2Check254  -- 4593,4595,4601,4602,4603
import Erdos634.Draft.AllN2Check255  -- 4607,4609,4613,4614,4615
import Erdos634.Draft.AllN2Check256  -- 4619,4622,4623,4627,4629
import Erdos634.Draft.AllN2Check257  -- 4630,4631,4634,4638,4639
import Erdos634.Draft.AllN2Check258  -- 4642,4643,4646,4647,4651
import Erdos634.Draft.AllN2Check259  -- 4654,4659,4661,4663,4667
import Erdos634.Draft.AllN2Check260  -- 4669,4670,4677,4678,4679
import Erdos634.Draft.AllN2Check261  -- 4681,4686,4687,4690,4691
import Erdos634.Draft.AllN2Check262  -- 4694,4697,4699,4701,4702
import Erdos634.Draft.AllN2Check263  -- 4703,4710,4711,4713,4715
import Erdos634.Draft.AllN2Check264  -- 4718,4722,4723,4726,4727
import Erdos634.Draft.AllN2Check265  -- 4730,4735,4737,4738,4739
import Erdos634.Draft.AllN2Check266  -- 4741,4742,4746,4747,4749
import Erdos634.Draft.AllN2Check267  -- 4751,4757,4758,4759,4763
import Erdos634.Draft.AllN2Check268  -- 4766,4769,4771,4774,4781
import Erdos634.Draft.AllN2Check269  -- 4782,4783,4787,4790,4791
import Erdos634.Draft.AllN2Check270  -- 4795,4798,4799,4803,4807
import Erdos634.Draft.AllN2Check271  -- 4811,4814,4818,4819,4821
import Erdos634.Draft.AllN2Check272  -- 4822,4823,4826,4827,4829
import Erdos634.Draft.AllN2Check273  -- 4831,4835,4837,4838,4839
import Erdos634.Draft.AllN2Check274  -- 4841,4843,4846,4847,4853
import Erdos634.Draft.AllN2Check275  -- 4854,4855,4857,4858,4859
import Erdos634.Draft.AllN2Check276  -- 4862,4863,4865,4866,4867
import Erdos634.Draft.AllN2Check277  -- 4870,4871,4873,4879,4881
import Erdos634.Draft.AllN2Check278  -- 4883,4886,4890,4891,4894
import Erdos634.Draft.AllN2Check279  -- 4895,4897,4898,4903,4906
import Erdos634.Draft.AllN2Check280  -- 4907,4910,4911,4915,4918
import Erdos634.Draft.AllN2Check281  -- 4919,4921,4922,4926,4927
import Erdos634.Draft.AllN2Check282  -- 4931,4934,4938,4939,4942
import Erdos634.Draft.AllN2Check283  -- 4943,4945,4951,4955,4958
import Erdos634.Draft.AllN2Check284  -- 4962,4963,4966,4967,4970
import Erdos634.Draft.AllN2Check285  -- 4971,4974,4978,4979,4982
import Erdos634.Draft.AllN2Check286  -- 4987,4989,4990,4991,4994
import Erdos634.Draft.AllN2Check287  -- 4997,4999
import Erdos634.Draft.AllN2Check288  -- 5001,5003,5005,5006,5007
import Erdos634.Draft.AllN2Check289  -- 5010,5011,5014,5015,5023
import Erdos634.Draft.AllN2Check290  -- 5026,5027,5029,5030,5033
import Erdos634.Draft.AllN2Check291  -- 5034,5035,5038,5039,5051
import Erdos634.Draft.AllN2Check292  -- 5053,5059,5062,5071,5074
import Erdos634.Draft.S2LCore
import Erdos634.Draft.S2LLayout
import Erdos634.Draft.S2LAssemble
import Erdos634.R88TilingBridge
import Erdos634.R126TilingBridge
import Erdos634.Draft.ADMLattice
import Erdos634.AllNew6
import Erdos634.AllNew7
-- modules that depend on a search certificate are in `Erdos634.AllSpectrum`
import Erdos634.BADAlgebra
import Erdos634.BADInstances
import Erdos634.BADPlacement
import Erdos634.BADPlacementGeo
import Erdos634.BADPlacementWit
import Erdos634.BADGridChar
import Erdos634.BADFluxTile
import Erdos634.BADFluxTile2
import Erdos634.BADTarget
import Erdos634.BADL2
import Erdos634.BADAngles
import Erdos634.BADFinal
import Erdos634.BADFinal2
import Erdos634.BADL2Wit
import Erdos634.B84Geom
import Erdos634.B84Final
import Erdos634.ATDAlg
import Erdos634.ATDL2
import Erdos634.ATDFinal
import Erdos634.ATDWit
import Erdos634.ARAGeom
import Erdos634.ARAForm
import Erdos634.ARAWit
import Erdos634.Draft.HBCFalse3
import Erdos634.Draft.HBCNQ
import Erdos634.Draft.HBCQ6
import Erdos634.Draft.HBCQ13
import Erdos634.Draft.HBCS6
import Erdos634.Draft.HBCS13
import Erdos634.Draft.HBCG
import Erdos634.Draft.GLCG1
import Erdos634.Draft.GLCG2
import Erdos634.Draft.GLCG2k
import Erdos634.Draft.GLCT4Wire
import Erdos634.Draft.GLCWit3
import Erdos634.Draft.GLGMain
import Erdos634.Draft.GLGWit
import Erdos634.Draft.GLIFinal
import Erdos634.Draft.GLIWit
import Erdos634.Draft.GLKBridge
import Erdos634.Draft.GLKChain60
import Erdos634.Draft.FDBMod12Converse
import Erdos634.Draft.BADCorFull
import Erdos634.Draft.CorAtomDivFull
import Erdos634.Draft.ChainGapA60
import Erdos634.Draft.FDEDefs
import Erdos634.Draft.FDEB_ov_1
import Erdos634.Draft.FDEB_ov_2
import Erdos634.Draft.FDEB_ov_3
import Erdos634.Draft.FDEB_ov_4
import Erdos634.Draft.FDEB_re_1
import Erdos634.Draft.FDEB_re_2
import Erdos634.Draft.FDEB_re_3
import Erdos634.Draft.FDEB_re_4
import Erdos634.Draft.FDEB_ex_1
import Erdos634.Draft.FDEB_ex_2
import Erdos634.Draft.FDEB_ex_3
import Erdos634.Draft.FDEB_ex_4
import Erdos634.Draft.FDEB_un_1
import Erdos634.Draft.FDEB_un_2
import Erdos634.Draft.FDEB_un_3
import Erdos634.Draft.FDEB_un_4
import Erdos634.Draft.FDEChecks
import Erdos634.Draft.FDACaseG1125
import Erdos634.Draft.FDBBaseBetaE1
import Erdos634.Draft.FDC63
import Erdos634.Draft.FDCCevianAtom
import Erdos634.Draft.FDCEqSpec
import Erdos634.Draft.FDCConicForm
import Erdos634.Draft.FDCConicFormPi3
import Erdos634.Draft.FDCConicFormPi3Wit
import Erdos634.Draft.FDCScaleReduce
import Erdos634.Draft.FDDSpectrumPaper
import Erdos634.Draft.InterfaceFloorSharp
import Erdos634.Draft.LemTightFormal
import Erdos634.Draft.AngleCalcFormal
import Erdos634.Draft.LemCensusFormal
import Erdos634.Draft.RemClosePairFormal
import Erdos634.Draft.FDDShapes
import Erdos634.Draft.FDDSpectrumArith
import Erdos634.Draft.FDDSpectrumTable
import Erdos634.Draft.FDFDepthWitness
import Erdos634.Draft.PrimeCharacterization
import Erdos634.Draft.S51CertData
import Erdos634.Draft.S51Bridge
import Erdos634.Draft.R8CompositeArg
import Erdos634.Draft.R8F2AreaFormula
import Erdos634.Draft.R8F2Contradiction
import Erdos634.Draft.R8F2to4Bridge
import Erdos634.Draft.R8F3AreaFormula
import Erdos634.Draft.R8F3Contradiction
import Erdos634.Draft.R8F3PrimeAreaFormula
import Erdos634.Draft.R8F3PrimeContradiction
import Erdos634.Draft.R8F4AreaFormula
import Erdos634.Draft.R8F4Contradiction
import Erdos634.Draft.R8F4PrimeAreaFormula
import Erdos634.Draft.R8F4PrimeContradiction
import Erdos634.Draft.R8N15Arith
import Erdos634.Draft.R8N15F2
import Erdos634.Draft.R8N15F3
import Erdos634.Draft.R8N15F3Prime
import Erdos634.Draft.R8N15F4
import Erdos634.Draft.R8N15F4Prime
import Erdos634.Draft.RAArith
import Erdos634.Draft.RAPieces
import Erdos634.Draft.RASetup
import Erdos634.Draft.RASquarefree
import Erdos634.Draft.RAAssemble
import Erdos634.Draft.RAStatementProof
import Erdos634.Draft.RWArith
import Erdos634.Draft.RWEast
import Erdos634.Draft.RWGlue
import Erdos634.Draft.RWPieces
import Erdos634.Draft.RWSquarefree
import Erdos634.Draft.RWAssemble
import Erdos634.Draft.RWStatementProof
import Erdos634.Draft.LemmaCArith
import Erdos634.Draft.LemmaCFigures
import Erdos634.Draft.LemmaCIso
import Erdos634.Draft.LemmaCShapes
import Erdos634.Draft.LemmaCSimilar
import Erdos634.Draft.LemmaCAssemble
import Erdos634.Draft.LemmaCFinal
import Erdos634.Draft.T30LC2Corner
import Erdos634.Draft.T30LC2Doubled
import Erdos634.Draft.T30LC2Forward
import Erdos634.Draft.T30LC2Strong
import Erdos634.Draft.T30LC2Wit
import Erdos634.Draft.T30LL3Corner
import Erdos634.Draft.T30LL3Far
import Erdos634.Draft.T30LL3Fill
import Erdos634.Draft.T30LL3Side
import Erdos634.Draft.T30LL3SideTile
import Erdos634.Draft.T30LL3Wit
import Erdos634.Draft.T30LL4Chain
import Erdos634.Draft.T30LL4Corner
import Erdos634.Draft.T30LL4T30
import Erdos634.Draft.T30LL4Tri
import Erdos634.Draft.T30LL4Wit
import Erdos634.Draft.T30LL4Wit2
import Erdos634.Draft.T30LL4Word
import Erdos634.Draft.T30LPi3Clamp
import Erdos634.Draft.T30LPi3Cone
import Erdos634.Draft.T30LPi3Corner
import Erdos634.Draft.T30LPi3Enum
import Erdos634.Draft.T30LPi3F6
import Erdos634.Draft.T30LPi3F6Corner
import Erdos634.Draft.T30LPi3F6CornerWit
import Erdos634.Draft.T30LPi3F6Geom
import Erdos634.Draft.T30LPi3F6T30
import Erdos634.Draft.T30LPi3F6Tile
import Erdos634.Draft.T30LPi3F6Wit
import Erdos634.Draft.T30LPi3L3
import Erdos634.Draft.T30LPi3Tile
import Erdos634.Draft.T30SideWalkArith
import Erdos634.Draft.T30LSectorFill
import Erdos634.Draft.GA2OCDefs
import Erdos634.Draft.GA2OC30
import Erdos634.Draft.GA2OC45
import Erdos634.Draft.GA2OC60
import Erdos634.Draft.GA2OC75
import Erdos634.Draft.GA2OC75a
import Erdos634.Draft.GA2OC75b
import Erdos634.Draft.GA2OC75c
import Erdos634.Draft.GA2OC75d
import Erdos634.Draft.GA2OC75e
import Erdos634.Draft.GA2OC75f
import Erdos634.Draft.GA2OC90
import Erdos634.Draft.GA2OC90a
import Erdos634.Draft.GA2OC90b
import Erdos634.Draft.GA2OC90c
import Erdos634.Draft.GA2OC90d
import Erdos634.Draft.GA2OC90e
import Erdos634.Draft.GA2OC90f
import Erdos634.Draft.TJCC1
import Erdos634.Draft.TJCC1App
import Erdos634.Draft.TJCC1App2
import Erdos634.Draft.TJCC1App3
import Erdos634.Draft.HBSTSP
import Erdos634.Draft.SporadicCounts
import Erdos634.Draft.Equilateral3
import Erdos634.Draft.SumTwoSquares
import Erdos634.Draft.PrimeWitness2
import Erdos634.Draft.PrimeWitness5
import Erdos634.Draft.F1AlgebraPin
import Erdos634.Draft.F1AlgebraReal
import Erdos634.Draft.F1AreaIdentity
import Erdos634.Draft.F1BEdgeBoundary
import Erdos634.Draft.F1BEdgeBoundaryM
import Erdos634.Draft.F1BoundaryK2
import Erdos634.Draft.F1Bridge
import Erdos634.Draft.F1CornerAlign
import Erdos634.Draft.F1CornerK
import Erdos634.Draft.F1EdgeAlign
import Erdos634.Draft.F1IrrationalRatio
import Erdos634.Draft.F1IrrationalRatioM
import Erdos634.Draft.F1K2Contradiction
import Erdos634.Draft.F1K2Core
import Erdos634.Draft.F1N15
import Erdos634.Draft.F1N3
import Erdos634.Draft.F1SideWord
import Erdos634.Draft.F1SideWordM
import Erdos634.Draft.F1TprimeExtract
import Erdos634.Draft.F1TprimeExtractM
import Erdos634.Draft.F1V2Corner
import Erdos634.Draft.F1c4aSide
import Erdos634.Draft.F1FreeProof
import Erdos634.Draft.F1FreeProofM
import Erdos634.Draft.CollarInputs
import Erdos634.Draft.CollarParam
import Erdos634.Draft.RegionTiling
import Erdos634.A2BranchRow3
import Erdos634.A36Reduction
import Erdos634.ApexRay
import Erdos634.BaseIdentity
import Erdos634.BaseWord
import Erdos634.BaseWordBlock
import Erdos634.BlockNeverCompletes
import Erdos634.BlockedPartner
import Erdos634.CLayerRigid
import Erdos634.CevianTiling28Bridge
import Erdos634.ChordChart
import Erdos634.ChordChartPlanar
import Erdos634.Congruence
import Erdos634.CornerBlock
import Erdos634.CornerCascade
import Erdos634.CornerRule
import Erdos634.CrossingCharacterised
import Erdos634.CrossingChirality
import Erdos634.CrossingCount
import Erdos634.CrossingHoldsInBlock
import Erdos634.CrossingHypothesis
import Erdos634.DescentUniform
import Erdos634.DoubleC
import Erdos634.E1Assembly
import Erdos634.EquilateralScaling
import Erdos634.EquilateralSpectrum
import Erdos634.FloorPropagation
import Erdos634.ForcedSecondRow
import Erdos634.GammaCount
import Erdos634.GammaTrap
import Erdos634.GoldenForm
import Erdos634.HeightLadder
import Erdos634.Irregular
import Erdos634.LayerLink
import Erdos634.LayerWord
import Erdos634.N15IsoA
import Erdos634.N15IsoALift
import Erdos634.OffsetInterior
import Erdos634.PrimeArithmetic
import Erdos634.PrimeRegimes
import Erdos634.R126CBridge
import Erdos634.R126CDefs
import Erdos634.R126CS0
import Erdos634.R126CS1
import Erdos634.R126CS2
import Erdos634.R126CS3
import Erdos634.R126CS4
import Erdos634.R126CS5
import Erdos634.R126Tiling
import Erdos634.R88Tiling
import Erdos634.RogueArea
import Erdos634.Route1
import Erdos634.Route1Filler
import Erdos634.SideForcing
import Erdos634.SixtyStructure
import Erdos634.SixtyUnsplittable
import Erdos634.StraddleBound
import Erdos634.StraddlerApex
import Erdos634.StraightEdgeSums
import Erdos634.StripIteration
import Erdos634.StripRigid
import Erdos634.TP_erdos
import Erdos634.TP_gonthier
import Erdos634.TP_hilbert
import Erdos634.TP_ramanujan
import Erdos634.TP_tao
import Erdos634.ThinCaseAnalysis
import Erdos634.ThinClosed
import Erdos634.ThinFamily
import Erdos634.ThinPrimes
import Erdos634.ThreeWords
import Erdos634.TileArithmetic
import Erdos634.TrichotomyCut
import Erdos634.UniformFill
import Erdos634.WalkStructure
import Erdos634.WallNeighbour
import Erdos634.WallStraddle
import Erdos634.WallsCircular
import Erdos634.WallsClosed
import Erdos634.WallsWord
import Erdos634.WedgeBound
import Erdos634.WordCount
import Erdos634.Z2Real
import Erdos634.Z3Real
import Erdos634.Draft.BrickGridF
import Erdos634.Draft.CaseALemmaH15
import Erdos634.Draft.CaseALemmaH15Exc
import Erdos634.Draft.CaseAN15
import Erdos634.Draft.CentroidSplit
import Erdos634.Draft.Chain15
import Erdos634.Draft.Chain15A
import Erdos634.Draft.Chain15F1
import Erdos634.Draft.Chain15Gaps
import Erdos634.Draft.Chain15H
import Erdos634.Draft.Chain15R8
import Erdos634.Draft.Chain15X
import Erdos634.Draft.ChordFar
import Erdos634.Draft.ChordWord
import Erdos634.Draft.CompositeGen2
import Erdos634.Draft.CutGen
import Erdos634.Draft.DiscNotSquarePrime
import Erdos634.Draft.E60VMod3
import Erdos634.Draft.FamAssembly
import Erdos634.Draft.Flux2Pi3Grid
import Erdos634.Draft.FluxCRow5N15
import Erdos634.Draft.FluxDRow4L8Recovered
import Erdos634.Draft.FluxDRow4L8Wiring
import Erdos634.Draft.FluxDRow4M1
import Erdos634.Draft.FluxDRow4M1AnyLabel
import Erdos634.Draft.FluxDRow4SqfreeArith
import Erdos634.Draft.FluxE2Pi3Row8Arith
import Erdos634.Draft.FluxE2Pi3Row8F2
import Erdos634.Draft.FluxE2Pi3Row8F3
import Erdos634.Draft.FluxE2Pi3Row8F4
import Erdos634.Draft.FluxE2Pi3Row8Mirrors
import Erdos634.Draft.FluxERow2Sqfree
import Erdos634.Draft.GLCArith
import Erdos634.Draft.GLCArith2
import Erdos634.Draft.GLCCase1
import Erdos634.Draft.GLCCase2
import Erdos634.Draft.GLCChain
import Erdos634.Draft.GLCCorner
import Erdos634.Draft.GLCFan
import Erdos634.Draft.GLCFar2a
import Erdos634.Draft.GLCFinish
import Erdos634.Draft.GLCForward
import Erdos634.Draft.GLCFwdEdge
import Erdos634.Draft.GLCGeom
import Erdos634.Draft.GLCHover
import Erdos634.Draft.GLCRay
import Erdos634.Draft.GLCReflect
import Erdos634.Draft.GLCT3
import Erdos634.Draft.GLCT4
import Erdos634.Draft.GLCT4Facts
import Erdos634.Draft.GLCWire
import Erdos634.Draft.GLCWit
import Erdos634.Draft.GLCWit2
import Erdos634.Draft.GLGArith
import Erdos634.Draft.GLGSide
import Erdos634.Draft.GLIApex
import Erdos634.Draft.GLICorner
import Erdos634.Draft.GLIG2
import Erdos634.Draft.GLIMain
import Erdos634.Draft.GLIModel
import Erdos634.Draft.GLIRev
import Erdos634.Draft.GLISum
import Erdos634.Draft.GLIWall
import Erdos634.Draft.GapE120Arith
import Erdos634.Draft.GapE120Dis
import Erdos634.Draft.GapE120SSS
import Erdos634.Draft.HalfAngle
import Erdos634.Draft.IntegrationTest
import Erdos634.Draft.IntegrationTest2
import Erdos634.Draft.IntegrationTest3
import Erdos634.Draft.IntegrationTest4
import Erdos634.Draft.IntegrationTest5
import Erdos634.Draft.IntegrationTest7
import Erdos634.Draft.IntegrationTest8
import Erdos634.Draft.IntegrationTest9
import Erdos634.Draft.IntegrationTest10
import Erdos634.Draft.IntegrationTest11
import Erdos634.Draft.IntegrationTest12
import Erdos634.Draft.IntegrationTest13
import Erdos634.Draft.IntegrationTest14
import Erdos634.Draft.IntegrationTest15
import Erdos634.Draft.IntegrationTest16
import Erdos634.Draft.IntegrationTest17
import Erdos634.Draft.IntegrationTest18
import Erdos634.Draft.IntegrationTest19
import Erdos634.Draft.MirrorLevel2
import Erdos634.Draft.R1N83
import Erdos634.Draft.RMinus4QNR
import Erdos634.Draft.RefineTiles
import Erdos634.Draft.Row11IsoQ
import Erdos634.Draft.ScaleBaseBetaQNR
import Erdos634.Draft.SecondEdgeReal
import Erdos634.Draft.SixTiles
import Erdos634.Draft.TJCHand
import Erdos634.Draft.TJCHandApp
import Erdos634.Draft.TJCHelp
import Erdos634.Draft.ThmIsoH9
import Erdos634.Draft.TileCountFamilies
import Erdos634.Draft.TileCountSpectrum
import Erdos634.Draft.TraceCoveringWitness
import Erdos634.Draft.WAdd
import Erdos634.Draft.WAddF
import Erdos634.Draft.WBrick
import Erdos634.Draft.WBrickF
import Erdos634.Draft.WFamily
import Erdos634.Draft.WFamilyF
import Erdos634.Draft.WFrame
import Erdos634.Draft.WFrameF
import Erdos634.Draft.WGrid
import Erdos634.Draft.WGridF
import Erdos634.Draft.WPgram
import Erdos634.Draft.WPgramF
import Erdos634.Draft.WSeed
import Erdos634.Draft.WtoDeltaF
import Erdos634.Draft.PI3HArithDefs
import Erdos634.Draft.PI3HArithWindow
import Erdos634.Draft.PI3HArithKill
import Erdos634.Draft.PI3HArithLink
import Erdos634.Draft.PI3HStripArith
import Erdos634.Draft.G1NAll
import Erdos634.Draft.S2GFrame
import Erdos634.Draft.S2GLayout
import Erdos634.Draft.S2GPieces
import Erdos634.Draft.S2GAssemble
import Erdos634.Draft.S2GControls
import Erdos634.Draft.NSQCaseB
import Erdos634.Draft.NSQCaseA
import Erdos634.Draft.NSQRA
import Erdos634.Draft.NSQRADvd
import Erdos634.Draft.NSQLegs
import Erdos634.Draft.NSQGammaChk
import Erdos634.Draft.NSQF1
import Erdos634.Draft.NSQS1
import Erdos634.Draft.NSQRW
import Erdos634.Draft.NSQChk
import Erdos634.Draft.NSQMain
import Erdos634.Draft.NSQCheck152
import Erdos634.Draft.N3EqCase
import Erdos634.AllNew9
-- AllNew10, WITHOUT its 26 modules that depend on a search certificate (those are in `Erdos634.AllSpectrum`) -- free-branch-point certificates; not_tile_56/60/70/76 (hypothesis-free), tileCounts_le_91
import Erdos634.PlacementCompletenessCone
import Erdos634.Refl.SoundM3
import Erdos634.Draft.RAInst
import Erdos634.Draft.RWInst
import Erdos634.ReflS.Sound
import Erdos634.ReflS.MT30Sound
import Erdos634.Draft.S3Inst
import Erdos634.Draft.AllN2CheckGap200a
import Erdos634.Draft.AllN2CheckGap200b
import Erdos634.Draft.PropReductionN2
import Erdos634.GammaTrapLt
import Erdos634.Draft.RATrap
import Erdos634.Draft.S5PinArith
import Erdos634.Draft.S5PinA
import Erdos634.Draft.S5PinB
import Erdos634.Draft.S5PinC
import Erdos634.Draft.RATrap2
import Erdos634.Draft.S5Family
import Erdos634.Draft.S5PinWitness
import Erdos634.Draft.B3Prime
import Erdos634.Draft.B3PrimeWitness
import Erdos634.Draft.AtomShape
-- AllNew11, WITHOUT its 11 modules that depend on a search certificate (those are in `Erdos634.AllSpectrum`) -- conjugate-kill certificates; eq105; not_tile_168/198; TileCount 189; tileCount_iff_le_200d
import Erdos634.Draft.GPairCert
import Erdos634.Draft.QuadConj
import Erdos634.ReflS.SoundN
import Erdos634.ReflS.SoundC
import Erdos634.ReflS609.MP120x60Sound
import Erdos634.ReflS1353.MP168x84Sound
import Erdos634.ReflS57.MP168x42Sound
import Erdos634.ReflS97.MP198x99Sound
import Erdos634.ReflS273.MP198x66Sound
import Erdos634.Draft.GPairArith
import Erdos634.ReflS.SoundCR
import Erdos634.R189TilingBridge
-- AllNew12, WITHOUT its 7 modules that depend on a search certificate (those are in `Erdos634.AllSpectrum`) -- Laczkovich's relation for the pi/3 tile (sixty_has_a_relation, e60Pair_of_not_isSquare); not_tile_171; tileCount_iff_le_200e
import Erdos634.Draft.E60Second
import Erdos634.Draft.E60Graph
import Erdos634.Draft.E60Heads
import Erdos634.Draft.E60Count
-- AllNew13, WITHOUT its 3 modules that depend on a search certificate (those are in `Erdos634.AllSpectrum`) -- Case A for N = 15 s^2, 30 s^2 (GAU.gapA_sq); gapE60_120; F1 pair certificates (f1Pair_of_cert); not_tile_120_of
import Erdos634.Draft.GAUFinal
import Erdos634.Draft.F1PairCert
import Erdos634.Draft.F1PairPar
-- AllNew14, WITHOUT its 3 modules that depend on a search certificate (those are in `Erdos634.AllSpectrum`) -- N = 120 excluded (N120.not_tile_120, certificate Refl.MF120); tileCount_iff_le_200f (8 undecided values); f1Pair_control
import Erdos634.Draft.F1PairControl
-- Certificate-free part: N = 105 excluded (N105.not_tile_105; also announced by Paliy); tileCount_iff_le_200g; tileCount_iff_le_131.  Modules depending on a search certificate are in `Erdos634.AllSpectrum`.
-- Certificate-free part: the gamma = 2 alpha leaf of 132 and 135 (caseG132, caseG135; certificates Refl.MG132, Refl.MG135) is in `Erdos634.AllSpectrum`.
-- Certificate-free part: TileCount (2p) for primes p (two_prime_tileCount_iff); also the other-spectra, wpgram, pgram-e1, widecol, addlaw, cevianatom, legcorner, spectral and nilptower statements.
import Erdos634.Draft.OtherSpectraFull
import Erdos634.Draft.NilpotentTowerFull
import Erdos634.Draft.SpectralFull
import Erdos634.Draft.WPgramWrap
import Erdos634.Draft.PgramE1Full
import Erdos634.Draft.WideColFull
import Erdos634.Draft.AddLawFull
import Erdos634.Draft.AddLawWitness
import Erdos634.Draft.CevianAtomFull
import Erdos634.Draft.CevianAtomWitness
import Erdos634.Draft.LegCornerFull
import Erdos634.Draft.WalksFull
-- Certificate-free part: squarefree N = 3 (mod 8), 3 not dividing N: not a tile count.
-- Certificate-free part: squarefree condition C3; 2pi/3 degree count and irrational pairs; 135 reduced to one pair; close-pair remarks.
import Erdos634.Draft.E120Fan
import Erdos634.Draft.E120Graph
import Erdos634.Draft.E120Heads
import Erdos634.Draft.E120Count
import Erdos634.Draft.ClosePairsFull
-- modules that depend on a search certificate are in `Erdos634.AllSpectrum`
import Erdos634.Draft.ChordArea
import Erdos634.Draft.ChordAreaWitness
import Erdos634.Draft.CensusScope
import Erdos634.Draft.InterfaceFloorGeom
import Erdos634.Draft.BlockedEnd
import Erdos634.Draft.ShadowWindow
import Erdos634.Draft.DirCoset
import Erdos634.Draft.DirCosetApps
import Erdos634.Draft.DirGroupIso
import Erdos634.Draft.OrientMonoSide
import Erdos634.Draft.DeBruijnKlarner
import Erdos634.Draft.E2StripFull
import Erdos634.Draft.FarRegion
import Erdos634.Draft.EdgeParity
import Erdos634.Draft.PierceScale
import Erdos634.Draft.PierceRung2
-- modules that depend on a search certificate are in `Erdos634.AllSpectrum`; 156 is reduced to one instance (Refl.MS156)
import Erdos634.Draft.ColumnLinesGeom
import Erdos634.Draft.TopJunctionGeom
import Erdos634.Draft.OffsetsExact
import Erdos634.Draft.LadderIdent
import Erdos634.Draft.SharpestAngle
import Erdos634.Draft.PinRayGeom
import Erdos634.Draft.PentagonNoTiling
import Erdos634.Draft.FanPruneRegion
import Erdos634.Draft.UnifyAngles
import Erdos634.Draft.MirroredFoot
import Erdos634.Draft.MarchAbstract
import Erdos634.Draft.NineToolsFull
import Erdos634.Draft.InflBdy
import Erdos634.Draft.PierceWitness44
-- 143 is a tile count; 264 (Paliy) is kernel-checked; sector N = 7 mod 8; the theorems on 154, 156, 184 that need the large certificates are in AllCert1.lean, not imported here (memory)
import Erdos634.R143TilingBridge
import Erdos634.R264TilingBridge
import Erdos634.Draft.N264
import Erdos634.Draft.InstLbl
import Erdos634.R234TilingBridge
import Erdos634.Draft.N234
import Erdos634.R207TilingBridge
import Erdos634.Draft.N207
import Erdos634.R240TilingBridge
import Erdos634.Draft.N240
-- kernel checks of two tilings of D. Paliy (github.com/DenisUkranian/erdos-634-tilings, commit 94566090):
-- 897 = (12,7,16) on (256,368,273) (Z[sqrt55]; R897Tiling, R897TilingBridgeA/P0-P37) and 990 = (8,7,13) on
-- (169,286,315) (Z[sqrt3]; R990Tiling, R990TilingBridgeA/P0-P41); the constructions are his
import Erdos634.Z55Real
import Erdos634.R897TilingBridge
import Erdos634.Draft.N897
import Erdos634.R990TilingBridge
import Erdos634.Draft.N990
-- 330 = (7,8,13) on (91,176,195) (F4, a<b, multiplier one; Z[sqrt3]; R330Tiling, R330TilingBridgeA/P0-P6/
-- T1-T4/D0-D9); our mrv2 tiling; Paliy announces F4 a<b at every multiplier (unrefereed)
import Erdos634.R330TilingBridge
import Erdos634.Draft.N330
import Erdos634.Refl.SoundMirror
import Erdos634.AllNew2 -- [composite N=15 (not_tile_15), N=30 (not_tile_30)]
import Erdos634.AllNew3
import Erdos634.AllNew4
import Erdos634.AllNew5
import Erdos634.Draft.NogoCount37
import Erdos634.Draft.NogoCount37Kernel
import Erdos634.Draft.NogoGamma37Kernel
import Erdos634.Draft.CornerStepWitness99
import Erdos634.Draft.PropNorm -- ℤ[√3] is a Euclidean domain and a PID; prime-norm elements are irreducible; Dirichlet infinitude; count 144 (native_decide for count_144 only)
import Erdos634.Draft.HeurFanLaw -- finite form of the fan law: floor(beta/alpha) table for f = 4..10; no completion
import Erdos634.Draft.HeurFinDep -- finite form of the dependence statement: no completion for every f >= 3; tests_uniform at the tile angles; d_BG instances
import Erdos634.Draft.HeurFib -- finite form of the Fibonacci statement: recurrence, a+2 Fibonacci, ratio vs phi on the reported list
import Erdos634.Draft.S2AllTheta
import Erdos634.Draft.S2All
import Erdos634.Draft.F4All
import Erdos634.Draft.F3All
import Erdos634.Draft.NSQMMainZ
import Erdos634.Draft.EqSemigroup
import Erdos634.Draft.Iso357Semigroup
import Erdos634.Draft.ZhangProps
import Erdos634.Draft.LaczFamily
