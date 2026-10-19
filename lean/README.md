# Lean formalization

This directory is the Lean 4 library `Erdos634` that accompanies the paper
`paper/erdos634_primes_and_N200.pdf`. Every Lean declaration cited by the paper (Appendix A, Table 3) is in it.

## Credits

Several modules formalize or adapt the work of others; each such module names its source in its leading docstring. In
particular: the `Draft/ThmC*` and `Draft/ThmD*` modules adapt the method of M. Beeson and G. Rosu (prime-tilings preprint,
16 October 2026: Lemmas 30, 32, 33, 34 and Theorem 37); `Draft/Herdt*` generalizes B. Herdt's 1125-tiling (published by
Beeson); `Draft/Lacz*` reconstructs M. Laczkovich's macro-dissection; `Draft/Zhang*` proves Y. X. Zhang's families for every
tile; the certificates `R897Tiling`, `R990Tiling`, `R240Tiling` and the modules `F3All`, `F4All`, `S2All` formalize tilings
and layouts of D. Paliy. See the paper's bibliography.

## Contents

* `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`: Lean `v4.30.0`, Mathlib tag `v4.30.0`
  (commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`) and its dependencies, pinned.
* `Erdos634/`: 4678 modules on disk. 3597 are written modules (including 43 hand-written files in `Refl/`); 1081 (`Erdos634/Refl/M*.lean`, about 490 MB) are
  generated search certificates of moderate size. The seven largest certificates (4462 generated modules, about
  1.7 GB) are not stored; `code/regen_cert.sh` regenerates them (see below).
* `Erdos634.lean`: the library root; it imports `Erdos634.All`.
* `axioms/Axioms<Aggregate>.lean`: `#print axioms` for every declaration of the table below, grouped by the
  first aggregate that contains it.

The modules are grouped in aggregates that do not import one another, because a single `lean` process for the
union would need too much memory:

| aggregate | modules | contents |
|---|---|---|
| `Erdos634.All` | 3093 | every module whose import closure contains no search certificate, among them the whole proof of Theorem 1.1 (primes) |
| `Erdos634.AllThreshold` | 1347 | the base-β row (Section 7), with 182 certificate modules |
| `Erdos634.AllSpectrum` | 2481 | the statements on the values up to 200 that use a search certificate, with 1081 certificate modules |
| `Erdos634.AllCert1` | 2480 | 154, 156, scale two, thresholds; certificates S1N156, ISO154, S4N184 |
| `Erdos634.AllCert2` | 1116 | 132; certificate ISO132 |
| `Erdos634.AllCert3` | 1013 | 161; certificate S3N161 |
| `Erdos634.AllCert4` | 1118 | 184; certificates S4N184, ISO184 |
| `Erdos634.AllCert5` | 3938 | 135; certificate EQ135 (2791 modules) |
| `Erdos634.AllCertW2` | 437 + 670 certificate modules, 5 others | 204 and 228 (second route); certificates G204 (437 modules) and G228 (670 modules), not stored: `code/regen_cert.sh G204`, `G228` |
| `Erdos634.AllR8` | 127 | 345 and 506 (tilings, Paliy's layouts, kernel-checked); the family theorems `PRevAll.prev_family`, `PF2All.pf2_family`, `PF3All.pf3_family` (Paliy's constructions, formalized) and the 22 R8 values as their instances; (v1.16) the eight template tile counts 11625, 66960, 119040, 121765, 167865, 186000, 364560, 603750 (`Draft/LadderFam`, `Draft/T<N>`, `Draft/AllTemplates`) |

(Module counts include the regenerated certificate modules for `AllCert1` to `AllCert5`.)

## Checking

Requirements: `elan` (it installs the toolchain of `lean-toolchain`), `git`, `python3`; for the certificates
also a Rust toolchain (`cargo`). Memory: one `lean` process of this library needs up to about 13.5 GB (measured: 13.4 GB for `R126TilingBridge.lean`, 11.9 GB for `Draft/G3CIso2673.lean`); build the
aggregates one at a time, and one module at a time (`lake build` alone starts about one `lean` per core). Disk:
about 7 GB for Mathlib and about 3 GB of build products for `All`, up to about 16 GB with every aggregate and certificate.
Lake also leaves one `.setup.json` file of 2 to 3 MB per module in `.lake/build/ir` (about 7 GB for `All`); these
files are only read when the module is compiled and can be deleted
(`find .lake/build/ir -name '*.setup.json' -delete`).

From the directory `lean/`:

```
lake exe cache get                                            # Mathlib build products
python3 ../code/lakeserial.py . build Erdos634.All            # serial build, one module at a time
lake env lean axioms/AxiomsAll.lean                           # axioms of the declarations in All
python3 ../code/lakeserial.py . build Erdos634.AllThreshold
lake env lean axioms/AxiomsAllThreshold.lean
python3 ../code/lakeserial.py . build Erdos634.AllSpectrum
lake env lean axioms/AxiomsAllSpectrum.lean
```

`code/lakeserial.py` builds the modules of the target in dependency order with a single `lean` process at a
time and stops the build if the resident memory of `lean`/`lake` exceeds `LAKE_RSS_LIMIT_GB` (default 14).
`lake build Erdos634.All` gives the same result on a machine with enough memory for the parallel build.
Every `#print axioms` line should read `[propext, Classical.choice, Quot.sound]`. No shipped module contains
`sorry` or declares an axiom. Exactly two modules contain a `native_decide` call: `Draft/NogoCount37.lean` (`nogoCount37_eq_10560`, `nogoGammaJunctions_eq_7`) and `Draft/PropNorm.lean` (`count_144`); both are imported by `Erdos634.All`, so `lake build Erdos634.All` builds them with `Lean.ofReducible`/`Lean.reduceBool`. No declaration cited by the paper depends on them: `axioms/*.lean` list only the three standard axioms for every cited declaration, and `code/axiom_gate.py` (run by `code/reproduce.sh`) fails otherwise. In particular the closures of the headline theorems (primes, the counts up to 200, Theorem D') contain neither module.

Measured on the author's machine (Apple silicon, 24 GB), serial build with Mathlib from the cache: the closure of
Theorem 1.1 (`Draft/PrimeCharacterization.lean`, `Draft/TheoremP6.lean`, 399 modules) in about 50 minutes; modules
that check explicit tilings or large decision tables take one to three minutes each, so that a serial build of all
of `All` (3093 modules) takes many hours. Peak memory of one `lean` process: 13.4 GB.

### The large certificates

The certificates S1N156, ISO154, S4N184, ISO132, S3N161, ISO184 and EQ135 are described by
`data/certificates/MANIFEST.tsv` (search parameters, node counts, SHA-256 of the search tree and of the
generated Lean text; the file documents its columns). From the repository root:

```
code/regen_cert.sh all            # or one name, e.g.  code/regen_cert.sh S4N184
```

For each certificate the script builds `rust/mrv2` and `rust/certgenm` (or `rust/certgenx`), reruns the float
search (`rust/mrv2/pf4.sh`, one thread, under 2 GB), checks the SHA-256 of the tree, replays it in exact
arithmetic into Lean modules under `lean/Erdos634/Refl/`, and checks the SHA-256 of the concatenated Lean text
against the manifest; any mismatch stops it. The float search is not trusted: the Lean kernel checks every node
of the exact certificate. Recorded search times: S4N184 3 s, ISO154 about 3 min, S1N156 about 10 min, ISO184
about 12 min, ISO132 about 24 min, S3N161 about 39 min, EQ135 about 3 min (search restricted at the root), plus
the exact replay (under a minute for S4N184). Then, from `lean/`:

```
python3 ../code/lakeserial.py . build Erdos634.AllCert1     # then AllCert2, ..., AllCert5, one at a time
lake env lean axioms/AxiomsAllCert1.lean                     # and so on
```

The kernel check of each certificate takes from minutes to a few hours; that of EQ135 (135 tiles,
1,326,256 nodes) about five hours.

Checked in this layout for S4N184: `code/regen_cert.sh S4N184` reproduced the tree and the 110 Lean modules
with the SHA-256 values of the manifest, in 50 s of wall time and 0.4 GB of memory (Rust build excluded).

## Lean map

Paper statement, Lean declaration (full name), file, and the first aggregate whose import closure contains
the file. The paper's Table 3 gives the same declarations; a statement is checked by building that aggregate
and running the corresponding file in `axioms/`.

| paper | Lean declaration | file (under `lean/Erdos634/`) | aggregate |
|---|---|---|---|
| Theorem 1.1 | `Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff` | `Draft/PrimeCharacterization.lean` | All |
|  | `Erdos634.Draft.TheoremP6.theoremP_6` | `Draft/TheoremP6.lean` | All |
| Theorem 1.2 | `Erdos634.Draft.BaseBetaFullUnc.basebeta_full_unc` | `Draft/BaseBetaFullUnc.lean` | All |
|  | `Erdos634.Draft.UniformThreshold.not_betaTilable_one` | `Draft/UniformThreshold.lean` | AllThreshold |
| Theorem 1.3 | `Erdos634.Draft.Spectrum200g.tileCount_iff_le_200g` | `Draft/Spectrum200g.lean` | AllSpectrum |
|  | `Erdos634.Draft.Spectrum200g.tileCount_iff_le_131` | `Draft/Spectrum200g.lean` | AllSpectrum |
|  | `Erdos634.Draft.N143.tileCount_143` | `Draft/N143.lean` | AllSpectrum |
|  | `Erdos634.Draft.N132F.not_tileCount_132` | `Draft/N132Final.lean` | AllCert2 |
|  | `Erdos634.Draft.Spectrum200Cond4.decided_154_156` | `Draft/Spectrum200Cond4.lean` | AllCert1 |
|  | `Erdos634.Draft.N161F.not_tileCount_161` | `Draft/N161Final.lean` | AllCert3 |
|  | `Erdos634.Draft.N184F.not_tileCount_184` | `Draft/N184Final.lean` | AllCert4 |
|  | `Erdos634.Draft.N135F.not_tileCount_135` | `Draft/N135Final.lean` | AllCert5 |
|  | `Erdos634.Draft.Spectrum200Excl.tileCount_iff_le_200_of_excl` | `Draft/Spectrum200Excl.lean` | AllSpectrum |
| Theorem 1.4 | `Erdos634.Draft.ISUMain.thmIso_unrestricted` | `Draft/ISUMain.lean` | All |
| Theorem 1.5 | `Erdos634.Draft.Residue.betaTilable_ge` | `Draft/ResidueSeed.lean` | AllThreshold |
|  | `Erdos634.Draft.Residue.wTilable_ge` | `Draft/ResidueSeed.lean` | AllThreshold |
| Theorem 1.6 | `Erdos634.Draft.SideRun.Setup.side_theorem'` | `Draft/SideRunRules.lean` | AllThreshold |
| Corollary 1.7 | `Erdos634.Draft.SideRun.wTilable_e1_iff` | `Draft/SideRun.lean` | AllThreshold |
|  | `Erdos634.Draft.SideRun.not_betaTilable_e1_le_half` | `Draft/SideRunHalf.lean` | AllThreshold |
| Theorem 1.8 | `Erdos634.Draft.SideRunG.thm_siderunall_angles_T` | `Draft/SideRunGAngles.lean` | AllThreshold |
|  | `Erdos634.Draft.SideRunG.thm_siderunall_angles_W` | `Draft/SideRunGAngles.lean` | AllThreshold |
| Corollary 1.9 | `Erdos634.Draft.SideRunG.ebelow_a` | `Draft/SideRunGMain.lean` | AllThreshold |
|  | `Erdos634.Draft.SideRunG.ebelow_b` | `Draft/SideRunGMain.lean` | AllThreshold |
| Corollary 1.10 | `Erdos634.Draft.SideRunGA.thickw_a` | `Draft/SideRunGThick.lean` | AllThreshold |
|  | `Erdos634.Draft.SideRunGA.thickw_b` | `Draft/SideRunGThick.lean` | AllThreshold |
|  | `Erdos634.Draft.SideRunGA.thickw_c` | `Draft/SideRunGThick.lean` | AllThreshold |
| Proposition 1.11 | `Erdos634.Draft.LayerE1.betaTilable_succ` | `Draft/LayerE1.lean` | AllThreshold |
|  | `Erdos634.Draft.LayerE1.exists_min_scale` | `Draft/LayerE1.lean` | AllThreshold |
|  | `Erdos634.Draft.LayerE1.threshold_e1_iff_top` | `Draft/LayerE1.lean` | AllThreshold |
| Proposition 2.2 | `Erdos634.Geometry.Dissection.volume_target` | `Dissection.lean` | All |
|  | `Erdos634.Geometry.Dissection.hasAngleSums` | `AngleSumDissection.lean` | All |
|  | `Erdos634.WallEndpoints.chain_endpoints` | `WallEndpoints.lean` | All |
| Lemma 2.3 | `Erdos634.RunPartition.run_partition` | `RunPartition.lean` | All |
| Proposition 2.4 | `Erdos634.Ladder.ladder` | `Ladder.lean` | All |
|  | `Erdos634.Draft.TileCountFamilies.tileCount_scale` | `Draft/TileCountFamilies.lean` | All |
|  | `Erdos634.Draft.TileCountFamilies.tileCount_two_squares` | `Draft/TileCountFamilies.lean` | All |
|  | `Erdos634.Draft.TileCountFamilies.tileCount_three_sq` | `Draft/TileCountFamilies.lean` | All |
|  | `Erdos634.Draft.TileCountFamilies.tileCount_six_sq` | `Draft/TileCountFamilies.lean` | All |
| Proposition 2.5 | `Erdos634.Draft.LemmaCFinal.lemmaC_general` | `Draft/LemmaCFinal.lean` | All |
|  | `Erdos634.Draft.LemmaPProof.lemmaP_general` | `Draft/LemmaPProof.lean` | All |
| Lemma 2.7 | `Erdos634.Geometry.vertex_multiplicities` | `Dissection.lean` | All |
|  | `Erdos634.BaseBetaCorners.corner_beta_unique` | `BaseBetaCorners.lean` | All |
|  | `Erdos634.BaseBetaCorners.corner_apex_unique` | `BaseBetaCorners.lean` | All |
| Lemma 3.1 | `Erdos634.Geometry.Paper.lem_cancel` | `Draft/FluxPaperLemCancel.lean` | All |
| Lemma 3.2 | `Erdos634.Geometry.Paper.lem_value_alpha` | `Draft/FluxPaper.lean` | All |
|  | `Erdos634.Geometry.Paper.lem_value_beta` | `Draft/FluxPaper.lean` | All |
| Corollary 3.3 | `Erdos634.Geometry.Paper.cor_int_anchored` | `Draft/FluxPaperCorIntAnchored.lean` | All |
| Lemma 3.4 | `Erdos634.NonIntegrality.k_not_dvd` | `NonIntegrality.lean` | All |
| Proposition 3.5 | `Erdos634.Rationality.tile_rational` | `Rationality.lean` | All |
| Proposition 3.6 | `Erdos634.Draft.OtherSpectraFull.otherspectra` | `Draft/OtherSpectraFull.lean` | All |
| Proposition 3.7 | `Erdos634.Draft.FDDSpectrumPaper.spectrum_paper` | `Draft/FDDSpectrumPaper.lean` | All |
| Proposition 4.1 | `Erdos634.Draft.FDBMod12Converse.thm_mod12` | `Draft/FDBMod12Converse.lean` | All |
| Lemma 4.3 | `Erdos634.Draft.PierceScale.thm_pierce_scale` | `Draft/PierceScale.lean` | All |
|  | `Erdos634.BaseBetaWalks.apex_leftover_nonrepresentable` | `BaseBetaWalks.lean` | All |
| Proposition 5.1 | `Erdos634.Geometry.Row5.theoremE_sixty` | `Draft/FluxCRow5.lean` | All |
|  | `Erdos634.Geometry.Row5.theoremE_twoPiThree` | `Draft/FluxCRow5.lean` | All |
| Theorem 5.2 | `Erdos634.Draft.E60Graph.sixty_has_a_relation` | `Draft/E60Count.lean` | All |
|  | `Erdos634.Draft.E120Graph.twoPiThree_has_a_relation` | `Draft/E120Count.lean` | All |
|  | `Erdos634.Draft.E60Irr.sixty_commensurable` | `Draft/E60Irr.lean` | AllSpectrum |
|  | `Erdos634.Draft.E120Irr.twoPiThree_commensurable` | `Draft/E120Irr.lean` | AllSpectrum |
| Corollary 5.3 | `Erdos634.Draft.E60Irr.e60Pair_of_not_isSquare` | `Draft/E60Irr.lean` | AllSpectrum |
|  | `Erdos634.Draft.E120Irr.e120Pair_of_not_isSquare` | `Draft/E120Irr.lean` | AllSpectrum |
| Proposition 6.1 | `Erdos634.Draft.TileCountSpectrum.tileCount_seven_sq_iff` | `Draft/TileCountSpectrum.lean` | All |
|  | `Erdos634.Draft.TileCountSpectrum.tileCount_eleven_sq_iff` | `Draft/TileCountSpectrum.lean` | All |
|  | `Erdos634.Draft.SporadicCounts.tc77` | `Draft/SporadicCounts.lean` | All |
|  | `Erdos634.R84TilingBridge.r84_nonempty_congruentDissection` | `R84TilingBridge.lean` | All |
|  | `Erdos634.R88TilingBridge.r88_nonempty_congruentDissection` | `R88TilingBridge.lean` | All |
|  | `Erdos634.R126TilingBridge.r126_nonempty_congruentDissection` | `R126TilingBridge.lean` | All |
|  | `Erdos634.R189TilingBridge.r189_nonempty_congruentDissection` | `R189TilingBridge.lean` | All |
|  | `Erdos634.Draft.N143.dissection_143_unit` | `Draft/N143.lean` | AllSpectrum |
| Proposition 6.2 | `Erdos634.Draft.N135.tileCount_135_iff` | `Draft/N135Red.lean` | AllSpectrum |
| Theorem 6.3 | `Erdos634.Draft.N135F.not_tileCount_135` | `Draft/N135Final.lean` | AllCert5 |
| Proposition 6.4 | `Erdos634.Draft.NSQM.s5_base_word2_hasSides` | `Draft/S5Family.lean` | All |
|  | `Erdos634.Draft.NSQM.s5_family_2k_hasSides` | `Draft/S5Family.lean` | All |
|  | `Erdos634.Draft.NSQM.atom_shape_te` | `Draft/AtomShape.lean` | All |
|  | `Erdos634.Draft.NSQM.atom_not_squarefree` | `Draft/AtomShape.lean` | All |
|  | `Erdos634.Draft.NSQM.b3prime` | `Draft/B3Prime.lean` | All |
| Proposition 6.5 | `Erdos634.Draft.GAU.gapA_sq` | `Draft/GAUFinal.lean` | All |
| Proposition 6.6 | `Erdos634.Draft.TwoPrime.two_prime_tileCount_iff` | `Draft/TwoPrime.lean` | AllSpectrum |
| Theorem 6.7 | `Erdos634.Draft.Sqfree3Mod8.not_tile_sqfree_3mod8` | `Draft/Sqfree3Mod8.lean` | AllSpectrum |
|  | `Erdos634.Draft.Sqfree7Mod8.tile_sqfree_7mod8_form` | `Draft/Sqfree7Mod8.lean` | AllSpectrum |
|  | `Erdos634.Draft.Sqfree7Mod8.sector_below_455` | `Draft/Sqfree7Mod8.lean` | AllSpectrum |
|  | `Erdos634.Draft.QPExact.tile_sqfree_5mod8_explicit` | `Draft/QPExact.lean` | AllSpectrum |
|  | `Erdos634.Draft.QPExact.sector5_below_517` | `Draft/QPExact.lean` | AllSpectrum |
| Theorem 7.1 | `Erdos634.Draft.WSeedG.beta_seed` | `Draft/WSeedGAssemble.lean` | AllThreshold |
|  | `Erdos634.Draft.WSeedG.w_seed` | `Draft/WSeedGW.lean` | AllThreshold |
| Proposition 7.2 | `Erdos634.Draft.BaseBetaScale2.basebeta_scale_two` | `Draft/BaseBetaScale2.lean` | AllCert1 |
|  | `Erdos634.Draft.BaseBetaScale2.scale_two_1_2_exists` | `Draft/BaseBetaScale2.lean` | AllCert1 |
| Proposition 7.3 | `Erdos634.Draft.SideRunGA.thm_cornerrun` | `Draft/SideRunGCornerMainB.lean` | AllThreshold |
|  | `Erdos634.Draft.SideRunGA.thm_cornerrun_addendum` | `Draft/SideRunGCornerMainB.lean` | AllThreshold |
| Proposition 7.4 | `Erdos634.Draft.SignedDecompW.signed_decomposition_member_W` | `Draft/SignedDecompW.lean` | AllThreshold |
|  | `Erdos634.Draft.LayerG.layer_real` | `Draft/LayerG.lean` | AllThreshold |
|  | `Erdos634.Draft.LayerG.layer_c_i` | `Draft/LayerG.lean` | AllThreshold |
|  | `Erdos634.Draft.LayerG.layer_c_ii` | `Draft/LayerGChord.lean` | AllThreshold |
| Proposition 7.5 | `Erdos634.Draft.WStripG.wstrip_step` | `Draft/WStrip.lean` | AllThreshold |
|  | `Erdos634.Draft.WStripChord.wstrip_c` | `Draft/WStripChord.lean` | AllThreshold |
|  | `Erdos634.Draft.WStripChord.wstrip_d` | `Draft/WStripChord.lean` | AllThreshold |
| Proposition 7.6 | `Erdos634.Draft.Residue.threshold_iff_small` | `Draft/ResidueSeed.lean` | AllThreshold |
|  | `Erdos634.Draft.UniformThreshold.threshold_1_2` | `Draft/UniformThreshold.lean` | AllThreshold |
|  | `Erdos634.Draft.UniformThreshold.threshold_1_3` | `Draft/UniformThresholdCert.lean` | AllCert1 |
|  | `Erdos634.Draft.UniformThreshold.threshold_2_3` | `Draft/UniformThresholdCert.lean` | AllCert1 |
|  | `Erdos634.Draft.UniformThreshold.threshold_1_4_of_ne_three` | `Draft/UniformThresholdCert.lean` | AllCert1 |
|  | `Erdos634.Draft.UniformThreshold.threshold_3_4_of_ne_three` | `Draft/UniformThresholdCert.lean` | AllCert1 |
|  | `Erdos634.Draft.E1ScaleTwo.thresholdAt_e1_of` | `Draft/E1ScaleTwo.lean` | AllThreshold |
|  | `Erdos634.Draft.SideRun.thresholdAt_e1_le_half` | `Draft/SideRunHalf.lean` | AllThreshold |
| Proposition 7.7 | `Erdos634.Draft.Blind.invariant_blind` | `Draft/ThresholdBlind.lean` | AllThreshold |
| Section 8.2 (text) | `Erdos634.Draft.N330.tileCount_330` | `Draft/N330.lean` | All |
| Section 8.2 (text) | `Erdos634.Draft.N897.tileCount_897` | `Draft/N897.lean` | All |
| Section 8.2 (text) | `Erdos634.Draft.S2All.s2_family_all` | `Draft/S2All.lean`, `Draft/S2AllTheta.lean` | All |
| Section 8.2 (text) | `Erdos634.Draft.F4All.f4_family` | `Draft/F4All.lean` | All |
| Section 8.2 (text) | `Erdos634.Draft.F3All.f3_family` | `Draft/F3All.lean` (+ F3Core, F3Defs, F3Disj1-4, F3Sub, F3Tile, F3Asm) | All |
| Section 6 (text) | `Erdos634.Draft.EqSemigroup.eq357_semigroup` | `Draft/EqSemigroup.lean` | All |
| Section 6 (text) | `Erdos634.Draft.Iso357Semigroup.iso357_semigroup` | `Draft/Iso357Semigroup.lean` | All |
| Section 8 (text) | `Erdos634.Draft.HerdtFamily.herdt_uniform` (Herdt macro-dissection uniform in (u,v), (v²−u²)³v² > u⁸) | `Draft/HerdtFamily.lean` | All |
| Section 8.2 (text) | `Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzE` | `Draft/NSQMMainZE.lean` | All |
| Section 8.2 (text) | `Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzET` (+ `no_dissection_168`, `no_dissection_248`) | `Draft/NSQMMainZET.lean`, `Draft/NSQRWT.lean`, `Draft/NSQMMainZETWitness.lean` | AllThreshold |
| Theorem 8.12 (Theorem D'; with Theorem 8.11 (C) and Corollary W_2, A' for d = 1 as cases) | `Erdos634.Draft.ThmD.thmD_standalone`, `Erdos634.Draft.ThmD.thmDStatement_geo` | `Draft/ThmDStatementGeo.lean` (about 105 modules `Draft/ThmD*.lean`, `Draft/ThmC*.lean`, `Draft/APrime*.lean`) | AllThreshold |
| Section 8.2 (text), final chain | `Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETWD`, `Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETW`, `Erdos634.Draft.NSQM.raStatement_of_s5w`, `Erdos634.Draft.SideRunGT.theta_word_hasSides` | `Draft/ThmDChainW.lean`, `Draft/NSQMMainZETW.lean`, `Draft/NSQMS5W.lean`, `Draft/SideRunGThetaMain.lean` | AllThreshold |
| Section 8.2 (text), witnesses | `Erdos634.Draft.NSQM.cnzETWD_204`, `cnzETWD_268`, `no_dissection_276`, `cnzETWD_279`, `not_cnzETWD_72`, `not_cnzETWD_143`, `not_cnzETWD_320` | `Draft/ThmDChainWitnessW.lean`, `Draft/ThmDChainWitnessC.lean` | AllThreshold |
| Section 8.2 (text) | `Erdos634.Draft.ZhangEqui.zhang_equi_m`, `Erdos634.Draft.ZhangProps.zhang_five` | `Draft/ZhangEqui.lean`, `Draft/ZhangProps.lean` (+ ZhangBase, ZhangTrap, ZhangRot, ZhangIso, ZhangF1) | All |
| Section 8.2 (text) | `Erdos634.Draft.N990.tileCount_990` | `Draft/N990.lean` | All |
| Computation 6.9 | none (status S: a count by a program, not checked by the kernel) |  |  |
| Proposition 8.1 | none (status W: written proof, not formalized) |  |  |
