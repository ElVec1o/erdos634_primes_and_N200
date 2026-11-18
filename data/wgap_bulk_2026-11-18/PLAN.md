# PLAN WGAP_BULK 2026-11-16 (priority: 6.0 release; kernel-checked `not TileCount N` for the CNzFixW-decided values)
N LIST: yield_wgap_audited 5,351 + rung2 77 + rung3 65 + rung4 98 + 175571 + 342563 = 5,593 (coordinator, CNzFixW TRUE on all by the Rust audit wlink_audit_20261116), minus 43 with an existing instance (25 WGapLinkI*, WGapD*/WGapFinal*; 3 of them rung2: 3808, 3976, 8919) = 5,550 to do (25 already built as test blocks 902-905). Rung2 was missing from my first union (added 2026-11-16: 74 values appended to REMAIN_B).
  FINDING: removed_lift57.txt (CENSUS_2026-11-16b) is 57 values that ARE tile counts (F1/F2 tilings): `not TileCount` is false for them -> EXCLUDED.
  CORRECTION: 20252, 21000 are in removed_lift57 (real tile counts), so their failing conjuncts are the correct negative control, not a gap. EVERY rung 2/3/4 value must pass CNzFixP2;
  a rung value that fails a conjunct is a FINDING (Lean vs Rust transcription disagree): recorded in FAILED.tsv, reported to the coordinator at once. REMAIN_B (228 values) runs last, one N per chain module.
Size classes of REMAIN_A (5,297): <3e4: 75; 3e4-1e5: 341; 1e5-5e5: 2,131; >=5e5: 2,750 (these split the heavy half of the conjuncts into a q module).
MODULES: per group of G values ONE chain module WGapB<blk>c<k> (rest conjuncts + pruned S2 pieces + assembler b_cp2c_N; q module for N>=5e5),
  merged from the old 3 modules per N. Measured (peak/secs): G=10 @2.6e4: 5.7 GB/27 s; G=6 @6e4: 5.4 GB/24 s; G=5 @2.5e5: 7.2 GB/52 s;
  G=4 @1e6: q 4.9 GB/49 s + c 6.1 GB/76 s (vs ~61 s + 3 modules per N before). Choice: G=8 (<1e5), 4 (<5e5), 3 (>=5e5), 1 (REMAIN_B).
  Then WGapB<blk>F (heavy batch, imports WGapLightLink2, theorems b_final_N) and WGapB<blk>X (#print axioms for every b_final_N).
BLOCKS: 50 N (first), 100, then 150 N per block, the ladder only while F peaks stay < 7 GB (flat ~5.6 GB measured for 3-16 N). ~40 blocks.
ESTIMATE: ~31 h chain work (rates above) + ~1.5 h batches + waits for memory/other Lean jobs = ~35 h, finishing about 2 days if the machine is shared.
DISK on the first block: per N about 0.35 MB kept (.olean, .ilean, .trace, hashes) + .c/.c.hash tiny + .setup.json 0.64 MB per module.
UP-TO-DATE TEST (module WGapB904c0, via code/the build script; stashed with mv, not deleted): removing .setup.json -> "0 serial module builds" PASS;
  removing .c+.c.hash -> rebuild (FAIL); removing .ilean+.ilean.hash -> rebuild (FAIL). So PRUNE_EXTS = setup.json only (about 0.6 GB in total).
  Everything else is needed by lake and stays (total about 2 GB on disk at the end, from 12 GB free). Driver verifies after the first pruned block
  (nothing to build on its first module); if not: pruning disabled (PRUNE_EXTS moved aside), STOPPED_BAD.
FILES: gen_bulk.sh (chain modules), gen_fx.sh (F, X from the built groups), drive_bulk.sh (driver), prune_block.sh (the only rm), lib.sh.
STOPS: STOP file; STOPPED_DISK (< 3 GB free at a build or < 4 GB at a block end); STOPPED_BAD (axioms not standard / batch fails / prune verify fails).
