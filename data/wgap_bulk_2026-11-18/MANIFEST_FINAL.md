# MANIFEST_FINAL WGAP_BULK 2026-11-18 13:51:17
GATE: GATE PASS Wed Nov 18 13:39:36 +07 2026
expected 5593 ; verified standard-axioms-only: 5593 ; missing: [] ; extra (outside list): []
N proved (kernel-checked not TileCount N, standard axioms only) / expected: see GATE line / 5593
by size class (expected list): <3e4: 147 ; 3e4-1e5: 380 ; 1e5-5e5: 2242 ; >=5e5: 2824
of which pre-existing instances (25 WGapLinkI + 18 WGapFinalS/L): 43
FAILED values: 0 (file FAILED.tsv; failN.txt: 0)
SCAN: SCAN Wed Nov 18 13:51:15 +07 2026 closure files: 5062 ; code-position hits (sorry|native_decide|ofReduceBool|axiom): 0
chain+batch build seconds (sum over blocks): 120136 ; disk free now: 8.4Gi
TODOCOUNT for the paper (the three markers): 5593, if GATE is PASS (the count of values with a kernel-checked not TileCount N from not_tileCount_of_CNzFixW).
REBUILD: sources are in lean/Erdos634/Draft/WGapB*.lean (+ generators in this work item). For each block id in BLOCKLIST: code/the build script Erdos634.Draft.WGapB<blk>c<k> ..., then WGapB<blk>F, WGapB<blk>X; or regenerate with gen_bulk.sh <blk> <G> <N...> then gen_fx.sh <blk>; drive_bulk.sh runs everything (the build only). Aggregates: code/the build script Erdos634.AllV6h0a ... Erdos634.AllV6h.
Credits: Beeson (theta targets, Lemma 52), Paliy, Beeson-Rosu, Laczkovich, Zhang, Herdt.
SHA256 of generator scripts and all sources: SHA256_SOURCES.txt (2870 files)
