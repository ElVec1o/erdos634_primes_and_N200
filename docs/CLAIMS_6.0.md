# Register of claims, version 6.0 (18 November 2026)

Labels: LEAN-INT = Lean, kernel-checked with the standard axioms propext, Classical.choice, Quot.sound only, internal audit only, no outside check. LEAN-STMT = Lean, statement audit by one internal reader. COMPUTED = exact check by program, not Lean. Program output = census list. No reader outside the project has checked any claim.

| claim | label | evidence (public file names) | what is NOT claimed |
|---|---|---|---|
| W-gap theorem: for coprime 2 <= e < f, f <= Me, M(f-e) < f, W_M(e,f) is not tiled by (2f^2-e^2)M^2 copies of (ef, f^2-e^2, f^2); rungs M(f-e) <= e+2..e+5 | LEAN-INT (`WGapRung.no_tiling_W_gap`, `no_tiling_W_rung2..5`) | `lean/Erdos634/AllV6*.lean`, `lean/axioms/AxiomsAllV6*.lean`, `lean/PAPER_MAP_V6.md`, `paper/erdos634_v6_main.pdf` | The bottom rung, e = 1, other targets; a rebuild in this repository (not done) |
| 5,593 values of N <= 10^6 are not tile counts, each by its own Lean theorem `not (TileCount N)` | LEAN-INT (aggregates `AllV6h*`; gate replay 5,593 of 5,593) | `data/wgap_bulk_2026-11-18/` (manifest, gate, scan, sha256 lists) | Anything about the other undecided values |
| Notch seed family, e = 1 threshold, band theorem, odd-e corollary, alpha hub; 1,410 TileCount instances | LEAN-INT (`thetaTiled_all`, `thetaTiled_e1_iff`, `thetaTiled_band`, `thetaTiled_oddE`, `alphaTiled_of_thetaTiled`) | `AllV6a..g`, `lean/PAPER_MAP_V6.md` | The forward half of the e = 1 threshold rests on one module whose audit carries an inherited gap |
| Structural corner theorems (`w_corner_run_long`, `w_bottom_rung_words`, `t_apex_one_leg_long`) | LEAN-STMT | `lean/PAPER_MAP_V6.md` | They decide no N |
| Foot property FOOT* is false for M > f (T_3(1,2), T_4(1,2)) | COMPUTED | `paper/erdos634_v6_main.pdf` | A proof for general M |
| 132 further explicit tile counts | COMPUTED (exact checkers with negative controls) | `data/registry/registry_tile_counts_TILING_EXISTS_6.0.tsv`, `data/witnesses/explicit_6.0/` (50 of 132 stored), `paper/erdos634_v6_companion.pdf` | Lean theorems (only the transfer step `isoTiled_of_f1Tiled` is Lean); outside verification |
| Census, non-squarefree N <= 10^6: 52,045 undecided (v5.0: 62,372) | Program output | `data/census/undecided_6.0.txt`, `RELEASE_NOTES_v6.0.md` | A Lean statement per N, except for the 5,593 above |
| Two code changes (`PropNorm`, `NogoCount37`: no `native_decide`) | LEAN-INT | `RELEASE_NOTES_v6.0.md` | Nothing new mathematically |
| Prime case, every N <= 200 decided, band theorem for base-beta | unchanged from v4.0, v5.0 | `RELEASE_NOTES_v4.0.md`, `RELEASE_NOTES_v5.0.md` | The full problem is open |
