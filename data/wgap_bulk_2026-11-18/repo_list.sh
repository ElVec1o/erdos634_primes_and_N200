#!/bin/bash
# NOTE (release 6.0): archived build script of the internal run; it refers to the project's internal directory layout and does not run in this repository. Kept for the record (commands, parameters).
# repo_list.sh : files to commit (sources and manifests only; NEVER build products under lean/.lake). Writes COMMIT_LIST.txt. No git commands.
ROOT=a scratch directory; R=$ROOT/internal working notes; cd $ROOT
{ ls lean/Erdos634/Draft/WGapB*.lean; ls lean/Erdos634/AllV6h*.lean
  for f in PLAN.md gen_bulk.sh gen_fx.sh gen_allv6h.sh drive_bulk.sh prune_block.sh lib.sh check_manifest.sh scan_closure.sh finalize.sh repo_list.sh manifest_final.sh BLOCKS.tsv BLOCKLIST PRUNE_EXTS expected5593.txt have43_map.txt SCAN_RESULT.txt GATE_RESULT.txt MANIFEST_FINAL.md SHA256_SOURCES.txt FAILED.tsv; do [ -e internal working notes ] && echo internal working notes; done
  ls internal working notes; } > $R/COMMIT_LIST.txt
grep -c "\.lake" $R/COMMIT_LIST.txt | sed 's/^/build-product lines (must be 0): /'; wc -l < $R/COMMIT_LIST.txt
