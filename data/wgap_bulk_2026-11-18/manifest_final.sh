#!/bin/bash
# NOTE (release 6.0): archived build script of the internal run; it refers to the project's internal directory layout and does not run in this repository. Kept for the record (commands, parameters).
ROOT=a scratch directory; R=$ROOT/internal working notes; cd $ROOT
{ ls lean/Erdos634/Draft/WGapB*.lean lean/Erdos634/AllV6h*.lean; for f in gen_bulk.sh gen_fx.sh gen_allv6h.sh drive_bulk.sh prune_block.sh lib.sh check_manifest.sh scan_closure.sh finalize.sh; do echo internal working notes; done; } | xargs shasum -a 256 > $R/SHA256_SOURCES.txt
total=$(grep -c . $R/expected5593.txt); gate=$(sed -n 2p $R/GATE_RESULT.txt)
tsecs=$(awk -F'\t' '$NF=="DONE"{for(i=1;i<=NF;i++) if($i ~ /^secs=/){sub("secs=","",$i); s+=$i}} END{print s+0}' $R/BLOCKS.tsv)
cls() { awk -v lo=$1 -v hi=$2 '$1>=lo && $1<hi' $R/expected5593.txt | grep -c .; }
{ echo "# MANIFEST_FINAL WGAP_BULK $(date '+%F %T')"
  echo "GATE: $(head -1 $R/GATE_RESULT.txt)"; echo "$gate"
  echo "N proved (kernel-checked not TileCount N, standard axioms only) / expected: see GATE line / $total"
  echo "by size class (expected list): <3e4: $(cls 0 30000) ; 3e4-1e5: $(cls 30000 100000) ; 1e5-5e5: $(cls 100000 500000) ; >=5e5: $(cls 500000 99999999)"
  echo "of which pre-existing instances (25 WGapLinkI + 18 WGapFinalS/L): $(grep -c . $R/have43.txt)"
  echo "FAILED values: $(grep -c . $R/FAILED.tsv) (file FAILED.tsv; failN.txt: $(grep -c . $R/failN.txt))"
  echo "SCAN: $(head -1 $R/SCAN_RESULT.txt)"
  echo "chain+batch build seconds (sum over blocks): $tsecs ; disk free now: $(df -h / | awk 'NR==2{print $4}')"
  echo "TODOCOUNT for the paper (the three markers): $total, if GATE is PASS (the count of values with a kernel-checked not TileCount N from not_tileCount_of_CNzFixW)."
  echo "REBUILD: sources are in lean/Erdos634/Draft/WGapB*.lean (+ generators in this work item). For each block id in BLOCKLIST: code/the build script Erdos634.Draft.WGapB<blk>c<k> ..., then WGapB<blk>F, WGapB<blk>X; or regenerate with gen_bulk.sh <blk> <G> <N...> then gen_fx.sh <blk>; drive_bulk.sh runs everything (the build only). Aggregates: code/the build script Erdos634.AllV6h0a ... Erdos634.AllV6h."
  echo "Credits: Beeson (theta targets, Lemma 52), Paliy, Beeson-Rosu, Laczkovich, Zhang, Herdt."
  echo "SHA256 of generator scripts and all sources: SHA256_SOURCES.txt ($(grep -c . $R/SHA256_SOURCES.txt) files)"; } > $R/MANIFEST_FINAL.md
cat $R/MANIFEST_FINAL.md
