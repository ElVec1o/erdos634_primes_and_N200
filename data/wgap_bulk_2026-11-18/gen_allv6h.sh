#!/bin/bash
# NOTE (release 6.0): archived build script of the internal run; it refers to the project's internal directory layout and does not run in this repository. Kept for the record (commands, parameters).
# gen_allv6h.sh : writes lean/Erdos634/AllV6h0a, AllV6h0b (the 43 pre-existing instances + #print axioms), AllV6h1..n (8 batch modules WGapB<blk>F each),
# and AllV6h (root over all). Imports only per-value final/batch modules. Never overwrites. Credits: Beeson, Paliy, Beeson-Rosu, Laczkovich, Zhang, Herdt.
ROOT=a scratch directory; R=$ROOT/internal working notes; L=$ROOT/lean/Erdos634
H="UNAUDITED beyond internal checks. No sorry, no native_decide. Credits: Beeson (theta targets, Lemma 52), Paliy, Beeson-Rosu, Laczkovich, Zhang, Herdt."
for f in AllV6h AllV6h0a AllV6h0b; do [ -e $L/$f.lean ] && { echo "refusing: $f exists"; exit 1; }; done
{ echo "/- AllV6h0a: the pre-existing WGapLinkI instances inside the CNzFixW list, with axioms. $H -/"
  grep "WGapLinkI" $R/have43_map.txt | awk '{print "import " $2}' | sort -u
  grep "WGapLinkI" $R/have43_map.txt | awk '{print "#print axioms " $3}'; } > $L/AllV6h0a.lean
{ echo "/- AllV6h0b: the pre-existing WGapFinal* instances inside the CNzFixW list, with axioms. $H -/"
  grep "WGapFinal" $R/have43_map.txt | awk '{print "import " $2}' | sort -u
  grep "WGapFinal" $R/have43_map.txt | awk '{print "#print axioms " $3}'; } > $L/AllV6h0b.lean
blks=$(awk -F'\t' '$NF=="DONE" && $3!="EMPTY"{print $1}' $R/BLOCKS.tsv | sort -u)
k=0; i=0; roots=""
for b in $blks; do
  [ -e $ROOT/lean/Erdos634/Draft/WGapB${b}F.lean ] || continue
  if [ $((i % 8)) -eq 0 ]; then k=$((k+1)); [ -e $L/AllV6h$k.lean ] && { echo "refusing: AllV6h$k exists"; exit 1; }
    echo "/- AllV6h$k: batch modules of the bulk WGap run (imports only). $H -/" > $L/AllV6h$k.lean; roots="$roots $k"; fi
  echo "import Erdos634.Draft.WGapB${b}F" >> $L/AllV6h$k.lean; i=$((i+1))
done
{ echo "/- AllV6h: root over AllV6h0a, AllV6h0b, AllV6h1..$k : every not-TileCount instance of the CNzFixW list (5,593 values). $H -/"
  echo "import Erdos634.AllV6h0a"; echo "import Erdos634.AllV6h0b"; for r in $roots; do echo "import Erdos634.AllV6h$r"; done; } > $L/AllV6h.lean
echo "AllV6h0a AllV6h0b $(for r in $roots; do echo -n "AllV6h$r "; done)AllV6h" > $R/allv6h_mods.txt
echo "$i batch modules in $k aggregates"
