#!/bin/bash
# NOTE (release 6.0): archived build script of the internal run; it refers to the project's internal directory layout and does not run in this repository. Kept for the record (commands, parameters).
# gen_fx.sh <BLK>: writes the batch module WGapB<BLK>F and the block axioms module WGapB<BLK>X from blocks/<BLK>.ok
# (lines "<chain module short name> N N ..." of the chain modules that BUILT). Never overwrites.
ROOT=a scratch directory; D=$ROOT/lean/Erdos634/Draft; R=$ROOT/internal working notes
BLK=$1
CRED="Credits: Beeson (theta targets, Lemma 52), Paliy, Beeson-Rosu, Laczkovich, Zhang, Herdt.  UNAUDITED beyond internal checks.  No sorry, no native_decide."
FB=$D/WGapB${BLK}F.lean; XB=$D/WGapB${BLK}X.lean
[ -e $FB ] || [ -e $XB ] && { echo "refusing: exists"; exit 1; }
ALLN=$(awk '{for(i=2;i<=NF;i++) printf "%s ", $i}' $R/blocks/$BLK.ok)
{ echo "/- WGapB${BLK}F: HEAVY batch of not-TileCount theorems (gen_fx.sh).  $CRED -/"
  echo "import Erdos634.Draft.WGapLightLink2"
  awk '{print "import Erdos634.Draft." $1}' $R/blocks/$BLK.ok
  echo "namespace Erdos634.Draft.WGapPure"
  for N in $ALLN; do echo "theorem b_final_$N : ¬ Erdos634.Draft.TileCountFamilies.TileCount $N := not_tileCount_of_P $N (cnzFixP_of_P2 b_cp2c_$N)"; done
  echo "end Erdos634.Draft.WGapPure"; } > $FB
{ echo "/- WGapB${BLK}X: axioms of every final theorem of block ${BLK} (gen_fx.sh).  $CRED -/"
  echo "import Erdos634.Draft.WGapB${BLK}F"
  for N in $ALLN; do echo "#print axioms Erdos634.Draft.WGapPure.b_final_$N"; done; } > $XB
printf '%s\n' $ALLN > $R/blocks/$BLK.nlist
