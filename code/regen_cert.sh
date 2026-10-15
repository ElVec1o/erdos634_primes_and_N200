#!/bin/bash
# regen_cert.sh NAME|all [OUTDIR] -- regenerate the Lean modules of a large search certificate.
#
# The seven certificates of data/certificates/MANIFEST.tsv (generated Lean text, about 1.7 GB in all) are not stored in
# the repository.  Each is a deterministic function of the sources in this repository:
#   1. the float search  rust/mrv2  (tile, target orientation, order, lookahead of the manifest row) writes a
#      refutation tree  rust/mrv2/out/pf4_<instance>_<tag>.tree   (seconds to hours; resumable, see rust/mrv2/pf4.sh);
#   2. the exact replay  rust/certgenm  turns the tree into  M<NAME>Inst.lean, M<NAME>Data<i>.lean, M<NAME>Sound.lean
#      (rows with a 14th column certgenx:...: the streaming generator rust/certgenx, which also writes M<NAME>SoundP<j>.lean).
# Both outputs are compared with the SHA-256 values of the manifest; a mismatch stops the script.
# OUTDIR defaults to lean/Erdos634/Refl (where the Lean files that use the certificates expect them); give another
# directory to regenerate without touching the tree, e.g. to check reproducibility.
# After regenerating, the kernel check is the build of the aggregates AllCert1 ... AllCert5, one module at a time:
#   python3 code/lakeserial.py lean build Erdos634.AllCert1      (and so on; see lean/README.md)
# Requirements: a Rust toolchain (cargo), python3.  Each search uses one thread and stays under 2 GB.
cd "$(dirname "$0")/.."
MAN=data/certificates/MANIFEST.tsv
sha() { cat "$@" | shasum -a 256 | cut -d' ' -f1; }
one() {
  NAME=$1; OUT=${2:-lean/Erdos634/Refl}
  row=$(grep -P "^$NAME\t" $MAN 2>/dev/null || grep "^$NAME	" $MAN)
  [ -n "$row" ] || { echo "$NAME: not in $MAN"; return 1; }
  IFS=$'\t' read -r name inst tile tgt N mode la nodes tbytes tsha nfiles lbytes lsha gen <<< "$row"
  # optional 14th column: certgenx:<mirror 0|1>:<root slots or -> = written by rust/certgenx (streaming; soundness in parts);
  # with root slots the search is restricted at the root (MRV_ROOTSLOTS, MRV_ROOTTREE=1) and MIRROR mode refutes the rest
  # 14th column certgenm+split:<PER>: written by rust/certgenm, then code/split_sound.py cuts M<NAME>Sound.lean into parts of
  # PER theorems (a module with 61,542 theorems overflows the stack of Lean, as for S3N161)
  mir=0; slots=-; genx=0; split=0
  case "$gen" in certgenx:*) genx=1; mir=$(echo "$gen" | cut -d: -f2); slots=$(echo "$gen" | cut -d: -f3);;
    certgenm+split:*) split=$(echo "$gen" | cut -d: -f2);; esac
  tag=$(echo "$tgt" | tr ' ' '_')_$(echo $mode | tr ':' '-')_la$la
  tree=rust/mrv2/out/pf4_${inst}_$tag.tree
  [ -x rust/mrv2/target/release/mrv2 ] || (cd rust/mrv2 && cargo build --release) || return 1
  [ -x rust/certgenm/target/release/certgenm ] || (cd rust/certgenm && cargo build --release) || return 1
  if [ $genx = 1 ]; then [ -x rust/certgenx/target/release/certgenx ] || (cd rust/certgenx && cargo build --release) || return 1; fi
  if [ ! -f $tree ]; then
    echo "$(date +%H:%M:%S) $NAME: tree missing, running the search ($inst, tile $tile on $tgt, $mode, la=$la)"
    mkdir -p rust/mrv2/out
    if [ "$slots" != "-" ]; then (cd rust/mrv2 && MRV_ROOTTREE=1 MRV_ROOTSLOTS=$slots ./pf4.sh $inst $tile $N 43200 "$tgt" $mode $la) || return 1
    else (cd rust/mrv2 && ./pf4.sh $inst $tile $N 43200 "$tgt" $mode $la) || return 1; fi
    [ -f $tree ] || { echo "$NAME: the search did not produce $tree (see rust/mrv2/out/pf4_$inst.log)"; return 1; }
  fi
  h=$(sha $tree)
  [ "$h" = "$tsha" ] || { echo "$NAME: TREE MISMATCH ($tree): sha256 $h, manifest $tsha"; return 1; }
  echo "$(date +%H:%M:%S) $NAME: tree ok ($nodes nodes)"
  args=$(python3 rust/mrv2/tricert.py $tgt $tile) || { echo "$NAME: tricert failed"; return 1; }
  eval "set -- $args"; Dn=$1; TGT=$2; TILE=$3
  mkdir -p "$OUT"
  rm -f "$OUT"/M${NAME}Inst.lean "$OUT"/M${NAME}Sound.lean "$OUT"/M${NAME}SoundP*.lean "$OUT"/M${NAME}Data*.lean
  if [ $genx = 1 ]; then
    CERTGENX_MIRROR=$mir rust/certgenx/target/release/certgenx $NAME $Dn "$TGT" "$TILE" $tree "$OUT" 150 700 4000 > "$OUT"/.regen_$NAME.log 2>&1 || { echo "$NAME: certgenx failed (see $OUT/.regen_$NAME.log)"; return 1; }
  else
    rust/certgenm/target/release/certgenm $NAME $Dn "$TGT" "$TILE" $tree "$OUT" 150 700 > "$OUT"/.regen_$NAME.log 2>&1 || { echo "$NAME: certgenm failed (see $OUT/.regen_$NAME.log)"; return 1; }
    if [ "$split" != 0 ]; then python3 code/split_sound.py $NAME $split "$OUT" >> "$OUT"/.regen_$NAME.log 2>&1 || { echo "$NAME: split_sound failed (see $OUT/.regen_$NAME.log)"; return 1; }; fi
  fi
  n=$(ls "$OUT"/M${NAME}Data*.lean | wc -l | tr -d ' ')
  np=$(ls "$OUT"/M${NAME}SoundP*.lean 2>/dev/null | wc -l | tr -d ' ')
  # hash by streaming the files in order (Inst, Data0.., SoundP0.., Sound): thousands of files do not fit a command line
  h=$( { cat "$OUT/M${NAME}Inst.lean"; i=0; while [ $i -lt $n ]; do cat "$OUT/M${NAME}Data$i.lean"; i=$((i+1)); done; i=0; while [ $i -lt $np ]; do cat "$OUT/M${NAME}SoundP$i.lean"; i=$((i+1)); done; cat "$OUT/M${NAME}Sound.lean"; } | shasum -a 256 | cut -d' ' -f1)
  [ "$h" = "$lsha" ] || { echo "$NAME: LEAN MISMATCH: sha256 $h, manifest $lsha ($((n+np+2)) files, manifest $nfiles)"; return 1; }
  rm -f "$OUT"/.regen_$NAME.log
  echo "$(date +%H:%M:%S) $NAME: $((n+np+2)) Lean files regenerated in $OUT, identical to the manifest; kernel check: build the AllCert aggregate that imports it (lean/README.md)"
}
if [ "$1" = all ]; then
  rc=0; for n in $(grep -v '^#' $MAN | tail -n +2 | cut -f1); do one $n "$2" || rc=1; done; exit $rc
else
  [ -n "$1" ] || { echo "usage: code/regen_cert.sh NAME|all [OUTDIR]"; exit 2; }
  one "$1" "$2"
fi
