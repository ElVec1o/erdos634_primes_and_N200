#!/bin/bash
# NOTE (release 6.0): archived build script of the internal run; it refers to the project's internal directory layout and does not run in this repository. Kept for the record (commands, parameters).
# prune_block.sh <BLK>   -- the ONLY place rm appears (user approval 2026-11-16: "approved, delete intermediates per block").
# Deletes ONLY build intermediates of the CHAIN modules (c<k>, q<k>) of block BLK, i.e. files
#   a scratch directory><...>.<ext>   with ext in PRUNE_EXTS (passed the lake up-to-date test).
# Never the batch F, the axioms X, never a .lean source. The full list is written first to logs/prune_<BLK>.txt.
R=a scratch directory working notes
B=a scratch directory
BLK=$1
[ -s $R/PRUNE_EXTS ] || { echo "no PRUNE_EXTS: not pruning"; exit 0; }
LIST=$R/logs/prune_$BLK.txt; : > $LIST
exts=$(cat $R/PRUNE_EXTS)
while read -r m; do
  short=${m##*.}
  case "$short" in WGapB${BLK}c[0-9]*|WGapB${BLK}q[0-9]*) ;; *) continue;; esac
  for e in $exts; do
    for f in $B/ir/Erdos634/Draft/$short.$e $B/lib/lean/Erdos634/Draft/$short.$e; do [ -e "$f" ] && echo "$f" >> $LIST; done
  done
done < $R/blocks/$BLK.mods
bad=0
while read -r f; do
  case "$f" in
    $B/*/WGapB[0-9]*) ;;
    *) bad=1;;
  esac
  case "$f" in *.lean|*F.*|*X.*) bad=1;; esac
  case "$f" in *.setup.json) ;; *) bad=1;; esac   # only the file type that passed the lake up-to-date test (PRUNE_EXTS = setup.json)
done < $LIST
[ $bad -eq 1 ] && { echo "REFUSED: path outside pattern" | tee -a $LIST; exit 1; }
bytes=$(xargs -I{} stat -f %z {} < $LIST 2>/dev/null | awk '{s+=$1} END{print s+0}')
while read -r f; do rm -f "$f"; done < $LIST
echo "$BLK pruned_files=$(wc -l < $LIST) bytes_freed=$bytes" >> $R/logs/prune_summary.txt
echo "$bytes"
