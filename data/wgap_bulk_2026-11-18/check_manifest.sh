#!/bin/bash
# NOTE (release 6.0): archived build script of the internal run; it refers to the project's internal directory layout and does not run in this repository. Kept for the record (commands, parameters).
# check_manifest.sh : AXIOMS GATE. Re-runs (replays, up to date => nothing recompiled) every block axioms module X and AllV6h0a/b through the build,
# parses the FRESH output, and confirms that every N of expected5593.txt has a theorem `not TileCount N` depending only on
# propext, Classical.choice, Quot.sound.  Output GATE_RESULT.txt (PASS/FAIL, counts, missing N).
source a scratch directory working notes
cd $ROOT
: > $R/logs/gate_ok.txt
parse() { # $1 = log, $2 = module file name (X.lean)
  grep "$2" $1 | grep "depends on axioms" | awk '{
     match($0, /_[0-9]+'"'"' depends on axioms: \[/); if(RSTART==0) next
     name=substr($0,RSTART+1,RLENGTH); n=name; sub(/'"'"'.*/,"",n)
     ax=$0; sub(/.*axioms: \[/,"",ax); sub(/\].*/,"",ax); gsub(/ /,"",ax); k=split(ax,a,","); ok=1
     for(i=1;i<=k;i++) if(a[i]!="propext" && a[i]!="Classical.choice" && a[i]!="Quot.sound") ok=0
     if(ok) print n }' | sort -u
}
for b in $(awk -F'\t' '$NF=="DONE" && $3!="EMPTY"{print $1}' $R/BLOCKS.tsv | sort -u); do
  r=$(build_mod WGapB${b}X); set -- $r; [ $1 -ne 0 ] && echo "X build failed $b" >> $R/logs/gate_fail.txt
  parse $ROOT/internal working notes "WGapB${b}X.lean" >> $R/logs/gate_ok.txt
done
for m in AllV6h0c1 AllV6h0c2 AllV6h0c3 AllV6h0c4 AllV6h0c5 AllV6h0c6 AllV6h0c7 AllV6h0b; do
  r=$(build_mod $m); set -- $r; [ $1 -ne 0 ] && echo "$m build failed" >> $R/logs/gate_fail.txt
  parse $ROOT/internal working notes "$m.lean" >> $R/logs/gate_ok.txt
done
sort -u $R/logs/gate_ok.txt > $R/logs/gate_ok_u.txt
sort -u $R/expected5593.txt > $R/logs/_exp_lex.txt
miss=$(comm -23 $R/logs/_exp_lex.txt $R/logs/gate_ok_u.txt | sort -n | tr '\n' ' ')
extra=$(comm -13 $R/logs/_exp_lex.txt $R/logs/gate_ok_u.txt | sort -n | tr '\n' ' ')
nok=$(comm -12 $R/logs/_exp_lex.txt $R/logs/gate_ok_u.txt | grep -c .)
res=PASS; [ -n "$(echo $miss)" ] || [ -s $R/logs/gate_fail.txt ] && res=FAIL
{ echo "GATE $res $(date)"; echo "expected 5593 ; verified standard-axioms-only: $nok ; missing: [$miss] ; extra (outside list): [$extra]"; cat $R/logs/gate_fail.txt 2>/dev/null; } > $R/GATE_RESULT.txt
cat $R/GATE_RESULT.txt
