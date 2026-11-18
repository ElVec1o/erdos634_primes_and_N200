#!/bin/bash
# NOTE (release 6.0): archived build script of the internal run; it refers to the project's internal directory layout and does not run in this repository. Kept for the record (commands, parameters).
# drive_bulk.sh -- detached, resumable driver (nohup). LANE 2 ONLY, one Lean build at a time (lib.sh wait_ready).
# Blocks: BLOCKLIST holds ids already generated (tests, retries, earlier runs); when it is exhausted the driver cuts new blocks
# from REMAIN_A.txt (CNzFixW yield, group size by N) then REMAIN_B.txt (rung values, group size 1), skipping N in DONE blocks.
# DONE blocks (BLOCKS.tsv last field DONE) are skipped => restart is safe. STOP file => stop after the current block.
# Credits: Beeson (theta targets, Lemma 52), Paliy, Beeson-Rosu, Laczkovich, Zhang, Herdt.
source a scratch directory working notes
cd $ROOT
T0=$(date +%s)
for f in STOPPED_DISK STOPPED_BAD STOPPED_STOP ALLDONE; do [ -e $R/$f ] && mv $R/$f $R/$f.old.$(date +%s); done
echo $$ > $R/logs/driver.pid
touch $R/BLOCKS.tsv $R/FAILED.tsv $R/BLOCKLIST $R/PROGRESS.md
[ -e $R/nextid ] || echo 1 > $R/nextid
[ -e $R/doneN.txt ] || : > $R/doneN.txt     # N proved (one per line, unsorted)
[ -e $R/failN.txt ] || : > $R/failN.txt     # N whose chain failed (conjunct false / not CNzFixW-decided)

summary() {
  local nb=$(awk -F'\t' '$NF=="DONE"{c++} END{print c+0}' $R/BLOCKS.tsv)
  local nd=$(grep -c . $R/doneN.txt) el=$(( $(date +%s) - T0 ))
  local left=$(( $(grep -c . $R/REMAIN_A.txt) + $(grep -c . $R/REMAIN_B.txt) - $(grep -cxFf $R/doneN.txt $R/REMAIN_A.txt) - $(grep -cxFf $R/doneN.txt $R/REMAIN_B.txt) - $(grep -cxFf $R/failN.txt $R/REMAIN_A.txt) - $(grep -cxFf $R/failN.txt $R/REMAIN_B.txt) ))
  { echo "SUMMARY $(date '+%F %T')"
    echo "blocks DONE $nb ; N proved $nd ; N failed (not CNzFixW-decided) $(grep -c . $R/failN.txt) ; N still to do (est.) $left"
    awk -v e=$el -v d=$nd -v l=$left 'BEGIN{ if(d>0) printf "this run %.1f h, rate %.1f s/N, projected %.1f h left\n", e/3600, e/d, l*e/d/3600 }'
    echo "disk free: $(df -h / | awk 'NR==2{print $4}')"; tail -3 $R/PROGRESS.md; } > $R/SUMMARY.md
}
nextid() { local i=$(cat $R/nextid); echo $((i+1)) > $R/nextid; printf '%03d' $i; }
# next chunk of N for a new block: sets CH_N, CH_G, CH_K
cut_chunk() {
  local done_or_fail=$(cat $R/doneN.txt $R/failN.txt | sort -u)
  local nd=$(awk -F'\t' '$NF=="DONE" && $1 !~ /^90/{c++} END{print c+0}' $R/BLOCKS.tsv)
  local K=50; [ $nd -ge 1 ] && K=100; [ $nd -ge 2 ] && K=150
  # batch size ladder only while F peaks stay < 7000 MB
  local fpk=$(awk '$3=="F" {gsub("MB","",$6); if($6+0>m)m=$6+0} END{print m+0}' $R/logs/modules.log 2>/dev/null)
  [ "${fpk:-0}" -ge 7000 ] && K=40
  CH_G=1
  for L in A B; do
    CH_N=$(grep -vxFf <(echo "$done_or_fail") $R/REMAIN_$L.txt | head -$K | tr '\n' ' ')
    [ -n "$(echo $CH_N)" ] && break
  done
  [ -z "$(echo $CH_N)" ] && return 1
  if [ $L = A ]; then
    local mx=$(echo $CH_N | tr ' ' '\n' | sort -n | tail -1)
    CH_G=8; [ $mx -ge 100000 ] && CH_G=4; [ $mx -ge 500000 ] && CH_G=3
  else CH_K=50; fi
  return 0
}
run_block() { # $1 = BLK ; builds chain modules, generates F/X, builds, checks axioms, prunes
  local BLK=$1 bt=$(date +%s) peak=0 m short out rc secs pk
  : > $R/blocks/$BLK.ok
  while read -r line; do
    short=${line%% *}; ns=${line#* }
    [ -e $R/STOP ] && { echo STOP > $R/STOPPED_STOP; summary; exit 0; }
    for q in $(grep -E "WGapB${BLK}q${short##*c}$" $R/blocks/$BLK.mods); do
      if [ -e $ROOT/lean/Erdos634/Draft/${q##*.}.lean ] ; then
        out=$(build_mod ${q##*.}); set -- $out; rc=$1; secs=$2; pk=$3
        [ $rc -eq 2 ] && { echo STOP > $R/STOPPED_STOP; summary; exit 0; }
        [ $rc -eq 3 ] && { summary; exit 0; }
        echo "$(date +%T) $BLK ${q##*.} rc=$rc ${secs}s ${pk}MB" >> $R/logs/modules.log
        [ "$pk" -gt "$peak" ] && peak=$pk
      fi
    done
    out=$(build_mod $short); set -- $out; rc=$1; secs=$2; pk=$3
    [ $rc -eq 2 ] && { echo STOP > $R/STOPPED_STOP; summary; exit 0; }
    [ $rc -eq 3 ] && { summary; exit 0; }
    echo "$(date +%T) $BLK $short rc=$rc ${secs}s ${pk}MB" >> $R/logs/modules.log
    [ "$pk" -gt "$peak" ] && peak=$pk
    if [ $rc -eq 0 ]; then echo "$short $ns" >> $R/blocks/$BLK.ok
    else
      # isolate failing N from the error log (line -> nearest preceding theorem line -> first number in its name)
      LG=$ROOT/internal working notes
      bad=$(grep -oE "^error: Erdos634/Draft/$short.lean:[0-9]+" $LG 2>/dev/null | sed -E 's/.*://' | sort -un | while read ln; do
              awk -v L=$ln 'NR<=L && /^theorem b_/ {t=$0} NR==L{print t}' $ROOT/lean/Erdos634/Draft/$short.lean; done |
            sed -E 's/^theorem b_[A-Za-z0-9]+_([0-9]+).*/\1/' | sort -u | tr '\n' ' ')
      [ -z "$(echo $bad)" ] && bad="$ns"          # could not isolate: the whole group fails
      surv=""; for n in $ns; do case " $bad " in *" $n "*) echo $n >> $R/failN.txt; printf '%s\t%s\t%s\n' "$n" "$BLK" "chain $short rc=$rc (conjunct false or build error)" >> $R/FAILED.tsv;; *) surv="$surv $n";; esac; done
      if [ -n "$(echo $surv)" ]; then   # survivors of a failed group: new block, same group size
        nb=$(nextid); NOFX=1 $R/gen_bulk.sh $nb 4 $surv >/dev/null && echo $nb >> $R/BLOCKLIST
        echo "$(date +%T) $BLK $short failed for [$bad]; survivors -> block $nb" >> $R/PROGRESS.md
      fi
    fi
  done < $R/blocks/$BLK.groups
  if [ ! -s $R/blocks/$BLK.ok ]; then printf '%s\t\tEMPTY\tDONE\n' "$BLK" >> $R/BLOCKS.tsv; return; fi
  [ -e $ROOT/lean/Erdos634/Draft/WGapB${BLK}F.lean ] || $R/gen_fx.sh $BLK
  local NLIST=$(tr '\n' ' ' < $R/blocks/$BLK.nlist)
  for s in F X; do
    out=$(build_mod WGapB$BLK$s); set -- $out; rc=$1; secs=$2; pk=$3
    [ $rc -eq 2 ] && { echo STOP > $R/STOPPED_STOP; summary; exit 0; }
    [ $rc -eq 3 ] && { summary; exit 0; }
    echo "$(date +%T) $BLK $s rc=$rc ${secs}s ${pk}MB" >> $R/logs/modules.log
    [ "$pk" -gt "$peak" ] && peak=$pk
    if [ $rc -ne 0 ]; then
      printf '%s\t%s\tbatch %s rc=%s\n' "$BLK" "$NLIST" "$s" "$rc" >> $R/FAILED.tsv
      printf '%s\t%s\tFAILED(batch %s)\n' "$BLK" "$NLIST" "$s" >> $R/BLOCKS.tsv
      echo "$(date +%T) $BLK FAILED batch $s -> STOPPED_BAD" >> $R/PROGRESS.md; echo "BAD $BLK batch" > $R/STOPPED_BAD; summary; exit 1
    fi
  done
  AX=$ROOT/internal working notes
  # the build replays the import closure's messages: look only at the b_final_ lines of this block's X module
  local n_ax=$(grep "WGapB${BLK}X.lean" $AX | grep -o "b_final_[0-9]*' depends on axioms" | sort -u | grep -c .) n_N=$(grep -c . $R/blocks/$BLK.nlist)
  local bad_ax=$(grep "WGapB${BLK}X.lean" $AX | grep "b_final_" | sed -E 's/.*\[(.*)\].*/\1/' | tr ',' '\n' | sed 's/ //g' | grep -v -x -E 'propext|Classical.choice|Quot.sound' | grep -c .)
  if grep "WGapB${BLK}X.lean" $AX | grep -q "sorryAx\|ofReduceBool\|error" || [ "$n_ax" -ne "$n_N" ] || [ "$bad_ax" -ne 0 ]; then
    printf '%s\t%s\tBAD(axioms n_ax=%s n_N=%s bad=%s)\n' "$BLK" "$NLIST" "$n_ax" "$n_N" "$bad_ax" >> $R/BLOCKS.tsv
    echo "BAD $BLK" > $R/STOPPED_BAD; echo "$(date +%T) $BLK BAD axioms" >> $R/PROGRESS.md; summary; exit 1
  fi
  local hashes=$(for m in $(cat $R/blocks/$BLK.mods); do f=$ROOT/lean/$(echo $m | tr . /).lean; [ -e $f ] && echo -n "${m##*.}=$(shasum -a 256 $f | cut -c1-16),"; done)
  tr ' ' '\n' <<< "$NLIST" | grep . >> $R/doneN.txt
  local pr=$($R/prune_block.sh $BLK 2>&1 | tail -1)
  # up-to-date check after the first pruned block (and a few later ones)
  local first=$(awk '{print $1}' $R/blocks/$BLK.ok | head -1)
  if [ ! -e $R/PRUNE_VERIFIED ] || [ $(( RANDOM % 25 )) -eq 0 ]; then
    wait_ready; code/the build script Erdos634.Draft.$first > /dev/null 2>&1
    if grep -q "after 0 serial module builds" internal working notes; then touch $R/PRUNE_VERIFIED; echo "$(date +%T) prune verify $BLK $first: nothing to build (OK)" >> $R/PROGRESS.md
    else mv $R/PRUNE_EXTS $R/PRUNE_EXTS.disabled.$(date +%s); echo BAD > $R/STOPPED_BAD; echo "$(date +%T) prune verify FAILED for $first: pruning disabled, stopped" >> $R/PROGRESS.md; summary; exit 1; fi
  fi
  printf '%s\t%s\tsha=%s\tsecs=%s\tpeakMB=%s\taxioms=OK\tpruned_bytes=%s\tDONE\n' "$BLK" "$NLIST" "$hashes" "$(( $(date +%s) - bt ))" "$peak" "$pr" >> $R/BLOCKS.tsv
  echo "$(date +%T) $BLK DONE ${n_N}N $(( $(date +%s) - bt ))s peak ${peak}MB pruned ${pr}B disk $(df -h / | awk 'NR==2{print $4}')" >> $R/PROGRESS.md
  local ndone=$(awk -F'\t' '$NF=="DONE"{c++} END{print c+0}' $R/BLOCKS.tsv); [ $((ndone % 10)) -eq 0 ] && summary
  local fr=$(df -g / | awk 'NR==2{print $4}'); [ "$fr" -lt 4 ] && { echo "disk $fr" > $R/STOPPED_DISK; summary; exit 0; }
}
while :; do
  [ -e $R/STOP ] && { echo STOP > $R/STOPPED_STOP; summary; exit 0; }
  BLK=""
  for b in $(cat $R/BLOCKLIST); do grep -qE "^$b"$'\t'".*DONE$" $R/BLOCKS.tsv || { BLK=$b; break; }; done
  if [ -z "$BLK" ]; then
    cut_chunk || break
    BLK=$(nextid)
    NOFX=1 $R/gen_bulk.sh $BLK $CH_G $CH_N > /dev/null || { echo "gen failed $BLK" >> $R/PROGRESS.md; echo "gen $BLK" > $R/STOPPED_BAD; exit 1; }
    echo $BLK >> $R/BLOCKLIST
  fi
  run_block $BLK
done
summary; echo done > $R/ALLDONE
