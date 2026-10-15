#!/bin/bash
# pf4.sh NAME ta tb tc N TL "A B C" mode la  -- ONE run with the progress estimator and a 2 GB RSS watchdog; keeps the
# tree if it finishes.  RESUMABLE: the run writes a checkpoint every 120 s (MRV_CKPT, see src/main.rs);
# calling this script again with the same arguments continues from the checkpoint, and a finished run is not redone.
# TL is CUMULATIVE over all segments (MRV_TL).  PF_NOTREE=1: verdict only (no tree, small memory); it can continue a
# checkpoint written in tree mode, e.g. after KILLED_RSS.  Environment such as MRV_NGCAP is passed through.
cd "$(dirname "$0")"
NAME=$1; ta=$2; tb=$3; tc=$4; N=$5; TL=$6; o=$7; m=$8; la=$9
tag=$(echo "$o" | tr ' ' '_')_$(echo $m | tr ':' '-')_la$la
tree=out/pf4_${NAME}_$tag.tree; ck=out/pf4_${NAME}_$tag.ck
[ -n "$PF_NOTREE" ] && { export MRV_NOTREE=1; tree=-; }
MRV_CKPT=$ck MRV_TL=$TL MRV_PROGRESS=out/pf4_${NAME}_$tag.prog target/release/mrv2 $ta $tb $tc $o $N $la 1 30000000 1000 $tree $m ng > out/pf4_${NAME}_$tag.out 2> out/pf4_${NAME}_$tag.err &
pid=$!; t0=$(date +%s); st=RUN
while kill -0 $pid 2>/dev/null; do
  rss=$(ps -o rss= -p $pid 2>/dev/null | tr -d ' '); rss=${rss:-0}
  if [ "$rss" -gt 2000000 ]; then kill $pid; st="KILLED_RSS"; break; fi
  if [ $(( $(date +%s) - t0 )) -gt $(( TL + 1800 )) ]; then kill $pid; st="TIMEOUT_WALL"; break; fi
  # disk guard: the search is PAUSED (SIGSTOP) below PF_MINFREE_MB and resumed 1500 MB above it
  dk=$(( (dk + 1) % 30 )); if [ "$dk" = 0 ]; then fr=$(df -k / | tail -1 | awk '{print int($4/1024)}'); if [ "${fr:-99999}" -lt ${PF_MINFREE_MB:-4000} ]; then kill -STOP $pid; echo "$(date +%H:%M:%S) $NAME: PAUSED (free ${fr} MB on /)" >> out/pf_pause.log; while [ "$(df -k / | tail -1 | awk '{print int($4/1024)}')" -lt $(( ${PF_MINFREE_MB:-4000} + 1500 )) ]; do /bin/sleep 30; done; kill -CONT $pid; echo "$(date +%H:%M:%S) $NAME: RESUMED" >> out/pf_pause.log; fi; fi
  /bin/sleep 2
done
wait $pid 2>/dev/null
# a process that ended without printing a verdict died (killed from outside, crash): its checkpoint stays
if [ "$st" = RUN ]; then if grep -q "verdict=" out/pf4_${NAME}_$tag.out 2>/dev/null; then st=DONE; else st=DIED; fi; fi
grep -q "verdict=TIMEOUT" out/pf4_${NAME}_$tag.out 2>/dev/null && st="TIMEOUT"
[ "$st" != DONE ] && [ "$tree" != "-" ] && rm -f $tree
r=$(tail -1 out/pf4_${NAME}_$tag.out | grep -o 'verdict=[A-Z_]*\|CERT=[0-9]*\|TREE=[0-9]*\|secs=[0-9.]*' | tr '\n' ' ')
p=$(tail -1 out/pf4_${NAME}_$tag.prog 2>/dev/null | cut -c1-140)
res=$(head -1 out/pf4_${NAME}_$tag.err 2>/dev/null | grep -o "resumed from.*" | cut -c1-90)
echo "$(date +%H:%M:%S) $NAME o=[$o] m=$m la=$la ng${PF_NOTREE:+ notree}: $st ${TL}s $r | $p${res:+ | $res}" >> out/pf4_$NAME.log
