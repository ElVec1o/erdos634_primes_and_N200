# shared helpers (sourced). ROOT/R set by caller.
# NOTE (release 6.0): archived build script of the internal run; it refers to the project's internal directory layout and does not run in this repository. Kept for the record (commands, parameters).
ROOT=a scratch directory
R=$ROOT/internal working notes
# wait until no ERDOS/634 lean runs and free+inactive+speculative >= 7 GB (page 16 KiB: 458752 pages); disk check
wait_ready() {
  while :; do
    [ -e $R/STOP_NOW ] && return 2
    n=$(ps -axo command | grep "bin/lean " | grep ERDOS/634 | grep -v grep | wc -l)
    pg=$(vm_stat | awk '/Pages free|Pages inactive|Pages speculative/{gsub("\\.","",$NF); s+=$NF} END{print s+0}')
    [ "$n" -eq 0 ] && [ "$pg" -ge 458752 ] && break
    sleep 30
  done
  free=$(df -g / | awk 'NR==2{print $4}')
  if [ "$free" -lt 4 ]; then echo "DISK ${free}G" > $R/STOPPED_DISK; return 3; fi
  return 0
}
# build_mod <ShortModuleName>: one build through the build with peak RSS; echo "rc secs peakMB"
build_mod() {
  local id=$1 t0=$(date +%s) rc try
  for try in 1 2; do
    wait_ready; rc=$?; [ $rc -ne 0 ] && { echo "$rc 0 0"; return; }
    t0=$(date +%s)
    mod=Erdos634.Draft.$id; case $id in AllV6h*) mod=Erdos634.$id;; esac
    $ROOT/code/the build script $mod > $R/logs/bq2_$id.out 2>&1; rc=$?
    [ $rc -eq 0 ] && break
    grep -q "code 137\|rc=137" $ROOT/internal working notes 2>/dev/null || break
    sleep 60
  done
  local peak=$(grep " $id OK " $ROOT/internal working notes | tail -1 | sed -E 's/.*peakRSS=([0-9]+)MB.*/\1/')
  echo "$rc $(( $(date +%s) - t0 )) ${peak:-0}"
}
