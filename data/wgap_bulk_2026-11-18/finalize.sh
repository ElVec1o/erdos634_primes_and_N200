#!/bin/bash
# NOTE (release 6.0): archived build script of the internal run; it refers to the project's internal directory layout and does not run in this repository. Kept for the record (commands, parameters).
# finalize.sh : waits for ALLDONE; retry of FAILED values (split path, one N per module, once); aggregates; gate; scan; manifest; commit list.
source a scratch directory working notes
cd $R
until [ -e ALLDONE ]; do ls STOPPED_DISK STOPPED_BAD STOPPED_STOP >/dev/null 2>&1 && exit 0; kill -0 $(cat logs/driver.pid) 2>/dev/null || exit 0; sleep 120; done
# (1) retries
if [ -s failN.txt ]; then
  nb=$(cat nextid); echo $((nb+1)) > nextid; id=$(printf '%03d' $nb)
  cp failN.txt failN_round1.txt; : > failN.txt
  SPLITAT=1 NOFX=1 ./gen_bulk.sh $id 1 $(sort -un failN_round1.txt | tr '\n' ' ') > /dev/null && echo $id >> BLOCKLIST
  echo "$(date +%T) retry block $id (split path, G=1) for failed $(grep -c . failN_round1.txt) values" >> PROGRESS.md
  mv ALLDONE ALLDONE.round1; nohup ./drive_bulk.sh > logs/driver2.out 2>&1 &
  sleep 30; until [ -e ALLDONE ]; do ls STOPPED_DISK STOPPED_BAD STOPPED_STOP >/dev/null 2>&1 && exit 0; kill -0 $(cat logs/driver.pid) 2>/dev/null || break; sleep 120; done
fi
# (2) aggregates, gate
./gen_allv6h.sh > logs/allv6h_gen.txt 2>&1
for m in $(cat allv6h_mods.txt); do r=$(build_mod $m); echo "$m $r" >> logs/allv6h_build.txt; done
./check_manifest.sh > logs/gate.out 2>&1
# (3) scan, (4) manifest, (5) commit list
./scan_closure.sh > logs/scan.out 2>&1
./manifest_final.sh > /dev/null 2>&1
./repo_list.sh > logs/repo_list.out 2>&1
echo done > FINALDONE
