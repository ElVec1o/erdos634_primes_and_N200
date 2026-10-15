#!/bin/bash
# reproduce.sh -- check every formal result of the paper, from a clean clone.
# Needs: elan (Lean toolchain from lean/lean-toolchain), Python 3, a Rust toolchain (cargo), about 16 GB of RAM,
# about 30 GB of free disk, and many hours (see lean/README.md for measured times).
# Lean modules are built ONE AT A TIME (code/lakeserial.py): a single lean process needs up to about 13.5 GB.
set -e
cd "$(dirname "$0")/.."
( cd lean && lake exe cache get )                                  # Mathlib build products
for t in All AllThreshold AllSpectrum; do                          # aggregates without the large certificates
  python3 code/lakeserial.py lean build "Erdos634.$t"
done
bash code/regen_cert.sh all                                        # regenerate the 7 large certificates, check SHA-256
for i in 1 2 3 4 5; do python3 code/lakeserial.py lean build "Erdos634.AllCert$i"; done
for f in lean/axioms/*.lean; do ( cd lean && lake env lean "../$f" ); done   # print the axioms of every cited result
