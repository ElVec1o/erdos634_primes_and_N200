#!/bin/bash
# reproduce.sh -- check every formal result of the paper, from a clean clone.
# Needs: elan (Lean toolchain from lean/lean-toolchain), Python 3, a Rust toolchain (cargo), about 16 GB of RAM,
# about 30 GB of free disk, and many hours (see lean/README.md for measured times).
# Lean modules are built ONE AT A TIME (code/lakeserial.py): a single lean process needs up to about 13.5 GB.
set -e
cd "$(dirname "$0")/.."
( cd lean && lake exe cache get )                                  # Mathlib build products
for t in All AllThreshold AllSpectrum AllR8; do                          # aggregates without the large certificates
  python3 code/lakeserial.py lean build "Erdos634.$t"
done
bash code/regen_cert.sh all                                        # regenerate the large certificates (incl. G204, G228), check SHA-256
for i in 1 2 3 4 5 W2; do python3 code/lakeserial.py lean build "Erdos634.AllCert$i"; done   # W2: 204, 228 (second route)
# print the axioms of every cited result and FAIL on anything outside {propext, Classical.choice, Quot.sound} or on sorryAx
for f in lean/axioms/*.lean; do
  ( cd lean && lake env lean "../$f" 2>&1 ) | python3 code/axiom_gate.py || { echo "axiom gate FAILED for $f"; exit 1; }
done
# exact verification of the template-search tilings of release v1.15 (an exact verifier, not Lean): every line must end in VERIFIED
( cd rust/bonfioli_tiling_engine && cargo build --release )
for f in data/witnesses/template_exact/*.gz data/witnesses/r8_exact/r8_*.gz; do   # (the u_*.gz files are checked by code/r8/fastverify.py; see r8_exact/verification_log_open_r8.txt)
  rust/bonfioli_tiling_engine/target/release/bte verify "$f" | grep -q "VERIFIED" || { echo "bte verify FAILED for $f"; exit 1; }
done
