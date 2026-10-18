#!/usr/bin/env python3
"""axiom_gate.py FILE... (or stdin): exit 1 unless every `#print axioms` result in the lean output is a subset of
{propext, Classical.choice, Quot.sound}.  Joins wrapped lines (a bracketed list may span several physical lines),
and also fails on 'declaration uses sorry', on 'error:' lines and on a file with zero axiom results.
Usage: code/lakeone.sh env lean lean/axioms/AxiomsAll.lean 2>&1 | python3 code/axiom_gate.py"""
import re, sys
OK = {"propext", "Classical.choice", "Quot.sound"}
txt = "".join(open(f, errors="replace").read() for f in sys.argv[1:]) if len(sys.argv) > 1 else sys.stdin.read()
bad, n = [], 0
for m in re.finditer(r"'([^']+)' depends on axioms: \[(.*?)\]", txt, re.S):
    n += 1
    ax = {a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()}
    if not ax <= OK: bad.append((m.group(1), sorted(ax - OK)))
n += len(re.findall(r"does not depend on any axioms", txt))
if re.search(r"declaration uses 'sorry'|declaration uses `sorry`", txt): bad.append(("<sorry warning>", ["sorry"]))
if re.search(r"^\S+:\d+:\d+: error", txt, re.M): bad.append(("<lean error>", ["error"]))
if n == 0: bad.append(("<no axiom results>", ["none"]))
for b in bad: print("AXIOM-GATE FAIL", b)
print(f"axiom_gate: {n} results, {len(bad)} failures"); sys.exit(1 if bad else 0)
