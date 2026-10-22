# Addendum to release v3.1, in release v4.0 (22 October 2026)

Labels: LEAN = theorem of the Lean library, standard axioms only, audited inside the project only; COMPUTED = program output, no proof of its own; CLAIMED = another author's public claim.

## 1. Band theorem (LEAN, internal audit)
For coprime 2 <= e < f and M >= 2 with f <= 2Me < f + e (so d = 2Me - f satisfies 0 <= d < e): T_M(e,f) has no dissection into congruent copies of (ef, f^2-e^2, f^2), any number of tiles, reflections allowed. Lean: `Erdos634.LaczJunction.Walk.band_theorem_free`. Variants: `no_tiling_U` (d <= 1), `no_tiling_U2` (d <= 2). The proof is an induction on the base word of the boundary (no j consecutive c-edges of one type before an alpha/gamma end) carried on a lattice frame at all levels.
Scope of the audit (the gaps): the statement, the arithmetic of the band (brute force, f < 60, 42,185 cases, no failure) and the axioms were checked by fresh sessions; the geometric induction was read line by line twice; the planar geometry layer was not re-read line by line beyond that; the check against actual tilings is weak (the induction step is not exercised by the known witnesses); a negative control shows the induction does not extend to j = e + 1. No reader outside the project has checked it.
Not covered: d >= e (M < f; 19,151 census values), e = 1 (39 values), the thin side.
Where the Lean is: public repository "Formalizing triangle tiling in Lean", commit d728130 (`Erdos634/Draft/LaczFormalMJFinal.lean`, `AllLaczWalk.lean` and imports). Not rebuilt in this repository.

## 2. Registry extract and the 918
`data/registry/registry_basebeta_NO_TILING_4.0.tsv`: 3,204 instances excluded by the theorems above. Row = instance (e, f, M); not a value of N. The census program declares an N excluded when each failing leaf is killed by such a row; the leaf model is the program's. 918 further non-squarefree values <= 10^6 are excluded this way (smallest 1,964; largest 999,452; none <= 1,000). COMPUTED.

## 3. Census (non-squarefree N <= 10^6, 392,074 values)
| | excluded | undecided |
|---|---|---|
| v3.1 | 199,364 | 63,593 |
| v4.0 | 200,282 | 62,421 |
The known column is not printed: changes since v3.1 come from sweeps and registry rows that have not all been rechecked exactly or against Paliy's repository.

## 4. Prime case: dates
`theoremP_6` (Lean, internal audit only), our release of 15 October 2026; Paliy, public proof 29 September 2026 (no change seen since 17 October); Beeson-Rosu arXiv:2607.23453 v2 (16 October 2026), v3 (21 October 2026): a result on prime tile counts, no claim here about the proof. Parallel works.

## 5. Unchanged
Every N <= 200 decided; Conjecture C (existence half); the corrections of v3.0; no outside reader for theoremP_6, Theorem W, the thick rungs or the band theorem.
