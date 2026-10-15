# Congruent dissections of a triangle: prime counts, the counts up to 200, and a family of isosceles targets

**Author:** Vico Bonfioli (vicobonfioli@gmail.com). The work was carried out with the assistance of Claude (Anthropic)
throughout, under the author's direction.

**Paper:** `paper/erdos634_primes_and_N200.pdf`, October 2026 (source `paper/erdos634_primes_and_N200.tex`).

Standing marks used below, as in the paper: **F** = theorem of the accompanying Lean 4 library, with the standard axioms
only (`propext`, `Classical.choice`, `Quot.sound`) and no `sorry`; **W** = written proof in the paper, not formalized;
**S** = outcome of a computer search or count without a kernel-checked certificate. The mark F says that the Lean kernel
has checked a proof of the formal statement. It does not say that an independent reader has compared the formal
statement with the mathematical one; that comparison has been made within this work only.

## Abstract

A positive integer N is a *tile count* if some triangle can be cut into N pairwise congruent triangles; Erdős asked for
the set of tile counts (Problem 634 of erdosproblems.com). The problem is not solved here. The results below are
theorems of an accompanying Lean 4 library unless stated otherwise. (1) A prime p is a tile count if and only if p = 3
or p ≢ 3 (mod 4). This is a theorem of the formal library, with the standard axioms; the formal statement has not yet
been compared with the mathematical one by an independent reader. (2) For 1 ≤ N ≤ 200 the tile counts are determined;
the largest search certificate, which excludes 135, has 1 326 256 nodes and is checked by the Lean kernel. (3) For a tile
with angles (α, β, 2π/3), α/π irrational, a signed-direction functional on directed edges gives two integrality
conditions; no prime number of such tiles tiles an isosceles, non-equilateral triangle. (4) For coprime 1 ≤ e < f let
T_M(e,f) be the isosceles triangle with legs Mf³ and base Me(3f² − e²), with the tile (ef, f² − e², f²). A tiling
exists for every M ≥ f (constructions of D. Paliy and M. Beeson, formalized here); there is none for M = 1, none when
2Me < f, and for e = 1 none when 2M ≤ f. The scales M ≥ 2 with f/(2e) < M < f are open, apart from three instances; the
open part is stated precisely.

## Conceptual abstract of the proof of Theorem 1.1

The tile is sorted into finitely many types by its angles. For each type, the area of the target and two boundary
weights give equations between integers. The weights come from a signed-direction functional: every edge of a tiling has
a direction jπ/3 + kα with integers j, k, the weight of a directed edge is its length times (-1)^j, the weight changes
sign when the edge is reversed, so the two sides of an interior segment cancel, and around one tile the weights add up to
±(c + a − b). The sum over the N tiles, about which nothing is known, is thereby exchanged for the weight of the boundary
of the target, which is explicit. For a prime N ≡ 3 (mod 4), N > 3, these equations have no solution in any case but one.
In the remaining case the tile is (ef, f² − e², f²) up to scale, and the target is the base-β target T_1(e,f), or W_1(e,f),
or an isosceles triangle with base angles α + β; in the last two cases gluing one or two scaled tiles to the target
produces a tiling of T_1(e,f). A prime number of tiles forces the scale to be one. So a statement about all triangles
and all tiles is exchanged for the absence of tilings of one explicit two-parameter family, Theorem 1.2.

No count can prove Theorem 1.2: the same tile tiles T_M(e,f) for all M ≥ f, and a quantity that depends on the scale
periodically or polynomially takes at scale one the value it takes at those scales (Proposition 7.7). The proof uses the
order of the tiles. Each side of the target is a word in the edge lengths a, b, c of the tile, and the length of the side
leaves few words. At a point of a side the angles of the tiles add up to π, which with α/π irrational leaves two figures
(Lemma 2.7), and this orients the tiles of the word one after the other. The step that carries the argument into the
interior is a partition lemma (Lemma 2.3): a segment that is a union of edges on one side and is closed off at both ends
is a union of whole edges on the other side as well. Since b is not a sum of other edges, and kb for k < f is a sum of
edges in one way only, a tile laid on such a segment forces the tile across it. One follows the forced tiles from a corner
until a point is reached where no figure is possible. For the members (1,f), f ≥ 3, the walk runs along the base; for the
others it starts at the apex (Section 4.3 of the paper).

## Priority

A proof of Theorem 1.1 was first made public by D. Paliy on 29 September 2026 (GitHub `DenisUkranian/erdos-634-tilings`,
commit `0730aafe`), by a column induction from a corner of the scale-one targets. The proof given here was obtained
independently, by different arguments at scale one (Section 4.3 of the paper); its exclusion of the family e = 1 was
public on 12 September 2026 (Zenodo version 3.2, doi:10.5281/zenodo.22721069), and the rest was completed without being
made public at the time. The dated record is in `TIMELINE.md`.

## Main results

Notation. For coprime integers 1 ≤ e < f let (a, b, c) = (ef, f² − e², f²); this triangle has angles (α, β, 2α + β) with
3α + 2β = π and α/π irrational. For an integer M ≥ 1, T_M(e,f) is the isosceles triangle with legs Mf³ and base
Me(3f² − e²) (base angles β, apex 3α), and W_M(e,f) is the triangle with sides Mf(f² − e²), Me(2f² − e²), Mf³ (angles β,
2α, α + β). They have M²(3f² − e²) and M²(2f² − e²) tiles of area equal to the tile. A *tiling* of such a triangle is a
tiling by copies of (a, b, c). Mirror images of the tile are allowed, and the pieces need not meet edge to edge. The
labels in parentheses are those of the paper's source.

### Results of Section 1

**Theorem 1.1** (`thm:primes`; F). Let p be a prime. Some triangle can be cut into p congruent triangles if and only if
p = 3 or p ≢ 3 (mod 4). In particular no triangle can be cut into 19 congruent triangles. Standing: formal, standard
axioms only; the formal statement and definitions have been compared with the mathematical ones within this work and
not yet by an independent reader.

**Theorem 1.2** (`thm:scaleone`; F). Let 1 ≤ e < f be coprime integers. No triangle with sides f³, f³, e(3f² − e²) can
be cut into congruent triangles with sides ef, f² − e², f², in any number. Standing as for Theorem 1.1; for e ≥ 2 there
is no continuous written proof.

**Theorem 1.3** (`thm:200`; F). Let 1 ≤ N ≤ 200. Then N is a tile count if and only if N is one of the following 105
numbers, which are the N ≤ 200 of the forms k², 3k², 6k², x² + y² (x, y ≥ 1), 7m², 11m² (m ≥ 2), together with 77, 84,
88, 126, 143 and 189:

> 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 16, 17, 18, 20, 24, 25, 26, 27, 28, 29, 32, 34, 36, 37, 40, 41, 44, 45, 48, 49,
> 50, 52, 53, 54, 58, 61, 63, 64, 65, 68, 72, 73, 74, 75, 77, 80, 81, 82, 84, 85, 88, 89, 90, 96, 97, 98, 99, 100, 101,
> 104, 106, 108, 109, 112, 113, 116, 117, 121, 122, 125, 126, 128, 130, 136, 137, 143, 144, 145, 146, 147, 148, 149,
> 150, 153, 157, 160, 162, 164, 169, 170, 173, 175, 176, 178, 180, 181, 185, 189, 192, 193, 194, 196, 197, 200.

The 95 values outside the list are the 23 primes ≡ 3 (mod 4) between 7 and 199, excluded by Theorem 1.1, and 72 composite
numbers. Theorem 1.3 is the conjunction of several Lean theorems that are not assembled into one formal statement (a
module importing several of the large certificates exceeds the available memory); the paper's Section 6.2 lists them.
Their formal statements have not been compared with the mathematical ones by an independent reader, and their proof
terms use Theorem 1.2. Section 6 of the paper gives the proof in stages: 143 is a tile count (Proposition 6.1), and 135
is not (Proposition 6.2, Theorem 6.3, certificate of 1 326 256 nodes).

**Theorem 1.4** (`thm:iso`; F). Let T have angles (α, β, 2π/3) with α/π irrational. Then no prime number of copies of T
tiles an isosceles triangle that is not equilateral. (Beeson proves the same statement by a different argument.)

**Theorem 1.5** (`thm:existence`; F; D. Paliy, M. Beeson). Let 1 ≤ e < f be coprime integers and M ≥ f. Then W_M(e,f)
and T_M(e,f) can be cut into congruent triangles with sides (ef, f² − e², f²). The statement and the constructions are
not ours; what is added is a formal proof for all members and scales.

**Theorem 1.6** (`thm:siderun`; F). Let f ≥ 2 and (a, b, c) = (f, f² − 1, f²), with angles α, β, γ opposite a, b, c. Let
Δ be a triangle with a side s whose two corners have the angles β, β or α + β, β, cut into copies of (a, b, c). Then
among the tiles with an edge on s there are f consecutive ones that lay their side c on s and show the angle α at the
same end of it; these f tiles are translates of one another, and |s| ≥ f³.

**Corollary 1.7** (`cor:below`; F). Let f ≥ 2 and M ≥ 1. (a) W_M(1,f) can be cut into copies of (f, f² − 1, f²) if and
only if M ≥ f. (b) If 2M ≤ f, then T_M(1,f) cannot be cut into copies of (f, f² − 1, f²).

**Theorem 1.8** (`thm:siderunall`; F). Theorem 1.6 for every member: with 1 ≤ e < f coprime and (a, b, c) = (ef, f² − e²,
f²), the same conclusion (f consecutive tiles laying c on s, showing α at the same end; in particular |s| ≥ f³) holds
for a triangle cut into copies of (a, b, c) with a side s whose corners have the angles β, β or α + β, β.

**Corollary 1.9** (`cor:ebelow`; F). Let 1 ≤ e < f be coprime and M ≥ 1. (a) If Me < f, then W_M(e,f) cannot be cut into
copies of (a, b, c). (b) If 2Me < f, then T_M(e,f) cannot be cut into copies of (a, b, c).

**Corollary 1.10** (`cor:thickw`; F). Let 1 ≤ e < f be coprime and M ≥ 1. (a) If M(f − e) ≤ e, then W_M(e,f) cannot be cut
into copies of (a, b, c). (b) For every f ≥ 2, W_M(f−1,f) can be cut into copies of (f(f−1), 2f−1, f²) if and only if
M ≥ f. (c) The triangle W_2(3,5), with sides 160, 246, 250, cannot be cut into copies of (15, 16, 25).

**Proposition 1.11** (`prop:layer`; F). Let f ≥ 2. (a) If M ≥ 1, 2M ≥ f and T_M(1,f) has a tiling, so has T_{M+1}(1,f).
(b) There is an integer M*(f) with f/2 < M*(f) ≤ f such that, for M ≥ 1, T_M(1,f) has a tiling if and only if
M ≥ M*(f). (c) M*(f) = f, that is, "T_M(1,f) has a tiling if and only if M ≥ f" holds for every M ≥ 1, if and only if
T_{f−1}(1,f) has no tiling.

### Further numbered results

These are stated in full in the paper; the table of the Lean map below lists each with its declarations. Lemmas and
propositions of Sections 2 and 3 (2.2 dissection basics, 2.3 partition lemma, 2.4 classical families, 2.5 types of
tiles, 2.7 vertex figures, 3.1 to 3.7 the signed-direction functional and its integrality, rationality and arithmetic
consequences) and Lemma 4.3 are tools of the proofs above and are in the table only.

* **Proposition 4.1** (F). A prime p > 3 equals 3f² − e² for coprime integers 1 ≤ e < f if and only if p ≡ 11 (mod 12).
* **Proposition 5.1** (F). Let an equilateral triangle of side S be cut into N copies of a tile with sides (a,b,c). For a tile of type (S) there are integers m₁ > m₂ ≥ 1 with m₁ ≤ N and m₁ ≡ m₂ ≡ N (mod 2) such that m₁(a + b − c) = 3S = m₂(a + b + c), S² = Nab and m₁m₂ = 3N. For a tile of type (H) there are integers 1 ≤ s, t ≤ N with s ≡ t ≡ N (mod 2) such that s(c + a − b) = 3S = t(c + b − a), S² = Nab and st = 3N.
* **Theorem 5.2** (F; Laczkovich; Beeson and Zhang). For a tile of type (S) (angles (α, 2π/3 − α, π/3)) or (H) (angles
  (α, π/3 − α, 2π/3)) that tiles an equilateral triangle, there are integers j ≥ 1, p, q ≥ 0 with ja = pb + qc and
  integers j' ≥ 1, p', q' ≥ 0 with j'b = p'a + q'c; consequently the sides a, b, c are pairwise commensurable.
* **Corollary 5.3** (F). In Proposition 5.1 the integer (m₁ + m₂)² − 16N, respectively (t − s)² + 16N, is a perfect square;
  so a pair for which it is not a square is the pair of no tiling.
* **Proposition 6.1** (F). The following dissections exist: T_M(1,2) and W_M(1,2) into 11M² and 7M² copies of (2,3,4) for
  every M ≥ 2; the triangle (16,28,33) into 77 and (24,24,42) into 84 copies of (2,3,4); (36,36,63) into 189 copies of
  (2,3,4); (21,55,56) into 88 and (39,49,55) into 143 copies of (3,5,7); (45,81,84) into 126 copies of (6,5,9). Moreover
  7m² and 11m² are tile counts if and only if m ≥ 2.
* **Proposition 6.2** (F). 135 is a tile count if and only if some equilateral triangle has a tiling by 135 copies of a
  tile of type (H) whose pair (s,t) of Proposition 5.1 is (15,27) or (27,15).
* **Theorem 6.3** (F). The equilateral triangle of side 45 cannot be cut into 135 copies of the triangle (3,5,7). Hence
  135 is not a tile count.
* **Proposition 6.4** (F). For coprime 0 < e < f, (a, b, c) = (ef, f² − e², f²) and t ≥ 1: (i) if the triangle with sides
  tfb, tfb, teb is cut into copies of (a,b,c), then teb = Pa + Qb + Rc with integers P, Q ≥ 0, R ≥ 2; (ii) for every
  k ≥ 1 the triangle with sides 2(k+1)(2k+1), 2(k+1)(2k+1), 2k(2k+1) cannot be cut into copies of
  (k(k+1), 2k+1, (k+1)²); (iii) if an isosceles triangle with base angles α + β (3α + 2β = π, α ∉ Qπ) is cut into N
  congruent triangles with angles (α, β, 2α + β), then N = t²(f² − e²) with t ≥ 2 and coprime 0 < e < f ≤ te; in
  particular N is neither prime nor squarefree.
* **Proposition 6.5** (F). For N = ds² with d ∈ {15, 30} and s ≥ 1, no triangle can be cut into N congruent triangles
  all of whose angles are rational multiples of π.
* **Proposition 6.6** (F). For a prime p, 2p is a tile count if and only if p = 3 or p ≢ 3 (mod 4).
* **Theorem 6.7** (F). Let N be squarefree with 3 ∤ N and a tile count. (i) N ≢ 3 (mod 8). (ii) If N ≡ 7 (mod 8), then
  N = ab or N = (a + 2b)(2a + b) with positive integers a, b such that a² + ab + b² is a square; below 455 the only such
  tile count is 143. (iii) If N ≡ 5 (mod 8), then N is a sum of two squares, or N = (2q² − p²)(3q² − p²) for coprime
  0 < p < q, or N = (f² − e²)(2f² − e²) for coprime 1 ≤ e < f; below 517 the only such tile count that is not a sum of
  two squares is 77. All three parts use Theorem 1.2.
* **Computation 6.9** (S). Of the 60 789 squarefree N with 7 ≤ N ≤ 10⁵, 13 600 are sums of two squares, 46 898 satisfy
  the decidable arithmetic condition of Remark 6.8 (which implies that N is not a tile count; the implication is a Lean
  theorem), and 291 are neither. The count is by a program and is not checked by the kernel value by value.
* **Theorem 7.1** (F; Beeson, Paliy). For integers 1 ≤ e < f, the triangle with sides f²(f² − e²), ef(2f² − e²), f⁴ can
  be cut into f²(2f² − e²) copies, and the triangle with sides f⁴, f⁴, ef(3f² − e²) into f²(3f² − e²) copies, of
  (ef, f² − e², f²). For coprime e, f these are W_f(e,f) and T_f(e,f).
* **Proposition 7.2** (F). For (e,f) ∈ {(1,3), (2,3), (1,4), (3,4)}, T_2(e,f) has no tiling by any number of copies of
  (ef, f² − e², f²). The triangle T_2(1,2) = (16,16,22) is cut into 44 copies of (2,3,4).
* **Proposition 7.3** (F). Sides from a corner 2α or 3α to a corner β or α + β: either the side carries f consecutive
  tiles of type C₁ (or of type C₂), or it begins with exactly k tiles of type C₁, e + 1 ≤ k ≤ f − 1, the first of which
  and its neighbour at the corner are mirror images in a common edge of length b (types and the full statement:
  Section 7.3 of the paper); for the members (f−1, f) the second alternative is empty.
* **Proposition 7.4** (F). Signed decomposition and layer for every member: with Q', Q, Z the points described in the
  paper, T_M(e,f) together with the triangle Q'QZ (a copy of the tile at scale Me) is the union of three copies of the
  tile at scale fM; if 2f(M − e) ≥ b, the part of T_M(e,f) above the line parallel to the base at height eH₁ is a translate
  of T_{M−e}(e,f), and the trapezoid below it is cut into (2Me − e²)(3f² − e²) copies of the tile; if 2fM ≥ b and
  T_M(e,f) has a tiling, so has T_{M+e}(e,f).
* **Proposition 7.5** (F). Strip of W_M(e,f): for M ≥ 2 the trapezoid between the side of length Mfb and the chord cutting
  off a translate of W_{M−1}(e,f) at the corner β is cut into (2M−1)(2f² − e²) copies of the tile when an integer z with
  z ≡ Mf (mod e), f ≤ z ≤ Mb/f exists, which holds if and only if M(f − e) ≥ f. Consequently W_M(e,f) has no tiling for
  every M < f if and only if W_{f−1}(e,f) has none, and W_{f−1}(e,f) has a tiling if and only if some tiling of W_f(e,f)
  has that chord as a wall.
* **Proposition 7.6** (F). For coprime 1 ≤ e < f, "T_M(e,f) has a tiling if and only if M ≥ f" holds for M = 1 and every
  M ≥ f, and holds for every M ≥ 1 if and only if T_M(e,f) has no tiling for 2 ≤ M < f. Moreover it holds for every M ≥ 1
  for (e,f) = (1,2), (1,3), (2,3); for every M ≠ 3 for (1,4) and (3,4); and for (1,f) whenever 2M ≤ f or M = 2 or M ≥ f.
* **Proposition 7.7** (F). Let ι be a function on the positive integers with values in a set X and z ∈ X with ι(M) = z
  whenever T_M(e,f) has a tiling. If ι(M) = z follows from ι(M') = z for all M' > M, then ι(M) = z for every M.
* **Proposition 8.1** (W). It is decidable, given N, whether N is a tile count (by the decidability of the first-order
  theory of the real field); this gives no usable bound and no description of the set.

### Open question (not a result)

**Question 1.12** (`q:threshold`). Let 1 ≤ e < f be coprime and 2 ≤ M < f. Can T_M(e,f) be cut into copies of
(ef, f² − e², f²)? The answer is no for (e,f,M) = (2,3,2), (3,4,2) and (1,3,2), for e = 1 and 2M ≤ f, and whenever 2Me < f;
these answers are formal. Open are the scales M ≥ 2 with f/(2e) < M < f other than these three; the first open cases
are T_3(1,4) (423 tiles), T_4(1,5) (1184) and, for e ≥ 2, T_3(3,4) (351). For the triangles W_M(e,f) the first open
cases are W_3(2,5), W_4(2,5) (736 tiles), W_3(3,5) and W_4(3,5) (656). Section 8 of the paper lists what a determination
of the set of tile counts still requires. No withdrawal or retraction notice is active.

## File map

| Path | Purpose |
|---|---|
| `README.md` | this index |
| `TIMELINE.md` | dated record of the results and of their public and pre-release copies |
| `.zenodo.json` | archive metadata for Zenodo |
| `LICENSE` | CC BY 4.0 for the text and data (`paper/`, `data/`), MIT for the code (`code/`, `lean/`, `rust/`) |
| `.gitignore` | excludes build products (`lean/.lake/`, `rust/*/target/`, `rust/mrv2/out/`) and LaTeX auxiliary files |
| `paper/` | `erdos634_primes_and_N200.tex` and `.pdf` (the paper), `tiling143.pdf` (figure: the triangle (39,49,55) cut into 143 copies of (3,5,7)) |
| `lean/` | the Lean 4 library `Erdos634`: `README.md` (build and map), `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `Erdos634.lean` (root), `Erdos634/` (4408 modules), `axioms/` (`#print axioms` for every declaration of the Lean map, one file per aggregate) |
| `code/` | `reproduce.sh` (one entry point: every check below, in order), `lakeserial.py` (serial, memory-guarded `lake` runner), `regen_cert.sh` (regenerates the large search certificates), `split_sound.py` (cuts a generated soundness module into parts) |
| `data/` | `certificates/MANIFEST.tsv`, the manifest of the seven large search certificates that are not stored |
| `rust/` | `mrv2` (floating-point refutation search and its driver `pf4.sh`, `tricert.py`), `certgenm` and `certgenx` (exact-arithmetic replay of a search tree into Lean modules) |

## Reproduction

One entry point runs every step below in order: `bash code/reproduce.sh` (about 16 GB of RAM, about 30 GB of disk, many hours).

Full instructions are in `lean/README.md`. Summary.

* Toolchain: Lean 4 `v4.30.0` (file `lean/lean-toolchain`), Mathlib at tag `v4.30.0` (commit
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`, pinned in `lean/lake-manifest.json`). Requirements: `elan`, `git`,
  `python3`; for the certificates also `cargo`.
* Mathlib build products: `lake exe cache get` (from `lean/`).
* Build order, one aggregate at a time and one module at a time, from `lean/`:
  `python3 ../code/lakeserial.py . build Erdos634.All`, then `lake env lean axioms/AxiomsAll.lean`; likewise
  `Erdos634.AllThreshold` with `axioms/AxiomsAllThreshold.lean`, and `Erdos634.AllSpectrum` with
  `axioms/AxiomsAllSpectrum.lean`. Expected output: every `#print axioms` line reads
  `[propext, Classical.choice, Quot.sound]`.
* Certificates: `code/regen_cert.sh all` (or one name, e.g. `code/regen_cert.sh S4N184`) reruns the float search, replays
  the tree in exact arithmetic into `lean/Erdos634/Refl/`, and compares SHA-256 values with the manifest; a mismatch stops
  it. Then `python3 ../code/lakeserial.py . build Erdos634.AllCert1` (and `AllCert2` to `AllCert5`) with the matching
  `axioms/AxiomsAllCert<i>.lean`. The float search is not trusted: the Lean kernel checks every node of the exact
  certificate.
* Memory: a single `lean` process needs up to about 13.5 GB (measured: 13.4 GB for `R126TilingBridge.lean`, 11.9 GB for
  `Draft/G3CIso2673.lean`). `lake build` alone starts about one `lean` process per core and can exhaust memory; use
  `code/lakeserial.py`, which stops the build if the resident memory of `lean`/`lake` exceeds `LAKE_RSS_LIMIT_GB`
  (default 14). Disk: about 7 GB for Mathlib, about 3 GB of build products for `All`, up to about 16 GB with every
  aggregate and certificate.
* Runtimes (author's machine, Apple silicon, 24 GB, serial build, Mathlib from the cache): the closure of Theorem 1.1
  (`Draft/PrimeCharacterization.lean`, `Draft/TheoremP6.lean`, 399 modules) about 50 minutes; a serial build of all of
  `All` (3092 modules) many hours; recorded search times S4N184 3 s, ISO154 about 3 min, S1N156 about 10 min, ISO184 about
  12 min, ISO132 about 24 min, S3N161 about 39 min, EQ135 about 3 min (search restricted at the root); the kernel check of
  each certificate takes from minutes to a few hours, that of EQ135 (135 tiles, 1 326 256 nodes) about five hours.
* There is no single reproduction script: the Lean build is the reproduction of the formal results, and
  `code/regen_cert.sh` that of the certificates.

## Formalization status

The Lean library `lean/Erdos634` has 4408 modules (3327 written, 1081 generated search certificates of moderate size in
`Erdos634/Refl/M*.lean`; the seven largest certificates, 4462 generated modules and about 1.7 GB, are regenerated by
`code/regen_cert.sh`). It contains no `sorry` and declares no axiom. Two modules not cited by the paper
(`Draft/NogoCount37.lean`, `Draft/PropNorm.lean`) use `native_decide` for three counting statements. The modules are grouped
in aggregates that do not import one another, because one `lean` process for their union would need too much memory:

| aggregate | modules | contents |
|---|---|---|
| `Erdos634.All` | 3092 | every module whose import closure contains no search certificate, among them the whole proof of Theorem 1.1 |
| `Erdos634.AllThreshold` | 1238 | the base-β targets above scale one (paper Section 7), with 182 certificate modules |
| `Erdos634.AllSpectrum` | 2481 | the statements on the values up to 200 that use a search certificate, with 1081 certificate modules |
| `Erdos634.AllCert1` to `AllCert5` | 2480, 1116, 1013, 1118, 3938 | 154, 156, scale two and thresholds; 132; 161; 184; 135 (module counts include the regenerated certificate modules) |

The formal statement behind Theorem 1.1 is
`theoremP_6 : ∀ N, ∀ D : CongruentDissection N, N prime → N % 4 = 3 → 3 < N → False`, and Theorem 1.1 itself is
`PrimeCharacterization.prime_tile_count_iff`; neither has a hypothesis beyond those displayed.

Three qualifications, as in the paper. First, Theorem 1.3 is a conjunction of formal theorems. Second, no formal statement
of the table has yet been compared with the mathematical one by an independent reader. Third, the formal statements of the
lemmas of Sections 2 and 3 are phrased for the structures of the library (for instance Lemma 2.3 with a linear functional
and two auxiliary points for the clamping).

### Lean map

Paper statement, standing, Lean declaration (full name), file (relative to `lean/Erdos634/`) and the first aggregate whose
import closure contains the file. A statement is checked by building that aggregate and running the matching file in
`lean/axioms/`. This table is the same as the one in `lean/README.md` and, up to the short names used there, as the paper's
Table 3.

| paper | standing | Lean declaration | file | aggregate |
|---|---|---|---|---|
| Theorem 1.1 | F | `Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff` | `Draft/PrimeCharacterization.lean` | All |
|  | F | `Erdos634.Draft.TheoremP6.theoremP_6` | `Draft/TheoremP6.lean` | All |
| Theorem 1.2 | F | `Erdos634.Draft.BaseBetaFullUnc.basebeta_full_unc` | `Draft/BaseBetaFullUnc.lean` | All |
|  | F | `Erdos634.Draft.UniformThreshold.not_betaTilable_one` | `Draft/UniformThreshold.lean` | AllThreshold |
| Theorem 1.3 | F | `Erdos634.Draft.Spectrum200g.tileCount_iff_le_200g` | `Draft/Spectrum200g.lean` | AllSpectrum |
|  | F | `Erdos634.Draft.Spectrum200g.tileCount_iff_le_131` | `Draft/Spectrum200g.lean` | AllSpectrum |
|  | F | `Erdos634.Draft.N143.tileCount_143` | `Draft/N143.lean` | AllSpectrum |
|  | F | `Erdos634.Draft.N132F.not_tileCount_132` | `Draft/N132Final.lean` | AllCert2 |
|  | F | `Erdos634.Draft.Spectrum200Cond4.decided_154_156` | `Draft/Spectrum200Cond4.lean` | AllCert1 |
|  | F | `Erdos634.Draft.N161F.not_tileCount_161` | `Draft/N161Final.lean` | AllCert3 |
|  | F | `Erdos634.Draft.N184F.not_tileCount_184` | `Draft/N184Final.lean` | AllCert4 |
|  | F | `Erdos634.Draft.N135F.not_tileCount_135` | `Draft/N135Final.lean` | AllCert5 |
|  | F | `Erdos634.Draft.Spectrum200Excl.tileCount_iff_le_200_of_excl` | `Draft/Spectrum200Excl.lean` | AllSpectrum |
| Theorem 1.4 | F | `Erdos634.Draft.ISUMain.thmIso_unrestricted` | `Draft/ISUMain.lean` | All |
| Theorem 1.5 | F | `Erdos634.Draft.Residue.betaTilable_ge` | `Draft/ResidueSeed.lean` | AllThreshold |
|  | F | `Erdos634.Draft.Residue.wTilable_ge` | `Draft/ResidueSeed.lean` | AllThreshold |
| Theorem 1.6 | F | `Erdos634.Draft.SideRun.Setup.side_theorem'` | `Draft/SideRunRules.lean` | AllThreshold |
| Corollary 1.7 | F | `Erdos634.Draft.SideRun.wTilable_e1_iff` | `Draft/SideRun.lean` | AllThreshold |
|  | F | `Erdos634.Draft.SideRun.not_betaTilable_e1_le_half` | `Draft/SideRunHalf.lean` | AllThreshold |
| Theorem 1.8 | F | `Erdos634.Draft.SideRunG.thm_siderunall_angles_T` | `Draft/SideRunGAngles.lean` | AllThreshold |
|  | F | `Erdos634.Draft.SideRunG.thm_siderunall_angles_W` | `Draft/SideRunGAngles.lean` | AllThreshold |
| Corollary 1.9 | F | `Erdos634.Draft.SideRunG.ebelow_a` | `Draft/SideRunGMain.lean` | AllThreshold |
|  | F | `Erdos634.Draft.SideRunG.ebelow_b` | `Draft/SideRunGMain.lean` | AllThreshold |
| Corollary 1.10 | F | `Erdos634.Draft.SideRunGA.thickw_a` | `Draft/SideRunGThick.lean` | AllThreshold |
|  | F | `Erdos634.Draft.SideRunGA.thickw_b` | `Draft/SideRunGThick.lean` | AllThreshold |
|  | F | `Erdos634.Draft.SideRunGA.thickw_c` | `Draft/SideRunGThick.lean` | AllThreshold |
| Proposition 1.11 | F | `Erdos634.Draft.LayerE1.betaTilable_succ` | `Draft/LayerE1.lean` | AllThreshold |
|  | F | `Erdos634.Draft.LayerE1.exists_min_scale` | `Draft/LayerE1.lean` | AllThreshold |
|  | F | `Erdos634.Draft.LayerE1.threshold_e1_iff_top` | `Draft/LayerE1.lean` | AllThreshold |
| Proposition 2.2 | F | `Erdos634.Geometry.Dissection.volume_target` | `Dissection.lean` | All |
|  | F | `Erdos634.Geometry.Dissection.hasAngleSums` | `AngleSumDissection.lean` | All |
|  | F | `Erdos634.WallEndpoints.chain_endpoints` | `WallEndpoints.lean` | All |
| Lemma 2.3 | F | `Erdos634.RunPartition.run_partition` | `RunPartition.lean` | All |
| Proposition 2.4 | F | `Erdos634.Ladder.ladder` | `Ladder.lean` | All |
|  | F | `Erdos634.Draft.TileCountFamilies.tileCount_scale` | `Draft/TileCountFamilies.lean` | All |
|  | F | `Erdos634.Draft.TileCountFamilies.tileCount_two_squares` | `Draft/TileCountFamilies.lean` | All |
|  | F | `Erdos634.Draft.TileCountFamilies.tileCount_three_sq` | `Draft/TileCountFamilies.lean` | All |
|  | F | `Erdos634.Draft.TileCountFamilies.tileCount_six_sq` | `Draft/TileCountFamilies.lean` | All |
| Proposition 2.5 | F | `Erdos634.Draft.LemmaCFinal.lemmaC_general` | `Draft/LemmaCFinal.lean` | All |
|  | F | `Erdos634.Draft.LemmaPProof.lemmaP_general` | `Draft/LemmaPProof.lean` | All |
| Lemma 2.7 | F | `Erdos634.Geometry.vertex_multiplicities` | `Dissection.lean` | All |
|  | F | `Erdos634.BaseBetaCorners.corner_beta_unique` | `BaseBetaCorners.lean` | All |
|  | F | `Erdos634.BaseBetaCorners.corner_apex_unique` | `BaseBetaCorners.lean` | All |
| Lemma 3.1 | F | `Erdos634.Geometry.Paper.lem_cancel` | `Draft/FluxPaperLemCancel.lean` | All |
| Lemma 3.2 | F | `Erdos634.Geometry.Paper.lem_value_alpha` | `Draft/FluxPaper.lean` | All |
|  | F | `Erdos634.Geometry.Paper.lem_value_beta` | `Draft/FluxPaper.lean` | All |
| Corollary 3.3 | F | `Erdos634.Geometry.Paper.cor_int_anchored` | `Draft/FluxPaperCorIntAnchored.lean` | All |
| Lemma 3.4 | F | `Erdos634.NonIntegrality.k_not_dvd` | `NonIntegrality.lean` | All |
| Proposition 3.5 | F | `Erdos634.Rationality.tile_rational` | `Rationality.lean` | All |
| Proposition 3.6 | F | `Erdos634.Draft.OtherSpectraFull.otherspectra` | `Draft/OtherSpectraFull.lean` | All |
| Proposition 3.7 | F | `Erdos634.Draft.FDDSpectrumPaper.spectrum_paper` | `Draft/FDDSpectrumPaper.lean` | All |
| Proposition 4.1 | F | `Erdos634.Draft.FDBMod12Converse.thm_mod12` | `Draft/FDBMod12Converse.lean` | All |
| Lemma 4.3 | F | `Erdos634.Draft.PierceScale.thm_pierce_scale` | `Draft/PierceScale.lean` | All |
|  | F | `Erdos634.BaseBetaWalks.apex_leftover_nonrepresentable` | `BaseBetaWalks.lean` | All |
| Proposition 5.1 | F | `Erdos634.Geometry.Row5.theoremE_sixty` | `Draft/FluxCRow5.lean` | All |
|  | F | `Erdos634.Geometry.Row5.theoremE_twoPiThree` | `Draft/FluxCRow5.lean` | All |
| Theorem 5.2 | F | `Erdos634.Draft.E60Graph.sixty_has_a_relation` | `Draft/E60Count.lean` | All |
|  | F | `Erdos634.Draft.E120Graph.twoPiThree_has_a_relation` | `Draft/E120Count.lean` | All |
|  | F | `Erdos634.Draft.E60Irr.sixty_commensurable` | `Draft/E60Irr.lean` | AllSpectrum |
|  | F | `Erdos634.Draft.E120Irr.twoPiThree_commensurable` | `Draft/E120Irr.lean` | AllSpectrum |
| Corollary 5.3 | F | `Erdos634.Draft.E60Irr.e60Pair_of_not_isSquare` | `Draft/E60Irr.lean` | AllSpectrum |
|  | F | `Erdos634.Draft.E120Irr.e120Pair_of_not_isSquare` | `Draft/E120Irr.lean` | AllSpectrum |
| Proposition 6.1 | F | `Erdos634.Draft.TileCountSpectrum.tileCount_seven_sq_iff` | `Draft/TileCountSpectrum.lean` | All |
|  | F | `Erdos634.Draft.TileCountSpectrum.tileCount_eleven_sq_iff` | `Draft/TileCountSpectrum.lean` | All |
|  | F | `Erdos634.Draft.SporadicCounts.tc77` | `Draft/SporadicCounts.lean` | All |
|  | F | `Erdos634.R84TilingBridge.r84_nonempty_congruentDissection` | `R84TilingBridge.lean` | All |
|  | F | `Erdos634.R88TilingBridge.r88_nonempty_congruentDissection` | `R88TilingBridge.lean` | All |
|  | F | `Erdos634.R126TilingBridge.r126_nonempty_congruentDissection` | `R126TilingBridge.lean` | All |
|  | F | `Erdos634.R189TilingBridge.r189_nonempty_congruentDissection` | `R189TilingBridge.lean` | All |
|  | F | `Erdos634.Draft.N143.dissection_143_unit` | `Draft/N143.lean` | AllSpectrum |
| Proposition 6.2 | F | `Erdos634.Draft.N135.tileCount_135_iff` | `Draft/N135Red.lean` | AllSpectrum |
| Theorem 6.3 | F | `Erdos634.Draft.N135F.not_tileCount_135` | `Draft/N135Final.lean` | AllCert5 |
| Proposition 6.4 | F | `Erdos634.Draft.NSQM.s5_base_word2_hasSides` | `Draft/S5Family.lean` | All |
|  | F | `Erdos634.Draft.NSQM.s5_family_2k_hasSides` | `Draft/S5Family.lean` | All |
|  | F | `Erdos634.Draft.NSQM.atom_shape_te` | `Draft/AtomShape.lean` | All |
|  | F | `Erdos634.Draft.NSQM.atom_not_squarefree` | `Draft/AtomShape.lean` | All |
|  | F | `Erdos634.Draft.NSQM.b3prime` | `Draft/B3Prime.lean` | All |
| Proposition 6.5 | F | `Erdos634.Draft.GAU.gapA_sq` | `Draft/GAUFinal.lean` | All |
| Proposition 6.6 | F | `Erdos634.Draft.TwoPrime.two_prime_tileCount_iff` | `Draft/TwoPrime.lean` | AllSpectrum |
| Theorem 6.7 | F | `Erdos634.Draft.Sqfree3Mod8.not_tile_sqfree_3mod8` | `Draft/Sqfree3Mod8.lean` | AllSpectrum |
|  | F | `Erdos634.Draft.Sqfree7Mod8.tile_sqfree_7mod8_form` | `Draft/Sqfree7Mod8.lean` | AllSpectrum |
|  | F | `Erdos634.Draft.Sqfree7Mod8.sector_below_455` | `Draft/Sqfree7Mod8.lean` | AllSpectrum |
|  | F | `Erdos634.Draft.QPExact.tile_sqfree_5mod8_explicit` | `Draft/QPExact.lean` | AllSpectrum |
|  | F | `Erdos634.Draft.QPExact.sector5_below_517` | `Draft/QPExact.lean` | AllSpectrum |
| Theorem 7.1 | F | `Erdos634.Draft.WSeedG.beta_seed` | `Draft/WSeedGAssemble.lean` | AllThreshold |
|  | F | `Erdos634.Draft.WSeedG.w_seed` | `Draft/WSeedGW.lean` | AllThreshold |
| Proposition 7.2 | F | `Erdos634.Draft.BaseBetaScale2.basebeta_scale_two` | `Draft/BaseBetaScale2.lean` | AllCert1 |
|  | F | `Erdos634.Draft.BaseBetaScale2.scale_two_1_2_exists` | `Draft/BaseBetaScale2.lean` | AllCert1 |
| Proposition 7.3 | F | `Erdos634.Draft.SideRunGA.thm_cornerrun` | `Draft/SideRunGCornerMainB.lean` | AllThreshold |
|  | F | `Erdos634.Draft.SideRunGA.thm_cornerrun_addendum` | `Draft/SideRunGCornerMainB.lean` | AllThreshold |
| Proposition 7.4 | F | `Erdos634.Draft.SignedDecompW.signed_decomposition_member_W` | `Draft/SignedDecompW.lean` | AllThreshold |
|  | F | `Erdos634.Draft.LayerG.layer_real` | `Draft/LayerG.lean` | AllThreshold |
|  | F | `Erdos634.Draft.LayerG.layer_c_i` | `Draft/LayerG.lean` | AllThreshold |
|  | F | `Erdos634.Draft.LayerG.layer_c_ii` | `Draft/LayerGChord.lean` | AllThreshold |
| Proposition 7.5 | F | `Erdos634.Draft.WStripG.wstrip_step` | `Draft/WStrip.lean` | AllThreshold |
|  | F | `Erdos634.Draft.WStripChord.wstrip_c` | `Draft/WStripChord.lean` | AllThreshold |
|  | F | `Erdos634.Draft.WStripChord.wstrip_d` | `Draft/WStripChord.lean` | AllThreshold |
| Proposition 7.6 | F | `Erdos634.Draft.Residue.threshold_iff_small` | `Draft/ResidueSeed.lean` | AllThreshold |
|  | F | `Erdos634.Draft.UniformThreshold.threshold_1_2` | `Draft/UniformThreshold.lean` | AllThreshold |
|  | F | `Erdos634.Draft.UniformThreshold.threshold_1_3` | `Draft/UniformThresholdCert.lean` | AllCert1 |
|  | F | `Erdos634.Draft.UniformThreshold.threshold_2_3` | `Draft/UniformThresholdCert.lean` | AllCert1 |
|  | F | `Erdos634.Draft.UniformThreshold.threshold_1_4_of_ne_three` | `Draft/UniformThresholdCert.lean` | AllCert1 |
|  | F | `Erdos634.Draft.UniformThreshold.threshold_3_4_of_ne_three` | `Draft/UniformThresholdCert.lean` | AllCert1 |
|  | F | `Erdos634.Draft.E1ScaleTwo.thresholdAt_e1_of` | `Draft/E1ScaleTwo.lean` | AllThreshold |
|  | F | `Erdos634.Draft.SideRun.thresholdAt_e1_le_half` | `Draft/SideRunHalf.lean` | AllThreshold |
| Proposition 7.7 | F | `Erdos634.Draft.Blind.invariant_blind` | `Draft/ThresholdBlind.lean` | AllThreshold |
| Section 8.2 (text) | F | `Erdos634.Draft.N330.tileCount_330` | `Draft/N330.lean` | All |
| Section 8.2 (text) | F | `Erdos634.Draft.N897.tileCount_897` | `Draft/N897.lean` | All |
| Section 8.2 (text) | F | `Erdos634.Draft.N990.tileCount_990` | `Draft/N990.lean` | All |
| Computation 6.9 | S | none |  |  |
| Proposition 8.1 | W | none |  |  |

## Data provenance

`data/` contains one file, `data/certificates/MANIFEST.tsv`: one row per large search certificate that is not stored. The
witness tilings (the positive results) are not in `data/`; each is a Lean module with exact coordinates in a ring
(1/d)Z[√K], checked by the kernel, in `lean/Erdos634/R*Tiling*.lean`. Provenance of the tilings, as attributed in the
paper (Sections 6.1 and 8.2): the tilings with 28 and 77 tiles by Beeson; those of the triangle (36,36,63) with 189 tiles
and of (21,55,56) with 88 tiles were exhibited by Harries; the 126-tiling is W_3(2,3), the case (2,3) of Theorem 7.1
(Beeson, Paliy); the tilings with 897 and 990 tiles by Paliy (kernel-checked here); the tiling of the equilateral triangle
of side 60 with 240 copies of (3,5,7) by Paliy (kernel-checked here); the tiling of (39,49,55) by 143 copies of (3,5,7) and
that of (91,176,195) by 330 copies of (7,8,13) were found in this work by exact search and kernel-checked. The paper
records no attribution for the tilings of (24,24,42) with 84 tiles and of T_M(1,2), W_M(1,2).

Columns of `MANIFEST.tsv` (the file documents them in its header): `name` (certificate name; the Lean modules are
`lean/Erdos634/Refl/M<name>Inst.lean`, `M<name>Data<i>.lean`, `M<name>SoundP<j>.lean`, `M<name>Sound.lean`), `instance`
(search run name, file names under `rust/mrv2/out`), `tile` (side lengths of the tile), `target` (side lengths of the
target in the order base, right side, left side), `N` (number of tiles), `mode` and `la` (branching order and lookahead of
`rust/mrv2`), `nodes` (nodes of the float refutation tree, nogood subtrees included), `tree_bytes` and `tree_sha256`
(size and SHA-256 of the tree file), `lean_files` and `lean_bytes` (number and total size of the generated Lean modules),
`lean_sha256` (SHA-256 of the concatenation Inst, Data0, Data1, ..., SoundP0, ..., Sound), `gen` (generator: empty for
`rust/certgenm`; `certgenm+split:<PER>`; `certgenx:<mirror>:<root slots>`).

The seven certificates:

| certificate | tile | target | N | float-tree nodes | Lean modules | aggregate |
|---|---|---|---|---|---|---|
| S1N156 | (12, 7, 16) | (128, 234, 128) | 156 | 234 239 | 350 | AllCert1 |
| ISO154 | (8, 7, 13) | (91, 154, 91) | 154 | 63 895 | 96 | AllCert1 |
| S4N184 | (10, 21, 25) | (184, 210, 250) | 184 | 71 173 | 110 | AllCert1, AllCert4 |
| ISO132 | (5, 3, 7) | (42, 66, 42) | 132 | 233 117 | 344 | AllCert2 |
| S3N161 | (12, 7, 16) | (112, 161, 112) | 161 | 345 746 | 525 | AllCert3 |
| ISO184 | (7, 8, 13) | (104, 184, 104) | 184 | 165 736 | 246 | AllCert4 |
| EQ135 | (3, 5, 7) | (45, 45, 45) | 135 | 1 822 966 | 2791 | AllCert5 |

For EQ135 the tree is restricted at the root and replayed by `rust/certgenx` in mirror mode; the exact certificate checked
by the kernel has 1 326 256 nodes (the number stated in the paper), against 1 822 966 in the float tree.
