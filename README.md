# Congruent dissections of a triangle: prime counts, the counts up to 200, and a family of isosceles targets

[![DOI](https://zenodo.org/badge/1420385447.svg)](https://doi.org/10.5281/zenodo.23400433)

This version (v4.0): DOI to be filled after the Zenodo record exists (placeholder; do not cite a version DOI for v4.0 until then). Previous version v3.1: doi:[10.5281/zenodo.23488114](https://doi.org/10.5281/zenodo.23488114); v3.0: doi:[10.5281/zenodo.23483290](https://doi.org/10.5281/zenodo.23483290). All versions (concept DOI): doi:[10.5281/zenodo.23400433](https://doi.org/10.5281/zenodo.23400433).

**Author:** Vico Bonfioli (vicobonfioli@gmail.com). The work was carried out with the assistance of Claude (Anthropic)
throughout, under the author's direction.

**Archive:** Zenodo, doi:[10.5281/zenodo.23400433](https://doi.org/10.5281/zenodo.23400433) (all versions); version 1.0: doi:[10.5281/zenodo.23400434](https://doi.org/10.5281/zenodo.23400434).

**Papers (version 3.0, two):** `paper/erdos634_v3W2.pdf` (Paper W, 13 pp., source `.tex`): Tilings of W_M and T_M below the threshold scale (Theorem W, the six-piece template); and `paper/erdos634_v3C.pdf` (companion): the collar family, macro-piece tile counts, the thick regime (no-tiling rungs), Conjecture C, the census, corrections and what is not proved. They share `paper/notation_table.tex`; the companion uses the version 2.2 paper for the exclusion side. **Companion papers:** `paper/erdos634_primes_and_N200.pdf` (version 2.2: runs, windows and the corner, Theorem F, the census to one million, the prime case), `paper/erdos634_primes_and_N200_v1.pdf` (the first paper). Talk and FAQ: `docs/`.

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

## Credits (what is taken or adapted from others)

* **M. Beeson and G. Rosu**, *Tiling a triangle into a prime number of congruent triangles* (preprint, 16 October 2026): the rigidity window (their Lemma 30), the trapezoid lemma for a stopped run (Lemma 32, p. 26), "how not to start a run" (Lemma 33, p. 28), the pigeonhole on the angles gamma at the ends of a side (Lemma 34, p. 30), and the row induction with the final counting of their Theorem 37 (p. 32). Our Theorems C and D' and Lemmas 32', 33', 34' and K for the target T(g) are adaptations of this method to gamma = 2 alpha (hand proofs, not formalized). Ours: the fan lemma at straight points, the two windows u and v, Lemma K.
* **M. Beeson**, other papers: arXiv:1206.1974 (Thm 11.7, the case g = 1; the 1125-tiling, Herdt's, as the instance of the Herdt family); Triangle tiling I and III (including Thm 11 for the tiling at M = f); *No triangle can be cut into seven congruent triangles* (classification of the tile types); *Tiling an equilateral triangle*; *No prime tiling of an isosceles triangle*; with Y. X. Zhang, *Rationality of certain triangle tilings* (Lemma 3.5, Thm 5.2); with M. Laczkovich and Y. X. Zhang, Erdos Problem 633.
* **D. Paliy**: first public proof of the prime case (29 September 2026); the exclusions of 60, 105, 135, 154 (announced earlier; ours are independent Lean certificates); the tilings with 240, 312, 897, 990 and 4830 tiles; the five-piece layouts of the rows F3, F4 and S2; the collar, the trapezoid of six pieces and the seeds of the base-beta construction; the reduction notes (square-class obstructions, uniform sectors); the claim ledger.
* **B. Herdt**: the 1125-tiling by (4,5,6) (published by Beeson); our macro-dissection family generalizes it.
* **M. Laczkovich**: the classification of the pairs (triangle, tile), the conjugate-tilings method, and the macro-dissection of the 183-tiling that our branch gamma = 2 alpha construction reconstructs in general.
* **Y. X. Zhang**: the 2 pi/3 families (arXiv:2512.22696); our uniform versions are in `Draft/Zhang*.lean`.
* **S. L. Snover, C. Waiveris and J. K. Williams**: rep-tiling for triangles. **J. P. Harries**: tilings of (21,55,56) and related triangles, and the status list of unresolved values.

The full references are in the bibliography of the paper.

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
| `docs/` | `TALK.md`, `FAQ.md` |
| `paper/` | `erdos634_v3W.tex`/`.pdf` (Paper W) and `erdos634_v3C.tex`/`.pdf` (companion), version 3.0, `erdos634_primes_and_N200.tex` and `.pdf` (the version 2.2 paper), `..._v1.tex` and `.pdf` (the first paper), `tiling143.pdf` (figure: the triangle (39,49,55) cut into 143 copies of (3,5,7)) |
| `lean/` | the Lean 4 library `Erdos634`: `README.md` (build and map), `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `Erdos634.lean` (root), `Erdos634/` (4768 modules), `axioms/` (`#print axioms` for every declaration of the Lean map, one file per aggregate) |
| `code/` | `reproduce.sh` (one entry point: every check below, in order), `lakeserial.py` (serial, memory-guarded `lake` runner), `regen_cert.sh` (regenerates the large search certificates), `split_sound.py` (cuts a generated soundness module into parts), `r8/` (decoders and verifier driver of the R8 layouts) |
| `data/` | `certificates/MANIFEST.tsv`, the manifest of the nine large search certificates that are not stored (and `certificates/trees/`, two search trees, gzipped); `witnesses/` (exact tilings of the 22 R8 values in `r8_exact/`; the 13 template tilings of release v1.15 in `template_exact/`; the 97 exact tilings of release v3.0 in `v3_exact/`: Theorem W, collar, macro pieces, Paliy's 4830) |
| `rust/` | `mrv2` (floating-point refutation search and its driver `pf4.sh`, `tricert.py`), `certgenm` and `certgenx` (exact-arithmetic replay of a search tree into Lean modules), `bonfioli_tiling_engine` (independent exact tiling verifier), `bonfioli_template` (the template search `bto` that found the tilings of v1.15; source only) |

## Release v4.0: band theorem, registry extract, census update

**The problem is not solved. Not refereed; not audited outside the project.** See `RELEASE_NOTES_v4.0.md` and `docs/ADDENDUM_v4.0.md`. The companion paper (`paper/erdos634_v3C.pdf`) is now version 4.0 (new Section "What is new in version 4.0"); Paper W is unchanged.

* **Band theorem (Lean, internal audit only).** For coprime 2 <= e < f, M >= 2, f <= 2Me < f + e, the triangle T_M(e,f) has no dissection into congruent copies of (ef, f^2-e^2, f^2) (`Erdos634.LaczJunction.Walk.band_theorem_free`; also `no_tiling_U`, `no_tiling_U2`). The Lean files are in the public repository "Formalizing triangle tiling in Lean" (github.com/ElVec1o/formalizing-triangle-tiling-in-lean, commit d728130; `Erdos634/Draft/LaczFormalMJFinal.lean` and its imports) and are not repeated here; not rebuilt in this repository. Fans-and-chords method after Laczkovich, Beeson and Beeson-Zhang.
* **Registry extract:** `data/registry/` (3,204 excluded instances of the base-beta family; internal extract).
* **Census** (non-squarefree N <= 10^6): 200,282 excluded / 62,421 undecided (v3.1: 199,364 / 63,593); the count of known tile counts is not printed for this version (not yet reconciled value by value).
* **Prime case: unchanged, dates.** `theoremP_6` in our release of 15 October 2026 (Lean, internal audit only); Paliy made a proof public on 29 September 2026; Beeson and Rosu, arXiv:2607.23453 (v2 16 October, v3 21 October 2026), state a result on prime tile counts, about whose proof we claim nothing. Parallel works; no announcement is made here.

## Release v3.1: follow-up to v3.0 (Lean aggregate AllV3c, census update, rung e+3 note)

**The prime case is unchanged. No paper is rewritten; see `RELEASE_NOTES_v3.1.md` and `docs/ADDENDUM_v3.1.md`.**

* **Lean (`lean/Erdos634/AllV3c.lean`, 77 new source modules; built in the author's working repository, NOT rebuilt here; axiom lines in `lean/axioms/AxiomsAllV3c.lean`, standard axioms only):** `no_dissection_win` (67 census-excluded values <= 10^5, including 270, 412, 750, 963; unaudited; controls `NSQWinCtl6`); 465 g^2 and 7672 g^2 are tile counts for every g >= 2 (`CollarFam465`, `CollarFam59`; Paliy's up-set covers K >= 153 for 7672).
* **Census** (non-squarefree N <= 10^6): 199,364 excluded / 129,117 tile counts / 63,593 undecided (hand-proved R2 row separate: 199,441 / 129,117 / 63,516); 67 of the exclusions are Lean-formal.
* **Rung e+3: computer-assisted case tree for 26 triples with f <= 40, 9,990 of 9,990 certificates verified by an independent verifier; NOT a theorem**, not in Lean, no outside read; trusted items in the addendum; engine sources not released.
* Further tile-count candidates from a sweep are listed in the addendum and are not claimed.

## Release v3.0: Theorem W, the collar family, macro-piece tile counts, Conjecture C

**The prime case is unchanged (no prime p ≡ 3 (mod 4), p > 3, is a tile count). Nothing in this release bears on Theorem 1.1 or on the base-beta question; it is existence work, a conjecture, and a list of corrections.** Standing marks as in the paper (version 3.0 uses five labels: proved in Lean / proved by hand / computed, exact / claimed by Paliy / conjecture).

* **Theorem W (proved in Lean `Draft.ThmW.thmW`; hand proof in Appendix A of the paper).** For coprime 2 <= e <= f-2 and M with Me >= f and (M-1)(f-e) >= f, the triangle W_M(e,f) is tiled by M^2(2f^2-e^2) copies of (ef, f^2-e^2, f^2), and T_M(e,f) by M^2(3f^2-e^2). The tiling is a layout of six pieces, each cut by the ladder subdivision. For e < f/2 the threshold Me >= f is sharp (the other direction is in the earlier releases). Consequence: the scale f is not the threshold for e >= 2; for example W_3(2,5) is tiled by 414 tiles, W_4(3,5) (sides 320, 492, 500) by 656. This answers the open case W_4(3,5) of the first paper and refutes the size conjecture that a target not similar to the tile has longest side at least c^2. Still open: the no side for e > f/2, the members e = 1 and e = f-1 of T, and the T side in general. Credit: the targets W, T, the framework and the thresholds M >= f are Paliy's and Beeson-Rosu's; the template was found by our template search (not shipped).
* **Collar family.** `CollarUp.tileCount_e1_up`: (f^2-1)(2f^2-1) g^2 is a tile count for all f >= 2, g >= f+1 (parametric seed and layer step; 189 = f = 2 is Beeson's and Harries's). Tails (Lean): 465 g^2 for g >= 5, 2485 g^2 and 966 g^2 for all g >= 2 (`CollarFam2`). **New (exact-verified tilings, not yet Lean): 465 g^2 for g = 2, 3, 4 (N = 1860, 4185, 7440; tile (4,15,16)), so 465 g^2 is a tile count for every g >= 2; the core 465 stays open.** **The up-set in g and the form b(b+c)K^2 are Paliy's (2026-09-29)**; our construction is independent, the explicit thresholds and the Lean proofs are ours. The collar step with arbitrary height is a hand proof (audited).
* **Thick regime (companion Section 7).** For coprime 2 <= e < f, M < f, Me >= f: W_M(e,f) has **no tiling if M(f-e) <= e+1** (Lean `SplusThick.wTilable_not_of_small_M`; hand proof audited only inside the project; 124 census values; formal in the exclusion chain: N = 412 = W_2(5,8) and N = 270). **Theorem R2 (hand proof only, `docs/THEOREM_R2_PROOF.md`)**: the same for M(f-e) = e+2 (+77 census values, kept as a separate row); audited twice inside the project by readers of the same model family, tested once by an exact region search at (4,7,2); Lean has its arithmetic half and a corollary conditional on `R2Count` (not proved in Lean); not read by anyone outside the project. Lemma W2 (hand): the side OB of W_2(e,f), e > f/2, carries exactly 2(f-e) a-tiles and 2(f-e) c-tiles; residual window e+3 <= k <= 2(f-e) is open. Also computed: the boundary words of the 52 known template tilings, and the threshold as a Beatty-interval identity (296,736 triples).
* **Macro-piece tile counts (Lean, `AllMacro`).** 375, 540, 735, 825, 630, 1120, 1750, 3864, 8694, 9940, 15456, 22365, 24150, 34776, 47334, 61824, 96600, 116886, 139104, 163254, 189336, 217350, 247296, 279174, 312984, 62125, and 78246 = 9 x 8694. Plus twelve square multiples (`TemplateSquares`) and the thirteen first W_M tilings below the threshold with their closures. 100 exact tilings (26 MB) are in `data/witnesses/v3_exact`, all verified by the exact verifier (`bte verify`), independently of Lean.
* **Conjecture C** (paper Section 6): the set of tile counts is the union of explicit families (classical, W/T, five-piece, 2pi/3, sporadic 88 and 143, base-alpha rows, gamma = 2alpha, 4830, theta). Its existence half is a Lean theorem on the proved ranges (`ConjC.Exist.conjC_existence`); its exclusion half is open. 183 is NOT a tile count (an earlier draft listed it by mistake).
* **Census** (non-squarefree N <= 10^6, 392,074 values): **199,364 excluded / 129,108 tile counts / 63,602 undecided** (Lean-formal exclusions; with the hand-proved Theorem R2 class as a separate row 199,441 / 129,108 / 63,525; v1.16: 199,140 / 102,613 / 90,321). The 26,495 new tile counts: 26,312 Lean, 145 exact tilings only, 35 by the hand collar step, 3 by a paper-formal closure. 134 further values lie in families that Paliy claims and that we have not verified; they are not counted. Squarefree values still open: about 770 (4830 is a tile count by Paliy's certificate, verified exactly here).
* **W3+ census (evidence only).** One-leg words for g = 3: (4,7) 191,940 of 191,940 words and (5,8) 84,462 of 84,462 are decided "no tiling" (exact arithmetic, conditional on the hand filters, no certificate); (7,12) is 95.06% of 8.43e9 words. No tiling found; this is not a proof and does not decide 297 or 351.
* **Corrections** (paper Section 9): 183; the pattern "threshold = f" for e >= 2; the claim that the template exists only for 4f < 9e; the size conjecture; Paliy's 4830 (a tiling; we had checked the wrong file); the theta statement; the attribution of the alpha up-set; counts in two notes.
* **What is not proved** (paper Section 10): the exclusion half of C; the no side of W for e > f/2; e = 1 and e = f-1 for T; V and A'; Theta and S3; 15m^2 for all m >= 4 as a Lean theorem; the squarefree values; and a check of the Lean statements, of theoremP_6 and of Theorem W by a person outside this project.
* **Checks.** `lean/Erdos634/AllV3.lean` (84 modules built one at a time, no `sorry`, no `native_decide` in the new modules); `lean/Erdos634/AllV3b.lean` (24 further modules: chain lemma, thick regime, R2 arithmetic half and conditional corollary, `CollarFam2`, `no_dissection_412`, `no_dissection_270`; axioms `lean/axioms/AxiomsAllV3b.lean`, gate 0 failures, no `sorry`); `lean/axioms/AxiomsAllV3.lean`: 98 declarations, every line `[propext, Classical.choice, Quot.sound]` (axiom gate 98/98); the build log of the full aggregate: 58,118 axiom lines, 0 failures. Exact verification of all 100 witness files: 100/100 VERIFIED.
* **Provenance.** The questions and directions are the author's. Claude (Anthropic) was used for exploration, computation, proof drafting and Lean development under that direction; the Lean proofs are checked by the kernel; the hand proof of Theorem W and the collar step were audited by separate instances and by exact computation (no reader outside the project). Search tools beyond those of release v1.16 are not part of this release.
* **Paper:** version 3.0 (`paper/erdos634_v3W2.pdf`, `paper/erdos634_v3C.pdf`); the version 2.2 paper is unchanged.

## Release v1.16: eight template tile counts are Lean theorems; W3+ census as evidence

**The prime case is unchanged. Nothing in this release bears on Theorem 1.1 or on the base-beta question.**

* **Eight template tile counts are Lean theorems** (mark F; standard axioms, no `sorry`, no `native_decide`; aggregate `Erdos634.AllR8`, axiom gate 35/35): `TileCount N` for N = 11,625; 66,960; 119,040; 121,765; 167,865; 186,000; 364,560; 603,750 (`Draft/T<N>`, generic module `Draft/LadderFam`, aggregate `Draft/AllTemplates`; tiles (4,15,16), (6,35,36), (10,21,25)). Each target is cut into a few convex pieces (similar triangles and trapezoids) found by our template engine, each tiled by cells of the ladder subdivision, with the covering obtained from an area identity. Credits: our engine for the templates; the skew-frame layer reconstructs Beeson-Rosu III Theorem 10; the macro dissections are of Laczkovich type; the multiplicative scaling follows Paliy's families. Statement-match audit within this work (all eight match `TileCount N`); no outside reader. These eight values were "computed, exact-verified" in v1.15; they are now Lean-formal. The five values above 10^6 (1,071,360; 1,183,350; 1,545,600; 1,904,640; 2,779,136) remain exact-verified only. Census unchanged: 199,140 / 102,613 / 90,321.
* **W3+ census (evidence only, not a theorem).** One-leg W3+ words at g = 3, exact arithmetic, conditional on the search filters (no Lean certificate). For (u,v) = (4,7) and (5,8) the word lists are complete (191,940 and 84,462 words); all but 323 and 630 words are decided "no tiling" within 2 s; a uniform sample of those, run 120 s each, decided about half, so roughly 160 and 315 words are still unresolved (an extrapolation, not a count). No tiling was found. For (7,12) (8.43e9 words) only a uniform sample of 19,999 was run: 19,994 "no tiling", 5 unresolved, none found. The conjecture is neither refuted nor proved by this.
* Paper: version 2.2 (new Section "What is new in version 2.2", credits row). A private-path comment was removed from `rust/bonfioli_template/src/search.rs`.

## Release v1.15: Paliy's nested-corner family theorems in Lean; 8 + 5 new tile counts from a template search; census recount

**The prime case is unchanged. Nothing in this release bears on Theorem 1.1 or on the base-beta question; it is census and existence work.**

* **Three family theorems formalized** (mark F; standard axioms, no `sorry`; aggregate `Erdos634.AllR8`, no search certificate): for naturals 0 < b < a with c^2 = a^2 + ab + b^2 (tile with sides a, b, c, angle 2 pi/3 opposite c), `Draft.PRevAll.prev_family` gives a tiling with (2a+b)(a+b) tiles if bc - a^2 lies in the semigroup generated by a, b, c; `Draft.PF2All.pf2_family` gives (a+2b)(2a+b) tiles under the same hypothesis; `Draft.PF3All.pf3_family` gives 3(a+b)(a+2b) tiles if a < 2b, with no semigroup hypothesis. **The constructions are D. Paliy's** (nested-corner layouts, from his public ledger); the symbolic Lean proof for all (a, b, c) and all semigroup witnesses is ours. Statement-match audit made within this work (all three match; non-vacuity by 22 instances); no outside reader. 48 new modules (`Draft/PCore`, `PHyp`, `PHypG`, `PRev*`, `PF2*`, `PF3*`).
* **All 22 squarefree R8 values are now Lean theorems** (instances `tileCount_N` of the three theorems; 345 and 506 also by `N345N506`). Squarefree N <= 10^6 still open: **771 at the exact and at the Lean level** (v1.14: 771 / 791).
* **134 further non-squarefree values N <= 10^6 are tile counts** (family theorem with scaling `TileCountFamilies.tileCount_scale`, the witness (a, b, c) found by search; **no Lean theorem is stated for each of them separately**, so these are counted as computed, not formal). Of 135 hits among the undecided values, one was already known.
* **Template search (COMPUTED, exact-verified, not Lean).** A search over macro-pieces (similar triangles, bricks, trapezoids) with integer scales (`rust/bonfioli_template`, binary `bto`) gave tilings with N = 11,625; 66,960; 119,040; 121,765; 167,865; 186,000; 364,560; 603,750 (<= 10^6) and 1,071,360; 1,183,350; 1,545,600; 1,904,640; 2,779,136 (> 10^6). Each was expanded to the individual tiles and checked by the independent exact verifier (`bte verify`: congruence, hull, disjoint interiors, area); the checks were rerun for this release, all VERIFIED. Witnesses: `data/witnesses/template_exact/*.gz` (63 MB). Each decides only its own value N = N0 g^2; the cores 465, 966, 2485, 2714 stay open. **Priority check:** none of these numbers occurs in D. Paliy's public ledger or in the papers searched; his archive of 220 files was not read.
* **Census** of the 392,074 non-squarefree N <= 10^6, recomputed from the label files by a script that first reproduces v1.14: **199,140 excluded / 102,613 known / 90,321 undecided** (v1.14: 199,140 / 102,471 / 90,463; +134 by the family theorems, +8 by the template tilings). The 382 values covered by the older families F3All/F4All were already among the 1,287 removed in v1.14 and are not new.
* Paper: version 2.1 (35 pages), new Section "What is new in version 2.1", updated census tables, credits row for Paliy's family theorems. Status: internally audited only; no outside check.

## Release v2.0: the self-contained readable paper; Theorem D' for every g >= 1 in the text

**Version 2.0 replaces the paper** (`paper/erdos634_primes_and_N200.pdf`, 34 pages, self-contained: own preamble and bibliography, marks F / W / S on every statement). The first paper is kept as `paper/erdos634_primes_and_N200_v1.tex` and `.pdf` for reference. `docs/TALK.md` (a talk outline) and `docs/FAQ.md` (questions and answers on the paper) are new. The paper has a new Section "What is new in version 2.0" and an Appendix "Reading record" (ten reads by readers who took no part in the writing, five rounds, scored 3/5, no mathematical error found; the author's own read approved the release).

Contributions, with dates (all internally audited only):

* 2026-10-18 (v1.14): Theorem D' for every integer g >= 1 in Lean (`ThmD.thmD_all_g`, `ThmD.thmD_g1`); the case g = 1 reproduces Beeson (2012), Thm 11.7, and is credited to him. The method is that of Beeson and Rosu, adapted to gamma = 2 alpha; the lemma on runs from a base corner is ours.
* 2026-10-18 (v1.14): all 199,140 non-squarefree exclusions N <= 10^6 from one Lean theorem, `NSQM.not_tile_of_conditionsNSQzETWDS`; the hypothesis is evaluated by a program for each N.
* 2026-10-18 (v1.14): 204 and 228 are not tile counts (already by the chain; two search certificates as a second route, a reproduction).
* 2026-10-18 (v1.14): 22 squarefree R8 values are tile counts by exact verification of D. Paliy's nested-corner layouts (credited); 345 and 506 in Lean.
* Squarefree N <= 10^6 still open: 771 (exact) / 791 (Lean).
* Axioms: `native_decide` occurs only in `NogoCount37` and `PropNorm`, which are outside the import closure of the headline theorems.
* Earlier: the prime case and N <= 200 (Theorem 1.1, 1.3), the isosceles family T_M(e,f) (v1.0 to v1.11); Theorems C and D' (v1.12, v1.13). See `TIMELINE.md`.

AI disclosure: an AI system (Claude, Anthropic) assisted; the prompts, questions and directions are by Vico Bonfioli, and the proofs are checked in Lean where marked F.

## Release v1.14: Theorem D' for every g >= 1; one theorem for all 199,140; 204 and 228 by certificates; 22 R8 tile counts

* **Theorem D' for every integer g >= 1** (`ThmD.thmD_all_g`, `ThmD.thmD_g1`; standard axioms, no `sorry`). The case g = 1 **reproduces Theorem 11.7 of M. Beeson (2012)**, "Tilings of an isosceles triangle", and is credited to him; it is the g = 1 instance of the run induction of Theorem D'. Changed modules: `Draft/ThmDGeo{Corner,Ctx,Leg1,LegCorner,Mirror,Unit}`, `ThmDFrame{Leg,Num}`, `ThmDStatementGeo` (a strict inequality relaxed to a non-strict one in the corner lemmas).
* **All 199,140 non-squarefree exclusions N <= 10^6 follow from ONE Lean theorem**, `NSQM.not_tile_of_conditionsNSQzETWDS` (module `Draft/ThmDChainWS`; the S1 clause is `S1Chk N or S1tChk N`, the sharpened S1 leaf of `Draft/NSQS1T`, Corollary ebelow(b)). v1.13.1 split them 196,273 + 2,867, the second set needing a combination made by the computation. Witness: `NSQM.no_dissection_428`. Axioms: propext, Classical.choice, Quot.sound.
* **204 and 228 are not tile counts, by a second route (a reproduction).** They are already excluded by the chain above (checked: `CN'zETWDS 204` and `CN'zETWDS 228` hold by `decide +kernel`). In addition the pairs (6, 34) and (6, 38) of the gamma = 2 alpha leaf are closed by search certificates, in the manner of N = 171: `Refl.MG204` (504,735 nodes; tile (49, 51, 70) on the triangle with legs 714, base 1020), `Refl.MG228` (752,117 nodes; tile (64, 57, 88) on legs 912, base 1254); theorems `NSQM.not_tile_204`, `NSQM.not_tile_228` in `Draft/N204N228.lean`, aggregate `Erdos634.AllCertW2` (standard axioms). The certificate modules (609 MB) are not stored; `code/regen_cert.sh G204` and `G228` regenerate them from the shipped search trees `data/certificates/trees/*.tree.gz` (rows in `data/certificates/MANIFEST.tsv`).
* **22 open squarefree values of the R8 rows are tile counts** by exact verification of D. Paliy's nested-corner layouts (credit: Paliy; the exact instances and the checks are ours): 345, 506, 12922, 18602, 25179, 35763, 57479, 65626, 135746, 146982, 156647, 196251, 201122, 247494, 388847, 397371, 428978, 538346, 624338, 686945, 746327, 914529. Each was verified by the independent exact checker `rust/bonfioli_tiling_engine` (tiles congruent, inside the hull, pairwise interior-disjoint, area equal); witnesses in `data/witnesses/` (`r8_exact/*.gz`, log `r8_exact/verification_log_open_r8.txt`), decoders in `code/r8/`. **345 and 506 are kernel-checked** (`Draft/N345N506.lean`, `N345N506.tileCount_345`, `.tileCount_506`, tile (7, 8, 13); aggregate `Erdos634.AllR8`). The other 20 are exact-program verified only, with no Lean; the symbolic family theorems for the rows are not formalized.
* **Squarefree N <= 10^6 still open: 771 at the exact level, 791 at the Lean level** (the recount of this release gave 793 before the 22 values; the figure 803 of an earlier release is not reconciled with it here).
* Status: all of this is internally audited only; no outside check.

## Release v1.13: Theorem D' (and C, W_2, A' for d = 1) formalized; census with the final chain

* **Theorem D'** (paper Section 8.5, Thm 8.12) is now a Lean theorem: `ThmD.thmDStatement_geo` and `ThmD.thmD_standalone` (about 105 modules `Draft/ThmD*.lean`, `Draft/ThmC*.lean`, in `Erdos634.AllThreshold`), standard axioms, no `sorry`. The irrationality of alpha/pi is derived inside the proof (Niven). **Theorem C**, **W_2** (every integer g = 2) and **Conjecture A' for v-u = 1** are cases of it (marks F). A statement-match audit inside the project found no soundness issue; no outside reader has checked it. Lemmas 8.x (fan, rigidity, words, 33, K, 34) stay marked W as separate statements; the Lean proof contains its own versions.
* **Credit:** the method (rigidity window, Lemmas 30, 32, 33, 34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu's prime-tilings preprint (16 October 2026); the transfer to gamma = 2 alpha is ours. Each module names this in its docstring.
* **Final chain:** `NSQM.not_tile_of_conditionsNSQzETWD` (`CN'zETWD N` implies N is not a tile count, unconditional) = the earlier conditions with the G leaf by Theorem D' and the S5 leaf by the word test (`NSQMS5W`, from `SideRunGT.theta_word_hasSides`). Witnesses: 204, 268, 276, 279 are excluded only by D' and the word leaf together (`no_dissection_276`, `cnzETWD_204`, ...); the condition fails at the tile counts 72, 143, 320.
* **Census** of the 392,074 non-squarefree N <= 10^6: **199,140 excluded / 102,471 known / 90,463 undecided** (v1.11: 71,039 / 102,471 / 218,564; the 128,101 new exclusions are the contribution of D' and the word leaf; known tile counts excluded: 0; self-test of `allncond2 --nsq-etw` with 0 mismatches). 196,273 of the excluded satisfy the hypothesis of the single theorem `ThmDChainW.not_tile_of_conditionsNSQzETWD`; the other 2,867 need in addition the formal sharpening Corollary ebelow(b) (2Me < f), combined by the computation. Correction (v1.13.1): v1.13 stated 62,150 / 136,990, which is the count of the older chain CN'zET (D' adds 134,123); the earlier release understated the formal part. The tool itself reports K = 101,184 / U = 91,750; the 1,287 values of U that are tile counts by the families of v1.10 and v1.11 (1,332 in all, 45 already in the tool's K) give the figures above.
* The hand-level triple 145,197 / 102,471 / 144,406 of v1.12.1 is superseded by the formal one.

## Correction (v1.12.1)

The v1.12 hand-level census of Theorems C and D' used an older label dump and undercounted. On the v1.11 dump: of the 74,697 undecided values (N <= 10^6, non-squarefree) failing only the branch gamma = 2 alpha, 74,158 have every pair of the branch covered by D' (64,961 by Theorem C alone) and 539 do not. With D' (hand proof, not formalized) the triple would be 145,197 excluded / 102,471 known / 144,406 undecided (Theorem C alone: 136,000 / 102,471 / 153,603). The formal v1.11 triple 71,039 / 102,471 / 218,564 is unchanged, and so are 167,727 / 150,381 of 201,952. Smallest values covered: 171, 204, 228, 276, 279, 304, 315, 348, 372, 380, 387, 460. Replaces 39,213 / 34,372 / +4,841 of v1.12. Paper-only patch; no Lean change.

## Release v1.12: Theorems C and D' on the target with base angles alpha (hand proofs, NOT formalized)

* Paper Section 8.5 (`sub:aprimehand`): **Theorem C** (Thm 8.11) and **Theorem D'** with **Lemma K** (Thm 8.12). For the gamma = 2 alpha tile (u^2, v^2-u^2, uv), u < v < 2u coprime, d = v-u, and an integer g, the isosceles triangle T(g) (base angles alpha, N = g^2 (v^2-u^2)) has no tiling if g d < u (Theorem C), and, for g >= 2, if (g-1) d < u (Theorem D'). Consequences: W_2 (every integer g = 2), and Conjecture A' for d = 1.
* Standing: **written proofs (mark W), adversarially audited twice inside the project, not formalized, no outside check.** The formal count of v1.11 (71,039 excluded / 102,471 known / 218,564 undecided) is unchanged. Lean drafts for the arithmetic layer exist in the working repository and are not compiled, so nothing is claimed of them.
* Honest gaps: (G1) the unstopped half of Lemma K is neither used nor claimed; (G2) D' is for g >= 2; (G3) the scope is integer g (the parametrisation of the pairs of the leaf is elementary, a reduction for rational g is not given); (G4) a remark about exit-march data is off by one for (3,5) and is not used.
* Hand-level census (separate from the formal count): of the 201,952 non-squarefree N <= 10^6 failing the branch gamma = 2 alpha, 167,727 have every pair covered by D' (150,381 by C alone). [Corrected in v1.12.1: the figures 39,213 / 34,372 originally given here were computed on an older label dump and undercounted; see the Correction note above.]
* Method credit: the rigidity window (Lemma 30), the trapezoid lemma (Lemma 32), Lemma 33, the pigeonhole of Lemma 34 and the row induction (Theorem 37) are from Beeson and Rosu's prime-tilings preprint (October 2026), and Lemmas 32', 33', 34' and K adapt them; the transfer to gamma = 2 alpha (fan lemma at straight points, the windows u and v, Lemma K) is ours.

## Release v1.11: non-squarefree census, formal count raised

* New Lean theorems `NSQM.not_tile_of_conditionsNSQzE` (pi/3 pair leaf by `E60Irr.e60Pair_of_not_isSquare`, no squarefree hypothesis) and `NSQM.not_tile_of_conditionsNSQzET` (also the S4 leaf by `SideRunGA.thickw_a`, Corollary 1.10(a), now formal; `thickw_a` is no longer outside the count). Rust mirror: `allncond2 --nsq-e`, `--nsq-et` (selftest, 0 mismatches).
* Census of the 392,074 non-squarefree N <= 10^6, with all families of v1.10 and v1.11: **71,039 excluded / 102,471 known / 218,564 undecided** (v1.10: 53,973 / 102,471 / 235,630, plus 5,908 by thickw(a) outside the formal count). The three sets are disjoint (checked on the value lists).
* (v1.11 figures) The 71,039 excluded: 62,150 by the single Lean theorem `NSQMMainZET.not_tile_of_conditionsNSQzET`; 8,889 more (X2) by the same conditions together with the formal sharpenings Corollary ebelow(b) (2Me < f, base-beta branch) and the exclusion of the pairs (2,2(2k+1)) on the branch gamma = 2 alpha (`GLIFinal.leafG_of_dissection`). Each sharpening is a formal statement; their combination with the other leaves is made by the computation, not by one Lean theorem.
* Of the 218,564 undecided values, 201,952 fail the branch gamma = 2 alpha and for 74,697 it is the only obstruction. Known tile counts excluded by the conditions: 0.
* The statement of v1.10 that thickw(a) is not formalized is withdrawn: it is formal (`SideRunGThick.lean`).

## Corrections to releases v1.5 to v1.9.1 (stated in v1.10)

* The non-squarefree census of v1.5 to v1.9.1 (59,881 excluded / 101,566 known / 230,627 undecided for the 392,074 non-squarefree N <= 10^6) added 5,908 values excluded by Corollary thickw(a) to the formal count. That corollary is proved in the paper and is not formalized. Formal figures with all families of v1.10: 53,973 excluded / 102,471 known / 235,630 undecided; thickw(a) excludes a further 5,908 (sound, not exhaustive).
* The sentence "every undecided value fails the branch gamma = 2 alpha" was false (27,812 of the 230,627 do not). Correct: 203,146 of the 236,962 values left by the conditions fail the branch, and for 39,216 it is the only obstruction.
* Squarefree open values for N <= 10^6: 803 (a stopping-bound bug in the S2 sieve had omitted two known values).

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
  `All` (3093 modules) many hours; recorded search times S4N184 3 s, ISO154 about 3 min, S1N156 about 10 min, ISO184 about
  12 min, ISO132 about 24 min, S3N161 about 39 min, EQ135 about 3 min (search restricted at the root); the kernel check of
  each certificate takes from minutes to a few hours, that of EQ135 (135 tiles, 1 326 256 nodes) about five hours.
* There is no single reproduction script: the Lean build is the reproduction of the formal results, and
  `code/regen_cert.sh` that of the certificates.

## Formalization status

The Lean library `lean/Erdos634` has 4678 modules on disk (3597 written, including 43 hand-written files in `Refl/`; 1081 generated search certificates of moderate size in
`Erdos634/Refl/M*.lean`; the seven largest certificates, 4462 generated modules and about 1.7 GB, are regenerated by
`code/regen_cert.sh`). It contains no `sorry` and declares no axiom. Exactly two modules contain a `native_decide` call: `Draft/NogoCount37.lean` (`nogoCount37_eq_10560`, `nogoGammaJunctions_eq_7`) and `Draft/PropNorm.lean` (`count_144`); both are imported by `Erdos634.All`, so `lake build Erdos634.All` builds them with `Lean.ofReducible`/`Lean.reduceBool`. No declaration cited by the paper depends on them: `axioms/*.lean` list only the three standard axioms for every cited declaration, and `code/axiom_gate.py` (run by `code/reproduce.sh`) fails otherwise. In particular the closures of the headline theorems (primes, the counts up to 200, Theorem D') contain neither module. The modules are grouped
in aggregates that do not import one another, because one `lean` process for their union would need too much memory:

| aggregate | modules | contents |
|---|---|---|
| `Erdos634.All` | 3093 | every module whose import closure contains no search certificate, among them the whole proof of Theorem 1.1 |
| `Erdos634.AllThreshold` | 1241 | the base-β targets above scale one (paper Section 7), with 182 certificate modules |
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
|  | F | `Erdos634.Draft.PRevAll.prev_family` (Paliy's construction) | `Draft/PRevAll.lean` | AllR8 |
|  | F | `Erdos634.Draft.PF2All.pf2_family` (Paliy's construction) | `Draft/PF2All.lean` | AllR8 |
|  | F | `Erdos634.Draft.PF3All.pf3_family` (Paliy's construction) | `Draft/PF3All.lean` | AllR8 |
|  | F | `Erdos634.Draft.T<N>.tileCount_<N>` for N = 11625, 66960, 119040, 121765, 167865, 186000, 364560, 603750 (template tilings, our engine) | `Draft/T<N>.lean`, `Draft/LadderFam.lean` | AllR8 |
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
| Section 8.2 (text) | F | `Erdos634.Draft.S2All.s2_family_all` (every 0 < p < q; Paliy's five-piece layout) | `Draft/S2All.lean` | All |
| Section 8.2 (text) | F | `Erdos634.Draft.F4All.f4_family` (F4 row, every 0 < a < b; Paliy's construction) | `Draft/F4All.lean` | All |
| Section 8.2 (text) | F | `Erdos634.Draft.F3All.f3_family` (F3 row, every 0 < a < b; Paliy's construction) | `Draft/F3All.lean` | All |
| Section 6 (text) | F | `Erdos634.Draft.EqSemigroup.eq357_semigroup` ((3,5,7) on the equilateral side 15m, m in the semigroup generated by 4 and 9) | `Draft/EqSemigroup.lean` | All |
| Section 6 (text) | F | `Erdos634.Draft.Iso357Semigroup.iso357_semigroup` ((3,5,7) on (21m,21m,33m), m in the semigroup generated by 4 and 9) | `Draft/Iso357Semigroup.lean` | All |
| Section 8.2 (text) | F | `Erdos634.Draft.ZhangProps.zhang_five` (Zhang's equilateral, isosceles and F1 constructions for every 2π/3 tile, m ≥ 3t0) | `Draft/ZhangProps.lean` | All |
| Section 8 (text) | F | `Erdos634.Draft.LaczFamily.lacz_family_uncond` (γ = 2α branch tiled for every (u,v) with (v²−u²)³v² > u⁸) | `Draft/LaczFamily.lean` | All |
| Section 8 (text) | F | `Erdos634.Draft.HerdtFamily.herdt_uniform` (Herdt macro-dissection uniform in (u,v); instances N=19600, 130977; decides no new value ≤ 10^6) | `Draft/HerdtFamily.lean` | All |
| Section 8.2 (text) | F | `Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzE` (non-squarefree conditions with the pi/3-pair leaf `E60Irr.e60Pair_of_not_isSquare`, no squarefree hypothesis) | `Draft/NSQMMainZE.lean` | All |
| Section 8.2 (text) | F | `Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzET` (the same with the S4 leaf closed by `SideRunGA.thickw_a` and `SideRunG.ebelow_a`; witnesses `no_dissection_168`, `no_dissection_248`) | `Draft/NSQMMainZET.lean`, `Draft/NSQRWT.lean`, `Draft/NSQMMainZETWitness.lean` | AllThreshold |
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
