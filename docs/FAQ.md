2026-10-19 T2 (MATH_RULES V10.1 H5) for paper version 3.0 (`paper/erdos634_v3.tex`). UNAUDITED draft. Section A answers the questions that blind readers asked of the version-3.0 draft in six rounds (reading log (not shipped)), and the questions a referee would ask; none changes a label. The FAQ for version 2.x is kept unchanged below `# FAQ for version 2.x`.

# FAQ for version 3.0

**A1. Is Theorem W really proved for T_M, in Lean?** The Lean statement `Draft.ThmW.thmW` gives the tiling for W_M and the *count* `TileCount (M^2(3f^2-e^2))` for T_M. The geometric tiling of T_M is the glue of one tile at scale Mf along the side Mfb (Section 3.3); that glue is the earlier-release Lean theorem `CollarG.betaTilable_of_wTilable`. The paper says this in the abstract, the Lean paragraph under Theorem 3.1 and the results table.

**A2. What is imported from the earlier releases?** Four facts, stated in Section 1.1: W_M untiled if Me<f and T_M untiled if 2Me<f (`cor:ebelow`); W_M untiled if M(f-e)<=e (`cor:thickw`(a)); the threshold f for e=1 and e=f-1; tilings for M>=f. The sharpness half of Corollary 3.2 is only as self-contained as `cor:ebelow`(a).

**A3. Why six pieces, and why n = floor(eM/f)?** Section 1.2 (the idea) and Section 3.4. The pieces are the ladder-subdividable shapes that fit around the bisector OP; n is the largest integer with fn <= eM, which makes the scale s_2 = fr - eM positive with r=n+1 and keeps all other scales positive when M >= M*(e,f) (sufficiency proved in Appendix A, Lemma C; that the canonical parameters work exactly when M >= M*(e,f) was checked by computation for f<=40, M<4f).

**A4. Where exactly are (H1) and (H2) used?** n>=1 (H1); dM>=f+d and s=M-n>=2 and dn>=e+1 (H2, with coprimality). Appendix A, Lemma C (P1)-(P5). The failing case (3,5,3) in Section 3.5 shows the factor fq-er = -1.

**A5. Is the hand proof checkable without the computer?** The area identity, the shape identities of Lemma A and the identity for (LB) are polynomial identities that can be expanded by hand; they were also verified by computer algebra and by the Lean kernel. The sign of each prefactor in Lemma B is a monomial in e,f,b,kappa times a fixed sign; the Lean modules have one lemma per factor.

**A6. Is 26 the number of inequalities?** The complete list of linear or quadratic factors in the cross products has 26 members (audit); Lemma B lists 13 factors (C2-C8, M>q, t>0, r>0, LA, LB, LC) and three expressions that are always positive.

**A7. Why does the text say the template was 'found by a search' if the proof is by hand?** The layout was found by a computer search (engine described only as far as the paper does); the proof of Theorem W does not use the search, only the layout.

**A8. Are the 13 first witnesses part of Theorem W?** They are instances; they were found before the theorem and are Lean theorems on their own (Appendix F). 'Smallest M known tiled before version 3.0' in the table of Section 3.1 means before this version.

**A9. Does Theorem W contradict a proved exclusion?** No: (H1) and (H2) imply that the hypotheses of the exclusions Me<f, 2Me<f, M(f-e)<=e fail (Section 3.6; a consistency check only). The 197 registry rows of recorded non-tilings (N, tile) do not meet the family.

**A10. What is open for W_M and T_M?** For W_M with e>f/2, the two scales with (M-1)(f-e)<f<(M+1)(f-e); for T_M, the scales with 2Me>=f and M<M*(e,f) (Section 3.7).

**A11. What did the collar step prove in Lean, and what by hand?** The one-layer case h=1 (for every row with ef <= f^2-e^2) in Lean; arbitrary height by hand. The tails 465g^2 (g>=5), 966g^2 (g>=17), 2485g^2 (g>=5) are Lean; the small g are the macro counts.

**A12. Is 15m^2 for all m>=4 proved?** No, as a Lean theorem: 15m^2 for m in the semigroup <4,9> and for the individual m=5,6,7 is Lean; the rest is Paliy's claim (Section 5.2).

**A13. Is Conjecture C a classification?** It is a conjecture stating the set of tile counts as a union of families; it is not claimed true; the existence half is a Lean theorem on a narrower collection of ranges; the exclusion half is open (Appendix B). The consistency check (c) there is partly circular and says so.

**A14. What does 'excluded' mean in the census?** The decidable arithmetic hypothesis of the single exclusion theorem of the earlier release fails for N; the evaluation is a program, the theorem is Lean; the theorem has been audited inside the project only (Appendix C).

**A15. Who proved what first?** Section 7 gives the dated credit table: Paliy (W/beta framework, caps and collars, alpha up-set 2026-09-29, 15m^2 seeds 2026-10-08, 4830), Beeson and Rosu (targets, methods), Herdt (1125), Harries (88, 189 as in Beeson's work), Laczkovich, Zhang. Nothing in the paper claims priority over Paliy for the results listed as his.

**A16. How was AI used?** An AI system (Claude, Anthropic) assisted in obtaining the results; the questions and directions were the author's; the proofs were checked in Lean or by hand as labelled; the provenance table is in the repository README.

**A17. Where do I send corrections?** To the author, Vico Bonfioli.

---

# FAQ for version 2.x

2026-10-18 T2 (MATH_RULES V10.1 H5), revised per REVISION_2.md and REVISION_3.md. UNAUDITED draft. Answers cite the files named; none changes a label.

**1. Is this just Beeson-Roșu?** The architecture of the section on T(g) is theirs (relation lattice and window, stopped run and quadratic patch, trapezoid lemma, how not to start a run, the pigeonhole on the ends, the side count). Ours: the transfer to the tile with gamma = 2 alpha (written out for this tile, with the fan lemma in place of gamma > pi/2), the split of the window into u and v, the corner start (Lemma K, which removes the 'tile across the ray' hypothesis at base corners), the counting identity and apex property used for the leg with alpha at both ends, and Theorem F. See `ours_vs_adapted.md`.

**2. What exactly is formal?** Theorem F (ThmD.thmDStatement_geo, ThmD.thmD_standalone, ThmDGeoUnit.thmD_geo_unit), with the fan lemma (ThmDHalfFan), rigidity (ThmCRigidity.ra_int, rb_int, rc_int_w, rc_int_all), the trapezoid lemma (ThmDL32.lemma32), the row lemma (ThmDInterior.lemma33_interior for interior starts, ThmDK2Final.lemmaK2_final and ThmDGeoLegCorner.leg_corner_start for corner starts), the counting identity (APrimeSeat1.counting_identity, ThmDCount.counting_identity_gen), the apex property (ThmDApex.apex_tiles_distinct), the leg statement (ThmDLegD1.leg_D1); the Herdt family (HerdtFamily.herdt_uniform), the census chain, and the 200-bound certificates, all Lean 4 with standard axioms. Lemma 34 carries three marks. (b) the counting form 'a leg has at least u edges c' is F: ThmDFrameLeg.leg_c_count_S1/S2, stated for real scale G > 1 and a positioned leg from a base corner to the apex or from the apex to a base corner (no hypothesis on the angle at the apex end of the leg, so either leg; not the base). (a) the pigeonhole, a c-run stopped at both ends of shape (backward)^k(forward)^l, is F as a statement about lists of oriented edges (ThmDPig.pig, run_shape); that the edge list of a leg satisfies its hypotheses is inside ThmDLegD1.leg_D1. (c) that the run itself has at least u edges is W: the Lean proof of (b) is by contradiction and never states the run. Theorem F uses only (b); the alpha-leg enters only through the word bound (counting identity, apex property). The same argument on the base is a written remark (W). Marked S: search results without certificate and the census partition table.

**3. Has anyone outside the project checked it?** No. The formal statements were compared with the written ones by audits inside the project; no outside reader has done so, and the paper says it in the abstract and at the theorem.

**4. What does Lemma K contribute, and which window does it use?** In the interior case the ray UW is made a wall by a tile across it, which costs (RB) for the segment w b, window u. At a base corner the ray is the side S', a wall at no cost, and no tile across exists. The proof then uses only (RA) for the diagonals w a and (RC) 'no b in w c' in the trapezoid lemma, both window v; the 'all c' half of (RC), window u, is not used. So a corner block stopped at its far end has at least v edges. Theorem F needs only 'at least u'; Lemma K's role is to handle the run that begins at a base corner (situation (E3) of Lemma 34). See Lemma rows and the paragraph after it.

**5. Is the window v sharp?** No claim is made. The induction breaks at n = v because the diagonal va = uc has a second decomposition; that is where the proof stops, not a statement about tilings. We know no example that shows the bound n >= v is attained, and Theorem F does not use it.

**6. What about (g-1)d >= u, d = v - u?** Not covered. Theorem F excludes (g-1)d < u only. By exact enumeration of coprime u < v < 2u and g >= 2 with (g-1)(v-u) >= u, the first, by N, are 45 at (u,v,g) = (2,3,3), 80 at (2,3,4), 112 at (3,4,4), 125 at (2,3,5), 144 at (3,5,3), 175 at (3,4,5), 180 at (2,3,6), 225 at (4,5,5); with d >= 2 the first are 144 at (3,5,3), 256 at (3,5,4), 297 at (4,7,3), 351 at (5,8,3), 384 at (5,7,4). All of the N up to 252 and 256, 320, 384 are tile counts by other families; the first with census status undecided are 297 and 351, then 816 at (7,10,4); 528 at (4,7,4) is a tile count (33*4^2, m = 4 in the semigroup generated by 4 and 9; the program's dump lists it undecided, the 1,287 later-found values remove it). A scan of the side words under the fan, Lemma 34 and Lemma K rules (u <= 8, g <= 4; S) rejects exactly the triples with (g-1)d < u; whether another argument excludes the rest is open.

**7. Does Theorem F contradict a known tiling?** No. Known tilings have g = 15 (Herdt, (2,3)), 35 ((3,5)), 63 ((4,7)) and 183 (Laczkovich's eight-piece construction at (2,3), g_0 = v(u^4 - u^2 v^2 + v^4); our Lean theorem is the family with the multiples 2buv g_0, and we have no tile-level witness of 183 itself), each with v | g, and none has (g-1)d < u. For that reason they cannot test Theorem F's hypothesis or its contradiction; they test the lemmas: the tilings with 19,600 and 130,977 tiles satisfy the fan lemma at every point of every side and carry stopped runs longer than u (S). Independently, N = 132 and N = 156 satisfy (g-1)d < u for (4,7) and (5,8) at g = 2 and are not tile counts (finite searches of the release paper); that is consistency, not a check of the proof.

**8. Why only integer g?** Integer g is the general case for the pairs the classification produces (ThmC.pair_param). Non-integer g is not treated and not claimed.

**9. Is Herdt's 1125 new?** No. The instance (2,3), g = 15 is Herdt's, published by Beeson (Fig. 23). The family over all coprime (u,v) with (v^2-u^2)^3 v^2 > u^8, the uniform scale, and the instances 19,600 and 130,977 are ours.

**10. Why does the same inequality appear for Laczkovich's eight-piece construction?** For the Herdt pieces the inequality (v^2-u^2)^3 v^2 > u^8 is proved here: the identity vb*E1 + u^4*E2 gives tau * ((v^2-u^2)^3 v^2 - u^8) = (positive) for any positive solution of E1, E2, and an explicit solution exists when the inequality holds. For Laczkovich's family the same domain was observed on all 127 coprime pairs with u <= 20 (S); we have no explanation, and we do not claim that the two share a sub-configuration.

**11. Which pairs are excluded from the family, and is anything known there?** The pairs (u, u+1) with u >= 3, and others such as (7,9), (9,11). No tiling of T(g) with v = u+1, u >= 3, is known to us. Theorem F excludes g < v for v = u+1.

**12. Does the Herdt family decide census values?** No new ones. The instances with N <= 10^6 that we computed are 1125 = 33^2 + 6^2, 19,600 = 140^2 and 130,977 = 33*63^2, where 63 = 7*9 lies in the semigroup generated by 4 and 9 and 33m^2 is a tile count of the tile (3,5,7) for such m (Iso357Semigroup.iso357_semigroup; the semigroup is generated by the seeds m = 4 and m = 9 of the equilateral triangles of side 15m tiled by (3,5,7)): all three are already tile counts in the census (status K). The admissible scales of other pairs were not enumerated.

**13. What does "excluded by a decidable condition" mean in the census?** There are fifteen leaves (Table 2 of the paper), one per family of pairs (target, tile). Each leaf is a Lean theorem: a decidable condition on N implies that N has no tiling in that family. The final chain CN'zETWD is their conjunction, with five sharpened leaves; NSQM.not_tile_of_conditionsNSQzETWD says CN'zETWD(N) implies N is not a tile count. A program evaluates the condition for every N up to 10^6 (checked against a literal triple loop for N <= 3000 and against Lean witnesses). Of the 199,140 exclusions, 196,273 satisfy the decidable hypothesis CN'zETWD of the single theorem NSQM.not_tile_of_conditionsNSQzETWD (62,150 of them already satisfy that of NSQMMainZET.not_tile_of_conditionsNSQzET; the other 134,123 fail the earlier G test and the earlier S5 parity test and use the new G test and the word test together, 126,730 with a pair outside the family (2,2(2k+1)), so Theorem F proper). The remaining 2,867 satisfy it only after the sharpening 2Me < f on the base-beta leaf S1 (the chain has S1 in the plain form 'no instance with M >= 2' and S4 already with M(f-e) <= e); that sharpening is a formal statement outside the chain theorem, applied by the program. The counts come from the program's dump, not from Lean. A value is a "tile count" only with a kernel-checked tiling or a theorem. Float verdicts are never final.

**14. Where does the census count 90,463 undecided come from, and is it stable?** From the final chain of conditions (NSQM.not_tile_of_conditionsNSQzETWD) applied to the 392,074 non-squarefree N up to 10^6: 199,140 + 102,471 + 90,463. It is the program's 91,750 minus 1,287 later found to be tile counts. The partition by failing leaves (S1, S4, G, S5 are called obstruction classes; 'wall' means only the geometric line of the row lemma): one obstruction class only 60,666 (28,615 + 18,619 + 10,964 + 2,468); several obstruction classes and no minor leaf 24,807 (G+S5 16,971, S1+S4 3,426, G+S4+S5 1,108, G+S1+S5 895, G+S4 877, G+S1 857, others 673); involving a minor leaf 4,990 (2,024 minor only, 2,966 with an obstruction class). 60,666 + 24,807 + 4,990 = 90,463. It decreases only when a new theorem or tiling is added.

**15. Is the prime result yours?** Paliy published a proof first (2026-09-29). Ours is independent and formal (TheoremP6.theoremP_6, PrimeCharacterization.prime_tile_count_iff). The paper says this in the abstract.

**16. How was AI used?** An AI system (Claude, Anthropic) assisted in obtaining the results; the prompts, questions and research directions came from Vico Bonfioli; the written proofs were machine-assisted and the checking is in Lean 4. The provenance table is in the repository README.

**17. Why Lean, and what does a Lean theorem not tell you?** It tells you the statement as formalized follows from the axioms. It does not tell you the formal statement is the intended one; that is why item 3 matters, and why every theorem carries its Lean name for comparison.

**18. Can I reproduce the 19,600-tile instance?** Yes. The exact coordinates are in `data/witnesses/herdt_family_gamma2alpha_macro.tsv` and the oblique tiling file `tiling_19600_gamma2alpha_3_5_g35.oblique.txt`. Figure 4 was checked in exact rational arithmetic: 11 pieces inside the target, pairwise disjoint interiors, areas sum to the target, tile count 13,706 + 5,894 = 19,600.

**19. What would change the result?** An error in a formal statement (item 3), or a tiling with (g-1)d < u, which would refute Theorem F. None is known.

**20. Where do I send corrections?** To the author, Vico Bonfioli. Corrections to the literature that we offer (for instance Beeson's Conjecture 1, refuted by the tiling of 143) are listed in `ours_vs_adapted.md`.

**21. Does Theorem F decide any new N, and which?** Yes, together with the word test for the theta targets. 204 = 4*51, 276 = 4*69 and 279 = 9*31 are not tile counts, are above 200, and were not excluded by the previous release (v1.11 census dump); in the chain each needs both. 268 = 4*67 was already excluded by the previous release (its pair (2,134) is of the form (G2)); it is a control, and its Lean witness is a check of the chain, not a new use of Theorem F. 204: pairs (M,M') = (6,34), (2,102), i.e. (u,v,g) = (7,10,2), (25,26,2); theta instances (t,e,f) = (2,7,10), (2,25,26). 268: (2,134) = (33,34,2); (2,33,34). 276: (6,46), (2,138) = (10,13,2), (34,35,2); (2,10,13), (2,34,35). 279: (3,93) = (15,16,3) (Theorem F at g = 3), and (1,279), (9,31) with g = 1; (3,15,16). For every instance t e b < f^3, so no word with z >= f exists. In Lean (Draft/ThmDChainWitnessW.lean, built 2026-10-18): cnzETWD_204, _268, _276, _279 by decide +kernel, no_dissection_276, no_dissection_279_w, and not_cnzETD_N, not_cnzETW_N (the chain with only one of the two ingredients fails). The claim is about the chain, not that other methods could not reach these values.

**22. What does 'wall' mean?** One thing: the definition before the row lemma (a line UP such that no point of UP just beyond P is interior to a tile). The four leaves S1, S4, G, S5 of the census are called obstruction classes.

**23. Does the proof of Theorem F cover g = 1, and is that new? (Revision 5)** The written proof does: Th1, Th2 and the leg lemma (case (O) needs only |S'| = g v b > n b, true for real g >= 1) give n_c = 0 < u for g = 1. It is a reproduction of Beeson's Theorem 11.7 (credited, clause (G1)), by a longer route; it is not new. In Lean the statement of Theorem F is for g >= 2 and the g = 1 case is `GPairArith.gPair_of_coprime`; an extension of the geometric Lean statements to g >= 1 (hG: 1 < G relaxed to 1 <= G, only `hbig` uses it) is in progress and was not built when the paper was revised.

**24. Is (g-1)d < u sharp?** Not known. (g-1)d = u forces d = 1 and g = u+1 (N = 45, 112, 225, ...). No tiling of those targets is known; float searches in the registry (45 = tile (4,5,6), 112 = tile (9,7,12)) found none (S, uncertified). So there is no sharpness example, and the known tilings (v | g) are far from the boundary.

**25. Which hypotheses does `leg_c_count_S1/S2` have?** u<v<2u coprime; hirr (alpha/pi irrational); G real, 1 < G; a CongruentDissection with model sides u^2, b, uv and target distances G u b, G u b, G v b; a RealLeg/LegPos/LegEnd chain; hang (first tile shows alpha at the first end). S1 reads the leg from a base corner; S2 reads the other leg from the apex and needs alpha at the apex, so it covers the alpha-leg, not an arbitrary leg. The earlier sentence "applies to either leg" is withdrawn (Section 5.1).

**26. Where is the apex case of Lemma 34(b) in Lean?** `apex_start`/`apex_end` are wrappers (angle sum pi-2alpha, interiority from `hwedge`, the tile across from `apex_ray_tile`, the chain hypothesis `hch`) that call the same `lemma33_interior` as the interior cases; not a separate induction. Written counterpart: Rw1 and Cs3 (Section 4.6, 5.2), Appendix A rows 2 and 8.

## Version 3.0 additions (2026-10-20)

**A30. Is Theorem R2 proved?** It is a hand proof (docs/THEOREM_R2_PROOF.md), audited twice inside the project by readers of the same model family as the author, and tested once by an exact region search at (4,7,2) that did not refute it. Lean has only its arithmetic half and a corollary conditional on `R2Count`. Nobody outside the project has read it. The 77 census values that use it are a separate row.

**A31. What is formal in the thick regime?** `SplusThick.wTilable_not_of_small_M` (M(f-e) <= e+1, M < f, Me >= f) and its instances; `NSQM.no_dissection_412` and `no_dissection_270` in the exclusion chain. The other census values excluded by the thick theorem are census-level (the leaf checks are too heavy for the kernel in the present interface).

**A32. Is 465 g^2 a tile count for all g >= 2?** Yes: g >= 5 by Lean (the up-set in g is Paliy's), g = 2, 3, 4 by exact-verified tilings (N = 1860, 4185, 7440) whose Lean certificates are planned. The core 465 is open.

**A33. Does this settle the prime case?** The prime case is unchanged: no prime p = 3 (mod 4), p > 3, is a tile count (primes = 1 mod 4 are sums of two squares). Nothing in this release changes it, and the Lean statement has been audited only inside the project.

## Version 4.0 additions (2026-10-22)

**A34. What is the band theorem and what does it not cover?** For coprime 2 <= e < f, M >= 2, f <= 2Me < f + e, T_M(e,f) has no tiling by (ef, f^2-e^2, f^2) (Lean `band_theorem_free`). It does not cover d = 2Me - f >= e (19,151 census values) or e = 1 (39 values).

**A35. Has anyone outside the project checked it?** No. The statement, arithmetic and axioms were audited by fresh sessions of the same model family; the induction was read twice line by line; nothing from outside.

**A36. Where are the Lean files?** In the public repository "Formalizing triangle tiling in Lean" (commit d728130). They are not rebuilt in this repository.

**A37. What are the 918?** Non-squarefree values <= 10^6 newly excluded by the census program using registry rows from the band theorem and its variants (199,364 -> 200,282). Program output; the leaf model is the program's.

**A38. Why is the number of known tile counts missing?** It has not been reconciled value by value against exact verification and Paliy's repository since v3.1.

**A39. Does this change the prime case?** No. Dates: Paliy 29 September 2026; our release 15 October 2026; Beeson-Rosu arXiv:2607.23453 v2 16 October, v3 21 October 2026. Parallel works; we claim nothing about their proof, and no announcement of the prime case is made here.
