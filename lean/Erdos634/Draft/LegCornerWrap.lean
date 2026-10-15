import Erdos634.Draft.GLCG1
import Erdos634.Draft.GLCG2k

/-!
# Leg corner lemma for γ=2α: wrapper

For the tile (a,b,c)=(k²,2k+1,k(k+1)), γ=2α,
in a CongruentDissection, at a target corner of angle α with both adjacent sides not of length b or c:

(G1) the second tile on each adjacent side starts with α; the corner tile and its
     point-reflection share the a-chord.
(G2) if the first two edges on the c-side are both c-edges, the third tile starts with α.

Lean content:
1. **`legcorner_G1`**: `GLCG1.corner_G1` — G1 for any TwoAlphaData tile with word lemma.
2. **`legcorner_G2_k`**: `GLCG2k.corner_G2_k` — G2 for tile (sk², s(2k+1), sk(k+1)), k≥2.

No sorry; standard axioms.

Notes:
- No single theorem states both (G1) and (G2) jointly; they are proved separately.
- `corner_G2_k` is not instantiated at (k=2, s=16).
- Adjacent-side length conditions (≠b, ≠c) are the Lean form of the ">2b" assumption;
  the equivalence is not formalized.
-/

namespace Erdos634.Draft.LegCornerWrap

open Erdos634.GLC

/-- prop:legcorner (G1): corner_G1 holds for any TwoAlphaData tile. Re-export of GLCG1.corner_G1. -/
def legcorner_G1 := @corner_G1

/-- prop:legcorner (G2): corner_G2_k holds for tile (sk², s(2k+1), sk(k+1)), k≥2.
    Re-export of GLCG2k.corner_G2_k. -/
def legcorner_G2_k := @corner_G2_k

#print axioms legcorner_G1
#print axioms legcorner_G2_k

end Erdos634.Draft.LegCornerWrap
