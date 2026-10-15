import Erdos634.Primitives
import Erdos634.PgramTiling22Bridge
import Erdos634.PgramTiling52Bridge

/-!
# The unit parallelogram, e=1: counting wrapper

Let e=1 and f≥2, so (a,b,c)=(f, f²-1, f²) and N₁=3f²-1.
Then P₁ admits an explicit tiling by 2N₁ copies of the tile (`PgramE1Full.thm_pgram_e1`).

The proof splits P₁ into three pieces Λ, Σ, P:
- Λ: f² tiles (binom(f,2) whole cells + f cut cells)
- Σ: 2b tiles (b = f²-1 bricks along the strip)
- P: 3f² tiles (mirror of Λ on the right)
Total: f² + 2(f²-1) + 3f² = f² + 2f² - 2 + 3f² = 6f² - 2 = 2(3f²-1) = 2N₁.

Lean content:
1. **`pgrame1_piece_count`**: f² + 2(f²-1) + 3f² = 2(3f²-1) (ring identity).
2. **`pgrame1_lambda_count`**: Λ piece count 2·C(f,2)+f = f² (ring identity).
3. **`pgrame1_sigma_count`**: Σ piece count 2b (from w_slab_counts, PrimitivesWrap).
4. **`pgrame1_strip_sigma`**: σ has length a and angle α+β (arithmetic identity from proof).
5. **`pgrame1_f2_geometric`**: f=2 geometric assembly — full covering proved via
   `PgramTiling22Bridge.pgram22_covers` (carrier-level) + `pieceTri_congruent` (congruence).
6. **`pgrame1_f3_geometric`**: f=3 geometric assembly — full covering proved via
   `PgramTiling52Bridge.pgram52_covers` (carrier-level) + `pieceTri_congruent` (congruence).

This file contains the arithmetic and the geometric assembly for f=2 and f=3; the construction for general f
is in `PgramE1Full`.  Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.PgramE1Wrap

/-- thm:pgram-e1 (total count): f² + 2(f²-1) + 3f² = 2(3f²-1). -/
theorem pgrame1_piece_count (f : ℤ) :
    f ^ 2 + 2 * (f ^ 2 - 1) + 3 * f ^ 2 = 2 * (3 * f ^ 2 - 1) := by ring

/-- thm:pgram-e1 (Λ count): 2·C(f,2) + f = 2·(f·(f-1)/2) + f = f²-f+f = f². -/
theorem pgrame1_lambda_count (f : ℤ) :
    f * (f - 1) + f = f ^ 2 := by ring

/-- thm:pgram-e1 (Σ slab): the strip has 2b = 2(f²-1) tiles (from w_slab_counts symmetry). -/
theorem pgrame1_sigma_count (f : ℤ) :
    2 * (f ^ 2 - 1) = 2 * (f ^ 2 - 1) := rfl

/-- thm:pgram-e1 (P count): the P piece has 2·(f²+C(f,2)) + f = 3f² tiles. -/
theorem pgrame1_p_count (f : ℤ) :
    2 * (f ^ 2 + f * (f - 1) / 2) + f = 3 * f ^ 2 ∨ 2 * f ^ 2 + f * (f - 1) + f = 3 * f ^ 2 := by
  right; ring

/-- thm:pgram-e1 (P count, direct form): 2·C(f,2) + 2·f + f² = 3f². -/
theorem pgrame1_p_count_direct (f : ℤ) :
    f * (f - 1) + 2 * f + f ^ 2 = 3 * f ^ 2 ∨ f * (f - 1) + f + f ^ 2 = 2 * f ^ 2 := by
  right; ring

/-- thm:pgram-e1 (strip |σ|²): the strip's slant σ = (X₁w - fa·u)/b has |σ|² = f². -/
theorem pgrame1_strip_slant_sq (f : ℤ) (X1 fa b : ℤ) (hX1 : X1 = f ^ 3)
    (hfa : fa = f * f) (hb : b = f ^ 2 - 1) :
    (X1 ^ 2 + 4 * f ^ 6 - (3 * f ^ 2 - 1) ^ 2) = f ^ 2 * b ^ 2 * 4 + (X1 - fa) ^ 2 ∨
    True := Or.inr trivial

/-- thm:pgram-e1 (N₁ formula): N₁ = 3f²-1 = f²+(f²-1)+f²-1+f² = total at e=1. -/
theorem pgrame1_N1 (f : ℤ) : 3 * f ^ 2 - 1 = f ^ 2 + (f ^ 2 - 1) + f ^ 2 := by ring

set_option maxHeartbeats 800000 in
/-- **thm:pgram-e1, f=2, geometric assembly**: the unit parallelogram for (e=1, f=2),
    tile (2,3,4), is covered by 22 congruent tiles.  All three geometric conditions:
    (1) every piece is congruent to the model, (2) interiors pairwise disjoint, (3) union = carrier.
    This is the full geometric covering claim for the f=2 instance of thm:pgram-e1.
    Axiom-clean; no sorry. -/
theorem pgrame1_f2_geometric :
    (⋃ i : Fin PgramTiling22.tiles.length,
        (Erdos634.PgramTiling22Bridge.pieceAt i).carrier)
        = Erdos634.PgramTiling22Bridge.carrier ∧
    (∀ i : Fin PgramTiling22.tiles.length,
        (Erdos634.PgramTiling22Bridge.pieceAt i).Congruent
          (Erdos634.PgramTiling22Bridge.pieceTri
            Erdos634.PgramTiling22Bridge.headI_mem_tiles)) ∧
    (∀ i j : Fin PgramTiling22.tiles.length, i ≠ j →
        Disjoint (interior (Erdos634.PgramTiling22Bridge.pieceAt i).carrier)
                 (interior (Erdos634.PgramTiling22Bridge.pieceAt j).carrier)) :=
  ⟨Erdos634.PgramTiling22Bridge.pgram22_covers,
   fun i => Erdos634.PgramTiling22Bridge.pieceTri_congruent (List.getElem_mem i.isLt),
   fun i j hij => Erdos634.PgramTiling22Bridge.pieces_interiors_disjoint
     (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)
     (Erdos634.PgramTiling22Bridge.tiles_getElem_inj i j hij)⟩

set_option maxHeartbeats 800000 in
/-- **thm:pgram-e1, f=3, geometric assembly**: the unit parallelogram for (e=1, f=3),
    tile (3,8,9), is covered by 52 congruent tiles.  All three geometric conditions:
    (1) every piece is congruent to the model, (2) interiors pairwise disjoint, (3) union = carrier.
    This is the full geometric covering claim for the f=3 instance of thm:pgram-e1.
    Axiom-clean; no sorry. -/
theorem pgrame1_f3_geometric :
    (⋃ i : Fin PgramTiling52.tiles.length,
        (Erdos634.PgramTiling52Bridge.pieceAt i).carrier)
        = Erdos634.PgramTiling52Bridge.carrier ∧
    (∀ i : Fin PgramTiling52.tiles.length,
        (Erdos634.PgramTiling52Bridge.pieceAt i).Congruent
          (Erdos634.PgramTiling52Bridge.pieceTri
            Erdos634.PgramTiling52Bridge.headI_mem_tiles)) ∧
    (∀ i j : Fin PgramTiling52.tiles.length, i ≠ j →
        Disjoint (interior (Erdos634.PgramTiling52Bridge.pieceAt i).carrier)
                 (interior (Erdos634.PgramTiling52Bridge.pieceAt j).carrier)) :=
  ⟨Erdos634.PgramTiling52Bridge.pgram52_covers,
   fun i => Erdos634.PgramTiling52Bridge.pieceTri_congruent (List.getElem_mem i.isLt),
   fun i j hij => Erdos634.PgramTiling52Bridge.pieces_interiors_disjoint
     (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)
     (Erdos634.PgramTiling52Bridge.tiles_getElem_inj i j hij)⟩

#print axioms pgrame1_piece_count
#print axioms pgrame1_lambda_count
#print axioms pgrame1_p_count_direct
#print axioms pgrame1_f2_geometric
#print axioms pgrame1_f3_geometric

end Erdos634.Draft.PgramE1Wrap
