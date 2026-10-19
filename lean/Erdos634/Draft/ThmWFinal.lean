-- Draft/ThmWFinal.lean — Theorem W, final statements (WTilable and the W / T tile counts) and instances.  UNAUDITED.  No sorry.
-- Credit: D. Paliy (W/beta framework, caps, eventual up-sets), M. Beeson & I. Rosu (W/T targets, S2L skew frame);
-- the six-piece template was found by our engine `bto`; hand proof (project working notes) (audited SOUND 2026-10-19).
import Erdos634.Draft.ThmW

open scoped Classical
open Erdos634.Draft.CollarG (WTilable)
open Erdos634.Draft.TileCountFamilies (TileCount)

namespace Erdos634.Draft.ThmW

/-- **Theorem W (Lean).**  For coprime `2 ≤ e ≤ f-2` and `M e ≥ f`, `(M-1)(f-e) ≥ f`: `W_M(e,f)` is tiled, and
`(2f²-e²)M²` and `M²(3f²-e²)` are tile counts. -/
theorem thmW (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f) (h1 : f ≤ M * e)
    (h2 : f ≤ (M - 1) * (f - e)) :
    WTilable e f M ∧ TileCount ((2 * f ^ 2 - e ^ 2) * M ^ 2) ∧ TileCount (M ^ 2 * (3 * f ^ 2 - e ^ 2)) := by
  have hw := thmW_wTilable e f M hco he hef h1 h2
  have hM1 : 1 ≤ M := by
    by_contra h0
    have : M = 0 := by omega
    subst this; simp at h1; omega
  have hMf : f ≤ M * (f - e) := le_trans h2 (Nat.mul_le_mul_right _ (Nat.sub_le M 1))
  have := Erdos634.Draft.DebtB.counts_of_wTilable e f M (by omega) (by omega) hco hM1 hMf hw M le_rfl
  exact ⟨hw, this.2.1, this.2.2⟩

theorem tileCount_W (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f) (h1 : f ≤ M * e)
    (h2 : f ≤ (M - 1) * (f - e)) : TileCount ((2 * f ^ 2 - e ^ 2) * M ^ 2) :=
  (thmW e f M hco he hef h1 h2).2.1

theorem tileCount_T (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f) (h1 : f ≤ M * e)
    (h2 : f ≤ (M - 1) * (f - e)) : TileCount (M ^ 2 * (3 * f ^ 2 - e ^ 2)) :=
  (thmW e f M hco he hef h1 h2).2.2

-- the thirteen known W tilings below the threshold are covered
theorem inst_656 : TileCount 656 := tileCount_W 3 5 4 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem inst_3088 : TileCount 3088 := tileCount_W 7 11 4 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
-- new cases from the audit
theorem inst_414 : TileCount 414 := tileCount_W 2 5 3 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem inst_801 : TileCount 801 := tileCount_W 3 7 3 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem inst_639 : TileCount 639 := tileCount_T 2 5 3 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem inst_27324 : TileCount 27324 := tileCount_T 3 16 6 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Erdos634.Draft.ThmW

#print axioms Erdos634.Draft.ThmW.thmW
#print axioms Erdos634.Draft.ThmW.inst_656
#print axioms Erdos634.Draft.ThmW.inst_3088
#print axioms Erdos634.Draft.ThmW.inst_414
#print axioms Erdos634.Draft.ThmW.inst_801
#print axioms Erdos634.Draft.ThmW.inst_639
#print axioms Erdos634.Draft.ThmW.inst_27324
