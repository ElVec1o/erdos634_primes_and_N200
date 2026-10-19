-- Draft/DebtBBridge.lean -- DEBT_B (2026-10-19), UNAUDITED.  No sorry, no native_decide.
/-
**Bridge from a skew-frame packing to `WTilable`, and upward closure of the W / T counts.**

The thirteen tilings `Draft/TW*.lean` (AllWBelow) are stated as `TileCount N` only.  Here the target and the model of the
packing (`LadderFam.pack_exists'` gives `D.target = tgt`, `D.model = brickL ..`) are identified with the sides of
`W_M(e,f)` and of the tile `(ef, f²-e², f²)`, so that each gives `WTilable e f M0`.  Then the existing Lean closure
`WStripChord.wstrip_mono` (W_{M-1} tiled => W_M tiled when `f ≤ M (f-e)`) and the count-carrying beta lift
`ConjC.BetaCount.tileCount_of_wTilable` give `TileCount ((2f²-e²)M²)` and `TileCount (M²(3f²-e²))` for all `M ≥ M0`.

Credits: D. Paliy (W/beta framework, collar and layer ideas, the upward closure in M, alpha up-set), M. Beeson and
I. Rosu (S2L skew frame, seed), our collar session (CollarG, WStrip); the template tilings are found by our engine `bto`.
-/
import Erdos634.Draft.CollarG
import Erdos634.Draft.WBrickF
import Erdos634.Draft.WStripChord
import Erdos634.ConjC.BetaCount

open scoped Classical
open Erdos634.Geometry
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.WFrameF (Phi sq_Phi)
open Erdos634.Draft.WBrickF (triC brickL triC_pts)
open Erdos634.Draft.CollarG (WTilable)
open Erdos634.Draft.TileCountFamilies (TileCount)

namespace Erdos634.Draft.DebtB

/-- squared distance in the skew frame -/
noncomputable def sqf (F : ℝ) (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 + (p.1 - q.1) * (p.2 - q.2) / F

theorem dist_Phi_of_sq {F : ℝ} (hF : 1 < F) (p q : ℝ × ℝ) {s : ℝ} (hs : 0 ≤ s) (h : sqf F p q = s ^ 2) :
    dist (Phi F p) (Phi F q) = s := by
  have := sq_Phi hF p q
  exact (sq_eq_sq₀ dist_nonneg hs).mp (by rw [this]; exact h)

/-- base form: the sides in the order `(BC, CA, AB)` -/
theorem hasSides_triC_base {F : ℝ} (hF : 1 < F) (a b c : ℝ × ℝ) (h)
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hbc : sqf F b c = x ^ 2) (hca : sqf F c a = y ^ 2) (hab : sqf F a b = z ^ 2) :
    HasSides (triC F hF a b c h) x y z := by
  refine ⟨Equiv.refl _, ?_, ?_, ?_⟩ <;> simp only [Equiv.refl_apply, triC_pts]
  · exact dist_Phi_of_sq hF b c hx hbc
  · exact dist_Phi_of_sq hF c a hy hca
  · exact dist_Phi_of_sq hF a b hz hab

/-- orientation 1: sides in the order `(AB, BC, CA)` -/
theorem hasSides_triC_o1 {F : ℝ} (hF : 1 < F) (a b c : ℝ × ℝ) (h)
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hab : sqf F a b = x ^ 2) (hbc : sqf F b c = y ^ 2) (hca : sqf F c a = z ^ 2) :
    HasSides (triC F hF a b c h) x y z :=
  hasSides_rot (hasSides_rot (hasSides_triC_base hF a b c h hy hz hx hbc hca hab))

/-- orientation 2: sides in the order `(BC, AB, CA)` -/
theorem hasSides_triC_o2 {F : ℝ} (hF : 1 < F) (a b c : ℝ × ℝ) (h)
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hbc : sqf F b c = x ^ 2) (hab : sqf F a b = y ^ 2) (hca : sqf F c a = z ^ 2) :
    HasSides (triC F hF a b c h) x y z :=
  hasSides_swap (hasSides_rot (hasSides_rot (hasSides_triC_base hF a b c h hx hz hy hbc hca hab)))

/-- the model brick `(0,0),(A,0),(A,B)` with `A = ef`, `B = f²-e²` has the sides of the tile -/
theorem hasSides_brick {e f : ℕ} (he : 1 ≤ e) (hef : e < f) {F : ℝ} (hFe : F = (f : ℝ) / e) (hF : 1 < F)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (hA' : A = (e : ℝ) * f) (hB' : B = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) :
    HasSides (brickL F hF A B hA hB) ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hf' : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
  have hdiag : A ^ 2 + B ^ 2 + A * B / F = ((f : ℝ) ^ 2) ^ 2 := by
    rw [hFe, hA', hB']; field_simp; ring
  have h := hasSides_triC_o1 hF (0, 0) (A, 0) (A, B) (by intro h; nlinarith [mul_pos hA hB])
    (x := (e : ℝ) * f) (y := (f : ℝ) ^ 2 - (e : ℝ) ^ 2) (z := (f : ℝ) ^ 2) (by positivity)
    (by rw [← hB']; exact hB.le) (by positivity)
    (by simp only [sqf]; rw [← hA']; ring) (by simp only [sqf]; rw [← hB']; ring)
    (by simp only [sqf]; rw [← hdiag]; ring)
  exact h

/-- **Bridge.**  A dissection into `(2f²-e²)M²` pieces whose target has the sides of `W_M(e,f)` and
whose model is the standard brick is a `WTilable e f M`. -/
theorem wTilable_of_pack {e f M N : ℕ} (he : 1 ≤ e) (hef : e < f) (hN : N = (2 * f ^ 2 - e ^ 2) * M ^ 2)
    {F : ℝ} (hFe : F = (f : ℝ) / e) (hF : 1 < F)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (hA' : A = (e : ℝ) * f) (hB' : B = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (D : CongruentDissection N) (T : Erdos634.Geometry.Tri) (hT : D.target = T) (hM : D.model = brickL F hF A B hA hB)
    (hs : HasSides T ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3)) :
    WTilable e f M := by
  subst hN
  exact ⟨D, by rw [hT]; exact hs, by rw [hM]; exact hasSides_brick he hef hFe hF A B hA hB hA' hB'⟩

/-- **Upward closure of the counts.**  If `W_{M0}(e,f)` is tiled and `f ≤ M0 (f-e)`, then for every `M ≥ M0`
`(2f²-e²)M²` and `M²(3f²-e²)` are tile counts. -/
theorem counts_of_wTilable (e f M0 : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM0 : 1 ≤ M0)
    (hMf : f ≤ M0 * (f - e)) (h : WTilable e f M0) :
    ∀ M, M0 ≤ M → WTilable e f M ∧ TileCount ((2 * f ^ 2 - e ^ 2) * M ^ 2) ∧ TileCount (M ^ 2 * (3 * f ^ 2 - e ^ 2)) := by
  intro M hM
  obtain ⟨k, rfl⟩ : ∃ k, M = M0 + k := ⟨M - M0, by omega⟩
  have hw := Erdos634.Draft.WStripChord.wstrip_mono e f M0 he hef hco hM0 hMf h k
  refine ⟨hw, ?_, ?_⟩
  · obtain ⟨D, -⟩ := hw
    exact ⟨D⟩
  · obtain ⟨g, rfl⟩ : ∃ g, f = e + g := ⟨f - e, by omega⟩
    have hc := Erdos634.ConjC.BetaCount.tileCount_of_wTilable e g (M0 + k) (by omega) (by omega) (by omega) hw
    have hle : e ^ 2 ≤ (e + g) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have key : (M0 + k) ^ 2 * (3 * (e + g) ^ 2 - e ^ 2) =
        (2 * (e + g) ^ 2 - e ^ 2) * (M0 + k) ^ 2 + (M0 + k) * (e + g) * ((M0 + k) * (e + g)) := by
      have e1 : 3 * (e + g) ^ 2 - e ^ 2 = (2 * (e + g) ^ 2 - e ^ 2) + (e + g) ^ 2 := by
        generalize (e + g) ^ 2 = V at hle ⊢; generalize e ^ 2 = U at hle ⊢; omega
      rw [e1]; ring
    rw [key]; exact hc

end Erdos634.Draft.DebtB

#print axioms Erdos634.Draft.DebtB.wTilable_of_pack
#print axioms Erdos634.Draft.DebtB.counts_of_wTilable
