-- Draft/ThetaCompose.lean -- tile count 778855 = theta_119(3,8) = W_55(3,8) u alpha_8(3,8), and the general family.  UNAUDITED.
-- No sorry, no native_decide.
/-
**`theta_{jQ}(e,f) = W_{jb}(e,f) u alpha_{jf}(e,f)` as a tile-count theorem.**

For the tile `(e f, b, f^2)`, `b = f^2 - e^2`, `Q = 2 f^2 - e^2`:

* `W_M(e,f)`: the triangle with sides `(M f b, M e Q, M f^3)`; tiled for every `M >= f` by
  `Draft.Residue.wTilable_ge` (Lean, paper statement by Paliy/Beeson; Lean proof by this project);
  `(2 f^2 - e^2) M^2` tiles.
* `alpha_g(e,f)`: the isosceles triangle with base `g b Q` and legs `g b f^2`; for a THIN row
  (`e f < b`) and `g >= 2` tiled by `b Q g^2` tiles: `Draft.G2Param` (UNAUDITED).  Here the G2 tiling
  is read off with its TARGET (`alpha_exists`), not only as a count: the target is the skew-frame
  triangle `(0,0), (b Q g, 0), (b^2 g, e f b g)` whose sides are computed.
* the gluing `Draft.ThetaComposeGlue.glue_cevian` (placement by explicit vectors; general union lemma
  `unionCongruentDissection` of the corpus).

MAIN RESULTS.
* `theta_exists`: for `e >= 1` coprime to `f`, `f^2 = e^2 + b`, thin row `e f < b`, `j >= 1` with `f <= j b`:
  a `CongruentDissection` of the isosceles triangle with legs `j b Q f`, base `j b Q e` by `b (j Q)^2`
  copies of the tile `(e f, b, f^2)`.
* `tileCount_778855 : TileCount 778855` (`(e,f,j) = (3,8,1)`, `b = 55`, `Q = 119`; `359975 + 418880`).

HYPOTHESES ARE SATISFIABLE and exhibited at `(3,8,1)`: `Nat.Coprime 3 8`, `64 = 9 + 55`, `3*8 < 55`, `8 <= 55`.
STATUS: the `W` input (`wTilable_ge`) is Lean-proved (audited internally); the `alpha` input
(`G2Param`) is UNAUDITED; this module is UNAUDITED.

CREDIT: the identity: Work item C (NEWWAYS_C, 2026-10-20); the theta family and up-sets: D. Paliy;
W/T and the skew frame: M. Beeson and I. Rosu; Herdt-style cevian cut; Laczkovich (macro dissection).
-/
import Erdos634.Draft.G2Param
import Erdos634.Draft.DebtBBridge
import Erdos634.Draft.ResidueSeed
import Erdos634.Draft.ThetaComposeGlue

open scoped Classical

namespace Erdos634.Draft.ThetaCompose

open Erdos634.Geometry
open Erdos634.Draft.RegionTiling Erdos634.Draft.CollarLayer Erdos634.Draft.CollarFam
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.TileCountFamilies (TileCount)
open Erdos634.Draft.DebtB (sqf hasSides_triC_base hasSides_triC_o1)

noncomputable section

/-- **The `alpha` tiling of a thin row with its target.**  For `f^2 = e^2 + b`, `e f < b` and `g >= 2` there is a
`CongruentDissection` into `b (b + f^2) g^2` copies of the tile whose target has sides
`(g b (2 f^2 - e^2), g b f^2, g b f^2)` (base, leg, leg), model sides `(e f, b, f^2)`. -/
theorem alpha_exists (e f b : ℕ) (he : 0 < e) (hb : f * f = e * e + b) (hq : e * f < b) (g : ℕ) (hg : 2 ≤ g) :
    ∃ D : CongruentDissection (b * (b + f * f) * g * g),
      HasSides D.target ((g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))
        ((g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (f : ℝ) ^ 2) ((g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (f : ℝ) ^ 2) ∧
      HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) := by
  have hef : e < f := Erdos634.Draft.G2Param.lt_of_thin e f b hb hq
  have hER : (0 : ℝ) < e := by exact_mod_cast he
  have hEFR : (e : ℝ) < f := by exact_mod_cast hef
  have hφ : 1 < (f : ℝ) / e := by rw [lt_div_iff₀ hER]; linarith
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  obtain ⟨R⟩ := up_rtiling hφ e f b (b * (b + f * f)) 2 he hef hb hq.le rfl rfl (by norm_num)
    (Erdos634.Draft.G2Param.g2_base e f b he hb hq hφ rfl) g hg
  obtain ⟨hb0, ha0, hc0⟩ := pos_facts hER hEFR
  have hB0 : 0 < pB0 (e : ℝ) f := by unfold pB0; positivity
  have hdet : ((pB0 (e : ℝ) f * g, (0 : ℝ)).1 - ((0 : ℝ), (0 : ℝ)).1) *
      (((f ^ 2 - e ^ 2 : ℝ) ^ 2 * g, (e : ℝ) * f * (f ^ 2 - e ^ 2) * g).2 - ((0 : ℝ), (0 : ℝ)).2) -
      (((f ^ 2 - e ^ 2 : ℝ) ^ 2 * g, (e : ℝ) * f * (f ^ 2 - e ^ 2) * g).1 - ((0 : ℝ), (0 : ℝ)).1) *
      ((pB0 (e : ℝ) f * g, (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2) ≠ 0 := by
    have : ((pB0 (e : ℝ) f * g, (0 : ℝ)).1 - ((0 : ℝ), (0 : ℝ)).1) *
      ((((f : ℝ) ^ 2 - e ^ 2) ^ 2 * g, (e : ℝ) * f * (f ^ 2 - e ^ 2) * g).2 - ((0 : ℝ), (0 : ℝ)).2) -
      ((((f : ℝ) ^ 2 - e ^ 2) ^ 2 * g, (e : ℝ) * f * (f ^ 2 - e ^ 2) * g).1 - ((0 : ℝ), (0 : ℝ)).1) *
      ((pB0 (e : ℝ) f * g, (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2)
        = pB0 (e : ℝ) f * g * ((e : ℝ) * f * (f ^ 2 - e ^ 2) * g) := by
      simp only []; ring
    rw [this]
    exact (mul_pos (mul_pos hB0 hg0) (mul_pos (mul_pos ha0 hb0) hg0)).ne'
  have hcar := Erdos634.Draft.WBrickF.carrier_triC ((f : ℝ) / e) hφ ((0 : ℝ), (0 : ℝ))
    (pB0 (e : ℝ) f * g, 0) (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 * g, (e : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * g) hdet
  have R' : RTiling (Erdos634.Draft.WBrickF.triC ((f : ℝ) / e) hφ ((0 : ℝ), (0 : ℝ))
      (pB0 (e : ℝ) f * g, 0) (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 * g, (e : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * g) hdet).carrier
      (Mrow hφ e f he hef) (b * (b + f * f) * g * g) := by
    rw [hcar]; exact R
  have hef0 : (e : ℝ) ≠ 0 := hER.ne'
  have hf0 : (f : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < f).ne'
  refine ⟨toCD R', ?_, ?_⟩
  · -- target sides
    have hbR : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      have : ((f * f : ℕ) : ℝ) = ((e * e + b : ℕ) : ℝ) := by rw [hb]
      push_cast at this; nlinarith
    have hF : (1 : ℝ) < (f : ℝ) / e := hφ
    have hs := hasSides_triC_base hF ((0 : ℝ), (0 : ℝ)) (pB0 (e : ℝ) f * g, 0)
      (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 * g, (e : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * g) hdet
      (x := (g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (f : ℝ) ^ 2)
      (y := (g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (f : ℝ) ^ 2)
      (z := (g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      (mul_nonneg (mul_nonneg hg0.le hb0.le) (sq_nonneg _))
      (mul_nonneg (mul_nonneg hg0.le hb0.le) (sq_nonneg _))
      (mul_nonneg (mul_nonneg hg0.le hb0.le) (by nlinarith)) ?_ ?_ ?_
    · exact hasSides_rot (hasSides_rot hs)
    · simp only [sqf, pB0]; field_simp; ring
    · simp only [sqf, pB0]; field_simp; ring
    · simp only [sqf, pB0]; field_simp; ring
  · -- model sides: the model is `brickL φ hφ b (e f)`
    have hbpos := hb0
    have h := hasSides_triC_o1 hφ ((0 : ℝ), (0 : ℝ)) (((f : ℝ) ^ 2 - (e : ℝ) ^ 2), 0)
      (((f : ℝ) ^ 2 - (e : ℝ) ^ 2), (e : ℝ) * f) (by intro h; nlinarith [mul_pos hb0 ha0])
      (x := (f : ℝ) ^ 2 - (e : ℝ) ^ 2) (y := (e : ℝ) * f) (z := (f : ℝ) ^ 2) hb0.le ha0.le hc0.le
      (by simp only [sqf]; ring) (by simp only [sqf]; ring)
      (by simp only [sqf]; field_simp; ring)
    exact hasSides_swap h

/-- `W_M` as a tiling with its target: from `wTilable_ge`. -/
theorem w_exists (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : f ≤ M) :
    ∃ D : CongruentDissection ((2 * f ^ 2 - e ^ 2) * M ^ 2),
      HasSides D.target ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
        ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3) ∧
      HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) :=
  Erdos634.Draft.Residue.wTilable_ge e f he hef hco M hM

/-- **`theta_{jQ}(e,f) = W_{jb}(e,f) u alpha_{jf}(e,f)`, tile-count form with the target.**
`f^2 = e^2 + b`, thin row `e f < b`, `e` coprime to `f`, `j >= 1`, `f <= j b`.  The isosceles triangle with legs
`j b Q f` and base `j b Q e` (`Q = 2 f^2 - e^2 = b + f^2`) is cut into `b (j Q)^2` copies of `(e f, b, f^2)`. -/
theorem theta_exists (e f b j : ℕ) (he : 1 ≤ e) (hco : Nat.Coprime e f) (hb : f * f = e * e + b) (hq : e * f < b)
    (hj : 1 ≤ j) (hjb : f ≤ j * b) :
    ∃ D : CongruentDissection (b * (j * (b + f * f)) * (j * (b + f * f))),
      HasSides D.target ((j : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((f : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
        ((j : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((f : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
        ((j : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ∧
      HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) := by
  have hef : e < f := Erdos634.Draft.G2Param.lt_of_thin e f b hb hq
  have hbR : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : ((f * f : ℕ) : ℝ) = ((e * e + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; nlinarith
  have hfpos : 2 ≤ f := by omega
  have hg : 2 ≤ j * f := by nlinarith
  obtain ⟨D1, h1t, h1m⟩ := w_exists e f (j * b) he hef hco hjb
  obtain ⟨D2, h2t, h2m⟩ := alpha_exists e f b (by omega) hb hq (j * f) hg
  have heR : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hjR : (0 : ℝ) < ((j * b : ℕ) : ℝ) := by
    have : 0 < j * b := by
      have : 0 < b := by nlinarith
      positivity
    exact_mod_cast this
  -- the sizes of the two pieces
  have hMg : ((j * f : ℕ) : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = ((j * b : ℕ) : ℝ) * f := by
    rw [← hbR]; push_cast; ring
  have hs2 : HasSides D2.target (((j * b : ℕ) : ℝ) * ((f : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (((j * b : ℕ) : ℝ) * (f : ℝ) ^ 3) (((j * b : ℕ) : ℝ) * (f : ℝ) ^ 3) := by
    refine Erdos634.Draft.UniformThreshold.hasSides_congr h2t ?_ ?_ ?_
    · linear_combination (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * hMg
    · linear_combination (f : ℝ) ^ 2 * hMg
    · linear_combination (f : ℝ) ^ 2 * hMg
  obtain ⟨D, hDt, hDm⟩ := Erdos634.Draft.ThetaComposeGlue.glue_cevian (e : ℝ) f ((j * b : ℕ) : ℝ) heR hefR hjR D1 D2 h1t h1m hs2 h2m
  have hcount : (2 * f ^ 2 - e ^ 2) * (j * b) ^ 2 + b * (b + f * f) * (j * f) * (j * f)
      = b * (j * (b + f * f)) * (j * (b + f * f)) := by
    have hf2 : f ^ 2 = e ^ 2 + b := by rw [pow_two, pow_two]; exact hb
    have h2 : 2 * f ^ 2 - e ^ 2 = b + f * f := by rw [pow_two] at hf2 ⊢; omega
    rw [h2]
    have : e * e + b = f * f := hb.symm
    nlinarith [this]
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Draft.CVCCevianCut.exists_reindex hcount D
  refine ⟨E, ?_, by rw [hEm]; exact hDm⟩
  rw [hEt]
  refine Erdos634.Draft.UniformThreshold.hasSides_congr hDt ?_ ?_ ?_ <;> (rw [← hbR]; push_cast; ring)

/-- **`778855 = 55 * 119^2` is a tile count.**  `theta_119(3,8) = W_55(3,8) u alpha_8(3,8)`:
`359975 + 418880 = 778855`; tile `(24, 55, 64)`. -/
theorem tileCount_778855 : TileCount 778855 := by
  obtain ⟨D, -, -⟩ := theta_exists 3 8 55 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨D⟩

end

end Erdos634.Draft.ThetaCompose

#print axioms Erdos634.Draft.ThetaCompose.alpha_exists
#print axioms Erdos634.Draft.ThetaCompose.w_exists
#print axioms Erdos634.Draft.ThetaCompose.theta_exists
#print axioms Erdos634.Draft.ThetaCompose.tileCount_778855
