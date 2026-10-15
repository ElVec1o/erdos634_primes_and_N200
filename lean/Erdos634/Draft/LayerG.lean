/-
Draft/LayerG.lean  In `AllThreshold`.

PAPER.  `prop:layerall` (b): "Let `2f(M − e) ≥ b`, and put `x_a = 2Mf − (f² + 2ef − e²)`, so that `x_a ≥ 0`.  The trapezoid cut from `T_M(e, f)` by the line parallel to the base at the height `eH₁` ...
can be cut into `(2Me − e²)(3f² − e²)` copies of the tile.  A layout is, from left to right along the base: the tile at scale `ef`, ...; `x_a` columns of `ef` parallelograms `a × b`; `eM` columns of `b`
parallelograms `b × a`; and the cap of Paliy's collar for the member `(e, f)`, a trapezoid of six pieces ...  the part of `T_M(e, f)` above the trapezoid is a translate of `T_{M−e}(e, f)`."
And (c)(i): "If `2fM ≥ b` and `T_M(e, f)` has a tiling, then `T_{M+e}(e, f)` has a tiling."

WHAT IS PROVED HERE (the geometry is `Draft/LayerGGeom.lean`, the tools `Draft/LayerGTools.lean`; frame `Φ_F`, `F = f/e` of `CollarG`, `u = e`, `g = f − e`, `f = u + g`; `T_M = DS (A M) (B M) (C M)`).
* `RLs1`, `RLa`, `RLb`: the tilings of the three new pieces: the tile at scale `ef` (`(ef)²` tiles), the rectangle of `ef × x_a` cells `b × a` (`2 ef x_a` tiles), the rectangle of `b × uM` cells `a × b` (`2 b e M` tiles);
  the six pieces of the cap are the tilings `CollarG.RT3, …, RT8` at `σ = 1`, translated by `(A (M − f − 1), 0)`;
* `layer_real`: **the layer with real parameters, and with the chord.**  A tiling `R₀` of the frame triangle `T_{M−u}` (translated by `(0, B u)`), no tile of which crosses the line `x = c` (`c ≤ A (M − u)`), together with the ten regions of `LayerGGeom`,
  gives a tiling `R` of `T_M` by `P M²` tiles (`P = 3f² − e²`) no tile of which crosses the line `x = c`: the tiles of the layer lie right of the chord `x = A (M − u)`, the tiles of the translate of `T_{M−u}` are those of `R₀`;
* `layer_nat_core`: the same with natural numbers `u, g, m` (inner scale `m`, outer scale `m + u`, condition `x_a ≥ 0` written `f² ≤ 2 m f + e²`);
* `layer_c_i`: **`prop:layerall` (c)(i)** in the notation of the paper (`e`, `f`, `M`): `2fM ≥ b` and `BetaTilable e f M` give `BetaTilable e f (M + e)`.
The count: `(ef)² + 2 ef x_a + 2 b e M + [(ef)² + 3 (e(f−e))² + 2 f(f−e) e(f−e) + 2 e(f−e) e²] + P (M−e)² = P M²`, so the layer has `(2Me − e²) P` tiles.

No sorry, no native_decide.
-/
import Erdos634.Draft.LayerGTools
import Erdos634.Draft.WStrip

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.LayerG
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (scaledRT baseTri baseTri_cong disjoint_image')
open Erdos634.Draft.WtoDeltaF (DS)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)
open Erdos634.Draft.UniformThreshold (BetaTilable)
open Erdos634.Draft.CollarG (gF hF1 hfr hvpos hapos hbpos cApos cBpos hPpos hab_id Mod cellA cellB volMod ca cb cA cB cC cL
  Z3 Z4 Z5 Z8 RT3 RT4 RT5 RT6 RT7 RT8)
open Erdos634.Draft.WStripG (pgram_rt)
open Erdos634.Draft.LayerE1 (shift_sub_exists)
open Erdos634.Draft.LayerE1Chord (skewX skewX_Phi)

/-! ## The tilings of the new pieces -/

section pieces
variable {u g M : ℝ}

theorem detS (hu : 0 < u) (hg : 0 < g) :
    ((lSb u g M).1 - (lSa u g M).1) * ((lSc u g M).2 - (lSa u g M).2)
      - ((lSc u g M).1 - (lSa u g M).1) * ((lSb u g M).2 - (lSa u g M).2) ≠ 0 := by
  have hE : ((lSb u g M).1 - (lSa u g M).1) * ((lSc u g M).2 - (lSa u g M).2)
      - ((lSc u g M).1 - (lSa u g M).1) * ((lSb u g M).2 - (lSa u g M).2)
      = -(cA u g * u * (ca u g * ca u g)) := by
    simp only [lSa, lSb, lSc]
    have e1 := lYt_sub (u := u) (g := g) (M := M)
    have e2 : lX1 u g M - lX0 u g M = cA u g * u := by simp only [lX0, lX1]; ring
    linear_combination (-(lYt u g M - lYa u g M)) * e2 + (-(cA u g * u)) * e1
  rw [hE]
  exact neg_ne_zero.mpr (mul_pos (mul_pos (cApos hu hg) hu) (mul_pos (hapos hu hg) (hapos hu hg))).ne'

/-- `LS1`: the tile at scale `e f` (`k = u (u + g)`), with its side `k a` on the base `x = A M` -/
noncomputable def RLs1 (hu : 0 < u) (hg : 0 < g) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = ca u g) :
    RTiling (Phi (gF u g) '' LS1 u g M) (Mod hu hg) (k * k) :=
  scaledRT (gF u g) (hfr hu hg) (lSa u g M) (lSb u g M) (lSc u g M) k hk0 (detS hu hg) _
    (baseTri_cong _ _ (ca u g) (cb u g) (((u + g) ^ 2) ^ 2) (hapos hu hg) (hbpos hu hg) (hab_id hu hg) _ _ _
      k hk0 _
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]
          simp only [lSa, lSb, lSc, lX0, lX1, lYa, lYb, lY1, lYt, lxa, cA, cB, cC, cL, ca, cb, gF]
          field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]
          simp only [lSa, lSb, lSc, lX0, lX1, lYa, lYb, lY1, lYt, lxa, cA, cB, cC, cL, ca, cb, gF]
          field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]
          simp only [lSa, lSb, lSc, lX0, lX1, lYa, lYb, lY1, lYt, lxa, cA, cB, cC, cL, ca, cb, gF]
          field_simp; ring))

/-- `LRa`: `n = e f` columns of width `b` and `m = x_a` rows of height `a`, cells `b × a` of type `A` (`n` or `m` may be `0`) -/
theorem RLa (hu : 0 < u) (hg : 0 < g) (n m : ℕ) (hn : (n : ℝ) = u * (u + g)) (hm : (m : ℝ) = lxa u g M) :
    ∃ S : Set Plane, Nonempty (RTiling S (Mod hu hg) (2 * n * m)) ∧ S ⊆ Phi (gF u g) '' LRa u g M := by
  have h := pgram_rt (hfr hu hg) (hfr hu hg) (hbpos hu hg) (hapos hu hg) (cellA hu hg) n m
    (lX0 u g M, lYb u g M) (cb u g, (0 : ℝ)) ((0 : ℝ), ca u g)
    (by show cb u g * ca u g - 0 * 0 ≠ 0
        rw [mul_zero, sub_zero]; exact (mul_pos (hbpos hu hg) (hapos hu hg)).ne')
    (by show cb u g ^ 2 + (0 : ℝ) ^ 2 + cb u g * 0 / gF u g = cb u g ^ 2; ring)
    (by show (0 : ℝ) ^ 2 + ca u g ^ 2 + 0 * ca u g / gF u g = ca u g ^ 2; ring)
    (by show (0 - cb u g) ^ 2 + (ca u g - 0) ^ 2 + (0 - cb u g) * (ca u g - 0) / gF u g
          = cb u g ^ 2 + ca u g ^ 2 - cb u g * ca u g / gF u g
        ring)
  rw [hn, hm] at h
  exact h

/-- `LRb`: `n = b` columns of width `a` and `m = u M` rows of height `b`, cells `a × b` of type `B` -/
theorem RLb (hu : 0 < u) (hg : 0 < g) (n m : ℕ) (hn : (n : ℝ) = cb u g) (hm : (m : ℝ) = u * M) :
    ∃ S : Set Plane, Nonempty (RTiling S (Mod hu hg) (2 * n * m)) ∧ S ⊆ Phi (gF u g) '' LRb u g M := by
  have h := pgram_rt (hfr hu hg) (hfr hu hg) (hapos hu hg) (hbpos hu hg) (cellB hu hg) n m
    (lX0 u g M, lY1 u g) (ca u g, (0 : ℝ)) ((0 : ℝ), cb u g)
    (by show ca u g * cb u g - 0 * 0 ≠ 0
        rw [mul_zero, sub_zero]; exact (mul_pos (hapos hu hg) (hbpos hu hg)).ne')
    (by show ca u g ^ 2 + (0 : ℝ) ^ 2 + ca u g * 0 / gF u g = ca u g ^ 2; ring)
    (by show (0 : ℝ) ^ 2 + cb u g ^ 2 + 0 * cb u g / gF u g = cb u g ^ 2; ring)
    (by show (0 - ca u g) ^ 2 + (cb u g - 0) ^ 2 + (0 - ca u g) * (cb u g - 0) / gF u g
          = ca u g ^ 2 + cb u g ^ 2 - ca u g * cb u g / gF u g
        ring)
  rw [hn, hm] at h
  exact h

end pieces

/-! ## Assembly: the ten regions fill `T_M` -/

/-- the regions in the plane; the four parallelogram regions are given as sets -/
noncomputable def regionL (u g M : ℝ) (Sa Sb S6 S7 : Set Plane) : Fin 10 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi (gF u g) '' LY0 u g M
  | ⟨1, _⟩ => Phi (gF u g) '' LS1 u g M
  | ⟨2, _⟩ => Sa
  | ⟨3, _⟩ => Sb
  | ⟨4, _⟩ => Phi (gF u g) '' Sh (lvsh u g M) (Z3 u g 1)
  | ⟨5, _⟩ => Phi (gF u g) '' Sh (lvsh u g M) (Z4 u g 1)
  | ⟨6, _⟩ => Phi (gF u g) '' Sh (lvsh u g M) (Z5 u g 1)
  | ⟨7, _⟩ => S6
  | ⟨8, _⟩ => S7
  | ⟨9, _⟩ => Phi (gF u g) '' Sh (lvsh u g M) (Z8 u g 1)
  | ⟨k + 10, h⟩ => absurd h (by omega)

/-- the tile counts of the ten regions -/
def lcnt (n0 k3 k4 nA mA nB mB k6 l6 k7 l7 : ℕ) : Fin 10 → ℕ := fun i => match i with
  | ⟨0, _⟩ => n0
  | ⟨1, _⟩ => k3 * k3
  | ⟨2, _⟩ => 2 * nA * mA
  | ⟨3, _⟩ => 2 * nB * mB
  | ⟨4, _⟩ => k3 * k3
  | ⟨5, _⟩ => k4 * k4
  | ⟨6, _⟩ => k4 * k4
  | ⟨7, _⟩ => 2 * (k6 + 1) * (l6 + 1)
  | ⟨8, _⟩ => 2 * (k7 + 1) * (l7 + 1)
  | ⟨9, _⟩ => k4 * k4
  | ⟨k + 10, h⟩ => absurd h (by omega)

theorem sum_lcnt (n0 k3 k4 nA mA nB mB k6 l6 k7 l7 : ℕ) :
    ∑ a, lcnt n0 k3 k4 nA mA nB mB k6 l6 k7 l7 a
      = n0 + (k3 * k3 + (2 * nA * mA + 2 * nB * mB + k3 * k3 + k4 * k4 + k4 * k4 + 2 * (k6 + 1) * (l6 + 1)
          + 2 * (k7 + 1) * (l7 + 1) + k4 * k4)) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_eight]
  rfl

/-- the family of the ten region tilings -/
noncomputable def Rfam {u g M : ℝ} (hu : 0 < u) (hg : 0 < g) (n0 k3 k4 nA mA nB mB k6 l6 k7 l7 : ℕ)
    {Sa Sb S6 S7 : Set Plane}
    (R0s : RTiling (Phi (gF u g) '' LY0 u g M) (Mod hu hg) n0)
    (R1 : RTiling (Phi (gF u g) '' LS1 u g M) (Mod hu hg) (k3 * k3))
    (Ra : RTiling Sa (Mod hu hg) (2 * nA * mA)) (Rb : RTiling Sb (Mod hu hg) (2 * nB * mB))
    (R3 : RTiling (Phi (gF u g) '' Sh (lvsh u g M) (Z3 u g 1)) (Mod hu hg) (k3 * k3))
    (R4 : RTiling (Phi (gF u g) '' Sh (lvsh u g M) (Z4 u g 1)) (Mod hu hg) (k4 * k4))
    (R5 : RTiling (Phi (gF u g) '' Sh (lvsh u g M) (Z5 u g 1)) (Mod hu hg) (k4 * k4))
    (R6 : RTiling S6 (Mod hu hg) (2 * (k6 + 1) * (l6 + 1)))
    (R7 : RTiling S7 (Mod hu hg) (2 * (k7 + 1) * (l7 + 1)))
    (R8 : RTiling (Phi (gF u g) '' Sh (lvsh u g M) (Z8 u g 1)) (Mod hu hg) (k4 * k4)) :
    ∀ a : Fin 10, RTiling (regionL u g M Sa Sb S6 S7 a) (Mod hu hg) (lcnt n0 k3 k4 nA mA nB mB k6 l6 k7 l7 a) :=
  fun a => match a with
  | ⟨0, _⟩ => R0s
  | ⟨1, _⟩ => R1
  | ⟨2, _⟩ => Ra
  | ⟨3, _⟩ => Rb
  | ⟨4, _⟩ => R3
  | ⟨5, _⟩ => R4
  | ⟨6, _⟩ => R5
  | ⟨7, _⟩ => R6
  | ⟨8, _⟩ => R7
  | ⟨9, _⟩ => R8
  | ⟨k + 10, h⟩ => absurd h (by omega)

section assemble
variable {u g M : ℝ} (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M)
include hu hg hx

/-- **The layer, real parameters, with the chord.**  A tiling `R₀` of `T_{M−u}` (translated by `(0, B u)`) no tile of which crosses the line `x = c`, `c ≤ A (M − u)`,
and the ten regions of `LayerGGeom` give a tiling `R` of `T_M` by `P M²` tiles, `P = 3f² − u²`, no tile of which crosses the line `x = c`.  The tiles of `R` are the tiles of `R₀`
(moved by `(0, B u)`) and the tiles of the nine regions of the layer, which lie right of the chord `x = A (M − u)`.  The counts are those of the paper:
`k3 = e f`, `k4 = e (f − e)`, `nA = e f`, `mA = x_a`, `nB = b`, `mB = e M`, `k6 + 1 = (f − e) f`, `l6 + 1 = e (f − e)`, `k7 + 1 = e (f − e)`, `l7 + 1 = e²`. -/
theorem layer_real (c : ℝ) (hc : c ≤ lX0 u g M) (n0 k3 k4 nA mA nB mB k6 l6 k7 l7 : ℕ)
    (hn0 : (n0 : ℝ) = cP u g * (M - u) ^ 2)
    (hk30 : 0 < k3) (hk3 : (k3 : ℝ) = ca u g) (hk40 : 0 < k4) (hk4 : (k4 : ℝ) = u * g)
    (hnA : (nA : ℝ) = u * (u + g)) (hmA : (mA : ℝ) = lxa u g M) (hnB : (nB : ℝ) = cb u g)
    (hmB : (mB : ℝ) = u * M)
    (hk6 : (k6 : ℝ) + 1 = g * (u + g)) (hl6 : (l6 : ℝ) + 1 = u * g) (hk7 : (k7 : ℝ) + 1 = u * g)
    (hl7 : (l7 : ℝ) + 1 = u ^ 2)
    (R0 : RTiling (Phi (gF u g) '' DS (cA u g * (M - u)) (cB u g * (M - u)) (cC u g * (M - u))) (Mod hu hg) n0)
    (h0 : SideOK (gF u g) c R0) :
    ∃ (N : ℕ) (R : RTiling (Phi (gF u g) '' LT u g M) (Mod hu hg) N), (N : ℝ) = cP u g * M ^ 2 ∧
      SideOK (gF u g) c R := by
  have hMp := lM_pos hu hg hx
  obtain ⟨Sa, ⟨Ra⟩, ha⟩ := RLa hu hg nA mA hnA hmA
  obtain ⟨Sb, ⟨Rb⟩, hb⟩ := RLb hu hg nB mB hnB hmB
  obtain ⟨S6, ⟨R6⟩, h6⟩ := shift_sub_exists (lvsh u g M) (RT6 hu hg (one_pos : (0 : ℝ) < 1) k6 l6 hk6 hl6)
  obtain ⟨S7, ⟨R7⟩, h7⟩ := shift_sub_exists (lvsh u g M) (RT7 hu hg (one_pos : (0 : ℝ) < 1) k7 l7 hk7 hl7)
  have sub_all : ∀ a : Fin 10, regionL u g M Sa Sb S6 S7 a ⊆ Phi (gF u g) '' Lf u g M a := fun a => match a with
    | ⟨0, _⟩ => subset_rfl
    | ⟨1, _⟩ => subset_rfl
    | ⟨2, _⟩ => ha
    | ⟨3, _⟩ => hb
    | ⟨4, _⟩ => subset_rfl
    | ⟨5, _⟩ => subset_rfl
    | ⟨6, _⟩ => subset_rfl
    | ⟨7, _⟩ => h6
    | ⟨8, _⟩ => h7
    | ⟨9, _⟩ => subset_rfl
    | ⟨k + 10, h⟩ => absurd h (by omega)
  have hS_all : ∀ a b : Fin 10, a ≠ b →
      Disjoint (interior (regionL u g M Sa Sb S6 S7 a)) (interior (regionL u g M Sa Sb S6 S7 b)) := fun a b hab =>
    (disjoint_image' (hfr hu hg) (dL_all hu hg hx a b hab)).mono (interior_mono (sub_all a))
      (interior_mono (sub_all b))
  have hsub_all : ∀ a : Fin 10, regionL u g M Sa Sb S6 S7 a ⊆ (TTri hu hg M hMp).carrier := fun a => by
    rw [carrier_TTri hu hg M hMp]
    exact (sub_all a).trans (Set.image_mono (Lf_sub hu hg hx a))
  have hsumR : ((∑ a, lcnt n0 k3 k4 nA mA nB mB k6 l6 k7 l7 a : ℕ) : ℝ) = cP u g * M ^ 2 := by
    rw [sum_lcnt]
    push_cast
    rw [hn0, hk3, hk4, hnA, hmA, hnB, hmB, hk6, hl6, hk7, hl7]
    simp only [cP, lxa, ca, cb]; ring
  have hvol : ((∑ a, lcnt n0 k3 k4 nA mA nB mB k6 l6 k7 l7 a : ℕ) : ENNReal) * MeasureTheory.volume (Mod hu hg).carrier
      = MeasureTheory.volume (TTri hu hg M hMp).carrier := by
    have hNR : (0 : ℝ) ≤ ((∑ a, lcnt n0 k3 k4 nA mA nB mB k6 l6 k7 l7 a : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [volMod hu hg, vol_TTri hu hg M hMp, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNR, hsumR]
    congr 2
    simp only [cP, cA, cC, ca, cb]; ring
  obtain ⟨D, hM, hT, hreg⟩ := pack_tracked (M := Mod hu hg) (T := TTri hu hg M hMp)
    (regionL u g M Sa Sb S6 S7) _
    (Rfam hu hg n0 k3 k4 nA mA nB mB k6 l6 k7 l7 (shiftR R0 (0, cB u g * u)) (RLs1 hu hg k3 hk30 hk3)
      Ra Rb (shiftR (RT3 hu hg (one_pos : (0 : ℝ) < 1) k3 hk30 hk3) (lvsh u g M))
      (shiftR (RT4 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M))
      (shiftR (RT5 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M)) R6 R7
      (shiftR (RT8 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M)))
    hS_all hsub_all hvol
  have hcongM : D.model.Congruent (Mod hu hg) := by rw [hM]; exact Erdos634.Geometry.Tri.Congruent.refl _
  have hcar : D.target.carrier = Phi (gF u g) '' LT u g M := by
    rw [hT]; exact carrier_TTri hu hg M hMp
  refine ⟨_, RTiling.cast hcar (RegionTiling.remodel (ofCD D) hcongM), hsumR, ?_⟩
  rw [SideOK_cast, SideOK_remodel]
  intro i
  obtain ⟨a, j, hij⟩ := hreg i
  have e : (ofCD D).tile i = (Rfam hu hg n0 k3 k4 nA mA nB mB k6 l6 k7 l7 (shiftR R0 (0, cB u g * u)) (RLs1 hu hg k3 hk30 hk3)
      Ra Rb (shiftR (RT3 hu hg (one_pos : (0 : ℝ) < 1) k3 hk30 hk3) (lvsh u g M))
      (shiftR (RT4 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M))
      (shiftR (RT5 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M)) R6 R7
      (shiftR (RT8 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M)) a).tile j := hij
  by_cases ha0 : a = ⟨0, by omega⟩
  · subst ha0
    have hs := SideOK_shift (hF1 hu hg) R0 (0, cB u g * u) rfl c h0 j
    rw [e]
    exact hs
  · right
    intro y hy
    rw [e] at hy
    have hy' : y ∈ regionL u g M Sa Sb S6 S7 a := by
      rw [← (Rfam hu hg n0 k3 k4 nA mA nB mB k6 l6 k7 l7 (shiftR R0 (0, cB u g * u)) (RLs1 hu hg k3 hk30 hk3)
        Ra Rb (shiftR (RT3 hu hg (one_pos : (0 : ℝ) < 1) k3 hk30 hk3) (lvsh u g M))
        (shiftR (RT4 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M))
        (shiftR (RT5 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M)) R6 R7
        (shiftR (RT8 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M)) a).covers]
      exact Set.mem_iUnion.mpr ⟨j, hy⟩
    obtain ⟨p, hp, rfl⟩ := sub_all a hy'
    rw [skewX_Phi (hF1 hu hg)]
    exact le_trans hc (Lf_right hu hg hx a ha0 p hp)

end assemble

/-! ## No tile of a tiling of `T_M` has points right of the base -/

/-- every tile of a tiling of `T_M` has its first frame coordinate at most `A M`: so it is `SideOK` for every line `x = c` with `A M ≤ c` -/
theorem sideOK_of_le {u g M c : ℝ} (hu : 0 < u) (hg : 0 < g) (hc : cA u g * M ≤ c) {N : ℕ}
    (R : RTiling (Phi (gF u g) '' LT u g M) (Mod hu hg) N) : SideOK (gF u g) c R := by
  intro i
  left
  intro y hy
  have hy' : y ∈ Phi (gF u g) '' LT u g M := by
    rw [← R.covers]; exact Set.mem_iUnion.mpr ⟨i, hy⟩
  obtain ⟨p, hp, rfl⟩ := hy'
  rw [skewX_Phi (hF1 hu hg)]
  exact le_trans hp.1 hc

/-! ## The layer for natural numbers -/

/-- **The layer, natural numbers.**  Member `(u, u + g)`, inner scale `m ≥ 1`, outer scale `m + u`; the condition `x_a ≥ 0` at the outer scale is `f² ≤ 2 m f + e²`.
A tiling of the frame triangle `T_m` (any number of tiles) no tile of which crosses the line `x = c`, `c ≤ A m`, gives a tiling of `T_{m+u}` by `P (m + u)²` tiles
no tile of which crosses the line `x = c`. -/
theorem layer_nat_core (u g m : ℕ) (hu : 0 < u) (hg : 0 < g) (hm : 0 < m)
    (hx : (u + g) ^ 2 ≤ 2 * m * (u + g) + u ^ 2) {N0 : ℕ}
    (R0 : RTiling (Phi (gF (u : ℝ) (g : ℝ)) '' LT (u : ℝ) (g : ℝ) (m : ℝ))
      (Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg)) N0)
    (c : ℝ) (hc : c ≤ cA (u : ℝ) (g : ℝ) * (m : ℝ)) (h0 : SideOK (gF (u : ℝ) (g : ℝ)) c R0) :
    ∃ (N : ℕ) (R : RTiling (Phi (gF (u : ℝ) (g : ℝ)) '' LT (u : ℝ) (g : ℝ) ((m + u : ℕ) : ℝ))
      (Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg)) N),
      N = (3 * (u + g) ^ 2 - u ^ 2) * (m + u) ^ 2 ∧ SideOK (gF (u : ℝ) (g : ℝ)) c R := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hMu : ((m + u : ℕ) : ℝ) - u = m := by push_cast; ring
  have hxR : 0 ≤ lxa (u : ℝ) (g : ℝ) ((m + u : ℕ) : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hx
    push_cast at h
    simp only [lxa]; push_cast; nlinarith [h]
  have hS : Phi (gF (u : ℝ) (g : ℝ)) '' LT (u : ℝ) (g : ℝ) (m : ℝ)
      = Phi (gF (u : ℝ) (g : ℝ)) '' DS (cA (u : ℝ) (g : ℝ) * (((m + u : ℕ) : ℝ) - u))
        (cB (u : ℝ) (g : ℝ) * (((m + u : ℕ) : ℝ) - u)) (cC (u : ℝ) (g : ℝ) * (((m + u : ℕ) : ℝ) - u)) := by
    rw [hMu]; rfl
  have hn0 : (N0 : ℝ) = cP (u : ℝ) (g : ℝ) * (((m + u : ℕ) : ℝ) - u) ^ 2 := by
    rw [hMu]
    exact tcountG hu' hg' (m : ℝ) hm' (RTiling.cast (carrier_TTri hu' hg' (m : ℝ) hm').symm R0)
  obtain ⟨k6, hk6n⟩ : ∃ k6, k6 + 1 = g * (u + g) := ⟨g * (u + g) - 1, Nat.sub_add_cancel (Nat.mul_pos hg (by omega))⟩
  obtain ⟨l6, hl6n⟩ : ∃ l6, l6 + 1 = u * g := ⟨u * g - 1, Nat.sub_add_cancel (Nat.mul_pos hu hg)⟩
  obtain ⟨l7, hl7n⟩ : ∃ l7, l7 + 1 = u ^ 2 := ⟨u ^ 2 - 1, Nat.sub_add_cancel (pow_pos hu 2)⟩
  have hk6 : (k6 : ℝ) + 1 = (g : ℝ) * ((u : ℝ) + g) := by exact_mod_cast hk6n
  have hl6 : (l6 : ℝ) + 1 = (u : ℝ) * g := by exact_mod_cast hl6n
  have hl7 : (l7 : ℝ) + 1 = (u : ℝ) ^ 2 := by exact_mod_cast hl7n
  have h1 : u ^ 2 ≤ (u + g) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmA : (((2 * m * (u + g) + u ^ 2 - (u + g) ^ 2 : ℕ)) : ℝ) = lxa (u : ℝ) (g : ℝ) ((m + u : ℕ) : ℝ) := by
    rw [Nat.cast_sub hx]; simp only [lxa]; push_cast; ring
  have hnB : ((((u + g) ^ 2 - u ^ 2 : ℕ)) : ℝ) = cb (u : ℝ) (g : ℝ) := by
    rw [Nat.cast_sub h1]; simp only [cb]; push_cast; ring
  obtain ⟨N, R, hN, hside⟩ := layer_real (u := (u : ℝ)) (g := (g : ℝ)) (M := ((m + u : ℕ) : ℝ)) hu' hg' hxR c
    (by simp only [lX0]; rw [hMu]; exact hc) N0 (u * (u + g)) (u * g) (u * (u + g))
    (2 * m * (u + g) + u ^ 2 - (u + g) ^ 2) ((u + g) ^ 2 - u ^ 2) (u * (m + u)) k6 l6 l6 l7
    hn0 (Nat.mul_pos hu (by omega)) (by simp [ca]) (Nat.mul_pos hu hg) (by simp)
    (by simp) hmA hnB (by simp) hk6 hl6 hl6 hl7
    (RTiling.cast hS R0) ((SideOK_cast hS R0).mpr h0)
  refine ⟨N, R, ?_, hside⟩
  have h2 : 1 ≤ 3 * (u + g) ^ 2 := by nlinarith [Nat.zero_le g, Nat.zero_le u]
  have h3 : u ^ 2 ≤ 3 * (u + g) ^ 2 := by nlinarith [Nat.zero_le g, Nat.zero_le u]
  have hc' : (N : ℝ) = (((3 * (u + g) ^ 2 - u ^ 2) * (m + u) ^ 2 : ℕ) : ℝ) := by
    rw [hN, Nat.cast_mul, Nat.cast_sub h3]; simp only [cP]; push_cast; ring
  exact_mod_cast hc'

/-- **`prop:layerall` (c)(i)**, in the notation of the paper: let `1 ≤ e < f`, `M ≥ 1`, `2fM ≥ b = f² − e²`.  If `T_M(e, f)` has a tiling (`BetaTilable e f M`, any number of tiles),
then `T_{M+e}(e, f)` has a tiling. -/
theorem layer_c_i (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hM : 1 ≤ M) (hb : f ^ 2 - e ^ 2 ≤ 2 * f * M)
    (h : BetaTilable e f M) : BetaTilable e f (M + e) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = e + g := ⟨f - e, by omega⟩
  have hg : 0 < g := by omega
  have hu : 0 < e := by omega
  have hx : (e + g) ^ 2 ≤ 2 * M * (e + g) + e ^ 2 := by
    have := (Nat.sub_le_iff_le_add).mp hb
    nlinarith [this]
  obtain ⟨N0, ⟨R0⟩⟩ := frameT_of_betaTilable e g M hu hg (by omega) h
  obtain ⟨N, R, -, -⟩ := layer_nat_core e g M hu hg (by omega) hx R0 _ le_rfl
    (sideOK_of_le (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) le_rfl R0)
  exact betaTilable_of_frameT e g (M + e) hu hg (by omega) R

end Erdos634.Draft.LayerG

#print axioms Erdos634.Draft.LayerG.RLs1
#print axioms Erdos634.Draft.LayerG.RLa
#print axioms Erdos634.Draft.LayerG.RLb
#print axioms Erdos634.Draft.LayerG.layer_real
#print axioms Erdos634.Draft.LayerG.layer_nat_core
#print axioms Erdos634.Draft.LayerG.layer_c_i
