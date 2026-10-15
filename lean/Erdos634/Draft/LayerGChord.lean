/-
Draft/LayerGChord.lean  In `AllThreshold`.

PAPER.  `prop:layerall` (c): "(ii) If `2fM ≥ b` and `k ≥ 1`, then `T_M(e, f)` has a tiling if and only if some tiling of `T_{M+ke}(e, f)` has the chord parallel to the base at the height `keH₁` as a wall.
(iii) For the members `(f−1, f)` the condition of (b) is `M ≥ f`: for these members the layer exists only from `M = f` on, so it relates no two scales below `f`."
(A *wall* of a tiling is a segment that contains no interior point of a tile.)

WHAT IS PROVED HERE (the layer is `Draft/LayerG.lean`; frame `Φ_F`, `F = f/e` of `CollarG`, `u = e`, `g = f − e`, `f = u + g`; `T_M = DS (A M) (B M) (C M)`; the chord at the height `keH₁` of `T_{M+ke}` is the line `x = A M`):
* `stack_frame`: **the layers stacked.**  A tiling of `T_{M₀}` and `f² ≤ 2 M₀ f + e²` (that is `2fM₀ ≥ b`, which is `x_a ≥ 0` at the scale `M₀ + e`, hence at every higher scale) give, for every `k`, a tiling of `T_{M₀ + ke}` no tile of which crosses the line `x = A M₀`
  (`k` applications of `LayerG.layer_nat_core`, the chord staying below the chords of the later layers);
* `frame_chord_T`, `chordTriT`, `chord_restrict_T`: the part of `T_{M'}` left of the line `x = A M` is the translate of `T_M` by `(0, B (M' − M))`; a congruent dissection of `T_{M'}` in which no tile crosses the line gives a tiling of `T_M`
  (`ChordCut.restrict_below`);
* `layer_c_ii`: **`prop:layerall` (c)(ii)**: for `2fM ≥ b` (`(e+g)^2 - e^2 ≤ 2 (e+g) M`), `k ≥ 1`: `BetaTilable e (e+g) M` iff there is a congruent dissection `D` of the frame triangle `T_{M+ke}` (target `TTri`, model `Mod`, any number of tiles) in which no tile has points strictly
  on both sides of the line `x = A M` (`straddlers = ∅`);
* `layer_c_ii_wall`: the same with the chord as a segment: the open segment from `Φ_F (A M, B ke)` to `Φ_F (A M, B ke + C M)` (the chord `x = A M` of `T_{M+ke}`) contains no interior point of a tile of `D`;
* `layer_c_iii`: for `e = f − 1`: the condition of (b) at the scale `M`, `f² + 2ef ≤ 2fM + e²` (`x_a ≥ 0`, that is `2f(M − e) ≥ b`), holds iff `f ≤ M`; the condition `b ≤ 2fM` of (c)(i), (c)(ii) holds iff `1 ≤ M`, and then `M + ke ≥ f` for every `k ≥ 1`.

No sorry, no native_decide.
-/
import Erdos634.Draft.LayerG

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.LayerG
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.WtoDeltaF (DS)
open Erdos634.Draft.UniformThreshold (BetaTilable)
open Erdos634.Draft.CollarG (gF hF1 hfr hvpos hapos hbpos cApos cBpos hPpos Mod ca cb cA cB cC)
open Erdos634.Draft.LayerE1Chord (skewX skewX_Phi skewX_ne_zero straddlers_empty_of_sides)
open Erdos634.ChordTraceReal (straddlers)

/-! ## The layers stacked -/

/-- **The layers stacked.**  Member `(u, u + g)`, `M₀ ≥ 1`, `f² ≤ 2 M₀ f + e²`.  A tiling of `T_{M₀}` gives, for every `k`, a tiling of `T_{M₀ + k u}` no tile of which crosses the line `x = A M₀`
(the chord at the height `k e H₁` of `T_{M₀ + ke}`). -/
theorem stack_frame (u g M0 : ℕ) (hu : 0 < u) (hg : 0 < g) (hM0 : 0 < M0)
    (hx : (u + g) ^ 2 ≤ 2 * M0 * (u + g) + u ^ 2) {N0 : ℕ}
    (R0 : RTiling (Phi (gF (u : ℝ) (g : ℝ)) '' LT (u : ℝ) (g : ℝ) (M0 : ℝ))
      (Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg)) N0) :
    ∀ k : ℕ, ∃ (N : ℕ) (R : RTiling (Phi (gF (u : ℝ) (g : ℝ)) '' LT (u : ℝ) (g : ℝ) ((M0 + k * u : ℕ) : ℝ))
      (Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg)) N),
      SideOK (gF (u : ℝ) (g : ℝ)) (cA (u : ℝ) (g : ℝ) * (M0 : ℝ)) R := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  intro k
  induction k with
  | zero =>
    have hS : Phi (gF (u : ℝ) (g : ℝ)) '' LT (u : ℝ) (g : ℝ) (M0 : ℝ)
        = Phi (gF (u : ℝ) (g : ℝ)) '' LT (u : ℝ) (g : ℝ) ((M0 + 0 * u : ℕ) : ℝ) := by simp
    exact ⟨N0, RTiling.cast hS R0, (SideOK_cast hS R0).mpr (sideOK_of_le hu' hg' le_rfl R0)⟩
  | succ k ih =>
    obtain ⟨N, R, hR⟩ := ih
    have hmpos : 0 < M0 + k * u := lt_of_lt_of_le hM0 (Nat.le_add_right _ _)
    have hxk : (u + g) ^ 2 ≤ 2 * (M0 + k * u) * (u + g) + u ^ 2 :=
      le_trans hx (by nlinarith [Nat.zero_le (k * u * (u + g))])
    have hc : cA (u : ℝ) (g : ℝ) * (M0 : ℝ) ≤ cA (u : ℝ) (g : ℝ) * ((M0 + k * u : ℕ) : ℝ) := by
      refine mul_le_mul_of_nonneg_left ?_ (cApos hu' hg').le
      push_cast
      have : (0 : ℝ) ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg k) hu'.le
      linarith
    obtain ⟨N', R', -, hs'⟩ := layer_nat_core u g (M0 + k * u) hu hg hmpos hxk R _ hc hR
    have hnat : M0 + k * u + u = M0 + (k + 1) * u := by ring
    have hS : Phi (gF (u : ℝ) (g : ℝ)) '' LT (u : ℝ) (g : ℝ) ((M0 + k * u + u : ℕ) : ℝ)
        = Phi (gF (u : ℝ) (g : ℝ)) '' LT (u : ℝ) (g : ℝ) ((M0 + (k + 1) * u : ℕ) : ℝ) := by rw [hnat]
    exact ⟨N', RTiling.cast hS R', (SideOK_cast hS R').mpr hs'⟩

/-- **The stacked layers as a congruent dissection with the chord uncrossed.**  Member `(u, u + g)`, `M ≥ 1`, `f² ≤ 2 M f + e²`: if `T_M` has a tiling, then for every `k` the frame triangle `T_{M + k u}` has a
congruent dissection (model `Mod`) in which no tile has points strictly on both sides of the line `x = A M`. -/
theorem stack_dissection (u g M k : ℕ) (hu : 0 < u) (hg : 0 < g) (hM : 0 < M)
    (hx : (u + g) ^ 2 ≤ 2 * M * (u + g) + u ^ 2) (h : BetaTilable u (u + g) M) :
    ∃ (N : ℕ) (D : CongruentDissection N),
      D.target = TTri (u := (u : ℝ)) (g := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg)
        ((M + k * u : ℕ) : ℝ) (Nat.cast_pos.mpr (lt_of_lt_of_le hM (Nat.le_add_right _ _))) ∧
      D.model = Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) ∧
      straddlers D.toDissection (skewX (gF (u : ℝ) (g : ℝ))) (cA (u : ℝ) (g : ℝ) * (M : ℝ)) = ∅ := by
  obtain ⟨N0, ⟨R0⟩⟩ := frameT_of_betaTilable u g M hu hg hM h
  obtain ⟨N, R, hR⟩ := stack_frame u g M hu hg hM hx R0 k
  have hpos : (0 : ℝ) < ((M + k * u : ℕ) : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hM (Nat.le_add_right _ _))
  refine ⟨N, toCD (T := TTri (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) ((M + k * u : ℕ) : ℝ) hpos)
    (RTiling.cast (carrier_TTri (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) _ hpos).symm R), rfl, rfl, ?_⟩
  exact straddlers_empty_of_SideOK _ ((SideOK_cast _ R).mpr hR)

/-! ## The chord in the frame -/

/-- the plane form: `Φ_F '' (S ∩ {x ≤ c}) = Φ_F '' S ∩ {skewX ≤ c}` -/
theorem image_inter_skewX {F : ℝ} (hF : 1 < F) (S : Set (ℝ × ℝ)) (c : ℝ) :
    Phi F '' (S ∩ {p | p.1 ≤ c}) = Phi F '' S ∩ {y | skewX F y ≤ c} := by
  ext y
  constructor
  · rintro ⟨p, ⟨hp, hpc⟩, rfl⟩
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    show skewX F (Phi F p) ≤ c
    rw [skewX_Phi hF]
    exact hpc
  · rintro ⟨⟨p, hp, rfl⟩, hy⟩
    refine ⟨p, ⟨hp, ?_⟩, rfl⟩
    have h : skewX F (Phi F p) ≤ c := hy
    rw [skewX_Phi hF] at h
    exact h

section chord
variable {u g : ℝ} (hu : 0 < u) (hg : 0 < g)
include hu hg

/-- **The part of `T_{M'}` left of the line `x = A M` is the translate of `T_M` by `(0, B (M' − M))`.** -/
theorem frame_chord_T {M M' : ℝ} (hM : 0 < M) (hMM : M ≤ M') :
    Sh (0, cB u g * (M' - M)) (LT u g M) = LT u g M' ∩ {p | p.1 ≤ cA u g * M} := by
  have hA := cApos hu hg
  have hM' : 0 < M' := lt_of_lt_of_le hM hMM
  have kA : cA u g * M ≤ cA u g * M' := mul_le_mul_of_nonneg_left hMM hA.le
  ext p
  simp only [Sh, LT, DS, Set.mem_setOf_eq, Set.mem_inter_iff, Prod.fst_sub, Prod.snd_sub, sub_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have k2 : M * (cA u g * cB u g * M') ≤ M * (cB u g * p.1 + cA u g * p.2) := by nlinarith [h2]
    have k3 : M * (cA u g * (p.2 - cB u g * M')) ≤ M * ((cC u g - cB u g) * p.1) := by nlinarith [h3]
    have l2 := le_of_mul_le_mul_left k2 hM
    have l3 := le_of_mul_le_mul_left k3 hM
    have m2 := mul_le_mul_of_nonneg_left l2 hM'.le
    have m3 := mul_le_mul_of_nonneg_left l3 hM'.le
    exact ⟨⟨by linarith, by nlinarith [m2], by nlinarith [m3]⟩, h1⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    have k2 : M' * (cA u g * cB u g * M') ≤ M' * (cB u g * p.1 + cA u g * p.2) := by nlinarith [h2]
    have k3 : M' * (cA u g * (p.2 - cB u g * M')) ≤ M' * ((cC u g - cB u g) * p.1) := by nlinarith [h3]
    have l2 := le_of_mul_le_mul_left k2 hM'
    have l3 := le_of_mul_le_mul_left k3 hM'
    have m2 := mul_le_mul_of_nonneg_left l2 hM.le
    have m3 := mul_le_mul_of_nonneg_left l3 hM.le
    exact ⟨h4, by nlinarith [m2], by nlinarith [m3]⟩

/-- **The part of `T_{M'}` left of the chord, as a triangle**: the translate of `T_M` by `Φ_F (0, B (M' − M))`. -/
noncomputable def chordTriT {M M' : ℝ} (hM : 0 < M) : Erdos634.Geometry.Tri :=
  Erdos634.DissectionMap.mapTri
    (Erdos634.Ladder.isoAff (IsometryEquiv.addRight (Phi (gF u g) (0, cB u g * (M' - M))))) (TTri hu hg M hM)

theorem carrier_chordTriT_eq {M M' : ℝ} (hM : 0 < M) :
    (chordTriT hu hg (M' := M') hM).carrier
      = (IsometryEquiv.addRight (Phi (gF u g) (0, cB u g * (M' - M)))) '' (TTri hu hg M hM).carrier := by
  have h1 := Erdos634.DissectionMap.mapTri_carrier
    (Erdos634.Ladder.isoAff (IsometryEquiv.addRight (Phi (gF u g) (0, cB u g * (M' - M))))) (TTri hu hg M hM)
  simp only [Erdos634.Ladder.isoAff_coe] at h1
  exact h1

theorem carrier_chordTriT {M M' : ℝ} (hM : 0 < M) :
    (chordTriT hu hg (M' := M') hM).carrier = Phi (gF u g) '' Sh (0, cB u g * (M' - M)) (LT u g M) := by
  have hc : (⇑(IsometryEquiv.addRight (Phi (gF u g) (0, cB u g * (M' - M)))) : Plane → Plane)
      = fun x => x + Phi (gF u g) (0, cB u g * (M' - M)) := by
    funext x
    rfl
  rw [carrier_chordTriT_eq hu hg hM, carrier_TTri hu hg M hM, hc]
  exact image_shift (gF u g) (0, cB u g * (M' - M)) _

theorem carrier_chordTriT_inter {M M' : ℝ} (hM : 0 < M) (hMM : M ≤ M') (hM' : 0 < M') :
    (chordTriT hu hg (M' := M') hM).carrier
      = (TTri hu hg M' hM').carrier ∩ {y | skewX (gF u g) y ≤ cA u g * M} := by
  rw [carrier_chordTriT hu hg hM, carrier_TTri hu hg M' hM', frame_chord_T hu hg hM hMM,
    image_inter_skewX (hF1 hu hg)]

/-- **A congruent dissection of `T_{M'}` in which no tile crosses the line `x = A M` gives a tiling of `T_M`.** -/
theorem chord_restrict_T {M M' : ℝ} (hM : 0 < M) (hMM : M ≤ M') (hM' : 0 < M') {N : ℕ}
    (D : CongruentDissection N) (hT : D.target = TTri hu hg M' hM') (hMo : D.model = Mod hu hg)
    (h0 : straddlers D.toDissection (skewX (gF u g)) (cA u g * M) = ∅) :
    ∃ N' : ℕ, Nonempty (RTiling (TTri hu hg M hM).carrier (Mod hu hg) N') := by
  have hT'c : (chordTriT hu hg (M' := M') hM).carrier
      = D.target.carrier ∩ {y | skewX (gF u g) y ≤ cA u g * M} := by
    rw [hT]
    exact carrier_chordTriT_inter hu hg hM hMM hM'
  obtain ⟨N', D', hD't, hD'm⟩ := Erdos634.Draft.ChordCut.restrict_below D (skewX (gF u g))
    (skewX_ne_zero (hF1 hu hg)) _ h0 (chordTriT hu hg (M' := M') hM) hT'c
  have R1 : RTiling (chordTriT hu hg (M' := M') hM).carrier (Mod hu hg) N' :=
    remodel (RTiling.cast (congrArg Erdos634.Geometry.Tri.carrier hD't) (ofCD D'))
      (by rw [hD'm, hMo]; exact Erdos634.Geometry.Tri.Congruent.refl _)
  have R2 := RegionTiling.map R1 (IsometryEquiv.addRight (Phi (gF u g) (0, cB u g * (M' - M)))).symm
  have hsymm : (IsometryEquiv.addRight (Phi (gF u g) (0, cB u g * (M' - M)))).symm ''
      (chordTriT hu hg (M' := M') hM).carrier = (TTri hu hg M hM).carrier := by
    rw [carrier_chordTriT_eq hu hg hM, Set.image_image]
    simp [IsometryEquiv.symm_apply_apply]
  exact ⟨N', ⟨RTiling.cast hsymm R2⟩⟩

end chord

/-! ## `prop:layerall` (c)(ii) -/

/-- **`prop:layerall` (c)(ii)**, member `(e, f)`, `f = e + g`: let `M ≥ 1`, `k ≥ 1`, `2fM ≥ b = f² − e²` (written `f² ≤ 2 M f + e²`).  Then `T_M(e, f)` has a tiling if and only if the frame triangle `T_{M+ke}(e, f)` has a
congruent dissection (model `Mod`, any number of tiles) in which no tile has points strictly on both sides of the chord `x = A M`, the chord parallel to the base at the height `k e H₁`. -/
theorem layer_c_ii (e g M k : ℕ) (he : 0 < e) (hg : 0 < g) (hM : 0 < M) (hk : 1 ≤ k)
    (hb : (e + g) ^ 2 - e ^ 2 ≤ 2 * (e + g) * M) :
    BetaTilable e (e + g) M ↔
      ∃ (N : ℕ) (D : CongruentDissection N),
        D.target = TTri (u := (e : ℝ)) (g := (g : ℝ)) (Nat.cast_pos.mpr he) (Nat.cast_pos.mpr hg)
          ((M + k * e : ℕ) : ℝ) (Nat.cast_pos.mpr (lt_of_lt_of_le hM (Nat.le_add_right _ _))) ∧
        D.model = Mod (u := (e : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr he) (Nat.cast_pos.mpr hg) ∧
        straddlers D.toDissection (skewX (gF (e : ℝ) (g : ℝ))) (cA (e : ℝ) (g : ℝ) * (M : ℝ)) = ∅ := by
  have hx : (e + g) ^ 2 ≤ 2 * M * (e + g) + e ^ 2 := by
    have := (Nat.sub_le_iff_le_add).mp hb
    nlinarith [this]
  constructor
  · intro h
    obtain ⟨N, D, hT, hMo, h0⟩ := stack_dissection e g M k he hg hM hx h
    exact ⟨N, D, hT, hMo, h0⟩
  · rintro ⟨N, D, hT, hMo, h0⟩
    have he' : (0 : ℝ) < e := Nat.cast_pos.mpr he
    have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
    have hM' : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
    have hMM : (M : ℝ) ≤ ((M + k * e : ℕ) : ℝ) := by
      have : M ≤ M + k * e := Nat.le_add_right _ _
      exact_mod_cast this
    obtain ⟨N', ⟨R⟩⟩ := chord_restrict_T he' hg' hM' hMM (Nat.cast_pos.mpr (lt_of_lt_of_le hM (Nat.le_add_right _ _))) D hT hMo h0
    exact betaTilable_of_frameT e g M he hg hM (RTiling.cast (carrier_TTri he' hg' (M : ℝ) hM') R)

/-! ## The chord as a segment: the paper's wording -/

section wall
variable {u g : ℝ} (hu : 0 < u) (hg : 0 < g)
include hu hg

/-- the end of the chord on the lower side of `T_{M'}`: `Φ_F (A M, B (M' − M))` -/
noncomputable def chordPT (u g M M' : ℝ) : Plane := Phi (gF u g) (cA u g * M, cB u g * (M' - M))

/-- the end of the chord on the upper side of `T_{M'}`: `Φ_F (A M, B (M' − M) + C M)` -/
noncomputable def chordQT (u g M M' : ℝ) : Plane := Phi (gF u g) (cA u g * M, cB u g * (M' - M) + cC u g * M)

theorem skewX_chordPT {M M' : ℝ} : skewX (gF u g) (chordPT u g M M') = cA u g * M :=
  skewX_Phi (hF1 hu hg) _

theorem skewX_chordQT {M M' : ℝ} : skewX (gF u g) (chordQT u g M M') = cA u g * M :=
  skewX_Phi (hF1 hu hg) _

theorem skewX_openSegment {M M' : ℝ} {y : Plane} (hy : y ∈ openSegment ℝ (chordPT u g M M') (chordQT u g M M')) :
    skewX (gF u g) y = cA u g * M := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  rw [map_add, map_smul, map_smul, skewX_chordPT hu hg, skewX_chordQT hu hg, smul_eq_mul, smul_eq_mul, ← add_mul,
    hab, one_mul]

/-- **The chord is the intersection of the target with the line.**  Every point of `T_{M'}` on the line `x = A M` lies on the segment `[chordPT, chordQT]`. -/
theorem chord_hline_T {M M' : ℝ} (hM : 0 < M) (hM' : 0 < M') :
    ∀ y ∈ (TTri hu hg M' hM').carrier, skewX (gF u g) y = cA u g * M →
      y ∈ segment ℝ (chordPT u g M M') (chordQT u g M M') := by
  have hA := cApos hu hg
  have hB := cBpos hu hg
  have hC : 0 < cC u g := lcC_pos hu hg
  intro y hy hl
  rw [carrier_TTri hu hg M' hM'] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  rw [skewX_Phi (hF1 hu hg)] at hl
  obtain ⟨h1, h2, h3⟩ := hp
  have hCM : 0 < cC u g * M := mul_pos hC hM
  set lo := cB u g * (M' - M) with hlo
  -- `lo ≤ p.2 ≤ lo + C M` on the line `p.1 = A M`
  have hlow : lo ≤ p.2 := by
    rw [hl] at h2
    have k : M' * (cA u g * cB u g * M') ≤ M' * (cB u g * (cA u g * M) + cA u g * p.2) := by nlinarith [h2]
    have k' := le_of_mul_le_mul_left k hM'
    have : cA u g * lo ≤ cA u g * p.2 := by simp only [hlo]; nlinarith [k']
    exact le_of_mul_le_mul_left this hA
  have hup : p.2 ≤ lo + cC u g * M := by
    rw [hl] at h3
    have k : M' * (cA u g * (p.2 - cB u g * M')) ≤ M' * ((cC u g - cB u g) * (cA u g * M)) := by nlinarith [h3]
    have k' := le_of_mul_le_mul_left k hM'
    have : cA u g * p.2 ≤ cA u g * (lo + cC u g * M) := by simp only [hlo]; nlinarith [k']
    exact le_of_mul_le_mul_left this hA
  set t := (p.2 - lo) / (cC u g * M) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hCM.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hCM]; linarith
  have hseg : p ∈ segment ℝ (cA u g * M, lo) (cA u g * M, lo + cC u g * M) := by
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [hl]; ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have hCM' : cC u g * M ≠ 0 := hCM.ne'
      rw [ht]
      field_simp
      ring
  have himg := (image_segment ℝ (Erdos634.Draft.WBrickF.PhiL (gF u g)).toAffineMap (cA u g * M, lo)
    (cA u g * M, lo + cC u g * M))
  have : Phi (gF u g) p ∈ (Erdos634.Draft.WBrickF.PhiL (gF u g)).toAffineMap '' segment ℝ
      (cA u g * M, lo) (cA u g * M, lo + cC u g * M) := ⟨p, hseg, rfl⟩
  rw [himg] at this
  exact this

end wall

/-- **`prop:layerall` (c)(ii), in the paper's wording**: `T_M(e, f)` has a tiling if and only if the frame triangle `T_{M+ke}(e, f)` has a congruent dissection in which the chord `x = A M`
(the chord parallel to the base at the height `k e H₁`, from `Φ_F (A M, B k e)` to `Φ_F (A M, B k e + C M)`) contains no interior point of a tile (the open segment is a wall). -/
theorem layer_c_ii_wall (e g M k : ℕ) (he : 0 < e) (hg : 0 < g) (hM : 0 < M) (hk : 1 ≤ k)
    (hb : (e + g) ^ 2 - e ^ 2 ≤ 2 * (e + g) * M) :
    BetaTilable e (e + g) M ↔
      ∃ (N : ℕ) (D : CongruentDissection N),
        D.target = TTri (u := (e : ℝ)) (g := (g : ℝ)) (Nat.cast_pos.mpr he) (Nat.cast_pos.mpr hg)
          ((M + k * e : ℕ) : ℝ) (Nat.cast_pos.mpr (lt_of_lt_of_le hM (Nat.le_add_right _ _))) ∧
        D.model = Mod (u := (e : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr he) (Nat.cast_pos.mpr hg) ∧
        ∀ y ∈ openSegment ℝ (chordPT (e : ℝ) (g : ℝ) (M : ℝ) ((M + k * e : ℕ) : ℝ))
            (chordQT (e : ℝ) (g : ℝ) (M : ℝ) ((M + k * e : ℕ) : ℝ)), ∀ i, y ∉ interior (D.tile i).carrier := by
  have he' : (0 : ℝ) < e := Nat.cast_pos.mpr he
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hM' : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hMk : (0 : ℝ) < ((M + k * e : ℕ) : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hM (Nat.le_add_right _ _))
  rw [layer_c_ii e g M k he hg hM hk hb]
  constructor
  · rintro ⟨N, D, hT, hMo, h0⟩
    refine ⟨N, D, hT, hMo, fun y hy i hyi => ?_⟩
    have hl := skewX_openSegment he' hg' hy
    exact Erdos634.Draft.ChordCut.not_straddles_of_empty D.toDissection _ _ h0 i
      (Erdos634.ChordTraceReal.interior_on_line_straddles (D.tile i) (skewX (gF (e : ℝ) (g : ℝ)))
        (skewX_ne_zero (hF1 he' hg')) _ hyi hl)
  · rintro ⟨N, D, hT, hMo, hw⟩
    refine ⟨N, D, hT, hMo, ?_⟩
    exact Erdos634.Draft.ChordCut.straddlers_eq_empty_of_wall D.toDissection (skewX (gF (e : ℝ) (g : ℝ))) _
      (P := chordPT (e : ℝ) (g : ℝ) (M : ℝ) ((M + k * e : ℕ) : ℝ))
      (Q := chordQT (e : ℝ) (g : ℝ) (M : ℝ) ((M + k * e : ℕ) : ℝ))
      (fun y hy hl => chord_hline_T he' hg' hM' hMk y (by rw [← hT]; exact hy) hl) hw

/-! ## `prop:layerall` (c)(iii): the members `(f − 1, f)` -/

/-- **`prop:layerall` (c)(iii).**  For `e = f − 1` (`f ≥ 2`, `b = 2f − 1`): the condition of (b) at the scale `M`, `x_a ≥ 0`, that is `f² + 2ef ≤ 2fM + e²` (`2f(M − e) ≥ b`), holds iff `f ≤ M`; the condition
`f² − e² ≤ 2fM` of (c)(i) and (c)(ii) holds iff `1 ≤ M`; and then every scale `M + ke`, `k ≥ 1`, is at least `f`.  So for these members the layer of (b) relates scales `M − e` and `M` only for `M ≥ f`, and (c)(i), (c)(ii)
relate `M ≥ 1` to scales `M + ke ≥ f`: no two scales below `f` are related. -/
theorem layer_c_iii (f M : ℕ) (hf : 2 ≤ f) :
    (f ^ 2 + 2 * (f - 1) * f ≤ 2 * f * M + (f - 1) ^ 2 ↔ f ≤ M) ∧
    (f ^ 2 - (f - 1) ^ 2 ≤ 2 * f * M ↔ 1 ≤ M) ∧
    (1 ≤ M → ∀ k, 1 ≤ k → f ≤ M + k * (f - 1)) := by
  obtain ⟨e, rfl⟩ : ∃ e, f = e + 1 := ⟨f - 1, by omega⟩
  have e1 : e + 1 - 1 = e := by omega
  rw [e1]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, fun hM k hk => ?_⟩
  · -- `(e+1)² + 2e(e+1) ≤ 2(e+1)M + e²` forces `M ≥ e + 1`
    by_contra hc
    have hM : M ≤ e := by omega
    nlinarith [Nat.mul_le_mul_left (2 * (e + 1)) hM]
  · nlinarith [Nat.mul_le_mul_left (2 * (e + 1)) h]
  · by_contra hc
    have hM : M = 0 := by omega
    subst hM
    have : (e + 1) ^ 2 - e ^ 2 = 2 * e + 1 := by
      have : e ^ 2 ≤ (e + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      zify [this]; ring
    omega
  · have h1 : e ^ 2 ≤ (e + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have : (e + 1) ^ 2 - e ^ 2 = 2 * e + 1 := by zify [h1]; ring
    rw [this]
    nlinarith [Nat.mul_le_mul_left (2 * (e + 1)) h]
  · nlinarith [Nat.mul_le_mul_right e hk]

end Erdos634.Draft.LayerG

#print axioms Erdos634.Draft.LayerG.stack_frame
#print axioms Erdos634.Draft.LayerG.stack_dissection
#print axioms Erdos634.Draft.LayerG.frame_chord_T
#print axioms Erdos634.Draft.LayerG.chord_restrict_T
#print axioms Erdos634.Draft.LayerG.layer_c_ii
#print axioms Erdos634.Draft.LayerG.chord_hline_T
#print axioms Erdos634.Draft.LayerG.layer_c_ii_wall
#print axioms Erdos634.Draft.LayerG.layer_c_iii
