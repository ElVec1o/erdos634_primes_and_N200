/-
Draft/ReframeB.lean  In `AllThreshold`.

The converse of `LayerE1Chord.layer_chord` and the equivalence (reframing, part (b)).

    frame_chord        -- in the skew frame: `Sh (0, B₀) (DS (A₀ t) (B₀ t) (C₀ t)) = DS (A₀ F) (B₀ F) (C₀ F) ∩ {x ≤ A₀ t}` for
                       --   `t + 1 = F` (the part of `T_F` on the side of the apex of the chord at the height of `T_1` is the
                       --   translate of `T_t` by `(0, B₀)`), by linear inequalities as in `SignedDecompE1`
    chordTri           -- that part as a triangle: the translate of `DeltaTri f _ (f−1) _` by `Φ_f (0, B₀)`
    chord_restrict     -- a congruent dissection `D` of `DeltaTri f _ f _` with model `MF f` in which the line
                       --   `x = A₀ (f−1)` is crossed by no tile gives `BetaTilable 1 f (f−1)`
                       --   (`ChordCut.restrict_below`, the translation back, `tcount`, `betaTilable_of_TClosed`)
    reframe_b          -- `BetaTilable 1 f (f−1) ↔ ∃ D, … ∧ straddlers D (skewX f) (A₀ (f−1)) = ∅`

`chord_restrict` and `reframe_b` are proved for every `f ≥ 2`; nothing in the
proof needs `f ≥ 3`: the upper part `T_1` is a genuine triangle.  For `f = 2` both sides of `reframe_b` are false
(`SideRun.not_betaTilable_e1_le_half 2 1`; the right side implies the left one), and for `f = 3` both sides are false
(`E1ScaleTwo.not_betaTilable_1_3_2` for the left side), so the equivalence has no instance with true sides at `f = 2, 3`; for
`f ≥ 4` whether the sides hold is an open question.  `chord_restrict` is an implication whose hypothesis (a dissection of `T_f(1,f)`
with the chord uncrossed) is satisfied by no known dissection: the seed tilings of `T_f(1,f)` (`f = 3, 4`) cross
the chord.  The Lean statement is the equivalence itself, not an instance.
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.LayerE1Chord
import Erdos634.Draft.ChordCut

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh RTiling.cast RTiling.castN)

namespace Erdos634.Draft.ReframeB
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.WtoDeltaF (DS DeltaTri carrier_DeltaTri)
open Erdos634.Draft.LayerE1 (TClosed tcount betaTilable_of_TClosed)
open Erdos634.Draft.LayerE1Chord (skewX skewX_Phi skewX_ne_zero layer_chord)
open Erdos634.Draft.UniformThreshold (BetaTilable)
open Erdos634.ChordTraceReal (straddlers)

/-! ## The chord in the frame -/

/-- `0 ≤ c * b ↔ 0 ≤ b` for `c > 0`, used with `a = c * b` -/
theorem nonneg_iff_of_pos {c a b : ℝ} (hc : 0 < c) (h : a = c * b) : 0 ≤ a ↔ 0 ≤ b := by
  rw [h]
  exact mul_nonneg_iff_of_pos_left hc

/-- **The part of `T_F` above the chord at the height of `T_1`.**  With `t + 1 = F`: the points of `DS (A₀ F) (B₀ F) (C₀ F)`
with `x ≤ A₀ t` are the translate by `(0, B₀)` of `DS (A₀ t) (B₀ t) (C₀ t)`. -/
theorem frame_chord (F t : ℝ) (hF : 1 < F) (ht : 0 < t) (htF : t + 1 = F) :
    Sh (0, 2 * F ^ 2 - 1) (DS (F * (F ^ 2 - 1) * t) ((2 * F ^ 2 - 1) * t) ((3 * F ^ 2 - 1) * t)) =
      DS (F * (F ^ 2 - 1) * F) ((2 * F ^ 2 - 1) * F) ((3 * F ^ 2 - 1) * F) ∩
        {p | p.1 ≤ F * (F ^ 2 - 1) * t} := by
  obtain rfl : F = t + 1 := htF.symm
  have hF0 : 0 < t + 1 := by linarith
  have hA : 0 < (t + 1) * ((t + 1) ^ 2 - 1) := mul_pos hF0 (by nlinarith)
  ext p
  simp only [Sh, DS, Set.mem_setOf_eq, Set.mem_inter_iff, Prod.fst_sub, Prod.snd_sub, sub_zero]
  have id2' : (2 * (t + 1) ^ 2 - 1) * t * p.1 + (t + 1) * ((t + 1) ^ 2 - 1) * t *
        (p.2 - (2 * (t + 1) ^ 2 - 1)) - (t + 1) * ((t + 1) ^ 2 - 1) * t * ((2 * (t + 1) ^ 2 - 1) * t)
      = t * ((2 * (t + 1) ^ 2 - 1) * p.1 + (t + 1) * ((t + 1) ^ 2 - 1) * p.2
        - (t + 1) * ((t + 1) ^ 2 - 1) * (2 * (t + 1) ^ 2 - 1) * (t + 1)) := by ring
  have id2 : (2 * (t + 1) ^ 2 - 1) * (t + 1) * p.1 + (t + 1) * ((t + 1) ^ 2 - 1) * (t + 1) * p.2
        - (t + 1) * ((t + 1) ^ 2 - 1) * (t + 1) * ((2 * (t + 1) ^ 2 - 1) * (t + 1))
      = (t + 1) * ((2 * (t + 1) ^ 2 - 1) * p.1 + (t + 1) * ((t + 1) ^ 2 - 1) * p.2
        - (t + 1) * ((t + 1) ^ 2 - 1) * (2 * (t + 1) ^ 2 - 1) * (t + 1)) := by ring
  have id3' : ((3 * (t + 1) ^ 2 - 1) * t - (2 * (t + 1) ^ 2 - 1) * t) * p.1
        - (t + 1) * ((t + 1) ^ 2 - 1) * t * (p.2 - (2 * (t + 1) ^ 2 - 1) - (2 * (t + 1) ^ 2 - 1) * t)
      = t * ((t + 1) ^ 2 * p.1 - (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1))) := by
    ring
  have id3 : ((3 * (t + 1) ^ 2 - 1) * (t + 1) - (2 * (t + 1) ^ 2 - 1) * (t + 1)) * p.1
        - (t + 1) * ((t + 1) ^ 2 - 1) * (t + 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1))
      = (t + 1) * ((t + 1) ^ 2 * p.1 - (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1))) := by
    ring
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hE1 : 0 ≤ (2 * (t + 1) ^ 2 - 1) * p.1 + (t + 1) * ((t + 1) ^ 2 - 1) * p.2
        - (t + 1) * ((t + 1) ^ 2 - 1) * (2 * (t + 1) ^ 2 - 1) * (t + 1) :=
      (nonneg_iff_of_pos ht id2').mp (by linarith)
    have hE2 : 0 ≤ (t + 1) ^ 2 * p.1 - (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1)) :=
      (nonneg_iff_of_pos ht id3').mp (by linarith)
    have g2 := mul_nonneg hF0.le hE1
    have g3 := mul_nonneg hF0.le hE2
    refine ⟨⟨?_, by linarith [g2, id2], by linarith [g3, id3]⟩, h1⟩
    nlinarith [hA]
  · rintro ⟨⟨_, h2, h3⟩, h1⟩
    have hE1 : 0 ≤ (2 * (t + 1) ^ 2 - 1) * p.1 + (t + 1) * ((t + 1) ^ 2 - 1) * p.2
        - (t + 1) * ((t + 1) ^ 2 - 1) * (2 * (t + 1) ^ 2 - 1) * (t + 1) :=
      (nonneg_iff_of_pos hF0 id2).mp (by linarith)
    have hE2 : 0 ≤ (t + 1) ^ 2 * p.1 - (t + 1) * ((t + 1) ^ 2 - 1) * (p.2 - (2 * (t + 1) ^ 2 - 1) * (t + 1)) :=
      (nonneg_iff_of_pos hF0 id3).mp (by linarith)
    have g2 := mul_nonneg ht.le hE1
    have g3 := mul_nonneg ht.le hE2
    exact ⟨h1, by linarith [g2, id2'], by linarith [g3, id3']⟩

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

/-! ## The upper triangle -/

/-- the translation of the plane by `Φ_f (0, B₀)`, `B₀ = 2f² − 1` -/
noncomputable def shiftE (f : ℕ) : Plane ≃ᵢ Plane :=
  IsometryEquiv.addRight (Phi (f : ℝ) (0, 2 * (f : ℝ) ^ 2 - 1))

/-- **The upper part of `T_f` cut by the chord at the height of `T_1`**, as a triangle: the translate of `T_{f−1}` by
`Φ_f (0, B₀)`. -/
noncomputable def chordTri (f : ℕ) (hf : 2 ≤ f) : Erdos634.Geometry.Tri :=
  Erdos634.DissectionMap.mapTri (Erdos634.Ladder.isoAff (shiftE f)) (DeltaTri f hf (f - 1) (by omega))

theorem carrier_chordTri_eq (f : ℕ) (hf : 2 ≤ f) :
    (chordTri f hf).carrier = shiftE f '' (DeltaTri f hf (f - 1) (by omega)).carrier := by
  have h1 := Erdos634.DissectionMap.mapTri_carrier (Erdos634.Ladder.isoAff (shiftE f))
    (DeltaTri f hf (f - 1) (by omega))
  simp only [Erdos634.Ladder.isoAff_coe] at h1
  exact h1

theorem carrier_chordTri (f : ℕ) (hf : 2 ≤ f) :
    (chordTri f hf).carrier = Phi (f : ℝ) '' Sh (0, 2 * (f : ℝ) ^ 2 - 1)
      (DS ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * ((f - 1 : ℕ) : ℝ)) ((2 * (f : ℝ) ^ 2 - 1) * ((f - 1 : ℕ) : ℝ))
        ((3 * (f : ℝ) ^ 2 - 1) * ((f - 1 : ℕ) : ℝ))) := by
  have hc : (⇑(shiftE f) : Plane → Plane) = fun x => x + Phi (f : ℝ) (0, 2 * (f : ℝ) ^ 2 - 1) := by
    funext x
    rfl
  rw [carrier_chordTri_eq, carrier_DeltaTri f hf (f - 1) (by omega), hc]
  exact image_shift (f : ℝ) (0, 2 * (f : ℝ) ^ 2 - 1) _

/-- the upper triangle is the part of the target on the side `{x ≤ A₀ (f−1)}` of the chord -/
theorem carrier_chordTri_inter (f : ℕ) (hf : 2 ≤ f) :
    (chordTri f hf).carrier = (DeltaTri f hf f (by omega)).carrier ∩
      {y | skewX (f : ℝ) y ≤ (f : ℝ) * ((f : ℝ) ^ 2 - 1) * ((f - 1 : ℕ) : ℝ)} := by
  have hF := Erdos634.Draft.WPgramF.hF f hf
  have hmR : ((f - 1 : ℕ) : ℝ) = (f : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hmpos : (0 : ℝ) < ((f - 1 : ℕ) : ℝ) := by rw [hmR]; linarith
  have htF : ((f - 1 : ℕ) : ℝ) + 1 = (f : ℝ) := by rw [hmR]; ring
  rw [carrier_chordTri, carrier_DeltaTri f hf f (by omega), frame_chord (f : ℝ) ((f - 1 : ℕ) : ℝ) hF hmpos htF,
    image_inter_skewX hF]

/-! ## The converse -/

/-- **(b), converse half.**  A congruent dissection `D` of `T_f(1,f)` with model `MF f` in which no tile has points
strictly on both sides of the line `x = A₀ (f−1)` gives a tiling of `T_{f−1}(1,f)`: the tiles on the side of the apex
form a congruent dissection of the translate of `T_{f−1}` (`ChordCut.restrict_below`), which is moved back by the
translation and counted by `tcount`.

Proved for every `f ≥ 2`.  This is an implication; no dissection satisfying its hypothesis is known (see the header). -/
theorem chord_restrict (f : ℕ) (hf : 2 ≤ f) {N : ℕ} (D : CongruentDissection N)
    (hT : D.target = DeltaTri f hf f (by omega))
    (hM : D.model = Erdos634.Draft.WBrickF.MF (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf))
    (h0 : straddlers D.toDissection (skewX (f : ℝ))
      ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * ((f - 1 : ℕ) : ℝ)) = ∅) :
    BetaTilable 1 f (f - 1) := by
  have hF := Erdos634.Draft.WPgramF.hF f hf
  have hm : 0 < f - 1 := by omega
  have hT'c : (chordTri f hf).carrier = D.target.carrier ∩
      {y | skewX (f : ℝ) y ≤ (f : ℝ) * ((f : ℝ) ^ 2 - 1) * ((f - 1 : ℕ) : ℝ)} := by
    rw [hT]
    exact carrier_chordTri_inter f hf
  obtain ⟨N', D', hD't, hD'm⟩ := Erdos634.Draft.ChordCut.restrict_below D (skewX (f : ℝ))
    (skewX_ne_zero hF) _ h0 (chordTri f hf) hT'c
  have R1 : RTiling (chordTri f hf).carrier (Erdos634.Draft.WBrickF.MF (f : ℝ) hF) N' :=
    remodel (RTiling.cast (congrArg Erdos634.Geometry.Tri.carrier hD't) (ofCD D'))
      (by rw [hD'm, hM]; exact Erdos634.Geometry.Tri.Congruent.refl _)
  have R2 := RegionTiling.map R1 (shiftE f).symm
  have hsymm : (shiftE f).symm '' (chordTri f hf).carrier = (DeltaTri f hf (f - 1) hm).carrier := by
    rw [carrier_chordTri_eq, Set.image_image]
    simp [IsometryEquiv.symm_apply_apply]
  have R3 : RTiling (DeltaTri f hf (f - 1) hm).carrier (Erdos634.Draft.WBrickF.MF (f : ℝ) hF) N' :=
    RTiling.cast hsymm R2
  have hN := tcount f hf (f - 1) hm R3
  exact betaTilable_of_TClosed f hf (f - 1) hm
    ⟨RTiling.castN hN (RTiling.cast (carrier_DeltaTri f hf (f - 1) hm) R3)⟩

/-- **Proposition `prop:reframe` (b).**  For `f ≥ 2`: the base-β target `T_{f−1}(1,f)` has a tiling if and only if
`T_f(1,f)` has a congruent dissection (target `DeltaTri f _ f _`, model `MF f`) in which no tile has points strictly on both
sides of the chord `x = A₀ (f−1)` parallel to the base at the height of `T_1`.

NO INSTANCE WITH TRUE SIDES IS KNOWN: for `f = 2, 3` both sides are false, for `f ≥ 4` they are the open question.  What is
proved is the equivalence (both directions: `LayerE1Chord.layer_chord`, `chord_restrict`). -/
theorem reframe_b (f : ℕ) (hf : 2 ≤ f) :
    BetaTilable 1 f (f - 1) ↔ ∃ (N : ℕ) (D : CongruentDissection N), D.target = DeltaTri f hf f (by omega) ∧
      D.model = Erdos634.Draft.WBrickF.MF (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf) ∧
      straddlers D.toDissection (skewX (f : ℝ)) ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * ((f - 1 : ℕ) : ℝ)) = ∅ :=
  ⟨layer_chord f hf, fun ⟨_, D, hT, hM, h0⟩ => chord_restrict f hf D hT hM h0⟩

end Erdos634.Draft.ReframeB

#print axioms Erdos634.Draft.ReframeB.frame_chord
#print axioms Erdos634.Draft.ReframeB.carrier_chordTri_inter
#print axioms Erdos634.Draft.ReframeB.chord_restrict
#print axioms Erdos634.Draft.ReframeB.reframe_b
