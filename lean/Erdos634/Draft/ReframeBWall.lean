/-
Draft/ReframeBWall.lean  In `AllThreshold`.

Remark-level corollary of `ReframeB.reframe_b`: the paper's wording.  A *wall* is a segment that contains no interior point of
a tile.  The chord of `T_f(1,f)` parallel to the base at the height of `T_1` is the segment `[chordP f, chordQ f]` (its ends
`Φ_f (A₀ (f−1), B₀)` and `Φ_f (A₀ (f−1), B₀ f + f² (f−1))` are on the two legs).  By `ChordCut.straddlers_eq_empty_of_wall` and
`interior_on_line_straddles`, "the open chord contains no interior point of a tile" is the same as "no tile crosses the line":

    reframe_b_wall   -- `BetaTilable 1 f (f−1) ↔ ∃ D (target DeltaTri f _ f _, model MF f), the open chord is a wall of D`

As for `reframe_b`: both sides are false for `f = 2, 3` and open for `f ≥ 4`; no instance with true sides is known.
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.ReframeB

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh)

namespace Erdos634.Draft.ReframeBWall
open Erdos634.Draft.WFrameF
open Erdos634.Draft.WBrickF (PhiL)
open Erdos634.Draft.WtoDeltaF (DS DeltaTri carrier_DeltaTri)
open Erdos634.Draft.LayerE1Chord (skewX skewX_Phi skewX_ne_zero)
open Erdos634.Draft.UniformThreshold (BetaTilable)
open Erdos634.ChordTraceReal (straddlers)

/-- the abscissa of the chord: `A₀ (f−1)`, `A₀ = f (f²−1)` -/
noncomputable def chordX (f : ℕ) : ℝ := (f : ℝ) * ((f : ℝ) ^ 2 - 1) * ((f - 1 : ℕ) : ℝ)

/-- the end of the chord on the leg `AB` -/
noncomputable def chordP (f : ℕ) : Plane := Phi (f : ℝ) (chordX f, 2 * (f : ℝ) ^ 2 - 1)

/-- the end of the chord on the leg `AC` -/
noncomputable def chordQ (f : ℕ) : Plane :=
  Phi (f : ℝ) (chordX f, (2 * (f : ℝ) ^ 2 - 1) * (f : ℝ) + (f : ℝ) ^ 2 * ((f - 1 : ℕ) : ℝ))

theorem skewX_chordP (f : ℕ) (hf : 2 ≤ f) : skewX (f : ℝ) (chordP f) = chordX f :=
  skewX_Phi (Erdos634.Draft.WPgramF.hF f hf) _

theorem skewX_chordQ (f : ℕ) (hf : 2 ≤ f) : skewX (f : ℝ) (chordQ f) = chordX f :=
  skewX_Phi (Erdos634.Draft.WPgramF.hF f hf) _

/-- every point of the open chord lies on the line `x = A₀ (f−1)` -/
theorem skewX_openSegment (f : ℕ) (hf : 2 ≤ f) {y : Plane} (hy : y ∈ openSegment ℝ (chordP f) (chordQ f)) :
    skewX (f : ℝ) y = chordX f := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  rw [map_add, map_smul, map_smul, skewX_chordP f hf, skewX_chordQ f hf, smul_eq_mul, smul_eq_mul, ← add_mul,
    hab, one_mul]

/-- **The chord is the intersection of the target with the line.**  Every point of `T_f` on the line `x = A₀ (f−1)` lies
on the segment `[chordP f, chordQ f]`. -/
theorem chord_hline (f : ℕ) (hf : 2 ≤ f) :
    ∀ y ∈ (DeltaTri f hf f (by omega)).carrier, skewX (f : ℝ) y = chordX f →
      y ∈ segment ℝ (chordP f) (chordQ f) := by
  have hF := Erdos634.Draft.WPgramF.hF f hf
  have hF0 : (0 : ℝ) < f := by linarith
  have hmR : ((f - 1 : ℕ) : ℝ) = (f : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  intro y hy hx
  rw [carrier_DeltaTri f hf f (by omega)] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  rw [skewX_Phi hF] at hx
  obtain ⟨h1, h2, h3⟩ := hp
  have hF2 : 1 < (f : ℝ) ^ 2 := by nlinarith
  have hA : 0 < (f : ℝ) * ((f : ℝ) ^ 2 - 1) := mul_pos hF0 (by linarith)
  have hu : 0 < (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (f : ℝ) := mul_pos hA hF0
  unfold chordX at hx
  rw [hmR] at hx
  -- the ordinates: `B₀ ≤ p.2 ≤ B₀ f + f² (f−1)`
  have hlow : 2 * (f : ℝ) ^ 2 - 1 ≤ p.2 := by
    have key : 0 ≤ (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (f : ℝ) * (p.2 - (2 * (f : ℝ) ^ 2 - 1)) := by
      rw [hx] at h2
      nlinarith [h2]
    have := (mul_nonneg_iff_of_pos_left hu).mp key
    linarith
  have hhigh : p.2 ≤ (2 * (f : ℝ) ^ 2 - 1) * (f : ℝ) + (f : ℝ) ^ 2 * ((f : ℝ) - 1) := by
    have key : (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (f : ℝ) *
        ((2 * (f : ℝ) ^ 2 - 1) * (f : ℝ) + (f : ℝ) ^ 2 * ((f : ℝ) - 1) - p.2) ≥ 0 := by
      rw [hx] at h3
      nlinarith [h3]
    have := (mul_nonneg_iff_of_pos_left hu).mp key
    linarith
  have hgap : 0 < (2 * (f : ℝ) ^ 2 - 1) * (f : ℝ) + (f : ℝ) ^ 2 * ((f : ℝ) - 1) - (2 * (f : ℝ) ^ 2 - 1) := by
    have e : (2 * (f : ℝ) ^ 2 - 1) * (f : ℝ) + (f : ℝ) ^ 2 * ((f : ℝ) - 1) - (2 * (f : ℝ) ^ 2 - 1)
        = ((f : ℝ) - 1) * (3 * (f : ℝ) ^ 2 - 1) := by ring
    rw [e]
    exact mul_pos (by linarith) (by nlinarith)
  have hQ : chordQ f = Phi (f : ℝ) (chordX f, (2 * (f : ℝ) ^ 2 - 1) * (f : ℝ) + (f : ℝ) ^ 2 * ((f : ℝ) - 1)) := by
    unfold chordQ
    rw [hmR]
  have hP : chordP f = Phi (f : ℝ) (chordX f, 2 * (f : ℝ) ^ 2 - 1) := rfl
  set y0 := 2 * (f : ℝ) ^ 2 - 1 with hy0
  set y1 := (2 * (f : ℝ) ^ 2 - 1) * (f : ℝ) + (f : ℝ) ^ 2 * ((f : ℝ) - 1) with hy1
  have hne : y1 - y0 ≠ 0 := hgap.ne'
  set b := (p.2 - y0) / (y1 - y0) with hb
  have hb0 : 0 ≤ b := div_nonneg (by linarith) hgap.le
  have hb1 : b ≤ 1 := by rw [hb, div_le_one hgap]; linarith
  have hseg : p ∈ segment ℝ (chordX f, y0) (chordX f, y1) := by
    refine ⟨1 - b, b, by linarith, hb0, by ring, ?_⟩
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      unfold chordX
      rw [hmR]
      linarith [hx]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [hb]
      field_simp
      ring
  have himg := (image_segment ℝ (PhiL (f : ℝ)).toAffineMap (chordX f, y0) (chordX f, y1))
  have : Phi (f : ℝ) p ∈ (PhiL (f : ℝ)).toAffineMap '' segment ℝ (chordX f, y0) (chordX f, y1) :=
    ⟨p, hseg, rfl⟩
  rw [himg] at this
  rw [hP, hQ]
  exact this

/-- **(b), in the paper's wording.**  For `f ≥ 2`: `T_{f−1}(1,f)` has a tiling if and only if `T_f(1,f)` has a congruent
dissection (target `DeltaTri f _ f _`, model `MF f`) in which the chord parallel to the base at the height of `T_1`
contains no interior point of a tile (the open segment `(chordP f, chordQ f)` is a wall).

As for `ReframeB.reframe_b`, no instance with true sides is known (false for `f = 2, 3`, open for `f ≥ 4`). -/
theorem reframe_b_wall (f : ℕ) (hf : 2 ≤ f) :
    BetaTilable 1 f (f - 1) ↔ ∃ (N : ℕ) (D : CongruentDissection N), D.target = DeltaTri f hf f (by omega) ∧
      D.model = Erdos634.Draft.WBrickF.MF (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf) ∧
      ∀ y ∈ openSegment ℝ (chordP f) (chordQ f), ∀ i, y ∉ interior (D.tile i).carrier := by
  have hF := Erdos634.Draft.WPgramF.hF f hf
  rw [Erdos634.Draft.ReframeB.reframe_b f hf]
  constructor
  · rintro ⟨N, D, hT, hM, h0⟩
    refine ⟨N, D, hT, hM, fun y hy i hyi => ?_⟩
    have hl : skewX (f : ℝ) y = chordX f := skewX_openSegment f hf hy
    exact Erdos634.Draft.ChordCut.not_straddles_of_empty D.toDissection _ _ h0 i
      (Erdos634.ChordTraceReal.interior_on_line_straddles (D.tile i) (skewX (f : ℝ)) (skewX_ne_zero hF) _ hyi hl)
  · rintro ⟨N, D, hT, hM, hw⟩
    refine ⟨N, D, hT, hM, ?_⟩
    exact Erdos634.Draft.ChordCut.straddlers_eq_empty_of_wall D.toDissection (skewX (f : ℝ)) _
      (P := chordP f) (Q := chordQ f) (fun y hy hl => chord_hline f hf y (by rw [← hT]; exact hy) hl) hw

end Erdos634.Draft.ReframeBWall

#print axioms Erdos634.Draft.ReframeBWall.chord_hline
#print axioms Erdos634.Draft.ReframeBWall.reframe_b_wall
