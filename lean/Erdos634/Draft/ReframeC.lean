/-
Draft/ReframeC.lean  In `AllThreshold`.

PIECE C3: Proposition `prop:reframe` (c).

    If every dissection of `T_f(1,f)` into copies of the tile has a wall that starts at `A`, lies on a cevian and has length at
    least `(f−1) f (f²−1)`, then `T_{f−1}(1,f)` cannot be cut into copies of the tile.

Route (the one of the survey): `LayerE1Chord.layer_chord` gives, from a tiling of `T_{f−1}(1,f)`, a dissection `D` of `T_f(1,f)`
with the chord at the height of `T_1` uncrossed; the hypothesis `H` applied to `D` gives the wall; the tiles of `D` above the
chord form a dissection `D'` of the apex triangle (`ChordCutTiles.restrict_below_tiles`, the tiles of `D'` are tiles of `D`); the
cevian of that triangle (the piece of the wall from the apex to the chord) meets no interior point of a tile of `D'`, so `D'` is
cut along it (`ReframeCWedge.cut_pieces`); the piece that is a triangle with the sides of `W_{f−1}(1,f)` is dissected, which
`SideRun.no_dissection_W` (Theorem C of the base-β threshold program) forbids.

THE TWO CEVIANS.  The two cevians `AQ'` and `AQ` of `T_f` (towards the points of the base at distance `f³` from the corners) are
treated by the two cases of one proof (`Qc = Φ (ptQ1 …)` and `Qc = Φ (ptQ …)`), not by a mirror symmetry: in the case of `AQ'`
the piece above the cevian is `W_{f−1}`, in the case of `AQ` the piece below it (`ReframeCWedge.sidesW_upper`, `sidesW_lower`).

THE HYPOTHESIS `H` IS NOT KNOWN FOR ANY `f ≥ 3`.  `reframe_c` is an implication.  `H` is a statement about all congruent
dissections of `T_f(1,f)` (target `DeltaTri f _ f _`, model `MF f`); for `f = 2` it is true (enumeration of the 252 dissections
of `T_2(1,2)` outside Lean, no Lean witness) and the conclusion `¬ BetaTilable 1 2 1` is `SideRun.not_betaTilable_e1_le_half`;
for `f = 3` the conclusion is `E1ScaleTwo.not_betaTilable_1_3_2` but `H` is not known (it is the "first statement left" of
`rem:reframe`); for `f ≥ 4` both `H` and its conclusion are open.  The seed tilings of `T_f(1,f)` do have a wall of the required
kind on one cevian (`f = 3`: the word `c^8` against `b^9` on the cevian to `Q`) but not on the other.  The theorem is
therefore a verified reduction, not an instance.
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.ReframeCWedge
import Erdos634.Draft.ReframeBWall
import Erdos634.Draft.ChordCutTiles
import Erdos634.Draft.SideRunMain

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.ReframeC
open Erdos634.Draft.WFrameF
open Erdos634.Draft.WBrickF (PhiL)
open Erdos634.Draft.WtoDeltaF (DS DeltaTri carrier_DeltaTri)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.LayerE1Chord (skewX skewX_Phi skewX_ne_zero layer_chord)
open Erdos634.Draft.UniformThreshold (BetaTilable)
open Erdos634.Draft.ReframeCWedge
open Erdos634.Draft.SignedDecompE1 (ptA ptQ1 ptQ sdU sdK sdV d_AQ1 d_AQ)

/-! ## Segments on a ray from the apex -/

/-- `lineMap` of a vertical-axis start point -/
theorem lineMap_prod (v a b s : ℝ) :
    AffineMap.lineMap ((0 : ℝ), v) (a, b) s = (s * a, (1 - s) * v + s * b) := by
  refine Prod.ext ?_ ?_
  · simp [AffineMap.lineMap_apply_module]
  · simp [AffineMap.lineMap_apply_module]

/-- on a ray from `A`, the open segment to the point at parameter `s` lies in the open segment to the point at `r ≥ s` -/
theorem openSegment_lineMap_sub {A B : Plane} {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    openSegment ℝ A (AffineMap.lineMap A B s) ⊆ openSegment ℝ A (AffineMap.lineMap A B r) := by
  intro y hy
  have hr : 0 < r := lt_of_lt_of_le hs hsr
  have hrne : r ≠ 0 := hr.ne'
  rw [openSegment_eq_image_lineMap] at hy ⊢
  obtain ⟨u, hu, rfl⟩ := hy
  refine ⟨u * s / r, ⟨div_pos (mul_pos hu.1 hs) hr, ?_⟩, ?_⟩
  · rw [div_lt_one hr]
    nlinarith [hu.1, hu.2]
  · simp only [AffineMap.lineMap_apply_module]
    match_scalars <;> field_simp <;> ring

/-- the parameter of a point of a segment from the distance -/
theorem param_ge {A B Q : Plane} {L s : ℝ} (hL : dist A B = L) (hL0 : 0 < L) (hQ : Q ∈ segment ℝ A B)
    (hd : s * L ≤ dist A Q) : ∃ r, s ≤ r ∧ Q = AffineMap.lineMap A B r := by
  rw [segment_eq_image_lineMap] at hQ
  obtain ⟨r, hr, rfl⟩ := hQ
  refine ⟨r, ?_, rfl⟩
  rw [dist_left_lineMap, hL, Real.norm_of_nonneg hr.1] at hd
  exact le_of_mul_le_mul_right hd hL0

/-- **A wall from `A` on the ray to `B` of length `≥ s · |AB|` contains the open segment from `A` to the point at
parameter `s`.** -/
theorem wall_sub {A B Q : Plane} {L s : ℝ} (hL : dist A B = L) (hL0 : 0 < L) (hs : 0 < s)
    (hQ : Q ∈ segment ℝ A B) (hd : s * L ≤ dist A Q) :
    openSegment ℝ A (AffineMap.lineMap A B s) ⊆ openSegment ℝ A Q := by
  obtain ⟨r, hsr, rfl⟩ := param_ge hL hL0 hQ hd
  exact openSegment_lineMap_sub hs hsr

/-- the point at parameter `t / F` on the cevian towards `Q'` is `(A₀ t, yK)` -/
theorem X_eq_K (F t : ℝ) (hF : 1 < F) (ht : 0 < t) (htF : t + 1 = F) :
    AffineMap.lineMap (Phi F (ptA F F)) (Phi F (ptQ1 F F)) (t / F) = Phi F (cX F t, yK F t) := by
  have hA : ptA F F = ((0 : ℝ), vA F) := rfl
  rw [hA]
  have hF0 : F ≠ 0 := by linarith
  have h := (AffineMap.apply_lineMap (PhiL F).toAffineMap ((0 : ℝ), vA F) (ptQ1 F F) (t / F)).symm
  have e : AffineMap.lineMap ((0 : ℝ), vA F) (ptQ1 F F) (t / F) = (cX F t, yK F t) := by
    simp only [ptQ1, sdU, sdK]
    rw [lineMap_prod]
    refine Prod.ext ?_ ?_
    · simp only [cX]
      first | (field_simp; ring1) | field_simp
    · simp only [vA, yK]
      obtain rfl : F = t + 1 := htF.symm
      first | (field_simp; ring1) | field_simp
  calc AffineMap.lineMap (Phi F (0, vA F)) (Phi F (ptQ1 F F)) (t / F)
      = (PhiL F).toAffineMap (AffineMap.lineMap ((0 : ℝ), vA F) (ptQ1 F F) (t / F)) := h
    _ = Phi F (cX F t, yK F t) := by rw [e]; rfl

/-- the point at parameter `t / F` on the horizontal cevian towards `Q` is `(A₀ t, vA)` -/
theorem X_eq_M (F t : ℝ) (hF : 1 < F) (ht : 0 < t) (htF : t + 1 = F) :
    AffineMap.lineMap (Phi F (ptA F F)) (Phi F (ptQ F F)) (t / F) = Phi F (cX F t, vA F) := by
  have hA : ptA F F = ((0 : ℝ), vA F) := rfl
  rw [hA]
  have hF0 : F ≠ 0 := by linarith
  have h := (AffineMap.apply_lineMap (PhiL F).toAffineMap ((0 : ℝ), vA F) (ptQ F F) (t / F)).symm
  have e : AffineMap.lineMap ((0 : ℝ), vA F) (ptQ F F) (t / F) = (cX F t, vA F) := by
    simp only [ptQ, sdU, sdV]
    rw [lineMap_prod]
    refine Prod.ext ?_ ?_
    · simp only [cX]
      first | (field_simp; ring1) | field_simp
    · simp only [vA]
      first | (field_simp; ring1) | field_simp
  calc AffineMap.lineMap (Phi F (0, vA F)) (Phi F (ptQ F F)) (t / F)
      = (PhiL F).toAffineMap (AffineMap.lineMap ((0 : ℝ), vA F) (ptQ F F) (t / F)) := h
    _ = Phi F (cX F t, vA F) := by rw [e]; rfl

/-! ## The statement -/

/-- **Proposition `prop:reframe` (c).**  Let `f ≥ 2`.  Suppose that every congruent dissection `D` of `T_f(1,f)` (target
`DeltaTri f _ f _`, model `MF f`) has a wall from the apex `A = Φ_f (ptA f f)` along one of the two cevians (`Qc` is the foot
of the cevian, `Φ_f (ptQ1 f f)` or `Φ_f (ptQ f f)`): a point `Q` of the cevian at distance at least `(f−1) f (f²−1)` from `A`
such that the open segment `(A, Q)` meets no interior point of a tile of `D`.  Then `T_{f−1}(1,f)` cannot be cut into copies of
the tile.

THIS IS AN IMPLICATION WHOSE HYPOTHESIS IS NOT KNOWN FOR ANY `f ≥ 3` (see the header). -/
theorem reframe_c (f : ℕ) (hf : 2 ≤ f)
    (H : ∀ (N : ℕ) (D : CongruentDissection N), D.target = DeltaTri f hf f (by omega) →
      D.model = Erdos634.Draft.WBrickF.MF (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf) →
      ∃ Qc Q : Plane,
        (Qc = Phi (f : ℝ) (ptQ1 (f : ℝ) (f : ℝ)) ∨ Qc = Phi (f : ℝ) (ptQ (f : ℝ) (f : ℝ))) ∧
        Q ∈ segment ℝ (Phi (f : ℝ) (ptA (f : ℝ) (f : ℝ))) Qc ∧
        ((f : ℝ) - 1) * (f : ℝ) * ((f : ℝ) ^ 2 - 1) ≤ dist (Phi (f : ℝ) (ptA (f : ℝ) (f : ℝ))) Q ∧
        ∀ y ∈ openSegment ℝ (Phi (f : ℝ) (ptA (f : ℝ) (f : ℝ))) Q, ∀ i,
          y ∉ interior (D.tile i).carrier) :
    ¬ BetaTilable 1 f (f - 1) := by
  intro hB
  have hFR := Erdos634.Draft.WPgramF.hF f hf
  obtain ⟨N, D, hT, hM, h0⟩ := layer_chord f hf hB
  obtain ⟨Qc, Q, hQc, hQseg, hdist, hwallQ⟩ := H N D hT hM
  -- the real parameters
  have hmR : ((f - 1 : ℕ) : ℝ) = (f : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have ht : (0 : ℝ) < ((f - 1 : ℕ) : ℝ) := by rw [hmR]; linarith
  have htF : ((f - 1 : ℕ) : ℝ) + 1 = (f : ℝ) := by rw [hmR]; ring
  have hFp : (0 : ℝ) < (f : ℝ) := by linarith
  have hF2 : (1 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hc : 0 < cX (f : ℝ) ((f - 1 : ℕ) : ℝ) :=
    mul_pos (mul_pos hFp (by linarith)) ht
  obtain ⟨o1, o2, o3, o4⟩ := ordinates (f : ℝ) ((f - 1 : ℕ) : ℝ) hFR ht htF
  have hab : yB (f : ℝ) < yC (f : ℝ) ((f - 1 : ℕ) : ℝ) := o3.trans o4
  -- the apex triangle of `T_f`
  have hT'c : (Tw (f : ℝ) hFR (vA (f : ℝ)) (cX (f : ℝ) ((f - 1 : ℕ) : ℝ)) (yB (f : ℝ))
      (yC (f : ℝ) ((f - 1 : ℕ) : ℝ)) hc hab).carrier =
      D.target.carrier ∩ {y | skewX (f : ℝ) y ≤ cX (f : ℝ) ((f - 1 : ℕ) : ℝ)} := by
    rw [carrier_Tw, hT, carrier_DeltaTri f hf f (by omega),
      frame_wedge (f : ℝ) ((f - 1 : ℕ) : ℝ) hFR ht htF]
    exact image_inter_iff _ (fun p => p.1 ≤ cX (f : ℝ) ((f - 1 : ℕ) : ℝ))
      (fun q => skewX (f : ℝ) q ≤ cX (f : ℝ) ((f - 1 : ℕ) : ℝ))
      (fun p => by dsimp only; rw [skewX_Phi hFR])
  obtain ⟨N', D', hD't, hD'm, hD'tiles⟩ := Erdos634.Draft.ChordCutTiles.restrict_below_tiles D
    (skewX (f : ℝ)) (skewX_ne_zero hFR) _ h0 _ hT'c
  -- the model
  obtain ⟨m1, m2, m3⟩ := Erdos634.Draft.WPgramWrap.MF_sides hFR
  have hMF0 : HasSides (Erdos634.Draft.WBrickF.MF (f : ℝ) hFR) (f : ℝ) ((f : ℝ) ^ 2) ((f : ℝ) ^ 2 - 1) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; exact m2,
      by simp only [Equiv.refl_apply]; rw [dist_comm]; exact m3,
      by simp only [Equiv.refl_apply]; exact m1⟩
  have hMs : HasSides (Erdos634.Draft.WBrickF.MF (f : ℝ) hFR) (f : ℝ) ((f : ℝ) ^ 2 - 1) ((f : ℝ) ^ 2) :=
    hasSides_rot (hasSides_swap hMF0)
  -- the wall in the frame
  have hLpos : (0 : ℝ) < (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (f : ℝ) :=
    mul_pos (mul_pos hFp (by linarith)) hFp
  have hs : (0 : ℝ) < ((f - 1 : ℕ) : ℝ) / (f : ℝ) := div_pos ht hFp
  have hsL : ((f - 1 : ℕ) : ℝ) / (f : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * (f : ℝ)) =
      ((f : ℝ) - 1) * (f : ℝ) * ((f : ℝ) ^ 2 - 1) := by
    rw [hmR]
    have hf0 : (f : ℝ) ≠ 0 := hFp.ne'
    first | (field_simp; ring1) | field_simp
  rcases hQc with rfl | rfl
  · -- the cevian towards `Q'`
    have hsub := wall_sub (d_AQ1 (f : ℝ) (f : ℝ) hFR hFp) hLpos hs hQseg (by rw [hsL]; exact hdist)
    rw [X_eq_K (f : ℝ) ((f - 1 : ℕ) : ℝ) hFR ht htF] at hsub
    have hwall' : ∀ y ∈ openSegment ℝ (Phi (f : ℝ) (0, vA (f : ℝ)))
        (Phi (f : ℝ) (cX (f : ℝ) ((f - 1 : ℕ) : ℝ), yK (f : ℝ) ((f - 1 : ℕ) : ℝ))), ∀ j,
        y ∉ interior (D'.tile j).carrier := by
      intro y hy j
      obtain ⟨i, hi⟩ := hD'tiles j
      rw [hi]
      exact hwallQ y (hsub hy) i
    obtain ⟨-, N2, D2, hD2t, hD2m⟩ := cut_pieces hFR hc o1 o2 D' hD't hwall'
    have hTs : HasSides D2.target (((f - 1 : ℕ) : ℝ) * (f : ℝ) ^ 3)
        (((f - 1 : ℕ) : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - 1))) (((f - 1 : ℕ) : ℝ) * (2 * (f : ℝ) ^ 2 - 1)) := by
      rw [hD2t]
      exact sidesW_upper (f : ℝ) ((f - 1 : ℕ) : ℝ) hFR ht htF hc o2
    have hMod : HasSides D2.model (f : ℝ) ((f : ℝ) ^ 2 - 1) ((f : ℝ) ^ 2) := by
      rw [hD2m, hD'm, hM]
      exact hMs
    exact Erdos634.Draft.SideRun.no_dissection_W f (f - 1) (by omega) (by omega) D2 hTs hMod
  · -- the horizontal cevian towards `Q`
    have hsub := wall_sub (d_AQ (f : ℝ) (f : ℝ) hFR hFp) hLpos hs hQseg (by rw [hsL]; exact hdist)
    rw [X_eq_M (f : ℝ) ((f - 1 : ℕ) : ℝ) hFR ht htF] at hsub
    have hwall' : ∀ y ∈ openSegment ℝ (Phi (f : ℝ) (0, vA (f : ℝ)))
        (Phi (f : ℝ) (cX (f : ℝ) ((f - 1 : ℕ) : ℝ), vA (f : ℝ))), ∀ j,
        y ∉ interior (D'.tile j).carrier := by
      intro y hy j
      obtain ⟨i, hi⟩ := hD'tiles j
      rw [hi]
      exact hwallQ y (hsub hy) i
    obtain ⟨⟨N1, D1, hD1t, hD1m⟩, -⟩ := cut_pieces hFR hc o3 o4 D' hD't hwall'
    have hTs : HasSides D1.target (((f - 1 : ℕ) : ℝ) * (f : ℝ) ^ 3)
        (((f - 1 : ℕ) : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - 1))) (((f - 1 : ℕ) : ℝ) * (2 * (f : ℝ) ^ 2 - 1)) := by
      rw [hD1t]
      exact sidesW_lower (f : ℝ) ((f - 1 : ℕ) : ℝ) hFR ht htF hc o3
    have hMod : HasSides D1.model (f : ℝ) ((f : ℝ) ^ 2 - 1) ((f : ℝ) ^ 2) := by
      rw [hD1m, hD'm, hM]
      exact hMs
    exact Erdos634.Draft.SideRun.no_dissection_W f (f - 1) (by omega) (by omega) D1 hTs hMod

end Erdos634.Draft.ReframeC

#print axioms Erdos634.Draft.ReframeC.openSegment_lineMap_sub
#print axioms Erdos634.Draft.ReframeC.wall_sub
#print axioms Erdos634.Draft.ReframeC.X_eq_K
#print axioms Erdos634.Draft.ReframeC.X_eq_M
#print axioms Erdos634.Draft.ReframeC.reframe_c
