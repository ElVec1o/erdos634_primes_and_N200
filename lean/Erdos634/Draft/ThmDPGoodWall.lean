import Mathlib.Tactic
import Erdos634.Draft.ThmDPGoodCorner
import Erdos634.Draft.ThmDWallFan
import Erdos634.Draft.ThmDRowVertex

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (4): `PGood` at a wall point (the interior start)  

`PGood_of_west` : if `P = lp 0 η` (`η > 0`) is interior to the target and `WestCover D FXT P` (the west half-disc is covered by one tile
lying west of the ray), then the end `P` is good: the fan (`pinfan_wall`), the east angle sum (`wall_east_sum`), the clamps of the
row and of the diagonal on the west side (`WestCover.no_straddle`).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem cross_rayT {u v ε x : ℝ} (hε : ε ^ 2 = 1) (ξ η : ℝ) (y : Plane) :
    cross (lpT u v ε x ξ (η + 1) - lpT u v ε x ξ η) y = (-ε) * FXT u v ε y := by
  unfold FXT lpT
  rw [lin_apply]
  simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]
  linear_combination (hhT u v * y 0) * hε

theorem PGood_of_west (C : CtxBaseT D u v α β γ L ax ay ε x) {η : ℝ} (hη : 0 < η)
    (hPint : lpT (u : ℝ) (v : ℝ) ε x 0 η ∈ interior D.target.carrier)
    (hW : WestCover D.toDissection (FXT (u : ℝ) (v : ℝ) ε) (lpT (u : ℝ) (v : ℝ) ε x 0 η)) :
    PGood D (u : ℝ) (v : ℝ) ε x α η := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hβpos : 0 < β := by
    have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
    have e : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
    rw [e] at h; exact h
  have h3α : 3 * α < Real.pi := by have := S.hβ; linarith
  set P := lpT (u : ℝ) (v : ℝ) ε x 0 η with hPdef
  set Q := lpT (u : ℝ) (v : ℝ) ε x η 0 with hQdef
  -- the cross vector
  set uvec : Plane := (-ε) • (lpT (u : ℝ) (v : ℝ) ε x 0 (0 + 1) - lpT (u : ℝ) (v : ℝ) ε x 0 0) with huvec
  have hcross : ∀ y, cross uvec y = 1 * FXT (u : ℝ) (v : ℝ) ε y := by
    intro y
    rw [huvec, cross_smul_left', cross_rayT hε, one_mul]
    linear_combination (FXT (u : ℝ) (v : ℝ) ε y) * hε
  have hu0 : uvec ≠ 0 := by
    intro h0
    refine FXT_ne hu huv hv2 hε (LinearMap.ext fun y => ?_)
    have := hcross y
    rw [h0] at this
    have h1 : cross (0 : Plane) y = 0 := by simp [cross]
    rw [h1] at this
    simpa using this.symm
  have hκ : (0 : ℝ) < 1 := one_pos
  have hFP : ∀ y, FXT (u : ℝ) (v : ℝ) ε y = FXT (u : ℝ) (v : ℝ) ε y := fun _ => rfl
  have hPQ : P ≠ Q := lpT_ne_eta hu huv hv2 hη.ne'
  have hGP : GST (u : ℝ) (v : ℝ) ε P = GST (u : ℝ) (v : ℝ) ε Q := by
    rw [hPdef, hQdef, GST_lp hε, GST_lp hε]; congr 1; congr 1; ring
  have hFXP : FXT (u : ℝ) (v : ℝ) ε P = lvT (u : ℝ) (v : ℝ) ε x 0 := by rw [hPdef, FXT_lp hε]
  have hFXQ : FXT (u : ℝ) (v : ℝ) ε Q = lvT (u : ℝ) (v : ℝ) ε x η := by rw [hQdef, FXT_lp hε]
  have hlv : lvT (u : ℝ) (v : ℝ) ε x 0 < lvT (u : ℝ) (v : ℝ) ε x η := lvT_lt hu huv hv2 hη
  obtain ⟨δ, hδ, hcl⟩ := hW.no_straddle
  have hPmem : P ∈ D.target.carrier := interior_subset hPint
  have hc : 0 < (u : ℝ) * v := mul_pos hu (hu.trans huv)
  have hu' : (u : ℝ) ≠ 0 := hu.ne'
  have hv0 : (v : ℝ) ≠ 0 := (hu.trans huv).ne'
  refine ⟨hPmem, ?_, ?_, ?_, ?_⟩
  · intro tW tE hne hvW hvE a a' hWa hEa
    obtain ⟨kW, hkW⟩ := hvW
    obtain ⟨kE, hkE⟩ := hvE
    exact pinfan_wall D S.hirr S.hM.hα' (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α hκ hu0 hcross
      hPint hW tW tE hne (fun i => hW.east_vertex hkW i) (fun i => hW.east_vertex hkE i) a a' hWa hEa
  · obtain ⟨S', hsum, hmem⟩ := wall_east_sum D hκ hu0 hcross hPint hW
    exact ⟨S', hsum, fun τ k hk => hmem τ (fun i => hW.east_vertex hk i)⟩
  · set s0 : ℝ := min 1 (δ / (2 * ((u : ℝ) * v))) with hs0
    have hs0pos : 0 < s0 := lt_min one_pos (div_pos hδ (by positivity))
    have hs0le : s0 ≤ δ / (2 * ((u : ℝ) * v)) := min_le_right _ _
    refine ⟨s0, hs0pos, fun Q' i k => hcl _ Q' ?_ ?_ i k⟩
    · rw [hPdef, dist_rowT (a := -s0) (b := 0) hu huv hv2 hε (by linarith)]
      have h1 : s0 * ((u : ℝ) * v) ≤ δ / 2 := by
        have := mul_le_mul_of_nonneg_right hs0le hc.le
        have e : δ / (2 * ((u : ℝ) * v)) * ((u : ℝ) * v) = δ / 2 := by field_simp
        linarith
      linarith
    · rw [hPdef, FXT_lp hε, FXT_lp hε]
      exact lvT_lt hu huv hv2 (by linarith)
  · have hd0pos : 0 < dist P Q := dist_pos.mpr hPQ
    set s : ℝ := min 1 (δ / (2 * dist P Q)) with hs
    have hspos : 0 < s := lt_min one_pos (div_pos hδ (by positivity))
    have hsle : s ≤ δ / (2 * dist P Q) := min_le_right _ _
    refine ⟨AffineMap.lineMap P Q (-s), ?_, ?_, fun i k => hcl _ Q ?_ ?_ i k⟩
    · rw [lineMap_lin, ← hGP]; ring
    · rw [openSegment_eq_image_lineMap]
      refine ⟨s / (1 + s), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_lt_one (by positivity)]; linarith
      · ext i
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
          PiLp.sub_apply, smul_eq_mul]
        field_simp
        ring
    · rw [dist_lineMap_left, Real.norm_eq_abs, abs_neg, abs_of_pos hspos]
      have := mul_le_mul_of_nonneg_right hsle hd0pos.le
      have e : δ / (2 * dist P Q) * dist P Q = δ / 2 := by field_simp
      linarith
    · rw [lineMap_lin, hFXP, hFXQ]
      nlinarith

#print axioms PGood_of_west
end Erdos634.Draft.ThmDRun
