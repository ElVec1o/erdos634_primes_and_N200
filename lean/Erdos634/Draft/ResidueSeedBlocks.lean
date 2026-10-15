/-
Draft/ResidueSeedBlocks.lean -- the residue seed: the tilings of the five pieces of the three outside blocks
(`rt_B1a`, `rt_B2a`, `rt_B3`: the tile at the scales `uv`, `ut`, `K`; `rt_B1b`, `rt_B2b`: lattice parallelograms).

The construction is due to D. Paliy, "unrestricted all-scale positive theorem for W and beta" (2026, unrefereed).
Part of the formal proof in `Draft.ResidueSeed`; split off to keep each Lean process small.
No sorry, no native_decide.
-/
import Erdos634.Draft.ResidueBlocksDefs

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.Residue
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (triC triC_pts carrier_triC brickL brickU brick_rt cong_U_cell grid scaledRT baseTri
  baseTri_cong vol_triC sq_Phi' dPhi' disjoint_image' f_ne)
open Erdos634.Draft.WBrickF (interior_disj_lin)
open Erdos634.Draft.CollarE1 (mapped_grid Pg)
open Erdos634.Draft.CollarG (φβ hφβ ca cb hapos hbpos hvpos hPpos WTilable)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.UniformThreshold (BetaTilable ThresholdAt hasSides_congr)

/-! ## The blocks -/
section blocks
variable {t r e : ℝ} (ht : 0 < t) (hr : 0 < r) (he : 0 < e)
include ht hr he

theorem rt_B1a (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = (t + r) * (t + r + e)) :
    Nonempty (RTiling (Phi (φβ (t + r) e) '' B1a t r e) (ModC (add_pos ht hr) he) (k * k)) := by
  have hu := add_pos ht hr
  have h1 : t + r ≠ 0 := hu.ne'
  have h2 : t + r + e ≠ 0 := by positivity
  have h3 : 3 * (t + r + e) ^ 2 - (t + r) ^ 2 ≠ 0 := (hPpos hu he).ne'
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have hdet : ((pE1 t r e).1 - (pQ0 t r e).1) * ((((0 : ℝ), (0 : ℝ)) : ℝ × ℝ).2 - (pQ0 t r e).2)
      - ((((0 : ℝ), (0 : ℝ)) : ℝ × ℝ).1 - (pQ0 t r e).1) * ((pE1 t r e).2 - (pQ0 t r e).2) ≠ 0 := by
    have hE : ((pE1 t r e).1 - (pQ0 t r e).1) * ((((0 : ℝ), (0 : ℝ)) : ℝ × ℝ).2 - (pQ0 t r e).2)
        - ((((0 : ℝ), (0 : ℝ)) : ℝ × ℝ).1 - (pQ0 t r e).1) * ((pE1 t r e).2 - (pQ0 t r e).2)
        = (t + r) ^ 3 * (t + r + e) ^ 5 := by
      simp only [pE1, pQ0]; field_simp; ring
    rw [hE]; positivity
  exact ⟨scaledRT (φβ (t + r) e) (hφβ hu he) (pQ0 t r e) (pE1 t r e) ((0 : ℝ), (0 : ℝ)) k hk0 hdet _
    (baseTri_cong _ _ (ca (t + r) e) ((t + r + e) ^ 2) ((cb (t + r) e) ^ 2) (hapos hu he) (hc2 hu he)
      (habC hu he) _ _ _ k hk0 _
      (by rw [hk]; simp only [pE1, pQ0, ca, φβ]; field_simp; ring)
      (by rw [hk]; simp only [pE1, pQ0, ca, φβ]; field_simp; ring)
      (by rw [hk]; simp only [pE1, pQ0, ca, cb, φβ]; field_simp; ring))⟩

theorem rt_B2a (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = (t + r) * t) :
    Nonempty (RTiling (Phi (φβ (t + r) e) '' B2a t r e) (ModC (add_pos ht hr) he) (k * k)) := by
  have hu := add_pos ht hr
  have h1 : t + r ≠ 0 := hu.ne'
  have h2 : t + r + e ≠ 0 := by positivity
  have h3 : 3 * (t + r + e) ^ 2 - (t + r) ^ 2 ≠ 0 := (hPpos hu he).ne'
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have hdet : ((pE2 t r e).1 - (pQ0 t r e).1) * ((pS t r e).2 - (pQ0 t r e).2)
      - ((pS t r e).1 - (pQ0 t r e).1) * ((pE2 t r e).2 - (pQ0 t r e).2) ≠ 0 := by
    have hE : ((pE2 t r e).1 - (pQ0 t r e).1) * ((pS t r e).2 - (pQ0 t r e).2)
        - ((pS t r e).1 - (pQ0 t r e).1) * ((pE2 t r e).2 - (pQ0 t r e).2)
        = -(t ^ 2 * (t + r) ^ 3 * (t + r + e) ^ 3) := by
      simp only [pE2, pS, pQ0]; field_simp; ring
    rw [hE]; exact neg_ne_zero.mpr (by positivity)
  exact ⟨scaledRT (φβ (t + r) e) (hφβ hu he) (pQ0 t r e) (pE2 t r e) (pS t r e) k hk0 hdet _
    (baseTri_cong _ _ (ca (t + r) e) ((t + r + e) ^ 2) ((cb (t + r) e) ^ 2) (hapos hu he) (hc2 hu he)
      (habC hu he) _ _ _ k hk0 _
      (by rw [hk]; simp only [pE2, pS, pQ0, ca, φβ]; field_simp; ring)
      (by rw [hk]; simp only [pE2, pS, pQ0, ca, φβ]; field_simp; ring)
      (by rw [hk]; simp only [pE2, pS, pQ0, ca, cb, φβ]; field_simp; ring))⟩

theorem rt_B3 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = e * ((t + r) + (t + r + e) + t)) :
    Nonempty (RTiling (Phi (φβ (t + r) e) '' B3 t r e) (ModC (add_pos ht hr) he) (k * k)) := by
  have hu := add_pos ht hr
  have h1 : t + r ≠ 0 := hu.ne'
  have h2 : t + r + e ≠ 0 := by positivity
  have h3 : 3 * (t + r + e) ^ 2 - (t + r) ^ 2 ≠ 0 := (hPpos hu he).ne'
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  have hdet : ((pR0 t r e).1 - (pV t r e).1) * ((pC t r e).2 - (pV t r e).2)
      - ((pC t r e).1 - (pV t r e).1) * ((pR0 t r e).2 - (pV t r e).2) ≠ 0 := by
    have hE : ((pR0 t r e).1 - (pV t r e).1) * ((pC t r e).2 - (pV t r e).2)
        - ((pC t r e).1 - (pV t r e).1) * ((pR0 t r e).2 - (pV t r e).2)
        = -(e ^ 2 * (t + r) * (t + r + e) ^ 3 * (e + 2 * r + 3 * t) ^ 2) := by
      simp only [pR0, pV, pC]; field_simp; ring
    rw [hE]; exact neg_ne_zero.mpr (by positivity)
  exact ⟨scaledRT (φβ (t + r) e) (hφβ hu he) (pV t r e) (pR0 t r e) (pC t r e) k hk0 hdet _
    (baseTri_cong _ _ (ca (t + r) e) ((t + r + e) ^ 2) ((cb (t + r) e) ^ 2) (hapos hu he) (hc2 hu he)
      (habC hu he) _ _ _ k hk0 _
      (by rw [hk]; simp only [pR0, pV, pC, ca, φβ]; field_simp; ring)
      (by rw [hk]; simp only [pR0, pV, pC, ca, φβ]; field_simp; ring)
      (by rw [hk]; simp only [pR0, pV, pC, ca, cb, φβ]; field_simp; ring))⟩

theorem rt_B1b (nk nl : ℕ) (hnk : 0 < nk) (hnl : 0 < nl) (ek : (nk : ℝ) = (t + r) * (t + r + e))
    (el : (nl : ℝ) = (t + r) * t) :
    ∃ S : Set Plane, Nonempty (RTiling S (ModC (add_pos ht hr) he) (2 * nk * nl)) ∧
      S ⊆ Phi (φβ (t + r) e) '' B1b t r e := by
  have hu := add_pos ht hr
  have h1 : t + r ≠ 0 := hu.ne'
  have h2 : t + r + e ≠ 0 := by positivity
  have h3 : 3 * (t + r + e) ^ 2 - (t + r) ^ 2 ≠ 0 := (hPpos hu he).ne'
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  obtain ⟨k, rfl⟩ : ∃ k, nk = k + 1 := ⟨nk - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, nl = l + 1 := ⟨nl - 1, by omega⟩
  have hk : (k : ℝ) + 1 = (t + r) * (t + r + e) := by rw [← ek]; push_cast; ring
  have hl : (l : ℝ) + 1 = (t + r) * t := by rw [← el]; push_cast; ring
  have h := mapped_grid (hφβ hu he) (hφβ hu he) (hapos hu he) (hc2 hu he) (cellAC hu he) k l (pE1 t r e)
    (vS t r e - vE t r e) (vE t r e)
    (by have hE : (vS t r e - vE t r e).1 * (vE t r e).2 - (vE t r e).1 * (vS t r e - vE t r e).2
            = (t + r) * (t + r + e) ^ 3 := by
          simp only [vS, vE, Prod.fst_sub, Prod.snd_sub]; field_simp; ring
        rw [hE]; positivity)
    (by simp only [vS, vE, ca, φβ, Prod.fst_sub, Prod.snd_sub]; field_simp; ring)
    (by simp only [vE, φβ]; field_simp; ring)
    (by simp only [vS, vE, ca, φβ, Prod.fst_sub, Prod.snd_sub]; field_simp; ring)
  rw [hk, hl] at h
  exact h

theorem rt_B2b (nk nl : ℕ) (hnk : 0 < nk) (hnl : 0 < nl) (ek : (nk : ℝ) = e * t) (el : (nl : ℝ) = (t + r) * t) :
    ∃ S : Set Plane, Nonempty (RTiling S (ModC (add_pos ht hr) he) (2 * nk * nl)) ∧
      S ⊆ Phi (φβ (t + r) e) '' B2b t r e := by
  have hu := add_pos ht hr
  have h1 : t + r ≠ 0 := hu.ne'
  have h2 : t + r + e ≠ 0 := by positivity
  have h3 : 3 * (t + r + e) ^ 2 - (t + r) ^ 2 ≠ 0 := (hPpos hu he).ne'
  have hb : e * (2 * t + 2 * r + e) ≠ 0 := by positivity
  obtain ⟨k, rfl⟩ : ∃ k, nk = k + 1 := ⟨nk - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, nl = l + 1 := ⟨nl - 1, by omega⟩
  have hk : (k : ℝ) + 1 = e * t := by rw [← ek]; push_cast; ring
  have hl : (l : ℝ) + 1 = (t + r) * t := by rw [← el]; push_cast; ring
  have h := mapped_grid (hφβ hu he) (hφβ hu he) (hapos hu he) (hc2 hu he) (cellAC hu he) k l (pE2 t r e)
    (vE2 t r e) (vS2 t r e - vE2 t r e)
    (by have hE : (vE2 t r e).1 * (vS2 t r e - vE2 t r e).2 - (vS2 t r e - vE2 t r e).1 * (vE2 t r e).2
            = -((t + r) * (t + r + e) ^ 3) := by
          simp only [vS2, vE2, Prod.fst_sub, Prod.snd_sub]; field_simp; ring
        rw [hE]; exact neg_ne_zero.mpr (by positivity))
    (by simp only [vE2, ca, φβ]; field_simp; ring)
    (by simp only [vS2, vE2, φβ, Prod.fst_sub, Prod.snd_sub]; field_simp; ring)
    (by simp only [vS2, vE2, ca, φβ, Prod.fst_sub, Prod.snd_sub]; field_simp; ring)
  rw [hk, hl] at h
  exact h

end blocks

end Erdos634.Draft.Residue
