-- Draft/ThetaUnitAssemble.lean -- region-tiling form of the UNIT THETA STEP (skew frame).  INTERNAL BUILD ONLY, UNAUDITED.
-- No sorry, no native_decide.
/-
**`step_rtiling`.**  Tile `(e f, b, f^2)`, `b = f^2 - e^2` (`f*f = e*e + b`), frame `Phi_phi`, `phi = f/e`, model `Mrow`
(the brick `(0,0),(b,0),(b,e f)`).  If `(f-e) n >= e` and the triangle `theta_n = (0,0), A1, A2`
(`A1 = (f b n, 0)`, `A2 = (0, e b n)`) is tiled by `b n^2` copies of the model, then the triangle
`theta_{n+1} = (0,0), O, B` (`O = (f b (n+1), 0)`, `B = (0, e b (n+1))`) is tiled by `b (n+1)^2` copies.

Proof: `theta_{n+1} = theta_n  u  T  u  R` with the two ladder trapezoids of `ThetaUnitCore`
(`T`: `(f+g)^2 - g^2 = f^2 + 2 f g` tiles; `R`: `g^2 - (g-e)^2` tiles; `g = (f-e) n`), packed by
`LadderFam.pack_exists'` (containment + disjoint interiors + equal area; the covering is derived from the area).

CREDIT and STATUS: see `ThetaUnitCore`.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaUnitPieces

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaUnit
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri vol_triC)
open MeasureTheory

/-- the region `theta_n` in the frame -/
def thetaSet (φ E F n : ℝ) : Set Plane :=
  Phi φ '' convexHull ℝ ({((0 : ℝ), (0 : ℝ)), tA1 E F n, tA2 E F n} : Set (ℝ × ℝ))

/-- the region `theta_{n+1}` in the frame -/
def thetaNext (φ E F n : ℝ) : Set Plane :=
  Phi φ '' convexHull ℝ ({((0 : ℝ), (0 : ℝ)), tO E F n, tB E F n} : Set (ℝ × ℝ))

theorem step_rtiling {φ : ℝ} (hφ : 1 < φ) (e f b n : ℕ) (he : 0 < e) (hef : e < f) (hb : f * f = e * e + b)
    (hφE : φ = (f : ℝ) / e) (hg : e ≤ (f - e) * n)
    (R0 : RTiling (thetaSet φ (e : ℝ) (f : ℝ) (n : ℝ)) (Mrow hφ e f he hef) (b * n * n)) :
    Nonempty (RTiling (thetaNext φ (e : ℝ) (f : ℝ) (n : ℝ)) (Mrow hφ e f he hef) (b * (n + 1) * (n + 1))) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hgR : (e : ℝ) ≤ ((f : ℝ) - e) * n := by
    have : ((e : ℕ) : ℝ) ≤ (((f - e) * n : ℕ) : ℝ) := by exact_mod_cast hg
    rwa [Nat.cast_mul, Nat.cast_sub hef.le] at this
  have hbR : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : ((f * f : ℕ) : ℝ) = ((e * e + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; nlinarith
  obtain ⟨hb0, ha0, hc0⟩ := pos_facts hE hEF
  have hF : (0 : ℝ) < f := by linarith
  set E : ℝ := (e : ℝ) with hEdef
  set F : ℝ := (f : ℝ) with hFdef
  set nR : ℝ := (n : ℝ) with hnRdef
  set M := Mrow hφ e f he hef with hMdef
  have hMeq : M = brickL φ hφ (F ^ 2 - E ^ 2) (E * F) hb0 ha0 := rfl
  -- natural-number scales
  set g : ℕ := (f - e) * n with hgdef
  have hgcast : (g : ℝ) = gg E F nR := by
    rw [hgdef, Nat.cast_mul, Nat.cast_sub hef.le]; rfl
  have hegle : e ≤ g := hg
  have hglek : g ≤ f + g := Nat.le_add_left _ _
  have hkpos : 0 < f + g := by omega
  have hgpos : 0 < g := by omega
  have hkcast : ((f + g : ℕ) : ℝ) = F + gg E F nR := by push_cast; rw [hgcast]
  have hspcast : ((g - e : ℕ) : ℝ) = gg E F nR - E := by rw [Nat.cast_sub hegle, hgcast]
  have hσT : (g : ℝ) / ((f + g : ℕ) : ℝ) = gg E F nR / (F + gg E F nR) := by rw [hgcast, hkcast]
  have hσR : ((g - e : ℕ) : ℝ) / (g : ℝ) = (gg E F nR - E) / gg E F nR := by rw [hspcast, hgcast]
  -- inequalities in the form needed
  have hTin := T_inTgt hE hEF hn hgR
  have hRin := R_inTgt hE hEF hn hgR
  have hTold := T_old hE hEF hn hgR
  have hRold := R_old hE hEF hn hgR
  have hTsep := T_sepR hE hEF hn hgR
  have hRsep := R_sepT hE hEF hn hgR
  have hOld := old_le hE hEF hn hgR
  have hOin := old_inTgt hE hEF hn hgR
  rw [← hσT] at hTin hTold hTsep
  rw [← hσR] at hRin hRold hRsep
  -- the three tile families
  let famT : TFam (Phi φ '' Preg (tY E F nR) (tO E F nR) (tU2 E F nR) ((g : ℝ) / ((f + g : ℕ) : ℝ))) M
      ((f + g) * (f + g) - g * g) :=
    ladderFam φ hφ (tY E F nR) (tO E F nR) (tU2 E F nR) (f + g) g hkpos hglek (det_T hE hEF hn hgR) M
      (cong_T hE hEF hn hgR hφ hφE hkpos hkcast hb0 ha0)
  let famR : TFam (Phi φ '' Preg (tAs E F nR) (tA2 E F nR) (tU1 E F nR) (((g - e : ℕ) : ℝ) / (g : ℝ))) M
      (g * g - (g - e) * (g - e)) :=
    ladderFam φ hφ (tAs E F nR) (tA2 E F nR) (tU1 E F nR) g (g - e) hgpos (Nat.sub_le g e) (det_R hE hEF hn hgR) M
      (cong_R hE hEF hn hgR hφ hφE hgpos hgcast hb0 ha0)
  let famO : TFam (thetaSet φ E F nR) M (b * n * n) := TFam.ofR R0
  -- target
  have hN0 : (0 : ℝ) < nR + 1 := by linarith
  have hB0 : 0 < F * (F ^ 2 - E ^ 2) * (nR + 1) := mul_pos (mul_pos hF hb0) hN0
  have hy0 : 0 < E * (F ^ 2 - E ^ 2) * (nR + 1) := mul_pos (mul_pos hE hb0) hN0
  have hdetT : ((tO E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tB E F nR).2 - ((0 : ℝ), (0 : ℝ)).2) -
      ((tB E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tO E F nR).2 - ((0 : ℝ), (0 : ℝ)).2) ≠ 0 := by
    have : ((tO E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tB E F nR).2 - ((0 : ℝ), (0 : ℝ)).2) -
        ((tB E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tO E F nR).2 - ((0 : ℝ), (0 : ℝ)).2)
        = (F * (F ^ 2 - E ^ 2) * (nR + 1)) * (E * (F ^ 2 - E ^ 2) * (nR + 1)) := by
      dsimp only [tO, tB]; ring
    rw [this]; exact (mul_pos hB0 hy0).ne'
  let tgt : Tri := triC φ hφ ((0 : ℝ), (0 : ℝ)) (tO E F nR) (tB E F nR) hdetT
  have tgt_car : tgt.carrier = thetaNext φ E F nR := carrier_triC _ _ _ _ _ _
  -- containment of a linear-inequality region in the target
  have inHull : ∀ p : ℝ × ℝ, InTgt E F nR p →
      p ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), tO E F nR, tB E F nR} : Set (ℝ × ℝ)) := by
    rintro ⟨X, Y⟩ ⟨h1, h2, h3⟩
    have hbN : 0 ≤ (F ^ 2 - E ^ 2) * (nR + 1) := (mul_pos hb0 hN0).le
    have h3' : 0 ≤ E * (F * (F ^ 2 - E ^ 2) * (nR + 1) - X) - F * Y := by
      dsimp only at h1 h2 h3; nlinarith
    have := mem_tri_iso (B := F * (F ^ 2 - E ^ 2) * (nR + 1)) (xA := 0) (yA := E * (F ^ 2 - E ^ 2) * (nR + 1))
      (X := X) (Y := Y) hB0 hy0 h1 (by nlinarith) (by
        have e1 : E * (F ^ 2 - E ^ 2) * (nR + 1) * (F * (F ^ 2 - E ^ 2) * (nR + 1) - X) -
            (F * (F ^ 2 - E ^ 2) * (nR + 1) - 0) * Y =
            ((F ^ 2 - E ^ 2) * (nR + 1)) * (E * (F * (F ^ 2 - E ^ 2) * (nR + 1) - X) - F * Y) := by ring
        rw [e1]; exact mul_nonneg hbN h3')
    exact this
  have hsub : ∀ a : Fin 3, (![thetaSet φ E F nR,
      Phi φ '' Preg (tY E F nR) (tO E F nR) (tU2 E F nR) ((g : ℝ) / ((f + g : ℕ) : ℝ)),
      Phi φ '' Preg (tAs E F nR) (tA2 E F nR) (tU1 E F nR) (((g - e : ℕ) : ℝ) / (g : ℝ))] a) ⊆ tgt.carrier := by
    intro a
    rw [tgt_car]
    fin_cases a
    · exact Set.image_mono (fun p hp => inHull p (hOin p hp))
    · exact Set.image_mono (fun p hp => inHull p (hTin p hp))
    · exact Set.image_mono (fun p hp => inHull p (hRin p hp))
  -- pairwise disjoint interiors
  have hE0 : E ≠ 0 := hE.ne'
  have hF0 : F ≠ 0 := hF.ne'
  have dOT : Disjoint (interior (thetaSet φ E F nR))
      (interior (Phi φ '' Preg (tY E F nR) (tO E F nR) (tU2 E F nR) ((g : ℝ) / ((f + g : ℕ) : ℝ)))) :=
    disjoint_image hφ (interior_disj_lin E F (E * F * (F ^ 2 - E ^ 2) * nR) hE0 hOld hTold)
  have dOR : Disjoint (interior (thetaSet φ E F nR))
      (interior (Phi φ '' Preg (tAs E F nR) (tA2 E F nR) (tU1 E F nR) (((g - e : ℕ) : ℝ) / (g : ℝ)))) :=
    disjoint_image hφ (interior_disj_lin E F (E * F * (F ^ 2 - E ^ 2) * nR) hE0 hOld hRold)
  have dRT : Disjoint
      (interior (Phi φ '' Preg (tAs E F nR) (tA2 E F nR) (tU1 E F nR) (((g - e : ℕ) : ℝ) / (g : ℝ))))
      (interior (Phi φ '' Preg (tY E F nR) (tO E F nR) (tU2 E F nR) ((g : ℝ) / ((f + g : ℕ) : ℝ)))) :=
    disjoint_image hφ (interior_disj_lin F E (E * F * (F ^ 2 - E ^ 2) * nR) hF0 hRsep hTsep)
  let S : Fin 3 → Set Plane := ![thetaSet φ E F nR,
      Phi φ '' Preg (tY E F nR) (tO E F nR) (tU2 E F nR) ((g : ℝ) / ((f + g : ℕ) : ℝ)),
      Phi φ '' Preg (tAs E F nR) (tA2 E F nR) (tU1 E F nR) (((g - e : ℕ) : ℝ) / (g : ℝ))]
  let cnt : Fin 3 → ℕ := ![b * n * n, (f + g) * (f + g) - g * g, g * g - (g - e) * (g - e)]
  let Rf : ∀ a : Fin 3, TFam (S a) M (cnt a) := fun a => match a with
    | ⟨0, _⟩ => famO
    | ⟨1, _⟩ => famT
    | ⟨2, _⟩ => famR
    | ⟨k + 3, h⟩ => absurd h (by omega)
  have hSd : ∀ a c : Fin 3, a ≠ c → Disjoint (interior (S a)) (interior (S c)) := by
    intro a c hac
    fin_cases a <;> fin_cases c <;>
      first
        | exact absurd rfl hac
        | exact dOT | exact dOT.symm | exact dOR | exact dOR.symm | exact dRT | exact dRT.symm
  have hsub' : ∀ a : Fin 3, S a ⊆ tgt.carrier := hsub
  have h2 : g * g ≤ (f + g) * (f + g) := Nat.mul_self_le_mul_self hglek
  have h3 : (g - e) * (g - e) ≤ g * g := Nat.mul_self_le_mul_self (Nat.sub_le g e)
  have hsum : (∑ a, cnt a) = b * (n + 1) * (n + 1) := by
    have e1 : (∑ a, cnt a) = b * n * n + ((f + g) * (f + g) - g * g) + (g * g - (g - e) * (g - e)) := by
      rw [Fin.sum_univ_three]; rfl
    rw [e1]
    apply Nat.cast_injective (R := ℝ)
    push_cast [Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub hegle, hgcast]
    rw [hbR]
    simp only [gg]
    ring
  have hvol : ((∑ a, cnt a : ℕ) : ENNReal) * volume M.carrier = volume tgt.carrier := by
    have hs := sD_pos hφ
    have hφ0 : 0 < φ := by linarith
    have hM : volume M.carrier = ENNReal.ofReal (sD φ / (2 * φ) * ((F ^ 2 - E ^ 2) * (E * F)))
        * volume Erdos634.AreaDet.stdCarrier := by
      rw [hMeq]; unfold brickL; rw [vol_triC]; congr 2
      rw [← abs_of_pos (show 0 < sD φ / (2 * φ) * ((F ^ 2 - E ^ 2) * (E * F)) from
        mul_pos (div_pos hs (by linarith)) (mul_pos hb0 ha0))]
      congr 1; simp only []; ring
    have hT : volume tgt.carrier = ENNReal.ofReal (sD φ / (2 * φ) *
        ((F * (F ^ 2 - E ^ 2) * (nR + 1)) * (E * (F ^ 2 - E ^ 2) * (nR + 1)))) * volume Erdos634.AreaDet.stdCarrier := by
      change volume (triC φ hφ _ _ _ hdetT).carrier = _
      rw [vol_triC]; congr 2
      rw [← abs_of_pos (show 0 < sD φ / (2 * φ) * ((F * (F ^ 2 - E ^ 2) * (nR + 1)) * (E * (F ^ 2 - E ^ 2) * (nR + 1))) from
        mul_pos (div_pos hs (by linarith)) (mul_pos hB0 hy0))]
      congr 1; dsimp only [tO, tB]; ring
    rw [hM, hT, hsum, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 2
    push_cast
    rw [hbR]; ring
  obtain ⟨D, hDm, hDt⟩ := pack_exists' (M := M) (T := tgt) S cnt Rf hSd hsub' hvol
  have key : ∀ N : ℕ, N = b * (n + 1) * (n + 1) → ∀ D : CongruentDissection N, D.model = M → D.target = tgt →
      Nonempty (RTiling (thetaNext φ E F nR) M (b * (n + 1) * (n + 1))) := by
    rintro N rfl D hm ht
    exact ⟨{ tile := D.tile
             covers := D.covers.trans (by rw [ht, tgt_car])
             disj := D.interiors_disjoint
             cong := fun i => by have := D.tiles_congruent i; rwa [hm] at this }⟩
  exact key _ hsum D hDm hDt

end

end Erdos634.Draft.ThetaUnit
