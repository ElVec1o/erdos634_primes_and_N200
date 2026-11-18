-- Draft/ThetaNotch2Main.lean -- STAGE 1b: the notch seed `ThetaTiled e f b (M + j f)` with rho = e M - f n > 0 and n1 = n.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
**Theorem N (notch seed family), case `rho > 0`, `n1 = n`**: L + U (T2 region at M with the two rho-pieces) + (Rh minus (en)tau) +
notch `(fn)tau`.  Hand proof `internal working notes` 2.1; generator `rust/audit_notch_20261114`.
CREDIT: Paliy (annulus / band steps on a seed), Beeson (the 48-tile seed for the tile `(2,3,4)`), Laczkovich (Lemma 2.2), Zhang,
Beeson-Rosu (skew frame), the unit theta step `ThetaUnitStep` (this project).  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch2Ass

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.DebtB (sqf hasSides_triC_base hasSides_triC_o1 hasSides_triC_o2)
open Erdos634.Draft.ThetaUnit (ThetaTiled mrow_hasSides)
open Erdos634.Draft.S2L (vol_triC)

namespace NP2
variable (P : NP2)

/-- the four group counts add up to `b t^2`, `t = M + j f` (uses `e M = f n + rho`) -/
theorem total_count2 :
    P.b * (P.s * P.s - P.n0N * P.n0N) +
      (P.vN * P.vN + (P.gnN * P.gnN - (P.gnN - P.e) * (P.gnN - P.e)) + 2 * P.f * P.gnN + P.rho * P.rho + 2 * (P.f - P.rho) * P.rho)
      + (2 * P.ppN * (P.qqN - P.enN) + 2 * (P.ppN - P.enN) * P.enN + P.enN * P.enN) + P.fnN * P.fnN
      = P.b * (P.M + P.j * P.f) * (P.M + P.j * P.f) := by
  have hn0s : P.n0N ≤ P.s := by unfold n0N; omega
  have h1 : P.n0N * P.n0N ≤ P.s * P.s := Nat.mul_self_le_mul_self hn0s
  have h2 : (P.gnN - P.e) * (P.gnN - P.e) ≤ P.gnN * P.gnN := Nat.mul_self_le_mul_self (Nat.sub_le _ _)
  have h3 := P.hen_q
  have h4 := P.hen_p
  have hn0c : (P.n0N : ℤ) = (P.s : ℤ) - (P.j : ℤ) * P.f := by
    unfold n0N; rw [Nat.cast_sub P.hks.le]; push_cast; ring
  have hvc : (P.vN : ℤ) = (P.f : ℤ) * P.M - (P.e : ℤ) * P.n - P.e := by
    unfold vN; rw [Nat.cast_sub P.vle]; push_cast; ring
  have hgnc : (P.gnN : ℤ) = (P.g : ℤ) * P.n := by unfold gnN; push_cast; ring
  have henc : (P.enN : ℤ) = (P.e : ℤ) * P.n := by unfold enN; push_cast; ring
  have hppc : (P.ppN : ℤ) = ((P.M : ℤ) + P.j * P.f - P.s) * P.f := by
    unfold ppN; rw [Nat.cast_mul, Nat.cast_sub P.hst.le]; push_cast; ring
  have hqqc : (P.qqN : ℤ) = (P.j : ℤ) * P.b := by unfold qqN; push_cast; ring
  have hfnc : (P.fnN : ℤ) = (P.f : ℤ) * P.n := by unfold fnN; push_cast; ring
  have hbZ : (P.b : ℤ) = (P.f : ℤ) * P.f - (P.e : ℤ) * P.e := by
    have : ((P.f * P.f : ℕ) : ℤ) = ((P.e * P.e + P.b : ℕ) : ℤ) := by rw [P.hb]
    push_cast at this; linarith
  have hgZ : (P.g : ℤ) = (P.f : ℤ) - P.e := by
    have : (P.f : ℤ) = P.e + P.g := by exact_mod_cast P.hfg
    linarith
  have hrZ : (P.e : ℤ) * P.M = (P.f : ℤ) * P.n + P.rho := by exact_mod_cast P.hrho
  have hge := P.hge
  have hfr := P.frho
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub h4, Nat.cast_sub hge, Nat.cast_sub hfr]
  rw [hn0c, hvc, hgnc, henc, hppc, hqqc, hfnc]
  have : (P.gnN : ℤ) - P.e = (P.g : ℤ) * P.n - P.e := by rw [hgnc]
  rw [hbZ, hgZ]
  linear_combination ((P.e : ℤ) * P.M - P.f * P.n + P.rho - 2 * P.f) * hrZ

end NP2

namespace NP2
variable (P : NP2)

theorem tpos2 : (0 : ℝ) < (P.M : ℝ) + P.j * P.f := by
  have H := P.rh
  have H := P.rh
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  positivity

theorem tgt_det2 : ((cH (P.e : ℝ) P.f P.s (0, 0)).1 - (cH (P.e : ℝ) P.f P.s ((P.M : ℝ) + P.j * P.f, 0)).1) *
      ((cH (P.e : ℝ) P.f P.s (0, (P.M : ℝ) + P.j * P.f)).2 - (cH (P.e : ℝ) P.f P.s ((P.M : ℝ) + P.j * P.f, 0)).2) -
    ((cH (P.e : ℝ) P.f P.s (0, (P.M : ℝ) + P.j * P.f)).1 - (cH (P.e : ℝ) P.f P.s ((P.M : ℝ) + P.j * P.f, 0)).1) *
      ((cH (P.e : ℝ) P.f P.s (0, 0)).2 - (cH (P.e : ℝ) P.f P.s ((P.M : ℝ) + P.j * P.f, 0)).2) ≠ 0 := by
  have H := P.rh
  have ht := P.tpos2
  refine det_cH_ne (P.s : ℝ) H.hE H.hEF _ _ _ ?_
  simp only
  intro h
  nlinarith [mul_pos ht ht]

/-- the target `theta_t`, `t = f (m + j)`: apex `(0,0)`, base vertices `(t,0)`, `(0,t)` -/
def tgtTri2 {φ : ℝ} (hφ : 1 < φ) : Erdos634.Geometry.Tri :=
  triC φ hφ (cH (P.e : ℝ) P.f P.s ((P.M : ℝ) + P.j * P.f, 0)) (cH (P.e : ℝ) P.f P.s (0, 0))
    (cH (P.e : ℝ) P.f P.s (0, (P.M : ℝ) + P.j * P.f)) P.tgt_det2

theorem tgt_hasSides2 {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e) :
    HasSides (P.tgtTri2 hφ) (((P.M + P.j * P.f : ℕ) : ℝ) * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) * P.f)
      (((P.M + P.j * P.f : ℕ) : ℝ) * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) * P.f)
      (((P.M + P.j * P.f : ℕ) : ℝ) * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) * P.e) := by
  have H := P.rh
  have hE := H.hE
  have hEF := H.hEF
  obtain ⟨hF, hB, -⟩ := H.pos
  have ht := P.tpos2
  have hc : (((P.M + P.j * P.f : ℕ) : ℝ)) = (P.M : ℝ) + P.j * P.f := by push_cast; ring
  rw [hc]
  refine hasSides_triC_o2 hφ _ _ _ P.tgt_det2 (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
  · rw [sqf_cH (P.s : ℝ) hE hEF hφE]; simp only [qf]; ring
  · rw [sqf_cH (P.s : ℝ) hE hEF hφE]; simp only [qf]; ring
  · rw [sqf_cH (P.s : ℝ) hE hEF hφE]; simp only [qf]; ring

end NP2

namespace NP2
variable (P : NP2)

open MeasureTheory in
/-- **the notch seed as a region tiling** (case `rho = 0`) -/
theorem notch1_rtiling {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e) :
    Nonempty (RTiling (P.tgtTri2 hφ).carrier (Mrow hφ P.e P.f P.he0 P.hef) (P.b * ((P.M + P.j * P.f)) * ((P.M + P.j * P.f)))) := by
  have H := P.rh
  have hE := H.hE
  have hEF := H.hEF
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have ht := P.tpos2
  have hks := H.hks
  have hst := H.hst
  have hj := H.hj
  set T := P.tgtTri2 hφ with hTdef
  have tgt_car : T.carrier = Phi φ '' convexHull ℝ ({cH (P.e : ℝ) P.f P.s ((P.M : ℝ) + P.j * P.f, 0),
      cH (P.e : ℝ) P.f P.s (0, 0), cH (P.e : ℝ) P.f P.s (0, (P.M : ℝ) + P.j * P.f)} : Set (ℝ × ℝ)) := carrier_triC _ _ _ _ _ _
  set M := Mrow hφ P.e P.f P.he0 P.hef with hMdef
  let S : Fin 4 → Set Plane := ![Phi φ '' slReg (P.e : ℝ) P.f P.j P.s, Phi φ '' su2Reg (P.e : ℝ) P.f P.M P.n P.j P.s,
    Phi φ '' rReg2 (P.e : ℝ) P.f P.M P.n P.j P.s, Phi φ '' n2Reg (P.e : ℝ) P.f P.M P.n P.j P.s]
  let cnt : Fin 4 → ℕ := ![P.b * (P.s * P.s - P.n0N * P.n0N),
    P.vN * P.vN + (P.gnN * P.gnN - (P.gnN - P.e) * (P.gnN - P.e)) + 2 * P.f * P.gnN + P.rho * P.rho + 2 * (P.f - P.rho) * P.rho,
    2 * P.ppN * (P.qqN - P.enN) + 2 * (P.ppN - P.enN) * P.enN + P.enN * P.enN, P.fnN * P.fnN]
  let Rf : ∀ a : Fin 4, TFam (S a) M (cnt a) := fun a => match a with
    | ⟨0, _⟩ => P.lFam2 hφ hφE
    | ⟨1, _⟩ => P.uFam2 hφ hφE
    | ⟨2, _⟩ => P.rFam2 hφ hφE
    | ⟨3, _⟩ => P.n2Fam hφ hφE
    | ⟨k + 4, h⟩ => absurd h (by omega)
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := n2_facts H.toR
  -- disjointness of the four groups
  have dLU : Disjoint (interior (Phi φ '' slReg (P.e : ℝ) P.f P.j P.s)) (interior (Phi φ '' su2Reg (P.e : ℝ) P.f P.M P.n P.j P.s)) :=
    disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inr one_ne_zero) (by norm_num) rfl rfl
      (fun p hp => hp.2.2.1) (fun p hp => hp.2.1))
  have dLR : Disjoint (interior (Phi φ '' slReg (P.e : ℝ) P.f P.j P.s)) (interior (Phi φ '' rReg2 (P.e : ℝ) P.f P.M P.n P.j P.s)) :=
    disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl one_ne_zero) (by norm_num) (by norm_num) rfl
      (fun p hp => hp.2.2.2) (fun p hp => hp.2.2.1))
  have dLN : Disjoint (interior (Phi φ '' slReg (P.e : ℝ) P.f P.j P.s)) (interior (Phi φ '' n2Reg (P.e : ℝ) P.f P.M P.n P.j P.s)) :=
    disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl one_ne_zero) (by norm_num) (by norm_num) rfl
      (fun p hp => hp.2.2.2) n3)
  have dUR : Disjoint (interior (Phi φ '' su2Reg (P.e : ℝ) P.f P.M P.n P.j P.s)) (interior (Phi φ '' rReg2 (P.e : ℝ) P.f P.M P.n P.j P.s)) :=
    disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inr (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
      (fun p hp => hp.2.1) (fun p hp => hp.2.1))
  have dUN : Disjoint (interior (Phi φ '' su2Reg (P.e : ℝ) P.f P.M P.n P.j P.s)) (interior (Phi φ '' n2Reg (P.e : ℝ) P.f P.M P.n P.j P.s)) :=
    disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by positivity)) rfl rfl rfl (fun p hp => hp.2.2.1) n5)
  have dRN : Disjoint (interior (Phi φ '' rReg2 (P.e : ℝ) P.f P.M P.n P.j P.s)) (interior (Phi φ '' n2Reg (P.e : ℝ) P.f P.M P.n P.j P.s)) :=
    disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by positivity)) rfl rfl rfl (fun p hp => hp.2.2.2.2) n6)
  have hSd : ∀ a c : Fin 4, a ≠ c → Disjoint (interior (S a)) (interior (S c)) := by
    intro a c hac
    fin_cases a <;> fin_cases c <;>
      first
        | exact absurd rfl hac
        | exact dLU | exact dLU.symm | exact dLR | exact dLR.symm | exact dLN | exact dLN.symm
        | exact dUR | exact dUR.symm | exact dUN | exact dUN.symm | exact dRN | exact dRN.symm
  -- containment in the target
  have hsubL : S ⟨0, by omega⟩ ⊆ T.carrier := by
    rw [tgt_car]
    refine Set.image_mono (fun p hp => mem_tgt (P.s : ℝ) _ hE hEF ht p ?_ ?_ ?_)
    · have := hp.1; linarith
    · have := hp.2.1; linarith
    · have := hp.2.2.2; linarith
  have hsubU : S ⟨1, by omega⟩ ⊆ T.carrier := by
    rw [tgt_car]
    refine Set.image_mono (fun p hp => mem_tgt (P.s : ℝ) _ hE hEF ht p ?_ ?_ ?_)
    · have := hp.1; linarith
    · have := hp.2.1; have : 0 ≤ (P.j : ℝ) * P.f := by positivity
      linarith
    · have := hp.2.2.2; linarith
  have hsubR : S ⟨2, by omega⟩ ⊆ T.carrier := by
    rw [tgt_car]
    refine Set.image_mono (fun p hp => mem_tgt (P.s : ℝ) _ hE hEF ht p ?_ ?_ ?_)
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hp; linarith
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hp; linarith
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hp; linarith
  have hsubN : S ⟨3, by omega⟩ ⊆ T.carrier := by
    rw [tgt_car]
    refine Set.image_mono (fun p hp => mem_tgt (P.s : ℝ) _ hE hEF ht p ?_ ?_ ?_)
    · have := n1 p hp; linarith
    · have := n2 p hp; linarith
    · have := n4 p hp; linarith
  have hsub : ∀ a, S a ⊆ T.carrier := by
    intro a; fin_cases a
    · exact hsubL
    · exact hsubU
    · exact hsubR
    · exact hsubN
  have hsum : (∑ a, cnt a) = P.b * ((P.M + P.j * P.f)) * ((P.M + P.j * P.f)) := by
    have := P.total_count2
    simpa [Fin.sum_univ_four, cnt] using this
  obtain ⟨hb0, ha0, hc0⟩ := pos_facts hE hEF
  have hbR := P.hbR
  have hMeq : M = brickL φ hφ ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ((P.e : ℝ) * P.f) hb0 ha0 := rfl
  have hvol : ((∑ a, cnt a : ℕ) : ENNReal) * volume M.carrier = volume T.carrier := by
    have hs := sD_pos hφ
    have hφ0 : 0 < φ := by linarith
    have hM : volume M.carrier = ENNReal.ofReal (sD φ / (2 * φ) * (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) * ((P.e : ℝ) * P.f)))
        * volume Erdos634.AreaDet.stdCarrier := by
      rw [hMeq]; unfold brickL; rw [vol_triC]; congr 2
      rw [← abs_of_pos (show 0 < sD φ / (2 * φ) * (((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) * ((P.e : ℝ) * P.f)) from
        mul_pos (div_pos hs (by linarith)) (mul_pos hb0 ha0))]
      congr 1; simp only []; ring
    have hT : volume T.carrier = ENNReal.ofReal (sD φ / (2 * φ) * ((P.f : ℝ) * P.e * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2 *
        (((P.M : ℝ) + P.j * P.f) ^ 2))) * volume Erdos634.AreaDet.stdCarrier := by
      rw [hTdef]; unfold tgtTri2; rw [vol_triC]; congr 2
      rw [det_cH (P.s : ℝ) hE hEF]
      have e1 : sD φ / (2 * φ) * ((P.f : ℝ) * P.e * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2 *
          ((0 - ((P.M : ℝ) + P.j * P.f)) * ((P.M : ℝ) + P.j * P.f - 0) - (0 - ((P.M : ℝ) + P.j * P.f)) * (0 - 0)))
          = -(sD φ / (2 * φ) * ((P.f : ℝ) * P.e * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2 * (((P.M : ℝ) + P.j * P.f) ^ 2))) := by ring
      simp only []
      rw [e1, abs_neg, abs_of_pos]
      exact mul_pos (div_pos hs (by linarith)) (by positivity)
    rw [hM, hT, hsum, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 2
    push_cast
    rw [hbR]; ring
  obtain ⟨D, hDm, hDt⟩ := pack_exists' (M := M) (T := T) S cnt Rf hSd hsub hvol
  have key : ∀ N : ℕ, N = P.b * ((P.M + P.j * P.f)) * ((P.M + P.j * P.f)) → ∀ D : CongruentDissection N, D.model = M →
      D.target = T → Nonempty (RTiling T.carrier M (P.b * ((P.M + P.j * P.f)) * ((P.M + P.j * P.f)))) := by
    rintro N rfl D hm ht
    exact ⟨{ tile := D.tile
             covers := D.covers.trans (by rw [ht])
             disj := D.interiors_disjoint
             cong := fun i => by have := D.tiles_congruent i; rwa [hm] at this }⟩
  exact key _ hsum D hDm hDt

end NP2


/-- **STAGE 1b (Theorem N, notch seed, case `rho > 0`, `n1 = n`).**  For every parameter set `P : NP2`,
`theta_t(e,f)` is tiled by the tile `(e f, b, f^2)` with `t = M + j f`:
`ThetaTiled P.e P.f P.b (P.M + P.j * P.f)`. -/
theorem thetaTiled_notch1 (P : NP2) : ThetaTiled P.e P.f P.b (P.M + P.j * P.f) := by
  have hE : (0 : ℝ) < P.e := by exact_mod_cast P.he0
  have hφ : 1 < (P.f : ℝ) / P.e := by rw [lt_div_iff₀ hE]; linarith [P.hEF]
  obtain ⟨R⟩ := P.notch1_rtiling hφ rfl
  exact ⟨toCD R, P.tgt_hasSides2 hφ rfl, mrow_hasSides hφ P.e P.f P.he0 P.hef rfl⟩

end

end Erdos634.Draft.ThetaNotch
