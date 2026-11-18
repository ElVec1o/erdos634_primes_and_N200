-- Draft/ThetaNotchMain.lean -- STAGE 1a: the notch seed `ThetaTiled e f b (f (m + j))` (case rho = 0, i.e. `e M = f n`).
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
**Theorem N (notch seed family), case `rho = 0`**, formalised as new leaf files `ThetaNotch*.lean`.
Hand proof: `internal working notes` section 2.1 (pieces L, U, Rh minus corner, notch (fn)tau);
exact generator `rust/audit_notch_20261114` (the specification of the pieces).
CREDIT: Paliy (annulus / band steps on a seed; the seed method), Beeson (the 48-tile seed for the tile `(2,3,4)`), Laczkovich
(Lemma 2.2), Zhang (the families), Beeson-Rosu (skew frame), the unit theta step `ThetaUnitStep` (T1, this project).
INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchAss

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

theorem sqf_cH {E F : ℝ} (s : ℝ) (hE : 0 < E) (hEF : E < F) {φ : ℝ} (hφE : φ = F / E) (p q : ℝ × ℝ) :
    sqf φ (cH E F s p) (cH E F s q) = qf E F p q := by
  obtain ⟨hF, hb⟩ := frame_pos hE hEF
  subst hφE
  simp only [sqf, qf, cH]
  field_simp
  ring

/-- the image of an apex point of the triangle lies in the hull of the three vertices -/
theorem mem_tgt_apex {E F : ℝ} (s t : ℝ) (ht : 0 < t) (q : ℝ × ℝ) (h1 : 0 ≤ q.1) (h2 : 0 ≤ q.2) (h3 : q.1 + q.2 ≤ t) :
    cH E F s q ∈ convexHull ℝ ({cH E F s (t, 0), cH E F s (0, 0), cH E F s (0, t)} : Set (ℝ × ℝ)) := by
  refine Erdos634.Draft.S2L.mem_hull3 (q.1 / t) ((t - q.1 - q.2) / t) (q.2 / t)
    (by positivity) (div_nonneg (by linarith) ht.le) (by positivity) (by field_simp; ring) _ ?_ ?_
  · simp only [cH]; field_simp; ring
  · simp only [cH]; field_simp; ring

/-- a point of the skew frame with apex coordinates in the triangle lies in the hull of the three vertices -/
theorem mem_tgt {E F : ℝ} (s t : ℝ) (hE : 0 < E) (hEF : E < F) (ht : 0 < t) (p : ℝ × ℝ) (h1 : 0 ≤ ax E F p) (h2 : 0 ≤ ay E F s p)
    (h3 : ax E F p + ay E F s p ≤ t) :
    p ∈ convexHull ℝ ({cH E F s (t, 0), cH E F s (0, 0), cH E F s (0, t)} : Set (ℝ × ℝ)) := by
  have := mem_tgt_apex (E := E) (F := F) s t ht (ax E F p, ay E F s p) h1 h2 h3
  rwa [cH_ax_ay s hE hEF] at this


namespace NP
variable (P : NP)

/-- the four group counts add up to `b t^2`, `t = f (m + j)` -/
theorem total_count :
    P.b * (P.s * P.s - P.n0 * P.n0) + (P.v * P.v + (P.gn * P.gn - (P.gn - P.e) * (P.gn - P.e)) + 2 * P.f * P.gn)
      + (2 * P.pp * (P.qq - P.en) + 2 * (P.pp - P.en) * P.en + P.en * P.en) + P.fn * P.fn
      = P.b * (P.f * (P.m + P.j)) * (P.f * (P.m + P.j)) := by
  have hn0s : P.n0 ≤ P.s := by unfold n0; omega
  have h1 : P.n0 * P.n0 ≤ P.s * P.s := Nat.mul_self_le_mul_self hn0s
  have h2 : (P.gn - P.e) * (P.gn - P.e) ≤ P.gn * P.gn := Nat.mul_self_le_mul_self (Nat.sub_le _ _)
  have h3 := P.hen_q.le
  have h4 := P.hen_p.le
  have hn0c : (P.n0 : ℤ) = (P.s : ℤ) - (P.j : ℤ) * P.f := by
    unfold n0; rw [Nat.cast_sub P.hks.le]; push_cast; ring
  have hvc : (P.v : ℤ) = (P.b : ℤ) * P.m - P.e := by
    unfold v; rw [Nat.cast_sub P.hbe]; push_cast; ring
  have hgnc : (P.gn : ℤ) = (P.g : ℤ) * (P.e * P.m) := by unfold gn; push_cast; ring
  have henc : (P.en : ℤ) = (P.e : ℤ) * (P.e * P.m) := by unfold en; push_cast; ring
  have hppc : (P.pp : ℤ) = ((P.f : ℤ) * (P.m + P.j) - P.s) * P.f := by
    unfold pp; rw [Nat.cast_mul, Nat.cast_sub P.hst.le]; push_cast; ring
  have hqqc : (P.qq : ℤ) = (P.j : ℤ) * P.b := by unfold qq; push_cast; ring
  have hfnc : (P.fn : ℤ) = (P.f : ℤ) * (P.e * P.m) := by unfold fn; push_cast; ring
  have hbZ : (P.b : ℤ) = (P.f : ℤ) * P.f - (P.e : ℤ) * P.e := by
    have : ((P.f * P.f : ℕ) : ℤ) = ((P.e * P.e + P.b : ℕ) : ℤ) := by rw [P.hb]
    push_cast at this; linarith
  have hgZ : (P.g : ℤ) = (P.f : ℤ) - P.e := by
    have : (P.f : ℤ) = P.e + P.g := by exact_mod_cast P.hfg
    linarith
  have hge := P.hge
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub h4, Nat.cast_sub hge]
  rw [hn0c, hvc, hgnc, henc, hppc, hqqc, hfnc]
  have : (P.gn : ℤ) - P.e = (P.g : ℤ) * (P.e * P.m) - P.e := by rw [hgnc]
  rw [hbZ, hgZ]
  ring

end NP


namespace NP
variable (P : NP)

theorem tpos : (0 : ℝ) < (P.f : ℝ) * (P.m + P.j) := by
  have H := P.rh
  have := H.pos
  have hm := H.hm; have hj := H.hj
  nlinarith [this.1]

theorem tgt_det : ((cH (P.e : ℝ) P.f P.s (0, 0)).1 - (cH (P.e : ℝ) P.f P.s ((P.f : ℝ) * (P.m + P.j), 0)).1) *
      ((cH (P.e : ℝ) P.f P.s (0, (P.f : ℝ) * (P.m + P.j))).2 - (cH (P.e : ℝ) P.f P.s ((P.f : ℝ) * (P.m + P.j), 0)).2) -
    ((cH (P.e : ℝ) P.f P.s (0, (P.f : ℝ) * (P.m + P.j))).1 - (cH (P.e : ℝ) P.f P.s ((P.f : ℝ) * (P.m + P.j), 0)).1) *
      ((cH (P.e : ℝ) P.f P.s (0, 0)).2 - (cH (P.e : ℝ) P.f P.s ((P.f : ℝ) * (P.m + P.j), 0)).2) ≠ 0 := by
  have H := P.rh
  have ht := P.tpos
  refine det_cH_ne (P.s : ℝ) H.hE H.hEF _ _ _ ?_
  simp only
  intro h
  nlinarith [mul_pos ht ht]

/-- the target `theta_t`, `t = f (m + j)`: apex `(0,0)`, base vertices `(t,0)`, `(0,t)` -/
def tgtTri {φ : ℝ} (hφ : 1 < φ) : Erdos634.Geometry.Tri :=
  triC φ hφ (cH (P.e : ℝ) P.f P.s ((P.f : ℝ) * (P.m + P.j), 0)) (cH (P.e : ℝ) P.f P.s (0, 0))
    (cH (P.e : ℝ) P.f P.s (0, (P.f : ℝ) * (P.m + P.j))) P.tgt_det

theorem tgt_hasSides {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e) :
    HasSides (P.tgtTri hφ) (((P.f * (P.m + P.j) : ℕ) : ℝ) * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) * P.f)
      (((P.f * (P.m + P.j) : ℕ) : ℝ) * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) * P.f)
      (((P.f * (P.m + P.j) : ℕ) : ℝ) * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) * P.e) := by
  have H := P.rh
  have hE := H.hE
  have hEF := H.hEF
  obtain ⟨hF, hB, -⟩ := H.pos
  have ht := P.tpos
  have hc : (((P.f * (P.m + P.j) : ℕ) : ℝ)) = (P.f : ℝ) * (P.m + P.j) := by push_cast; ring
  rw [hc]
  refine hasSides_triC_o2 hφ _ _ _ P.tgt_det (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
  · rw [sqf_cH (P.s : ℝ) hE hEF hφE]; simp only [qf]; ring
  · rw [sqf_cH (P.s : ℝ) hE hEF hφE]; simp only [qf]; ring
  · rw [sqf_cH (P.s : ℝ) hE hEF hφE]; simp only [qf]; ring

end NP


namespace NP
variable (P : NP)

open MeasureTheory in
/-- **the notch seed as a region tiling** (case `rho = 0`) -/
theorem notch0_rtiling {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e) :
    Nonempty (RTiling (P.tgtTri hφ).carrier (Mrow hφ P.e P.f P.he0 P.hef) (P.b * (P.f * (P.m + P.j)) * (P.f * (P.m + P.j)))) := by
  have H := P.rh
  have hE := H.hE
  have hEF := H.hEF
  obtain ⟨hF, hB, hEF', hv, hm0, hj0⟩ := H.pos
  have ht := P.tpos
  have hks := H.hks
  have hst := H.hst
  have hm := H.hm
  have hj := H.hj
  set T := P.tgtTri hφ with hTdef
  have tgt_car : T.carrier = Phi φ '' convexHull ℝ ({cH (P.e : ℝ) P.f P.s ((P.f : ℝ) * (P.m + P.j), 0),
      cH (P.e : ℝ) P.f P.s (0, 0), cH (P.e : ℝ) P.f P.s (0, (P.f : ℝ) * (P.m + P.j))} : Set (ℝ × ℝ)) := carrier_triC _ _ _ _ _ _
  set M := Mrow hφ P.e P.f P.he0 P.hef with hMdef
  let S : Fin 4 → Set Plane := ![Phi φ '' slReg (P.e : ℝ) P.f P.j P.s, Phi φ '' suReg (P.e : ℝ) P.f P.m P.j P.s,
    Phi φ '' rReg (P.e : ℝ) P.f P.m P.j P.s, Phi φ '' nReg (P.e : ℝ) P.f P.m P.j P.s]
  let cnt : Fin 4 → ℕ := ![P.b * (P.s * P.s - P.n0 * P.n0),
    P.v * P.v + (P.gn * P.gn - (P.gn - P.e) * (P.gn - P.e)) + 2 * P.f * P.gn,
    2 * P.pp * (P.qq - P.en) + 2 * (P.pp - P.en) * P.en + P.en * P.en, P.fn * P.fn]
  let Rf : ∀ a : Fin 4, TFam (S a) M (cnt a) := fun a => match a with
    | ⟨0, _⟩ => P.lFam hφ hφE
    | ⟨1, _⟩ => P.uFam hφ hφE
    | ⟨2, _⟩ => P.rFam hφ hφE
    | ⟨3, _⟩ => P.nFam hφ hφE
    | ⟨k + 4, h⟩ => absurd h (by omega)
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := n_facts H
  -- disjointness of the four groups
  have dLU : Disjoint (interior (Phi φ '' slReg (P.e : ℝ) P.f P.j P.s)) (interior (Phi φ '' suReg (P.e : ℝ) P.f P.m P.j P.s)) :=
    disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inr one_ne_zero) (by norm_num) rfl rfl
      (fun p hp => hp.2.2.1) (fun p hp => hp.2.1))
  have dLR : Disjoint (interior (Phi φ '' slReg (P.e : ℝ) P.f P.j P.s)) (interior (Phi φ '' rReg (P.e : ℝ) P.f P.m P.j P.s)) :=
    disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl one_ne_zero) (by norm_num) (by norm_num) rfl
      (fun p hp => hp.2.2.2) (fun p hp => hp.2.2.1))
  have dLN : Disjoint (interior (Phi φ '' slReg (P.e : ℝ) P.f P.j P.s)) (interior (Phi φ '' nReg (P.e : ℝ) P.f P.m P.j P.s)) :=
    disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl one_ne_zero) (by norm_num) (by norm_num) rfl
      (fun p hp => hp.2.2.2) n3)
  have dUR : Disjoint (interior (Phi φ '' suReg (P.e : ℝ) P.f P.m P.j P.s)) (interior (Phi φ '' rReg (P.e : ℝ) P.f P.m P.j P.s)) :=
    disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inr (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
      (fun p hp => hp.2.1) (fun p hp => hp.2.1))
  have dUN : Disjoint (interior (Phi φ '' suReg (P.e : ℝ) P.f P.m P.j P.s)) (interior (Phi φ '' nReg (P.e : ℝ) P.f P.m P.j P.s)) :=
    disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by positivity)) rfl rfl rfl (fun p hp => hp.2.2) n5)
  have dRN : Disjoint (interior (Phi φ '' rReg (P.e : ℝ) P.f P.m P.j P.s)) (interior (Phi φ '' nReg (P.e : ℝ) P.f P.m P.j P.s)) :=
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
    · obtain ⟨hx, hy, hu⟩ := hp
      by_contra hc; push_neg at hc
      have hx0 : 0 ≤ ax (P.e : ℝ) P.f p := by linarith
      nlinarith [mul_pos hB (sub_pos.2 hc), mul_nonneg (sq_nonneg (P.e : ℝ)) hx0]
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
  have hsum : (∑ a, cnt a) = P.b * (P.f * (P.m + P.j)) * (P.f * (P.m + P.j)) := by
    have := P.total_count
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
        (((P.f : ℝ) * (P.m + P.j)) ^ 2))) * volume Erdos634.AreaDet.stdCarrier := by
      rw [hTdef]; unfold tgtTri; rw [vol_triC]; congr 2
      rw [det_cH (P.s : ℝ) hE hEF]
      have e1 : sD φ / (2 * φ) * ((P.f : ℝ) * P.e * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2 *
          ((0 - (P.f : ℝ) * (P.m + P.j)) * ((P.f : ℝ) * (P.m + P.j) - 0) - (0 - (P.f : ℝ) * (P.m + P.j)) * (0 - 0)))
          = -(sD φ / (2 * φ) * ((P.f : ℝ) * P.e * ((P.f : ℝ) ^ 2 - (P.e : ℝ) ^ 2) ^ 2 * (((P.f : ℝ) * (P.m + P.j)) ^ 2))) := by ring
      simp only []
      rw [e1, abs_neg, abs_of_pos]
      exact mul_pos (div_pos hs (by linarith)) (by positivity)
    rw [hM, hT, hsum, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 2
    push_cast
    rw [hbR]; ring
  obtain ⟨D, hDm, hDt⟩ := pack_exists' (M := M) (T := T) S cnt Rf hSd hsub hvol
  have key : ∀ N : ℕ, N = P.b * (P.f * (P.m + P.j)) * (P.f * (P.m + P.j)) → ∀ D : CongruentDissection N, D.model = M →
      D.target = T → Nonempty (RTiling T.carrier M (P.b * (P.f * (P.m + P.j)) * (P.f * (P.m + P.j)))) := by
    rintro N rfl D hm ht
    exact ⟨{ tile := D.tile
             covers := D.covers.trans (by rw [ht])
             disj := D.interiors_disjoint
             cong := fun i => by have := D.tiles_congruent i; rwa [hm] at this }⟩
  exact key _ hsum D hDm hDt

end NP


/-- **STAGE 1a (Theorem N, notch seed, case `rho = 0`).**  For every parameter set `P : NP`,
`theta_t(e,f)` is tiled by the tile `(e f, b, f^2)` with `t = f (m + j)`:
`ThetaTiled P.e P.f P.b (P.f * (P.m + P.j))`. -/
theorem thetaTiled_notch0 (P : NP) : ThetaTiled P.e P.f P.b (P.f * (P.m + P.j)) := by
  have hE : (0 : ℝ) < P.e := by exact_mod_cast P.he0
  have hφ : 1 < (P.f : ℝ) / P.e := by rw [lt_div_iff₀ hE]; linarith [P.hEF]
  obtain ⟨R⟩ := P.notch0_rtiling hφ rfl
  exact ⟨toCD R, P.tgt_hasSides hφ rfl, mrow_hasSides hφ P.e P.f P.he0 P.hef rfl⟩

end

end Erdos634.Draft.ThetaNotch
