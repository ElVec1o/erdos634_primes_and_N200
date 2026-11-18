-- Draft/ThetaNotch2Ass.lean -- STAGE 1b: group families (L, U with rho-pieces, R) and group regions of the notch seed with rho > 0, n1 = n.
-- INTERNAL BUILD ONLY, UNAUDITED (reading audit 2026-11-14, SOUND WITH GAPS, internal audit).  No sorry, no native_decide.
/-
Credit: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch2Fam

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.ThetaUnit (gg)

theorem LF.mono {E F s : ℝ} {S : Set (ℝ × ℝ)} {al be ga ga' : ℝ} (h : LF E F s S al be ga) (hg : ga ≤ ga') : LF E F s S al be ga' :=
  fun p hp => le_trans (h p hp) hg

def TFam.join5 {M : Erdos634.Geometry.Tri} {S S1 S2 S3 S4 S5 : Set Plane} {n1 n2 n3 n4 n5 : ℕ} (R1 : TFam S1 M n1) (R2 : TFam S2 M n2)
    (R3 : TFam S3 M n3) (R4 : TFam S4 M n4) (R5 : TFam S5 M n5) (h1 : S1 ⊆ S) (h2 : S2 ⊆ S) (h3 : S3 ⊆ S) (h4 : S4 ⊆ S) (h5 : S5 ⊆ S)
    (d12 : Disjoint (interior S1) (interior S2)) (d13 : Disjoint (interior S1) (interior S3)) (d14 : Disjoint (interior S1) (interior S4))
    (d15 : Disjoint (interior S1) (interior S5)) (d23 : Disjoint (interior S2) (interior S3)) (d24 : Disjoint (interior S2) (interior S4))
    (d25 : Disjoint (interior S2) (interior S5)) (d34 : Disjoint (interior S3) (interior S4)) (d35 : Disjoint (interior S3) (interior S5))
    (d45 : Disjoint (interior S4) (interior S5)) :
    TFam S M (n1 + n2 + n3 + n4 + n5) :=
  castTF rfl (by simp [Fin.sum_univ_five]) (TFam.join (m := 5) S ![S1, S2, S3, S4, S5] ![n1, n2, n3, n4, n5]
    (fun a => match a with | ⟨0, _⟩ => R1 | ⟨1, _⟩ => R2 | ⟨2, _⟩ => R3 | ⟨3, _⟩ => R4 | ⟨4, _⟩ => R5 | ⟨k + 5, h⟩ => absurd h (by omega))
    (fun a => by fin_cases a <;> assumption)
    (fun a b hab => by
      fin_cases a <;> fin_cases b <;>
        first | exact absurd rfl hab | exact d12 | exact d12.symm | exact d13 | exact d13.symm | exact d14 | exact d14.symm | exact d15 | exact d15.symm | exact d23 | exact d23.symm | exact d24 | exact d24.symm | exact d25 | exact d25.symm | exact d34 | exact d34.symm | exact d35 | exact d35.symm | exact d45 | exact d45.symm)) 
/-- the region of the U group: the convex quadrilateral `D, W, Q', V2` -/
def su2Reg (E F M n j s : ℝ) : Set (ℝ × ℝ) :=
  {p | (-1) * ax E F p + 0 * ay E F s p ≤ 0 ∧ 0 * ax E F p + (-1) * ay E F s p ≤ -(j * F) ∧
    F ^ 2 * ax E F p + (F ^ 2 - E ^ 2) * ay E F s p ≤ c0f E F M n j ∧ 1 * ax E F p + 1 * ay E F s p ≤ M + j * F}

def rReg2 (E F M n j s : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 * ax E F p + (-1) * ay E F s p ≤ 0 ∧ 0 * ax E F p + 1 * ay E F s p ≤ j * F ∧
    (-1) * ax E F p + (-1) * ay E F s p ≤ -s ∧ 1 * ax E F p + 1 * ay E F s p ≤ M + j * F ∧
    F ^ 2 * ax E F p + (2 * F ^ 2 - E ^ 2) * ay E F s p ≤ c5f E F M n j}

namespace NP2
variable (P : NP2)

def n0N : ℕ := P.s - P.j * P.f
def kkN : ℕ := P.j * P.f

theorem n0_add : P.n0N + P.kkN = P.s := by
  unfold n0N kkN; have := P.hks; omega

theorem hgn0 : P.e ≤ (P.f - P.e) * P.n0N := by
  have hD := P.hD
  have h1 : P.f - P.e = P.g := by have := P.hfg; omega
  rw [h1]
  have h2 := P.n0_add
  unfold kkN at h2
  have : P.g * P.s = P.g * P.n0N + P.g * (P.j * P.f) := by rw [← Nat.mul_add, ← h2]
  omega

theorem strip_hg (i : ℕ) : P.e ≤ (P.f - P.e) * (P.n0N + i) := by
  have := P.hgn0
  calc P.e ≤ (P.f - P.e) * P.n0N := this
    _ ≤ (P.f - P.e) * (P.n0N + i) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

theorem sum_strips2 (k : ℕ) (n0 : ℕ) : (∑ i : Fin k, P.b * (2 * (n0 + (i : ℕ)) + 1)) = P.b * ((n0 + k) * (n0 + k) - n0 * n0) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => P.b * (2 * (n0 + i) + 1)) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : n0 * n0 ≤ (n0 + k) * (n0 + k) := Nat.mul_self_le_mul_self (Nat.le_add_right _ _)
    have h2 : n0 * n0 ≤ (n0 + (k + 1)) * (n0 + (k + 1)) := Nat.mul_self_le_mul_self (Nat.le_add_right _ _)
    apply Nat.cast_injective (R := ℤ)
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring

section lf
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- **the L group**: `k` unit theta strips tile `{y <= k, x + y <= s}`, `b (s^2 - (s-k)^2)` tiles -/
def lFam2 : TFam (Phi φ '' slReg (P.e : ℝ) P.f P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.b * (P.s * P.s - P.n0N * P.n0N)) := by
  have H := P.rh
  have hE := H.hE
  have hEF := H.hEF
  let R : ∀ i : Fin P.kkN, TFam (Phi φ '' bandReg (P.e : ℝ) P.f (((P.n0N + (i : ℕ) : ℕ) : ℝ))) (Mrow hφ P.e P.f P.he0 P.hef)
      (P.b * (2 * (P.n0N + (i : ℕ)) + 1)) := fun i =>
    castTF rfl (strip_cnt P.e P.f P.b (P.n0N + i) P.hef P.hb (P.strip_hg i)) (stripFam hφ P.e P.f P.b (P.n0N + i) P.he0 P.hef P.hb hφE (P.strip_hg i))
  have hcnt : (∑ i : Fin P.kkN, P.b * (2 * (P.n0N + (i : ℕ)) + 1)) = P.b * (P.s * P.s - P.n0N * P.n0N) := by
    rw [P.sum_strips2 P.kkN P.n0N, P.n0_add]
  refine castTF rfl hcnt (TFam.join (m := P.kkN) (Phi φ '' slReg (P.e : ℝ) P.f P.j P.s)
    (fun i => Phi φ '' bandReg (P.e : ℝ) P.f (((P.n0N + (i : ℕ) : ℕ) : ℝ))) _ R ?_ ?_)
  · intro i
    refine Set.image_mono (band_sub (P.s : ℝ) _ (P.j : ℝ) hE hEF ?_ ?_)
    · have : P.n0N + (i : ℕ) + 1 ≤ P.s := by have := i.2; have := P.n0_add; unfold kkN at *; omega
      exact_mod_cast this
    · have h2 : P.s = P.n0N + P.j * P.f := by have := P.n0_add; unfold kkN at this; omega
      have : (P.s : ℝ) - P.j * P.f ≤ ((P.n0N + (i : ℕ) : ℕ) : ℝ) := by
        have : (P.s : ℝ) = P.n0N + P.j * P.f := by exact_mod_cast h2
        push_cast; have := (Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ ((i : ℕ) : ℝ)); linarith
      exact this
  · intro i j hij
    have hi := i.2; have hj := j.2
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine disjoint_image hφ (bands_disj hE hEF _ _ ?_)
      have : P.n0N + (i : ℕ) + 1 ≤ P.n0N + (j : ℕ) := by omega
      exact_mod_cast this
    · refine (disjoint_image hφ (bands_disj hE hEF _ _ ?_)).symm
      have : P.n0N + (j : ℕ) + 1 ≤ P.n0N + (i : ℕ) := by omega
      exact_mod_cast this

end lf

theorem hMn : (P.n : ℝ) ≤ P.M := by
  have H := P.rh
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have := H.hr0; have := H.hEF; have := H.hE
  nlinarith [mul_pos H.hE hn0]

section ug
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- **the U group**: `v-tau + pi5 + pi4 + rho-tau + rho-par` tile the quadrilateral `D, W, Q', V2` -/
def uFam2 : TFam (Phi φ '' su2Reg (P.e : ℝ) P.f P.M P.n P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef)
    (P.vN * P.vN + (P.gnN * P.gnN - (P.gnN - P.e) * (P.gnN - P.e)) + 2 * P.f * P.gnN + P.rho * P.rho + 2 * (P.f - P.rho) * P.rho) := by
  have H := P.rh
  have hE := H.hE
  have hEF := H.hEF
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  obtain ⟨v1, v2, v3, v4, v5⟩ := vt2_facts (P.s : ℝ) H.toU
  obtain ⟨q1, q2, q3, q4, q5⟩ := p52_facts (P.s : ℝ) H.toU
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := p42_facts (P.s : ℝ) H.toU
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := rt2_facts (P.s : ℝ) H.toU
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := rp2_facts (P.s : ℝ) H.toU
  have hMn := P.hMn
  have hr0 := H.hr0
  have hrE : 0 ≤ ((P.e : ℝ) * P.M - P.f * P.n) / P.e := (div_pos hr0 hE).le
  have hrM : ((P.e : ℝ) * P.M - P.f * P.n) / P.e ≤ P.M - P.n := by
    rw [div_le_iff₀ hE]; nlinarith [H.hEF, hn0]
  have q1' : LF (P.e : ℝ) P.f (P.s : ℝ) (p52Reg (P.e : ℝ) P.f P.M P.n P.j P.s) (-1) 0 (-(((P.e : ℝ) * P.M - P.f * P.n) / P.e)) :=
    q1.mono (by linarith)
  refine TFam.join5 (vt2Fam P hφ hφE) (p52Fam P hφ hφE) (p42Fam P hφ hφE) (rt2Fam P hφ hφE) (rp2Fam P hφ hφE) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Set.image_mono (fun p hp => ⟨v1 p hp, v2 p hp, v3 p hp, v4 p hp⟩)
  · exact Set.image_mono (fun p hp => ⟨by have := q1 p hp; linarith, q2 p hp, q3 p hp, q4 p hp⟩)
  · exact Set.image_mono (fun p hp => ⟨by have := r1 p hp; linarith, r3 p hp, r4 p hp, r5 p hp⟩)
  · exact Set.image_mono (fun p hp => ⟨t1 p hp, t3 p hp, t4 p hp, t5 p hp⟩)
  · exact Set.image_mono (fun p hp => ⟨u1 p hp, u3 p hp, u4 p hp, u5 p hp⟩)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by positivity)) rfl rfl rfl v5 q5)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by positivity)) rfl rfl rfl v5 r6)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by positivity)) rfl rfl rfl v5 t6)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by positivity)) rfl rfl rfl v5 u6)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by norm_num)) (by norm_num) (by norm_num) (by norm_num) q1 r2)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by norm_num)) (by norm_num) (by norm_num) (by norm_num) q1' t2)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by norm_num)) (by norm_num) (by norm_num) (by norm_num) q1' u2)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by norm_num)) (by norm_num) (by norm_num) (by norm_num) r1 t2)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (by norm_num)) (by norm_num) (by norm_num) (by norm_num) r1 u2)
  · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl (neg_ne_zero.mpr (pow_ne_zero 2 hF.ne'))) (neg_neg _).symm (neg_neg _).symm (neg_neg _).symm t7 u7)

end ug

/-- weaken the region of a tile family -/
def TFam.weaken {M : Erdos634.Geometry.Tri} {S S' : Set Plane} {n : ℕ} (R : TFam S M n) (h : S ⊆ S') : TFam S' M n :=
  { tile := R.tile, sub := fun i => (R.sub i).trans h, disj := R.disj, cong := R.cong }

theorem qq_pos_real (hq : ¬ P.qqN = P.enN) : 0 < qR (P.e : ℝ) P.f P.j - P.e * P.n := by
  have : (P.enN : ℝ) < P.qqN := by exact_mod_cast lt_of_le_of_ne P.hen_q (Ne.symm hq)
  rw [P.qqR, P.enR] at this; linarith
theorem pp_pos_real (hp : ¬ P.ppN = P.enN) : 0 < pR2 (P.f : ℝ) P.M P.j P.s - P.e * P.n := by
  have : (P.enN : ℝ) < P.ppN := by exact_mod_cast lt_of_le_of_ne P.hen_p (Ne.symm hp)
  rw [P.ppR, P.enR] at this; linarith

section rg
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE



/-- **the Rh group**: `C1 + C2 + C3` tile the pentagon `Rh minus (en)tau`; `C1` (resp. `C2`) is absent when `q = en` (resp. `p = en`),
i.e. in the equality cases of (b), (c) -/
def rFam2 : TFam (Phi φ '' rReg2 (P.e : ℝ) P.f P.M P.n P.j P.s) (Mrow hφ P.e P.f P.he0 P.hef)
    (2 * P.ppN * (P.qqN - P.enN) + 2 * (P.ppN - P.enN) * P.enN + P.enN * P.enN) := by
  have H := P.rh
  have hE := H.hE
  have hEF := H.hEF
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := c32_facts H.toR
  have s3 : Phi φ '' c32Reg (P.e : ℝ) P.f P.M P.n P.j P.s ⊆ Phi φ '' rReg2 (P.e : ℝ) P.f P.M P.n P.j P.s :=
    Set.image_mono (fun p hp => ⟨c1 p hp, c2 p hp, c3 p hp, c4 p hp, c5 p hp⟩)
  by_cases hq : P.qqN = P.enN
  · by_cases hp : P.ppN = P.enN
    · refine castTF rfl (by rw [hq, hp]; simp) (TFam.weaken (c32Fam P hφ hφE) s3)
    · obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := c22_facts H.toR (P.pp_pos_real hp)
      refine castTF rfl (by rw [hq]; simp) (TFam.join2 (c22Fam P hφ hφE) (c32Fam P hφ hφE) ?_ s3
        (d := disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl one_ne_zero) (by norm_num) (by norm_num) (by norm_num) b7 c7)))
      exact Set.image_mono (fun p hp => ⟨b1 p hp, b2 p hp, b3 p hp, b4 p hp, b5 p hp⟩)
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := c12_facts H.toR (P.qq_pos_real hq)
    by_cases hp : P.ppN = P.enN
    · refine castTF rfl (by rw [hp]; simp) (TFam.join2 (c12Fam P hφ hφE) (c32Fam P hφ hφE) ?_ s3
        (d := disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inr one_ne_zero) (by norm_num) (by norm_num) rfl a6 c6)))
      exact Set.image_mono (fun p hp => ⟨a1 p hp, a2 p hp, a3 p hp, a4 p hp, a5 p hp⟩)
    · obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := c22_facts H.toR (P.pp_pos_real hp)
      refine TFam.join3 (c12Fam P hφ hφE) (c22Fam P hφ hφE) (c32Fam P hφ hφE) ?_ ?_ s3 ?_ ?_ ?_
      · exact Set.image_mono (fun p hp => ⟨a1 p hp, a2 p hp, a3 p hp, a4 p hp, a5 p hp⟩)
      · exact Set.image_mono (fun p hp => ⟨b1 p hp, b2 p hp, b3 p hp, b4 p hp, b5 p hp⟩)
      · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inr one_ne_zero) (by norm_num) (by norm_num) rfl a6 b6)
      · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inr one_ne_zero) (by norm_num) (by norm_num) rfl a6 c6)
      · exact disjoint_image hφ (disjLF (P.s : ℝ) hE hEF (Or.inl one_ne_zero) (by norm_num) (by norm_num) (by norm_num) b7 c7)

end rg


end NP2

end

end Erdos634.Draft.ThetaNotch
