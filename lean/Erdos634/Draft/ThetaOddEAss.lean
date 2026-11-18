-- Draft/ThetaOddEAss.lean -- ODD-E formalization, module 4: group families L (k unit strips), U (at n1) and strip group (n .. n1-1) for NP4; the R group is a hypothesis of the assembly.
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
Copy of `ThetaNotch3Ass` for `NP4` (natural `k` instead of `j f`; the real parameter of the regions is `P.jR = k / f`).
The notch construction is the project's (Bonfioli); the first instance `theta_13(3,4)` was found by computer search on 2026-11-15;
the family proof is `internal working notes`.  Credit as in `ThetaNotch3Ass`: Paliy (band steps on a seed),
Beeson (48-tile seed), Laczkovich, Zhang, Beeson-Rosu (skew frame).  INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddEFam

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.ThetaUnit (gg)

namespace NP4
variable (P : NP4)

def n0N : ℕ := P.s - P.k
def kkN : ℕ := P.k

theorem n0_add : P.n0N + P.kkN = P.s := by
  unfold n0N kkN; have := P.hks; omega

theorem hgn0 : P.e ≤ (P.f - P.e) * P.n0N := by
  have hD := P.hD
  have h1 : P.f - P.e = P.g := by have := P.hfg; omega
  rw [h1]
  have h2 := P.n0_add
  unfold kkN at h2
  have : P.g * P.s = P.g * P.n0N + P.g * P.k := by rw [← Nat.mul_add, ← h2]
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
def lFam2 : TFam (Phi φ '' slReg (P.e : ℝ) P.f P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.b * (P.s * P.s - P.n0N * P.n0N)) := by
  have H := P.rhR
  have hE := H.hE
  have hEF := H.hEF
  let R : ∀ i : Fin P.kkN, TFam (Phi φ '' bandReg (P.e : ℝ) P.f (((P.n0N + (i : ℕ) : ℕ) : ℝ))) (Mrow hφ P.e P.f P.he0 P.hef)
      (P.b * (2 * (P.n0N + (i : ℕ)) + 1)) := fun i =>
    castTF rfl (strip_cnt P.e P.f P.b (P.n0N + i) P.hef P.hb (P.strip_hg i)) (stripFam hφ P.e P.f P.b (P.n0N + i) P.he0 P.hef P.hb hφE (P.strip_hg i))
  have hcnt : (∑ i : Fin P.kkN, P.b * (2 * (P.n0N + (i : ℕ)) + 1)) = P.b * (P.s * P.s - P.n0N * P.n0N) := by
    rw [P.sum_strips2 P.kkN P.n0N, P.n0_add]
  refine castTF rfl hcnt (TFam.join (m := P.kkN) (Phi φ '' slReg (P.e : ℝ) P.f P.jR P.s)
    (fun i => Phi φ '' bandReg (P.e : ℝ) P.f (((P.n0N + (i : ℕ) : ℕ) : ℝ))) _ R ?_ ?_)
  · intro i
    refine Set.image_mono (band_sub (P.s : ℝ) _ (P.jR : ℝ) hE hEF ?_ ?_)
    · have : P.n0N + (i : ℕ) + 1 ≤ P.s := by have := i.2; have := P.n0_add; unfold kkN at *; omega
      exact_mod_cast this
    · have h2 : P.s = P.n0N + P.k := by have := P.n0_add; unfold kkN at this; omega
      have : (P.s : ℝ) - P.jR * P.f ≤ ((P.n0N + (i : ℕ) : ℕ) : ℝ) := by
        have : (P.s : ℝ) = P.n0N + P.jR * P.f := by rw [P.jRf]; exact_mod_cast h2
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

theorem hMn : (P.n1 : ℝ) ≤ P.M := by
  have H := P.rhU
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  have := H.hr0; have := H.hEF; have := H.hE
  nlinarith [mul_pos H.hE hn0]


section ug
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- **the U group**: `v-tau + pi5 + pi4 + rho-tau + rho-par` tile the quadrilateral `D, W, Q', V2` -/
def uFam2 : TFam (Phi φ '' su2Reg (P.e : ℝ) P.f P.M P.n1 P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef)
    (P.vN * P.vN + (P.gnN * P.gnN - (P.gnN - P.e) * (P.gnN - P.e)) + 2 * P.f * P.gnN + P.rho * P.rho + 2 * (P.f - P.rho) * P.rho) := by
  have H := P.rhU
  have hE := H.hE
  have hEF := H.hEF
  obtain ⟨hF, hB, hEF', hn0, hM, hj0, hv, hen⟩ := H.pos
  obtain ⟨v1, v2, v3, v4, v5⟩ := vt2_factsB (P.s : ℝ) H
  obtain ⟨q1, q2, q3, q4, q5⟩ := p52_factsB (P.s : ℝ) H
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := p42_factsB (P.s : ℝ) H
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := rt2_factsB (P.s : ℝ) H
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := rp2_factsB (P.s : ℝ) H
  have hMn := P.hMn
  have hr0 := H.hr0
  have hrE : 0 ≤ ((P.e : ℝ) * P.M - P.f * P.n1) / P.e := (div_pos hr0 hE).le
  have hrM : ((P.e : ℝ) * P.M - P.f * P.n1) / P.e ≤ P.M - P.n1 := by
    rw [div_le_iff₀ hE]; nlinarith [H.hEF, hn0]
  have q1' : LF (P.e : ℝ) P.f (P.s : ℝ) (p52Reg (P.e : ℝ) P.f P.M P.n1 P.jR P.s) (-1) 0 (-(((P.e : ℝ) * P.M - P.f * P.n1) / P.e)) :=
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



theorem sum_strips3 (m : ℕ) : (∑ i : Fin m, P.b * (2 * (P.n + (i : ℕ)) + 1)) = P.b * ((P.n + m) * (P.n + m) - P.n * P.n) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => P.b * (2 * (P.n + i) + 1)) m]
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : P.n * P.n ≤ (P.n + k) * (P.n + k) := Nat.mul_self_le_mul_self (Nat.le_add_right _ _)
    have h2 : P.n * P.n ≤ (P.n + (k + 1)) * (P.n + (k + 1)) := Nat.mul_self_le_mul_self (Nat.le_add_right _ _)
    apply Nat.cast_injective (R := ℤ)
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring

section sg
variable {φ : ℝ} (hφ : 1 < φ) (hφE : φ = (P.f : ℝ) / P.e)
include hφE

/-- **the strip group**: the strips `n, ..., n1 - 1` tile `{y >= k, c0(n1) <= F^2 x + B y <= c0(n)}`, `b (n1^2 - n^2)` tiles -/
def sFam3 : TFam (Phi φ '' sgReg (P.e : ℝ) P.f P.M P.n P.n1 P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef) (P.b * (P.n1 * P.n1 - P.n * P.n)) := by
  have H := P.rhR
  have hE := H.hE
  have hEF := H.hEF
  have hm : P.n + (P.n1 - P.n) = P.n1 := by have := P.hnn; omega
  let R : ∀ i : Fin (P.n1 - P.n), TFam (Phi φ '' sbReg (P.e : ℝ) P.f P.M ((P.n + (i : ℕ) : ℕ) : ℝ) P.jR P.s) (Mrow hφ P.e P.f P.he0 P.hef)
      (P.b * (2 * (P.n + (i : ℕ)) + 1)) := fun i =>
    P.stripFam3 hφ hφE (P.n + i) (Nat.le_add_right _ _) (by have := i.2; have := P.hnn; omega)
  have hcnt : (∑ i : Fin (P.n1 - P.n), P.b * (2 * (P.n + (i : ℕ)) + 1)) = P.b * (P.n1 * P.n1 - P.n * P.n) := by
    rw [P.sum_strips3 (P.n1 - P.n), hm]
  refine castTF rfl hcnt (TFam.join (m := P.n1 - P.n) (Phi φ '' sgReg (P.e : ℝ) P.f P.M P.n P.n1 P.jR P.s)
    (fun i => Phi φ '' sbReg (P.e : ℝ) P.f P.M ((P.n + (i : ℕ) : ℕ) : ℝ) P.jR P.s) _ R ?_ ?_)
  · intro i
    refine Set.image_mono (sb_sub (P.s : ℝ) hE hEF P.M P.jR P.n P.n1 _ ?_ ?_)
    · push_cast; have := (Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ ((i : ℕ) : ℝ)); linarith
    · have : P.n + (i : ℕ) + 1 ≤ P.n1 := by have := i.2; omega
      exact_mod_cast this
  · intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine (disjoint_image hφ (sb_disj (P.s : ℝ) hE hEF P.M P.jR _ _ ?_)).symm
      have : P.n + (i : ℕ) + 1 ≤ P.n + (j : ℕ) := by omega
      exact_mod_cast this
    · refine disjoint_image hφ (sb_disj (P.s : ℝ) hE hEF P.M P.jR _ _ ?_)
      have : P.n + (j : ℕ) + 1 ≤ P.n + (i : ℕ) := by omega
      exact_mod_cast this

end sg

end NP4

end

end Erdos634.Draft.ThetaNotch
