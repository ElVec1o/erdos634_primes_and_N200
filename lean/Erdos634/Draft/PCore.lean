/-
Draft/PCore.lean — generic layer for the Paliy nested-corner family theorems (`PRev`, `PF2`, `PF3`): the model tile `ModK`
at an arbitrary frame scale `K` (legs `b K`, `a K`, hypotenuse `K c`), congruence of a triangle with `ModK` for every ordering of
its side lengths, scale-`k` triangles (`triRTK`), parallelograms (`parRT'`), the empty tiling and conditional regions.
Generalises `F3Core` (where `K = c`) to the scale `K` of a general frame.  No sorry, no native_decide.
-/
import Erdos634.Draft.F3Core

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd Sh_Rect)

namespace Erdos634.Draft.PCore
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.Draft.F4All (hf1)
open Erdos634.Draft.S2L (rect_subset tri_le tri_ge mem_hull3' pack_exists)
open Erdos634.Draft.F3Core (triC_rot triC_swap nq sqd_triC01 TriR ParR parRT par_le par_ge disj_line mem_tri_pos subset_of_corners)

/-! ### the model tile at scale `K` -/
noncomputable def ModK {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 < K) : Tri :=
  brickL 1 hf1 (b * K) (a * K) (by positivity) (by positivity)

section mod
variable {a b c K : ℝ} (ha : 0 < a) (hb : 0 < b) (hc0 : 0 < c) (hK : 0 < K)

def n0 : ℝ × ℝ := (0, 0)
def n1 (b K : ℝ) : ℝ × ℝ := (b * K, 0)
def n2 (a b K : ℝ) : ℝ × ℝ := (b * K, a * K)

abbrev detf (p q r : ℝ × ℝ) : ℝ := (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

include ha hb hK in
theorem detm (p q r : ℝ × ℝ) (hp : p = n0 ∨ p = n1 b K ∨ p = n2 a b K) (hq : q = n0 ∨ q = n1 b K ∨ q = n2 a b K)
    (hr : r = n0 ∨ r = n1 b K ∨ r = n2 a b K) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    detf p q r ≠ 0 := by
  have h1 := mul_pos (mul_pos hb hK) (mul_pos ha hK)
  have h2 : (0:ℝ) < b * K := mul_pos hb hK
  have h3 : (0:ℝ) < a * K := mul_pos ha hK
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;>
    first | exact absurd rfl hpq | exact absurd rfl hpr | exact absurd rfl hqr |
      (simp only [detf, n0, n1, n2]; intro h; nlinarith)

include ha hb hK in
theorem ne01 : n0 ≠ n1 b K := by
  simp only [n0, n1, ne_eq, Prod.mk.injEq]; intro h; nlinarith [mul_pos hb hK]
include ha hb hK in
theorem ne02 : n0 ≠ n2 a b K := by
  simp only [n0, n2, ne_eq, Prod.mk.injEq]; intro h; nlinarith [mul_pos hb hK]
include ha hb hK in
theorem ne12 : n1 b K ≠ n2 a b K := by
  simp only [n1, n2, ne_eq, Prod.mk.injEq]; intro h; nlinarith [mul_pos ha hK]

include ha hb hK in
theorem d_012 : detf n0 (n1 b K) (n2 a b K) ≠ 0 := detm ha hb hK n0 (n1 b K) (n2 a b K) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (ne01 ha hb hK) (ne02 ha hb hK) (ne12 ha hb hK)
include ha hb hK in
theorem d_120 : detf (n1 b K) (n2 a b K) n0 ≠ 0 := detm ha hb hK (n1 b K) (n2 a b K) n0 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl) (ne12 ha hb hK) (ne01 ha hb hK).symm (ne02 ha hb hK).symm
include ha hb hK in
theorem d_201 : detf (n2 a b K) n0 (n1 b K) ≠ 0 := detm ha hb hK (n2 a b K) n0 (n1 b K) (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl)) (ne02 ha hb hK).symm (ne12 ha hb hK).symm (ne01 ha hb hK)
include ha hb hK in
theorem d_102 : detf (n1 b K) n0 (n2 a b K) ≠ 0 := detm ha hb hK (n1 b K) n0 (n2 a b K) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) (ne01 ha hb hK).symm (ne12 ha hb hK) (ne02 ha hb hK)
include ha hb hK in
theorem d_021 : detf n0 (n2 a b K) (n1 b K) ≠ 0 := detm ha hb hK n0 (n2 a b K) (n1 b K) (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (ne02 ha hb hK) (ne01 ha hb hK) (ne12 ha hb hK).symm
include ha hb hK in
theorem d_210 : detf (n2 a b K) (n1 b K) n0 ≠ 0 := detm ha hb hK (n2 a b K) (n1 b K) n0 (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (Or.inl rfl) (ne12 ha hb hK).symm (ne02 ha hb hK).symm (ne01 ha hb hK).symm

include ha hb hK in
theorem ModK_eq : ModK ha hb hK = triC 1 hf1 n0 (n1 b K) (n2 a b K) (d_012 ha hb hK) := by
  unfold ModK brickL n0 n1 n2; rfl

include ha hb hK in
theorem modk1 : (ModK ha hb hK).Congruent (triC 1 hf1 (n1 b K) (n2 a b K) n0 (d_120 ha hb hK)) := by
  rw [ModK_eq ha hb hK]; exact triC_rot _ _ _ _ _
include ha hb hK in
theorem modk2 : (ModK ha hb hK).Congruent (triC 1 hf1 (n2 a b K) n0 (n1 b K) (d_201 ha hb hK)) :=
  (modk1 ha hb hK).trans (triC_rot _ _ _ _ _)
include ha hb hK in
theorem modk3 : (ModK ha hb hK).Congruent (triC 1 hf1 (n1 b K) n0 (n2 a b K) (d_102 ha hb hK)) := by
  rw [ModK_eq ha hb hK]; exact triC_swap _ _ _ _ _
include ha hb hK in
theorem modk4 : (ModK ha hb hK).Congruent (triC 1 hf1 n0 (n2 a b K) (n1 b K) (d_021 ha hb hK)) :=
  (modk2 ha hb hK).trans (triC_swap _ _ _ _ _)
include ha hb hK in
theorem modk5 : (ModK ha hb hK).Congruent (triC 1 hf1 (n2 a b K) (n1 b K) n0 (d_210 ha hb hK)) :=
  (modk1 ha hb hK).trans (triC_swap _ _ _ _ _)

variable (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
include hc

theorem nq_01 : nq n0 (n1 b K) = (b * K) ^ 2 := by simp only [nq, n0, n1]; ring
theorem nq_12 : nq (n1 b K) (n2 a b K) = (a * K) ^ 2 := by simp only [nq, n1, n2]; ring
theorem nq_20 : nq (n2 a b K) n0 = (K * c) ^ 2 := by simp only [nq, n2, n0]; linear_combination (-K ^ 2) * hc
theorem nq_10 : nq (n1 b K) n0 = (b * K) ^ 2 := by simp only [nq, n0, n1]; ring
theorem nq_21 : nq (n2 a b K) (n1 b K) = (a * K) ^ 2 := by simp only [nq, n1, n2]; ring
theorem nq_02 : nq n0 (n2 a b K) = (K * c) ^ 2 := by simp only [nq, n2, n0]; linear_combination (-K ^ 2) * hc

-- congruence with `ModK` from the three squared sides of a triangle, in each of the six orders
include ha hb hK in
theorem cong_v0 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (b * K) ^ 2) (e12 : nq q r = (a * K) ^ 2) (e20 : nq r p = (K * c) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (ModK ha hb hK) := by
  rw [ModK_eq ha hb hK]
  exact triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_01 hc).symm) (e12.trans (nq_12 hc).symm)
    (e20.trans (nq_20 hc).symm)
include ha hb hK in
theorem cong_v1 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (a * K) ^ 2) (e12 : nq q r = (K * c) ^ 2) (e20 : nq r p = (b * K) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (ModK ha hb hK) :=
  (triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_12 hc).symm)
    (e12.trans (nq_20 hc).symm) (e20.trans (nq_01 hc).symm)).trans
    (modk1 ha hb hK).symm
include ha hb hK in
theorem cong_v2 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (K * c) ^ 2) (e12 : nq q r = (b * K) ^ 2) (e20 : nq r p = (a * K) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (ModK ha hb hK) :=
  (triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_20 hc).symm)
    (e12.trans (nq_01 hc).symm) (e20.trans (nq_12 hc).symm)).trans
    (modk2 ha hb hK).symm
include ha hb hK in
theorem cong_v3 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (b * K) ^ 2) (e12 : nq q r = (K * c) ^ 2) (e20 : nq r p = (a * K) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (ModK ha hb hK) :=
  (triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_10 hc).symm)
    (e12.trans (nq_02 hc).symm) (e20.trans (nq_21 hc).symm)).trans
    (modk3 ha hb hK).symm
include ha hb hK in
theorem cong_v4 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (K * c) ^ 2) (e12 : nq q r = (a * K) ^ 2) (e20 : nq r p = (b * K) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (ModK ha hb hK) :=
  (triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_02 hc).symm)
    (e12.trans (nq_21 hc).symm) (e20.trans (nq_10 hc).symm)).trans
    (modk4 ha hb hK).symm
include ha hb hK in
theorem cong_v5 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (a * K) ^ 2) (e12 : nq q r = (b * K) ^ 2) (e20 : nq r p = (K * c) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (ModK ha hb hK) :=
  (triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_21 hc).symm)
    (e12.trans (nq_10 hc).symm) (e20.trans (nq_02 hc).symm)).trans
    (modk5 ha hb hK).symm
end mod

/-! ### scale-`k` triangles, parallelograms, empty tiling, conditional regions -/
noncomputable def triRTK {a b c K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 < K) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (V0 V1 V2 : ℝ × ℝ) (k : ℕ) (hk0 : 0 < k) (hdet : (V1.1 - V0.1) * (V2.2 - V0.2) - (V2.1 - V0.1) * (V1.2 - V0.2) ≠ 0)
    (H01 : (V1.1 - V0.1) ^ 2 + (V1.2 - V0.2) ^ 2 + (V1.1 - V0.1) * (V1.2 - V0.2) / 1 = ((k : ℝ) * (b * K)) ^ 2)
    (H12 : (V2.1 - V1.1) ^ 2 + (V2.2 - V1.2) ^ 2 + (V2.1 - V1.1) * (V2.2 - V1.2) / 1 = ((k : ℝ) * (a * K)) ^ 2)
    (H20 : (V2.1 - V0.1) ^ 2 + (V2.2 - V0.2) ^ 2 + (V2.1 - V0.1) * (V2.2 - V0.2) / 1 = ((k : ℝ) * (K * c)) ^ 2) :
    RTiling (Phi 1 '' TriR V0 V1 V2) (ModK ha hb hK) (k * k) :=
  scaledRT 1 hf1 V0 V1 V2 k hk0 hdet _
    (baseTri_cong 1 hf1 (b * K) (a * K) ((K * c) ^ 2) (by positivity) (by positivity)
      (by linear_combination (-K ^ 2) * hc) V0 V1 V2 k hk0 hdet H01 H12 (by rw [H20]; ring))

/-- a parallelogram of `k × l` cells (`k, l ≥ 1`), `2 k l` tiles -/
noncomputable def parRT' {M : Tri} (u w o : ℝ × ℝ) (hdet : u.1 * w.2 - u.2 * w.1 ≠ 0)
    (c1 : (TL hf1 u w hdet).Congruent M) (c2 : (TU hf1 u w hdet).Congruent M) (k l : ℕ) (hk0 : 0 < k) (hl0 : 0 < l)
    {K L : ℝ} (hK : (k : ℝ) = K) (hL : (l : ℝ) = L) :
    RTiling (Phi 1 '' ParR o u w K L) M (2 * k * l) :=
  RTiling.castN (by rw [Nat.sub_add_cancel hk0, Nat.sub_add_cancel hl0])
    (parRT u w o hdet c1 c2 (k - 1) (l - 1) K L (by rw [← hK, Nat.cast_pred hk0]; ring)
      (by rw [← hL, Nat.cast_pred hl0]; ring))

/-- the empty region has the empty tiling -/
def emptyRT (M : Tri) : RTiling (∅ : Set Plane) M 0 where
  tile := fun i => i.elim0
  covers := by simp
  disj := fun i => i.elim0
  cong := fun i => i.elim0

/-- a region that vanishes when `p` holds -/
def condSet (p : Prop) (S : Set Plane) : Set Plane := if p then ∅ else S

theorem cd_left {p : Prop} {S T : Set Plane} (h : Disjoint (interior S) (interior T)) :
    Disjoint (interior (condSet p S)) (interior T) := by
  unfold condSet; split_ifs
  · simp
  · exact h
theorem cd_right {p : Prop} {S T : Set Plane} (h : Disjoint (interior S) (interior T)) :
    Disjoint (interior S) (interior (condSet p T)) := (cd_left (p := p) h.symm).symm
theorem cd_sub {p : Prop} {S T : Set Plane} (h : ¬p → S ⊆ T) : condSet p S ⊆ T := by
  unfold condSet; split_ifs with hp
  · exact Set.empty_subset _
  · exact h hp
noncomputable def condRT {p : Prop} {S : Set Plane} {M : Tri} {n : ℕ} (hn : p → n = 0) (R : ¬p → RTiling S M n) :
    RTiling (condSet p S) M n := by
  unfold condSet
  by_cases hp : p
  · rw [if_pos hp]; exact RTiling.castN (hn hp).symm (emptyRT M)
  · rw [if_neg hp]; exact R hp

end Erdos634.Draft.PCore
