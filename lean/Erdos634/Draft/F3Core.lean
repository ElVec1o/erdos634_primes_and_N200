/-
Draft/F3Core.lean — generic layer for `Draft.F3All` (the F3 family, `a < b`): the model tile `Mod3`, congruence of a triangle with `Mod3`
for every ordering of its side lengths, tilings of translated parallelograms and of scale-`k` triangles, half-plane bounds on
parallelograms, membership in a triangle by cross products, and transport of a `CongruentDissection` onto a congruent triangle.
UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.F4All

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd Sh_Rect)

namespace Erdos634.Draft.F3Core
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.Draft.F4All (hf1)
open Erdos634.Draft.S2L (rect_subset tri_le tri_ge mem_hull3' pack_exists)
open Erdos634.Draft.WBrickF (interior_disj_lin)

/-! ### the model tile -/
noncomputable def Mod3 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc0 : 0 < c) : Tri :=
  brickL 1 hf1 (b * c) (a * c) (by positivity) (by positivity)

/-- squared distance between skew points, as in `sq_Phi'` -/
theorem sqd_triC01 (p q r : ℝ × ℝ) (h) :
    dist ((triC 1 hf1 p q r h).pts 0) ((triC 1 hf1 p q r h).pts 1) ^ 2
      = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 + (p.1 - q.1) * (p.2 - q.2) / 1 := by
  simp only [triC_pts]; exact sq_Phi' hf1 p q

section tricong
/-- rotation of the vertex list is a congruence -/
theorem triC_rot (p q r : ℝ × ℝ) (h h') : (triC 1 hf1 p q r h).Congruent (triC 1 hf1 q r p h') := by
  refine ⟨IsometryEquiv.refl _, (⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩ : Equiv.Perm (Fin 3)), fun k => ?_⟩
  fin_cases k <;> simp [triC_pts] <;> rfl

theorem triC_swap (p q r : ℝ × ℝ) (h h') : (triC 1 hf1 p q r h).Congruent (triC 1 hf1 q p r h') := by
  refine ⟨IsometryEquiv.refl _, (⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩ : Equiv.Perm (Fin 3)), fun k => ?_⟩
  fin_cases k <;> simp [triC_pts] <;> rfl
end tricong

section mod
variable {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc0 : 0 < c)
include ha hb hc0

/-- the three model vertices -/
def m0 : ℝ × ℝ := (0, 0)
def m1 (b c : ℝ) : ℝ × ℝ := (b * c, 0)
def m2 (a b c : ℝ) : ℝ × ℝ := (b * c, a * c)

abbrev detf (p q r : ℝ × ℝ) : ℝ := (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

theorem detm (p q r : ℝ × ℝ) (hp : p = m0 ∨ p = m1 b c ∨ p = m2 a b c) (hq : q = m0 ∨ q = m1 b c ∨ q = m2 a b c)
    (hr : r = m0 ∨ r = m1 b c ∨ r = m2 a b c) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    detf p q r ≠ 0 := by
  have h1 := mul_pos (mul_pos hb hc0) (mul_pos ha hc0)
  have h2 : (0:ℝ) < b * c := mul_pos hb hc0
  have h3 : (0:ℝ) < a * c := mul_pos ha hc0
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;>
    first | exact absurd rfl hpq | exact absurd rfl hpr | exact absurd rfl hqr |
      (simp only [detf, m0, m1, m2]; intro h; nlinarith)

theorem ne01 : m0 ≠ m1 b c := by
  simp only [m0, m1, ne_eq, Prod.mk.injEq]; intro h; nlinarith [mul_pos hb hc0]
theorem ne02 : m0 ≠ m2 a b c := by
  simp only [m0, m2, ne_eq, Prod.mk.injEq]; intro h; nlinarith [mul_pos hb hc0]
theorem ne12 : m1 b c ≠ m2 a b c := by
  simp only [m1, m2, ne_eq, Prod.mk.injEq]; intro h; nlinarith [mul_pos ha hc0]

theorem d_012 : detf m0 (m1 b c) (m2 a b c) ≠ 0 := detm ha hb hc0 m0 (m1 b c) (m2 a b c) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (ne01 ha hb hc0) (ne02 ha hb hc0) (ne12 ha hb hc0)
theorem d_120 : detf (m1 b c) (m2 a b c) m0 ≠ 0 := detm ha hb hc0 (m1 b c) (m2 a b c) m0 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl) (ne12 ha hb hc0) (ne01 ha hb hc0).symm (ne02 ha hb hc0).symm
theorem d_201 : detf (m2 a b c) m0 (m1 b c) ≠ 0 := detm ha hb hc0 (m2 a b c) m0 (m1 b c) (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl)) (ne02 ha hb hc0).symm (ne12 ha hb hc0).symm (ne01 ha hb hc0)
theorem d_102 : detf (m1 b c) m0 (m2 a b c) ≠ 0 := detm ha hb hc0 (m1 b c) m0 (m2 a b c) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) (ne01 ha hb hc0).symm (ne12 ha hb hc0) (ne02 ha hb hc0)
theorem d_021 : detf m0 (m2 a b c) (m1 b c) ≠ 0 := detm ha hb hc0 m0 (m2 a b c) (m1 b c) (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (ne02 ha hb hc0) (ne01 ha hb hc0) (ne12 ha hb hc0).symm
theorem d_210 : detf (m2 a b c) (m1 b c) m0 ≠ 0 := detm ha hb hc0 (m2 a b c) (m1 b c) m0 (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (Or.inl rfl) (ne12 ha hb hc0).symm (ne02 ha hb hc0).symm (ne01 ha hb hc0).symm

theorem Mod3_eq : Mod3 ha hb hc0 = triC 1 hf1 m0 (m1 b c) (m2 a b c) (d_012 ha hb hc0) := by
  unfold Mod3 brickL m0 m1 m2; rfl

theorem modk1 : (Mod3 ha hb hc0).Congruent (triC 1 hf1 (m1 b c) (m2 a b c) m0 (d_120 ha hb hc0)) := by
  rw [Mod3_eq ha hb hc0]; exact triC_rot _ _ _ _ _
theorem modk2 : (Mod3 ha hb hc0).Congruent (triC 1 hf1 (m2 a b c) m0 (m1 b c) (d_201 ha hb hc0)) :=
  (modk1 ha hb hc0).trans (triC_rot _ _ _ _ _)
theorem modk3 : (Mod3 ha hb hc0).Congruent (triC 1 hf1 (m1 b c) m0 (m2 a b c) (d_102 ha hb hc0)) := by
  rw [Mod3_eq ha hb hc0]; exact triC_swap _ _ _ _ _
theorem modk4 : (Mod3 ha hb hc0).Congruent (triC 1 hf1 m0 (m2 a b c) (m1 b c) (d_021 ha hb hc0)) :=
  (modk2 ha hb hc0).trans (triC_swap _ _ _ _ _)
theorem modk5 : (Mod3 ha hb hc0).Congruent (triC 1 hf1 (m2 a b c) (m1 b c) m0 (d_210 ha hb hc0)) :=
  (modk1 ha hb hc0).trans (triC_swap _ _ _ _ _)

/-- skew quadratic form -/
noncomputable def nq (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 + (p.1 - q.1) * (p.2 - q.2) / 1

variable (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
include hc

theorem nq_01 : nq m0 (m1 b c) = (b * c) ^ 2 := by simp only [nq, m0, m1]; ring
theorem nq_12 : nq (m1 b c) (m2 a b c) = (a * c) ^ 2 := by simp only [nq, m1, m2]; ring
theorem nq_20 : nq (m2 a b c) m0 = (c ^ 2) ^ 2 := by simp only [nq, m2, m0]; linear_combination (-c ^ 2) * hc
theorem nq_10 : nq (m1 b c) m0 = (b * c) ^ 2 := by simp only [nq, m0, m1]; ring
theorem nq_21 : nq (m2 a b c) (m1 b c) = (a * c) ^ 2 := by simp only [nq, m1, m2]; ring
theorem nq_02 : nq m0 (m2 a b c) = (c ^ 2) ^ 2 := by simp only [nq, m2, m0]; linear_combination (-c ^ 2) * hc

/-- congruence with `Mod3` from the three squared sides of a triangle, in each of the six orders -/
theorem cong_v0 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (b * c) ^ 2) (e12 : nq q r = (a * c) ^ 2) (e20 : nq r p = (c ^ 2) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (Mod3 ha hb hc0) := by
  rw [Mod3_eq ha hb hc0]
  exact triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_01 ha hb hc0 hc).symm) (e12.trans (nq_12 ha hb hc0 hc).symm)
    (e20.trans (nq_20 ha hb hc0 hc).symm)
theorem cong_v1 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (a * c) ^ 2) (e12 : nq q r = (c ^ 2) ^ 2) (e20 : nq r p = (b * c) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (Mod3 ha hb hc0) :=
  (triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_12 ha hb hc0 hc).symm)
    (e12.trans (nq_20 ha hb hc0 hc).symm) (e20.trans (nq_01 ha hb hc0 hc).symm)).trans
    (modk1 ha hb hc0).symm
theorem cong_v2 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (c ^ 2) ^ 2) (e12 : nq q r = (b * c) ^ 2) (e20 : nq r p = (a * c) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (Mod3 ha hb hc0) :=
  (triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_20 ha hb hc0 hc).symm)
    (e12.trans (nq_01 ha hb hc0 hc).symm) (e20.trans (nq_12 ha hb hc0 hc).symm)).trans
    (modk2 ha hb hc0).symm
theorem cong_v3 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (b * c) ^ 2) (e12 : nq q r = (c ^ 2) ^ 2) (e20 : nq r p = (a * c) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (Mod3 ha hb hc0) :=
  (triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_10 ha hb hc0 hc).symm)
    (e12.trans (nq_02 ha hb hc0 hc).symm) (e20.trans (nq_21 ha hb hc0 hc).symm)).trans
    (modk3 ha hb hc0).symm
theorem cong_v4 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (c ^ 2) ^ 2) (e12 : nq q r = (a * c) ^ 2) (e20 : nq r p = (b * c) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (Mod3 ha hb hc0) :=
  (triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_02 ha hb hc0 hc).symm)
    (e12.trans (nq_21 ha hb hc0 hc).symm) (e20.trans (nq_10 ha hb hc0 hc).symm)).trans
    (modk4 ha hb hc0).symm
theorem cong_v5 (p q r : ℝ × ℝ) (h) (e01 : nq p q = (a * c) ^ 2) (e12 : nq q r = (b * c) ^ 2) (e20 : nq r p = (c ^ 2) ^ 2) :
    (triC 1 hf1 p q r h).Congruent (Mod3 ha hb hc0) :=
  (triC_cong hf1 p q r _ _ _ h _ (e01.trans (nq_21 ha hb hc0 hc).symm)
    (e12.trans (nq_10 ha hb hc0 hc).symm) (e20.trans (nq_02 ha hb hc0 hc).symm)).trans
    (modk5 ha hb hc0).symm

end mod

/-! ### triangles and parallelograms as regions -/
/-- `S` translated by `o` in skew coordinates -/
theorem image_shiftPhi (o : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    (fun x : Plane => x + Phi 1 o) '' (Phi 1 '' S) = Phi 1 '' ((fun z => z + o) '' S) := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p + o, ⟨p, hp, rfl⟩, by simp only [Phi_add]⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨Phi 1 p, ⟨p, hp, rfl⟩, by simp only [Phi_add]⟩

noncomputable def shiftRT {S : Set (ℝ × ℝ)} {M : Tri} {N : ℕ} (R : RTiling (Phi 1 '' S) M N) (o : ℝ × ℝ) :
    RTiling (Phi 1 '' ((fun z => z + o) '' S)) M N :=
  RTiling.cast (image_shiftPhi o S) (Erdos634.Draft.RegionTiling.map R (IsometryEquiv.addRight (Phi 1 o)))

/-- the parallelogram `o + Lam u w [0,K]×[0,L]` -/
def ParR (o u w : ℝ × ℝ) (K L : ℝ) : Set (ℝ × ℝ) := (fun z => z + o) '' (Lam u w '' Rect 0 K 0 L)
/-- the triangle with vertices `A B C` -/
def TriR (A B C : ℝ × ℝ) : Set (ℝ × ℝ) := convexHull ℝ {A, B, C}

/-- a parallelogram of `(k+1) × (l+1)` cells, `2 (k+1)(l+1)` tiles -/
noncomputable def parRT {M : Tri} (u w o : ℝ × ℝ) (hdet : u.1 * w.2 - u.2 * w.1 ≠ 0)
    (c1 : (TL hf1 u w hdet).Congruent M) (c2 : (TU hf1 u w hdet).Congruent M) (k l : ℕ) (K L : ℝ)
    (hK : (k : ℝ) + 1 = K) (hL : (l : ℝ) + 1 = L) :
    RTiling (Phi 1 '' ParR o u w K L) M (2 * (k + 1) * (l + 1)) := by
  have G := gridT (ThH hf1 u w hdet) (ThH_add hf1 u w hdet) (A := 1) (B := 1) one_pos one_pos
    (cellRT hf1 u w hdet M c1 c2) k l
  rw [ThH_image] at G
  subst hK hL
  rw [one_mul, one_mul] at G
  exact shiftRT G o

/-- a scale-`k` triangle, vertices ordered `(b-side, a-side, c-side)` -/
noncomputable def triRT {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc0 : 0 < c) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (V0 V1 V2 : ℝ × ℝ) (k : ℕ) (hk0 : 0 < k) (hdet : (V1.1 - V0.1) * (V2.2 - V0.2) - (V2.1 - V0.1) * (V1.2 - V0.2) ≠ 0)
    (H01 : (V1.1 - V0.1) ^ 2 + (V1.2 - V0.2) ^ 2 + (V1.1 - V0.1) * (V1.2 - V0.2) / 1 = ((k : ℝ) * (b * c)) ^ 2)
    (H12 : (V2.1 - V1.1) ^ 2 + (V2.2 - V1.2) ^ 2 + (V2.1 - V1.1) * (V2.2 - V1.2) / 1 = ((k : ℝ) * (a * c)) ^ 2)
    (H20 : (V2.1 - V0.1) ^ 2 + (V2.2 - V0.2) ^ 2 + (V2.1 - V0.1) * (V2.2 - V0.2) / 1 = (k : ℝ) ^ 2 * (c ^ 2) ^ 2) :
    RTiling (Phi 1 '' TriR V0 V1 V2) (Mod3 ha hb hc0) (k * k) :=
  scaledRT 1 hf1 V0 V1 V2 k hk0 hdet _
    (baseTri_cong 1 hf1 (b * c) (a * c) ((c ^ 2) ^ 2) (by positivity) (by positivity)
      (by linear_combination (-c ^ 2) * hc) V0 V1 V2 k hk0 hdet H01 H12 H20)

/-! ### half-plane bounds -/
theorem par_le (p q r : ℝ) (o u w : ℝ × ℝ) (K L : ℝ)
    (h00 : p * o.1 + q * o.2 ≤ r) (h10 : p * (o.1 + K * u.1) + q * (o.2 + K * u.2) ≤ r)
    (h01 : p * (o.1 + L * w.1) + q * (o.2 + L * w.2) ≤ r)
    (h11 : p * (o.1 + K * u.1 + L * w.1) + q * (o.2 + K * u.2 + L * w.2) ≤ r) :
    ∀ x ∈ ParR o u w K L, p * x.1 + q * x.2 ≤ r := by
  rintro _ ⟨_, ⟨z, ⟨hz1, hz2, hz3, hz4⟩, rfl⟩, rfl⟩
  simp only [Lam, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  set α := p * u.1 + q * u.2 with hα
  set β := p * w.1 + q * w.2 with hβ
  have e1 : p * (z.1 * u.1 + z.2 * w.1 + o.1) + q * (z.1 * u.2 + z.2 * w.2 + o.2)
      = (p * o.1 + q * o.2) + z.1 * α + z.2 * β := by rw [hα, hβ]; ring
  have e2 : p * (o.1 + K * u.1) + q * (o.2 + K * u.2) = (p * o.1 + q * o.2) + K * α := by rw [hα]; ring
  have e3 : p * (o.1 + L * w.1) + q * (o.2 + L * w.2) = (p * o.1 + q * o.2) + L * β := by rw [hβ]; ring
  have e4 : p * (o.1 + K * u.1 + L * w.1) + q * (o.2 + K * u.2 + L * w.2)
      = (p * o.1 + q * o.2) + K * α + L * β := by rw [hα, hβ]; ring
  rw [e1]
  rw [e2] at h10; rw [e3] at h01; rw [e4] at h11
  rcases le_total 0 α with hA | hA <;> rcases le_total 0 β with hB | hB
  · nlinarith [mul_le_mul_of_nonneg_right hz2 hA, mul_le_mul_of_nonneg_right hz4 hB]
  · nlinarith [mul_le_mul_of_nonneg_right hz2 hA, mul_nonneg hz3 (neg_nonneg.mpr hB)]
  · nlinarith [mul_nonneg hz1 (neg_nonneg.mpr hA), mul_le_mul_of_nonneg_right hz4 hB]
  · nlinarith [mul_nonneg hz1 (neg_nonneg.mpr hA), mul_nonneg hz3 (neg_nonneg.mpr hB)]

theorem par_ge (p q r : ℝ) (o u w : ℝ × ℝ) (K L : ℝ)
    (h00 : r ≤ p * o.1 + q * o.2) (h10 : r ≤ p * (o.1 + K * u.1) + q * (o.2 + K * u.2))
    (h01 : r ≤ p * (o.1 + L * w.1) + q * (o.2 + L * w.2))
    (h11 : r ≤ p * (o.1 + K * u.1 + L * w.1) + q * (o.2 + K * u.2 + L * w.2)) :
    ∀ x ∈ ParR o u w K L, r ≤ p * x.1 + q * x.2 := by
  intro x hx
  have := par_le (-p) (-q) (-r) o u w K L (by linarith) (by linarith) (by linarith) (by linarith) x hx
  linarith

/-- separation by a line `p x + q y = r` (any `(p,q) ≠ 0`) -/
theorem disj_line {A B : Set (ℝ × ℝ)} (p q r : ℝ) (hpq : p ≠ 0 ∨ q ≠ 0)
    (hA : ∀ x ∈ A, p * x.1 + q * x.2 ≤ r) (hB : ∀ x ∈ B, r ≤ p * x.1 + q * x.2) :
    Disjoint (interior A) (interior B) := by
  rcases eq_or_ne p 0 with hp | hp
  · have hq : q ≠ 0 := hpq.resolve_left (not_not.mpr hp)
    subst hp
    rcases lt_or_gt_of_ne hq with hq' | hq'
    · refine (interior_disj_snd (r / q) ?_ ?_).symm
      · intro x hx; have := hB x hx; simp only [zero_mul, zero_add] at this
        rw [le_div_iff_of_neg hq']; linarith
      · intro x hx; have := hA x hx; simp only [zero_mul, zero_add] at this
        rw [div_le_iff_of_neg hq']; linarith
    · refine interior_disj_snd (r / q) ?_ ?_
      · intro x hx; have := hA x hx; simp only [zero_mul, zero_add] at this
        rw [le_div_iff₀ hq']; linarith
      · intro x hx; have := hB x hx; simp only [zero_mul, zero_add] at this
        rw [div_le_iff₀ hq']; linarith
  · exact interior_disj_lin p q r hp hA hB

/-- membership in a triangle by cross products (positive orientation) -/
theorem mem_tri_pos {A B C p : ℝ × ℝ} (D : ℝ) (hD : 0 < D)
    (hDe : (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) = D)
    (hx : 0 ≤ (B.1 - p.1) * (C.2 - p.2) - (C.1 - p.1) * (B.2 - p.2))
    (hy : 0 ≤ (C.1 - p.1) * (A.2 - p.2) - (A.1 - p.1) * (C.2 - p.2))
    (hz : 0 ≤ (A.1 - p.1) * (B.2 - p.2) - (B.1 - p.1) * (A.2 - p.2)) :
    p ∈ convexHull ℝ ({A, B, C} : Set (ℝ × ℝ)) := by
  refine mem_hull3' D _ _ _ hD hx hy hz (by rw [← hDe]; ring) p ?_ ?_
  · rw [← hDe]; ring
  · rw [← hDe]; ring

/-- membership in a triangle by cross products (negative orientation) -/
theorem mem_tri_neg {A B C p : ℝ × ℝ} (D : ℝ) (hD : 0 < D)
    (hDe : (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) = -D)
    (hx : (B.1 - p.1) * (C.2 - p.2) - (C.1 - p.1) * (B.2 - p.2) ≤ 0)
    (hy : (C.1 - p.1) * (A.2 - p.2) - (A.1 - p.1) * (C.2 - p.2) ≤ 0)
    (hz : (A.1 - p.1) * (B.2 - p.2) - (B.1 - p.1) * (A.2 - p.2) ≤ 0) :
    p ∈ convexHull ℝ ({A, B, C} : Set (ℝ × ℝ)) := by
  have hD' : D = -((B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2)) := by linarith
  refine mem_hull3' D (-((B.1 - p.1) * (C.2 - p.2) - (C.1 - p.1) * (B.2 - p.2)))
    (-((C.1 - p.1) * (A.2 - p.2) - (A.1 - p.1) * (C.2 - p.2)))
    (-((A.1 - p.1) * (B.2 - p.2) - (B.1 - p.1) * (A.2 - p.2))) hD (by linarith) (by linarith) (by linarith)
    (by rw [hD']; ring) p ?_ ?_
  · rw [hD']; ring
  · rw [hD']; ring

theorem subset_of_corners {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) {o u w : ℝ × ℝ} {M L : ℝ} (hM : 0 < M) (hL : 0 < L)
    (c00 : o ∈ K) (c10 : o + M • u ∈ K) (c01 : o + L • w ∈ K) (c11 : o + M • u + L • w ∈ K) :
    ParR o u w M L ⊆ K := by
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  have hK' : Convex ℝ {z : ℝ × ℝ | Lam u w z + o ∈ K} := by
    have : Convex ℝ ((fun x => x + o) ⁻¹' K) := hK.translate_preimage_left o
    exact (this.linear_preimage (LamL u w))
  have key := rect_subset hK' hM hL (x0 := 0) (y0 := 0) (x1 := M) (y1 := L)
    (by show Lam u w (0, 0) + o ∈ K; simpa [Lam] using c00)
    (by show Lam u w (M, 0) + o ∈ K; simpa [Lam, add_comm] using c10)
    (by show Lam u w (0, L) + o ∈ K; simpa [Lam, add_comm] using c01)
    (by show Lam u w (M, L) + o ∈ K; simpa [Lam, add_comm, add_assoc] using c11)
  exact key hz

/-! ### transport of a congruent dissection onto a triangle with prescribed vertices -/
theorem dist01_of (p q r : ℝ × ℝ) (h) (x : ℝ) (hx : 0 ≤ x) (e : nq p q = x ^ 2) :
    dist ((triC 1 hf1 p q r h).pts 0) ((triC 1 hf1 p q r h).pts 1) = x :=
  Erdos634.Draft.F4All.f4_eq_of_sq dist_nonneg hx (by rw [sqd_triC01]; exact e)
theorem dist12_of (p q r : ℝ × ℝ) (h) (x : ℝ) (hx : 0 ≤ x) (e : nq q r = x ^ 2) :
    dist ((triC 1 hf1 p q r h).pts 1) ((triC 1 hf1 p q r h).pts 2) = x :=
  Erdos634.Draft.F4All.f4_eq_of_sq dist_nonneg hx (by rw [triC_pts]; show dist (Phi 1 q) (Phi 1 r) ^ 2 = x ^ 2; rw [sq_Phi' hf1]; exact e)
theorem dist20_of (p q r : ℝ × ℝ) (h) (x : ℝ) (hx : 0 ≤ x) (e : nq r p = x ^ 2) :
    dist ((triC 1 hf1 p q r h).pts 2) ((triC 1 hf1 p q r h).pts 0) = x :=
  Erdos634.Draft.F4All.f4_eq_of_sq dist_nonneg hx (by rw [triC_pts]; show dist (Phi 1 r) (Phi 1 p) ^ 2 = x ^ 2; rw [sq_Phi' hf1]; exact e)

theorem rt_nonempty {N : ℕ} (D : CongruentDissection N) (U M : Tri) (hT : D.target.Congruent U)
    (hM : D.model.Congruent M) : Nonempty (RTiling U.carrier M N) := by
  obtain ⟨f, σ, hf⟩ := hT
  exact ⟨RTiling.cast (Erdos634.CongruentArea.image_carrier_of_congruent hf)
    (remodel (Erdos634.Draft.RegionTiling.map (ofCD D) f) hM)⟩

theorem rt_tri_of_cd {N : ℕ} (D : CongruentDissection N) (p q r : ℝ × ℝ) (h : (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2) ≠ 0) (M : Tri) (hM : D.model.Congruent M)
    (s01 s12 s20 : ℝ) (h0 : 0 ≤ s01) (h1 : 0 ≤ s12) (h2 : 0 ≤ s20)
    (hD01 : dist (D.target.pts 0) (D.target.pts 1) = s01) (hD12 : dist (D.target.pts 1) (D.target.pts 2) = s12)
    (hD20 : dist (D.target.pts 2) (D.target.pts 0) = s20)
    (e01 : nq p q = s01 ^ 2) (e12 : nq q r = s12 ^ 2) (e20 : nq r p = s20 ^ 2) :
    Nonempty (RTiling (Phi 1 '' TriR p q r) M N) := by
  have hT : D.target.Congruent (triC 1 hf1 p q r h) :=
    Erdos634.SssCongruent.congruent_of_dist_three (by rw [hD01, dist01_of p q r h s01 h0 e01])
      (by rw [hD12, dist12_of p q r h s12 h1 e12]) (by rw [hD20, dist20_of p q r h s20 h2 e20])
  obtain ⟨R⟩ := rt_nonempty D _ M hT hM
  rw [carrier_triC] at R
  exact ⟨R⟩

end Erdos634.Draft.F3Core
