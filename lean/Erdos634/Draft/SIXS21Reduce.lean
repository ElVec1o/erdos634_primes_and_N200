-- Draft/SIXS21Reduce.lean
-- Reduction of `S3Closed 21` (base-α target (α,α,α+2β), N = 21) to ONE concrete geometric instance:
-- after rescaling by `4/c`, the target has sides (12,12,21) (oppLen 0,1,2) and the model has sides
-- (2,3,4) in some vertex order.  The Row-11 reduction (`Row11.area`, `Row11.sides`, the leg-word
-- divisibility `isoalpha_X_forces`) is replayed from `Row11.excluded_isoQ`; the arithmetic leaf
-- `sol21` shows (e,d,m) = (1,1,1) is the only solution at N = 21.
import Erdos634.Draft.Row11IsoQ
import Erdos634.Realizable

open scoped Classical

namespace Erdos634.Geometry
namespace SIX

open Rows11_13AnyLabel

/-- The reduced Row-11 equation at `N = 21` has the single solution `(e,d,m) = (1,1,1)`. -/
theorem sol21 (e d m : ℕ) (he : 1 ≤ e) (hd : 1 ≤ d)
    (heq : 21 * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))) :
    e = 1 ∧ d = 1 ∧ m = 1 := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at heq; omega
    · exact h
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  have hle : (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2) ≤ 21 * d := by
    calc (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)
        = 1 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by ring
      _ ≤ m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) :=
          Nat.mul_le_mul_right _ hm2
      _ = 21 * d := heq.symm
  have he2 : e ≤ 2 := by nlinarith [Nat.zero_le (d * d), Nat.zero_le (e * d)]
  have hd2 : d ≤ 2 := by nlinarith [Nat.zero_le (d * d), Nat.zero_le (e * d)]
  have hm3 : m ≤ 1 := by
    by_contra hcon
    have : 2 ≤ m := by omega
    have h4 : 4 ≤ m ^ 2 := by nlinarith
    interval_cases e <;> interval_cases d <;> nlinarith
  interval_cases e <;> interval_cases d <;> (try omega) <;> (have : m = 1 := by omega) <;> simp_all

/-- **The numbers of the base-α target at `N = 21`** (target angles `α` at vertices 0, 1):
`a = c/2`, `b = 3c/4`, legs `3c`, base `21c/4`. -/
theorem six21_numbers {N : ℕ} (hN : N = 21) (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α) (hP1 : D.target.angleAt 1 = α) :
    0 < c ∧ a = c / 2 ∧ b = 3 * c / 4 ∧ D.target.oppLen 0 = 3 * c ∧
      D.target.oppLen 1 = 3 * c ∧ D.target.oppLen 2 = 21 * c / 4 := by
  obtain ⟨s, M, hs0, hs1, hc, ha, hb, hM1, hleg, harea⟩ := Row11.area D hα hrel h hP0 hP1
  obtain ⟨r, hr⟩ := Row11.rational D hα hrel h hP0 hP1
  have hsr : s = r := by
    have : c * (s - r) = 0 := by rw [ha] at hr; linear_combination hr
    linarith [(mul_eq_zero.mp this).resolve_left hc.ne']
  have hr0 : 0 < r := by exact_mod_cast (hsr ▸ hs0 : (0 : ℝ) < r)
  obtain ⟨e, he⟩ : ∃ e : ℕ, r.num = e := ⟨r.num.toNat, (Int.toNat_of_nonneg (Rat.num_pos.mpr hr0).le).symm⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ, f = r.den := ⟨_, rfl⟩
  have hf0 : 0 < f := hfdef ▸ r.den_pos
  have hcop : Nat.Coprime e f := by
    have := r.reduced; rw [he, ← hfdef] at this; simpa using this
  have hsef : s = (e : ℝ) / f := by
    rw [hsr, ← Rat.num_div_den r, he, ← hfdef]
    push_cast <;> ring
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf0
  have he1 : 1 ≤ e := by
    have : (0 : ℝ) < e := by
      have h1 := hs0; rw [hsef] at h1
      have h2 := mul_pos h1 hfR
      rwa [div_mul_cancel₀ _ hfR.ne'] at h2
    exact_mod_cast this
  have hef : e < f := by
    have : (e : ℝ) < f := by
      have := hs1; rw [hsef, div_lt_one hfR] at this; exact this
    exact_mod_cast this
  obtain ⟨d, hd⟩ : ∃ d, f = e + d := ⟨f - e, by omega⟩
  have hd1 : 1 ≤ d := by omega
  obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le (by linarith : (0 : ℤ) ≤ M)
  push_cast at hleg harea
  have hfd : (f : ℝ) = e + d := by rw [hd]; push_cast; ring
  have hNeq : N * d * (3 * e + 2 * d) ^ 2 = m' ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
    have hf' : (f : ℝ) ≠ 0 := hfR.ne'
    have key : (N : ℝ) * d * (3 * e + 2 * d) ^ 2 - (m' : ℝ) ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))
        = (f : ℝ) ^ 3 * ((N : ℝ) * (1 - s) * (2 + s) ^ 2 - (m' : ℝ) ^ 2 * (1 + s) * (2 - s ^ 2)) := by
      rw [hsef, hfd]
      have hed : (e : ℝ) + d ≠ 0 := by rw [← hfd]; exact hf'
      field_simp <;> ring
    rw [harea, sub_self, mul_zero, sub_eq_zero] at key
    exact_mod_cast key
  obtain ⟨na, nb, nc, hw⟩ := D.side_word_threeAlpha h 0
  set X' : ℕ := na * (e * (e + d)) + nb * (d * (2 * e + d)) + nc * (e + d) ^ 2 with hX'def
  have hXeq : X' * (2 * (e + d) + e) = m' * ((e + d + e) * (e + d) ^ 2) := by
    have hf' : (f : ℝ) ≠ 0 := hfR.ne'
    have hX'R : (X' : ℝ) * c = D.target.oppLen 0 * (f : ℝ) ^ 2 := by
      rw [hw, ha, hb, hsef, hfd, hX'def]
      have hed : (e : ℝ) + d ≠ 0 := by rw [← hfd]; exact hf'
      push_cast
      field_simp <;> ring
    have hlegf : D.target.oppLen 0 * (2 * f + e) = m' * c * (f + e) := by
      have := hleg
      rw [hsef] at this
      field_simp at this
      linear_combination this
    have hc' : c ≠ 0 := hc.ne'
    have : c * ((X' : ℝ) * (2 * (e + d) + e) - m' * ((e + d + e) * (e + d) ^ 2)) = 0 := by
      rw [hfd] at hlegf hX'R
      linear_combination (2 * ((e : ℝ) + d) + e) * hX'R + ((e : ℝ) + d) ^ 2 * hlegf
    have h2 := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc')
    exact_mod_cast h2
  have hcop' : Nat.Coprime e (e + d) := by rw [← hd]; exact hcop
  obtain ⟨m, hm⟩ := Erdos634.IsoAlpha.isoalpha_X_forces e (e + d) m' X' hcop' hXeq
  have hred : N * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
    rw [hm] at hNeq
    have h3 : 0 < (3 * e + 2 * d) ^ 2 := by positivity
    have e2 : 2 * (e + d) + e = 3 * e + 2 * d := by ring
    rw [e2] at hNeq
    have : (3 * e + 2 * d) ^ 2 * (N * d) = (3 * e + 2 * d) ^ 2 * (m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))) := by
      calc (3 * e + 2 * d) ^ 2 * (N * d) = N * d * (3 * e + 2 * d) ^ 2 := by ring
        _ = ((3 * e + 2 * d) * m) ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := hNeq
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_left h3 this
  subst hN
  obtain ⟨rfl, rfl, rfl⟩ := sol21 e d m he1 hd1 hred
  -- now e = 1, d = 1, m = 1: f = 2, s = 1/2, M = m' = 5
  have hf2 : (f : ℝ) = 2 := by rw [hfd]; norm_num
  have hs : s = 1 / 2 := by rw [hsef, hf2]; norm_num
  have hm5 : (m' : ℝ) = 5 := by
    have : m' = (2 * (1 + 1) + 1) * 1 := hm
    rw [this]; norm_num
  rw [hm5, hs] at hleg
  have hX : D.target.oppLen 0 = 3 * c := by linarith
  have hP2 : D.target.angleAt 2 = α + 2 * β := by
    have := D.target.angleAt_sum; rw [hP0, hP1] at this; linarith
  obtain ⟨s2, hs20, hs21, hc2, hX0, ha2, hb2, hX2, hX1⟩ := Row11.sides D hrel h hP0 hP1 hP2
  have hss : s2 = s := by
    have : c * (s2 - s) = 0 := by rw [ha] at ha2; linear_combination -ha2
    linarith [(mul_eq_zero.mp this).resolve_left hc.ne']
  rw [hss, hs] at hX2
  refine ⟨hc, ?_, ?_, hX, ?_, ?_⟩
  · rw [ha, hs]; ring
  · rw [hb, hs]; ring
  · rw [hX1, hX]
  · rw [hX2, hX]; ring

theorem tgt_oppLen_scale {N : ℕ} (r : ℝ) (hr : r ≠ 0) (D : CongruentDissection N) (k : Fin 3) :
    (Erdos634.Realizable.scaleDissection 0 r hr D).target.oppLen k = |r| * D.target.oppLen k := by
  unfold Tri.oppLen
  rw [Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.scaleDissection_target_pts]
  exact Erdos634.Realizable.homothetyEquiv_dist _ _ _ _ _

theorem mod_oppLen_scale {N : ℕ} (r : ℝ) (hr : r ≠ 0) (D : CongruentDissection N) (k : Fin 3) :
    (Erdos634.Realizable.scaleDissection 0 r hr D).model.oppLen k = |r| * D.model.oppLen k := by
  unfold Tri.oppLen
  rw [Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.scaleDissection_model_pts]
  exact Erdos634.Realizable.homothetyEquiv_dist _ _ _ _ _

/-- **The geometric instance, up to rescaling.**  A `CongruentDissection N` (N = 21) of the base-α
target admits a rescaled copy with target sides `(12,12,21)` and model sides `(2,3,4)`. -/
theorem six21_scaled {N : ℕ} (hN : N = 21) (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α) (hP1 : D.target.angleAt 1 = α) :
    ∃ D' : CongruentDissection N,
      D'.target.oppLen 0 = 12 ∧ D'.target.oppLen 1 = 12 ∧ D'.target.oppLen 2 = 21 ∧
      ∃ σ : Equiv.Perm (Fin 3), D'.model.oppLen (σ 0) = 2 ∧ D'.model.oppLen (σ 1) = 3 ∧
        D'.model.oppLen (σ 2) = 4 := by
  obtain ⟨hc, ha, hb, h0, h1, h2⟩ := six21_numbers hN D hα hrel h hP0 hP1
  have hr : (4 / c : ℝ) ≠ 0 := by positivity
  have habs : |(4 / c : ℝ)| = 4 / c := abs_of_pos (by positivity)
  refine ⟨Erdos634.Realizable.scaleDissection 0 (4 / c) hr D, ?_, ?_, ?_, ?_⟩
  · rw [tgt_oppLen_scale, habs, h0]; field_simp; ring
  · rw [tgt_oppLen_scale, habs, h1]; field_simp; ring
  · rw [tgt_oppLen_scale, habs, h2]; field_simp
  · obtain ⟨σ, -, o0, -, o1, -, o2⟩ := h
    refine ⟨σ, ?_, ?_, ?_⟩
    · rw [mod_oppLen_scale, habs, o0, ha]; field_simp; ring
    · rw [mod_oppLen_scale, habs, o1, hb]; field_simp
    · rw [mod_oppLen_scale, habs, o2]; field_simp

end SIX
end Erdos634.Geometry

#print axioms Erdos634.Geometry.SIX.six21_scaled
