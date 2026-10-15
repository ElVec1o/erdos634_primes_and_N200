/-
Draft/NSQS1.lean — S1 (target (β, β, 3α)) WITHOUT `Squarefree N`.

For squarefree `N`, `s1_arith_sqfree` forces `M = p + q` in `N (p+q)² = M² (3q²−p²)` and `s1_baseBetaTiled_of_arith` +
I6 close the branch.  For general `N` the equation gives (this file, `s1_arith_t`)  `M = t (p+q)`  and  `N = t² (3q²−p²)`
for a positive integer `t`; `t = 1` is the base-β member `(e,f) = (p,q)` (closed by I6), `t ≥ 2` is the scaled member.
`S1Free N`: there is no `t ≥ 2` with `N = t² (3q²−p²)`, `0 < p < q` coprime.   `s1Closed_of_free : S1Free N → S1Closed N`.
(Alternative closure, N-general, already in Lean: an odd-valuation prime ℓ with 3 a non-residue: `scaleBaseBeta_qnr`.)  No sorry, no native_decide.
-/
import Erdos634.Draft.CompositeFinal4

namespace Erdos634.Draft.NSQS1

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeS1Arith

theorem s1_arith_t {N : ℕ} {p q M : ℤ} (hp : 0 < p) (hpq : p < q) (hcop : IsCoprime p q) (hM : 0 < M)
    (heq : (N : ℤ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2)) :
    ∃ t : ℤ, 0 < t ∧ M = t * (p + q) ∧ (N : ℤ) = t ^ 2 * (3 * q ^ 2 - p ^ 2) := by
  have hdpos : 0 < p + q := by omega
  have hYpos : 0 < 3 * q ^ 2 - p ^ 2 := by nlinarith
  have hgcd : 0 < Int.gcd (p + q) M := Int.gcd_pos_of_ne_zero_right _ hM.ne'
  obtain ⟨g, d', M', hg, hg1, hd, hM'⟩ := Int.exists_gcd_one' hgcd
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hd'pos : 0 < d' := by
    by_contra h; push Not at h; nlinarith
  have hM'pos : 0 < M' := by
    by_contra h; push Not at h; nlinarith
  set Y : ℤ := 3 * q ^ 2 - p ^ 2 with hY
  have h1 : (N : ℤ) * d' ^ 2 = M' ^ 2 * Y := by
    have : (g : ℤ) ^ 2 * ((N : ℤ) * d' ^ 2) = (g : ℤ) ^ 2 * (M' ^ 2 * Y) := by
      have := heq; rw [hd, hM'] at this; linear_combination this
    exact mul_left_cancel₀ (pow_pos hgZ 2).ne' this
  have hcop' : IsCoprime d' M' := Int.isCoprime_iff_gcd_eq_one.mpr hg1
  have hdY : d' ^ 2 ∣ Y := by
    have : d' ^ 2 ∣ Y * M' ^ 2 := ⟨N, by rw [mul_comm, ← h1]; ring⟩
    exact (hcop'.pow (m := 2) (n := 2)).dvd_of_dvd_mul_right this
  have hd'd : d' ∣ p + q := ⟨g, by linarith [hd]⟩
  have hcp : IsCoprime (p + q) p := Erdos634.Draft.CompositeFinal4.isCoprime_sum_left' hcop
  have hd'p : IsCoprime d' p := hcp.of_isCoprime_of_dvd_left hd'd
  have hd'Y : d' ∣ Y := Dvd.dvd.trans (dvd_pow_self d' two_ne_zero) hdY
  have hd'2 : d' ∣ 2 * p ^ 2 := by
    have e : 2 * p ^ 2 = Y - (p + q) * (3 * (q - p)) := by rw [hY]; ring
    rw [e]
    exact dvd_sub hd'Y (Dvd.dvd.mul_right hd'd _)
  have hd'2' : d' ∣ 2 := (hd'p.pow_right (n := 2)).dvd_of_dvd_mul_right hd'2
  have hle : d' ≤ 2 := Int.le_of_dvd (by norm_num) hd'2'
  have hd'12 : d' = 1 ∨ d' = 2 := by omega
  rcases hd'12 with rfl | rfl
  · refine ⟨M', hM'pos, ?_, ?_⟩
    · rw [hM', hd]; ring
    · have := h1; linarith
  · exfalso
    -- d' = 2 : 2 ∣ p + q, so p, q are both odd, but then 4 ∤ Y while 4 ∣ Y
    obtain ⟨k, hk⟩ := hdY
    have h2d : (2 : ℤ) ∣ p + q := hd'd
    have hnb : ¬ ((2 : ℤ) ∣ p ∧ (2 : ℤ) ∣ q) := by
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      obtain ⟨u, v, huv⟩ := hcop
      have : 2 * (u * a + v * b) = 1 := by rw [ha, hb] at huv; linarith
      omega
    rcases Int.even_or_odd' p with ⟨a, ha | ha⟩ <;> rcases Int.even_or_odd' q with ⟨b, hb | hb⟩
    · exact hnb ⟨⟨a, by omega⟩, ⟨b, by omega⟩⟩
    · omega
    · omega
    · have : Y = 4 * (3 * b ^ 2 + 3 * b - a ^ 2 - a) + 2 := by rw [hY, ha, hb]; ring
      omega

/-- The arithmetic hypothesis replacing `Squarefree N` in S1: no `t ≥ 2` with `N = t² (3q² − p²)`, `0 < p < q` coprime. -/
def S1Free (N : ℕ) : Prop :=
  ∀ t p q : ℤ, 2 ≤ t → 0 < p → p < q → IsCoprime p q → (N : ℤ) = t ^ 2 * (3 * q ^ 2 - p ^ 2) → False

theorem s1_arith_of_free {N : ℕ} (h : S1Free N) :
    ∀ p q M : ℤ, 0 < p → p < q → IsCoprime p q → 0 < M →
    (N : ℤ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2) → M = p + q := by
  intro p q M hp hpq hcop hM heq
  obtain ⟨t, ht, hMt, hNt⟩ := s1_arith_t hp hpq hcop hM heq
  by_cases h1 : t = 1
  · rw [hMt, h1]; ring
  · exact (h t p q (by omega) hp hpq hcop hNt).elim

theorem s1Closed_of_free (N : ℕ) (h : S1Free N) : S1Closed N := by
  intro D α β a b c r hα hrel hmod har hbr htgt
  exact not_baseBetaTiled
    (Erdos634.Draft.CompositeFinal4.s1_baseBetaTiled_of_arith N (s1_arith_of_free h) D α β a b c r hα hrel hmod har hbr htgt)

end Erdos634.Draft.NSQS1

#print axioms Erdos634.Draft.NSQS1.s1_arith_t
#print axioms Erdos634.Draft.NSQS1.s1Closed_of_free
