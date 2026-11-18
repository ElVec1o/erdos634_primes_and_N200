-- Draft/ThetaNotch4Rho.lean -- TASK A: for coprime 2 <= e < f the residue rho0f e f = (e * M0f) % f is nonzero; the clean corollary.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
**`rho0f e f != 0` for coprime `2 <= e < f`.**  Reason (from the definitions of `n0f`, `M0f`):
* `f - e >= 2`: with `n = n0f e f = ceil(e/(f-e))` one has `2 n <= e + 1`, and then both `ceil(f n / e) <= f - 1` and
  `n + ceil(e n / f) <= f - 1`; so `0 < M0f < f`; `f | e M0f` with `gcd(e,f) = 1` would give `f | M0f`, impossible.
* `f - e = 1` (`f = e + 1`): `n = e`, `M0f = 2 e`, and `e + 1 | 2 e` forces `e = 1`.
Coprimality is NEEDED for `e >= 2`: awk survey (`e < f <= 600`, all `e`): 2745 non-coprime pairs with `e >= 2` and `f | e M0f`
(first ones `(2,4), (2,6), (3,6), (2,8), (4,8), (3,9), (2,10)`).  `e = 1` has `rho = 0` for `(1,2), (1,3), (1,6)` at least, handled by
`thetaTiled_e1` (`t0f 1 f = 2 f`, proved here).
CORROLARY `thetaTiled_all`: coprime `1 <= e < f`, every `t >= t0f e f`: `ThetaTiled e f (f*f - e*e) t`.
CREDIT: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  INTERNAL BUILD ONLY, UNAUDITED.
Prior art for `thetaTiled_all` (existence, not the explicit threshold): M. Beeson, arXiv 1206.2229 v5 (8 Nov 2026), Theorem 24
and Corollary 4 (every rational tile with 3 alpha + 2 beta = pi tiles some isosceles triangle with base angles alpha + beta,
for some, in general very large, N; Theorem 24 for a^2 c < b (a^2 + b^2), Theorem 23 = Laczkovich's construction for
b/c < 0.5698 and Lemma 50 for the dichotomy); eventual tiling of every row theta_t: Paliy (note of 29 Sep 2026).  What `thetaTiled_all`
adds is the explicit threshold `t0f e f` and all t >= t0f.  The 48-tile seed for (2,3,4): Beeson, Fig. 16 of 1206.2229 v5.
Scale-one lower bounds of the same kind for the same target: Beeson Lemma 8, Lemma 52, Theorem 25 (1206.2229 v5).
-/
import Erdos634.Draft.ThetaNotch3Fin
import Erdos634.Draft.ThetaNotchInst

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled)
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- thick/ordinary case `f - e >= 2`: both ceilings are `<= f - 1` -/
theorem M0_aux (d k n : ℕ) (h1 : 2 + d ≤ (2 + k) * n) (h2 : (2 + k) * n < (2 + d) + (2 + k)) :
    ((4 + d + k) * n + (2 + d) - 1) / (2 + d) < 4 + d + k ∧
    n + ((2 + d) * n + (4 + d + k) - 1) / (4 + d + k) < 4 + d + k ∧ 0 < n := by
  have hn1 : 1 ≤ n := by
    by_contra hc
    have h0 : n = 0 := by omega
    subst h0; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h3 : 2 * m < 2 + d := by nlinarith [Nat.zero_le (k * m)]
  have h4 : 2 * (m + 1) ≤ (2 + d) + 1 := by omega
  refine ⟨?_, ?_, by omega⟩
  · rw [Nat.div_lt_iff_lt_mul (by omega)]
    have hX : (4 + d + k) * (m + 1) + (2 + d) ≤ (4 + d + k) * (2 + d) := by
      nlinarith [Nat.zero_le (d * k), Nat.zero_le (d * d), Nat.zero_le (k * m), Nat.zero_le (d * m)]
    have : (4 + d + k) * (2 + d) = (4 + d + k) * (2 + d) := rfl
    omega
  · -- r = f - 1 - n
    obtain ⟨r, hr⟩ : ∃ r, 4 + d + k = (m + 1) + 1 + r := ⟨4 + d + k - (m + 1) - 1, by omega⟩
    have hen : (2 + d) * (m + 1) ≤ r * (4 + d + k) := by
      have e1 : (4 + d + k) * ((m + 1) + 1 + r) = (4 + d + k) * (4 + d + k) := by rw [← hr]
      have h5 : (m + 1) * ((2 + d) + (4 + d + k)) + (4 + d + k) ≤ (4 + d + k) * (4 + d + k) := by
        nlinarith [Nat.zero_le (d * k), Nat.zero_le (d * d), Nat.zero_le (k * m), Nat.zero_le (d * m),
          Nat.zero_le (k * k), Nat.zero_le (m * m)]
      nlinarith [e1, h5]
    have hc : ((2 + d) * (m + 1) + (4 + d + k) - 1) / (4 + d + k) < r + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have : (r + 1) * (4 + d + k) = r * (4 + d + k) + (4 + d + k) := by ring
      omega
    omega

theorem M0f_pos_lt (e f : ℕ) (he : 2 ≤ e) (hg : e + 2 ≤ f) : 0 < M0f e f ∧ M0f e f < f := by
  obtain ⟨d, rfl⟩ : ∃ d, e = 2 + d := ⟨e - 2, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, f = 4 + d + k := ⟨f - 4 - d, by omega⟩
  have hs : 4 + d + k - (2 + d) = 2 + k := by omega
  obtain ⟨c1, c2⟩ := ceil_facts (2 + d) (4 + d + k - (2 + d)) (by omega)
  have hn : n0f (2 + d) (4 + d + k) = ((2 + d) + (4 + d + k - (2 + d)) - 1) / (4 + d + k - (2 + d)) := rfl
  rw [← hn] at c1 c2
  rw [hs] at c1 c2
  obtain ⟨a1, a2, a3⟩ := M0_aux d k (n0f (2 + d) (4 + d + k)) c1 (by omega)
  unfold M0f
  constructor
  · apply lt_max_of_lt_right
    exact lt_of_lt_of_le a3 (Nat.le_add_right _ _)
  · exact max_lt a1 a2

/-- the `f = e + 1` case: `M0f e (e+1) = 2 e` for `e >= 1` -/
theorem M0f_succ (e : ℕ) (he : 1 ≤ e) : M0f e (e + 1) = 2 * e := by
  have hn : n0f e (e + 1) = e := by
    unfold n0f
    have : e + 1 - e = 1 := by omega
    rw [this]; simp
  unfold M0f
  rw [hn]
  have t2 : e + (e * e + (e + 1) - 1) / (e + 1) = 2 * e := by
    have : (e * e + (e + 1) - 1) / (e + 1) = e := by
      have h : e * e + (e + 1) - 1 = e * e + e := by omega
      rw [h]
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
    omega
  have t1 : ((e + 1) * e + e - 1) / e ≤ 2 * e := by
    apply Nat.div_le_of_le_mul
    have hx : (e + 1) * e = e * e + e := by ring
    have hy : e * (2 * e) = 2 * (e * e) := by ring
    have hee : 2 * e ≤ e * e + 1 := by nlinarith
    omega
  rw [t2]
  exact max_eq_right t1

/-- **TASK A.**  For coprime `e, f` with `2 <= e < f`, `rho0f e f != 0`. -/
theorem rho0f_ne_zero (e f : ℕ) (he : 2 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) : rho0f e f ≠ 0 := by
  intro h0
  unfold rho0f at h0
  have hdvd : f ∣ e * M0f e f := Nat.dvd_of_mod_eq_zero h0
  have hdvd2 : f ∣ M0f e f := Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hco) hdvd
  by_cases hg : e + 2 ≤ f
  · obtain ⟨p, q⟩ := M0f_pos_lt e f he hg
    have := Nat.le_of_dvd p hdvd2
    omega
  · have hf : f = e + 1 := by omega
    subst hf
    rw [M0f_succ e (by omega)] at hdvd2
    obtain ⟨c, hc⟩ := hdvd2
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith

/-- `t0f 1 f = 2 f` for `f >= 2` -/
theorem t0f_one (f : ℕ) (hf : 2 ≤ f) : t0f 1 f = 2 * f := by
  have hn : n0f 1 f = 1 := by
    unfold n0f
    have : 1 + (f - 1) - 1 = f - 1 := by omega
    rw [this]
    exact Nat.div_self (by omega)
  have hb : 0 < f * f - 1 * 1 := by
    have : 4 ≤ f * f := by nlinarith
    omega
  have hj : j0f 1 f = 1 := by
    unfold j0f
    rw [hn]
    have : 1 * 1 + (f * f - 1 * 1) - 1 = f * f - 1 * 1 := by omega
    rw [this]
    exact Nat.div_self hb
  have hM : M0f 1 f = f := by
    unfold M0f
    rw [hn]
    have t2 : 1 + (1 * 1 + f - 1) / f = 2 := by
      have : (1 * 1 + f - 1) / f = 1 := by
        have : 1 * 1 + f - 1 = f := by omega
        rw [this]; exact Nat.div_self (by omega)
      omega
    have t1 : (f * 1 + 1 - 1) / 1 = f := by simp
    rw [t1, t2]
    exact max_eq_left hf
  unfold t0f
  rw [hj, hM]; ring

/-- **THE CLEAN COROLLARY.**  For coprime `1 <= e < f` and every `t >= t0f e f`, `theta_t(e,f)` is tiled
(`e = 1`: `thetaTiled_e1`; `e >= 2`: `thetaTiled_general` with `rho0f_ne_zero`). -/
theorem thetaTiled_all (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    ∀ t, t0f e f ≤ t → ThetaTiled e f (f * f - e * e) t := by
  by_cases h1 : e = 1
  · subst h1
    intro t ht
    rw [t0f_one f (by omega)] at ht
    exact thetaTiled_e1 f (by omega) t ht
  · exact thetaTiled_general e f he hef (rho0f_ne_zero e f (by omega) hef hco)

theorem tileCount_all (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (t : ℕ) (ht : t0f e f ≤ t) :
    TileCount ((f * f - e * e) * t * t) := by
  obtain ⟨D, -, -⟩ := thetaTiled_all e f he hef hco t ht
  exact ⟨D⟩

/-! witnesses / controls -/
theorem coprime_witnesses : Nat.Coprime 2 3 ∧ Nat.Coprime 3 4 ∧ Nat.Coprime 5 7 ∧ Nat.Coprime 3 8 := by decide

/-- controls: the lemma is not vacuous (nonzero residues at several rows, computed) and noncoprime rows do vanish (so coprimality
cannot be dropped). -/
theorem rho_values : rho0f 2 3 ≠ 0 ∧ rho0f 3 4 ≠ 0 ∧ rho0f 5 7 ≠ 0 ∧ rho0f 3 8 ≠ 0 ∧ rho0f 7 10 ≠ 0 := by decide
theorem rho_noncoprime_zero : rho0f 2 4 = 0 ∧ rho0f 2 6 = 0 ∧ rho0f 3 6 = 0 := by decide

end
end Erdos634.Draft.ThetaNotch
