import Mathlib.Tactic

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem C, module 1: the rigidity window of the `γ = 2α` tile  (; formalization of conjV.md §2 (R))

Tile `(a, b, c) = (u², v² − u², uv)`, `gcd(u, v) = 1`, `u < v`.  The relation lattice
`{(x, y, z) ∈ ℤ³ : x a + y b + z c = 0}` is `{(wu + vs, uw, −su − wv)}` (`rel_param`), and from it:

* `rigid_a` (RA): `n a = x a + y b + z c` with `n < v` forces `(x, y, z) = (n, 0, 0)`;
* `rigid_b` (RB): `n b = …` with `n < u` forces `(0, n, 0)`;
* `rigid_c` (RC): `n c = …` with `n < v` forces `y = 0`, and with `n < u` forces `(0, 0, n)`;
* sharpness `ra_sharp, rb_sharp, rc_sharp` (`v a = u c`, `u b = d (a + c)`): the bounds `v, u, v` are attained.

No geometry; pure arithmetic.  Does NOT use the tile being a triangle.
-/

namespace Erdos634.Draft.ThmC

/-- Parametrisation of the relation lattice of `(u², v² − u², uv)`. -/
theorem rel_param {u v x y z : ℤ} (hcop : IsCoprime u v) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : x * u ^ 2 + y * (v ^ 2 - u ^ 2) + z * (u * v) = 0) :
    ∃ s w : ℤ, x = w * u + v * s ∧ y = u * w ∧ z = -(s * u) - w * v := by
  have hcu : IsCoprime u (v ^ 2 - u ^ 2) := by
    obtain ⟨a, b, hab⟩ := (hcop.pow_right : IsCoprime u (v ^ 2))
    exact ⟨a + b * u, b, by linear_combination hab⟩
  have h1 : u ∣ y * (v ^ 2 - u ^ 2) := ⟨-(x * u) - z * v, by linear_combination h⟩
  have h2 : u ∣ y := hcu.dvd_of_dvd_mul_right h1
  obtain ⟨w, hw⟩ := h2
  subst hw
  have h3 : x * u + w * (v ^ 2 - u ^ 2) + z * v = 0 := by
    have : u * (x * u + w * (v ^ 2 - u ^ 2) + z * v) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left hu
  have h4 : v ∣ u * (x - w * u) := ⟨-(w * v) - z, by linear_combination h3⟩
  have h5 : v ∣ x - w * u := hcop.symm.dvd_of_dvd_mul_left h4
  obtain ⟨s, hs⟩ := h5
  have hx : x = w * u + v * s := by linarith
  refine ⟨s, w, hx, rfl, ?_⟩
  have h6 : v * (z + s * u + w * v) = 0 := by linear_combination h3 - u * hx
  have := (mul_eq_zero.mp h6).resolve_left hv
  linarith

/-! ### integer cores -/

theorem ra_int {u v n x y z s w : ℤ} (hu : 0 < u) (huv : u < v) (hn0 : 0 ≤ n) (hnv : n < v)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (e1 : x - n = w * u + v * s) (e2 : y = u * w) (e3 : z = -(s * u) - w * v) :
    x = n ∧ y = 0 ∧ z = 0 := by
  have hw0 : 0 ≤ w := by
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_pos hu (neg_pos.mpr hneg)]
  have hw : w = 0 := by
    by_contra hne
    have hw1 : 1 ≤ w := by omega
    have hs : s ≤ -w - 1 := by
      by_contra hcon
      push_neg at hcon
      have h0 : -w ≤ s := by omega
      have h1 : -w * u ≤ s * u := by nlinarith [mul_nonneg (sub_nonneg.mpr h0) hu.le]
      nlinarith [mul_pos (by omega : (0 : ℤ) < w) (sub_pos.mpr huv)]
    have h2 : v * s ≤ v * (-w - 1) := mul_le_mul_of_nonneg_left hs (by linarith)
    nlinarith [mul_pos (by omega : (0 : ℤ) < w) (sub_pos.mpr huv)]
  subst hw
  have hv : 0 < v := by linarith
  have hs0 : s ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos hcon hu]
  have hs1 : 0 ≤ s := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -1 - s) hv.le]
  have : s = 0 := le_antisymm hs0 hs1
  subst this
  refine ⟨by linarith, by linarith, by linarith⟩

theorem rb_int {u v n x y z s w : ℤ} (hu : 0 < u) (huv : u < v) (hn0 : 0 ≤ n) (hnu : n < u)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (e1 : x = w * u + v * s) (e2 : y - n = u * w) (e3 : z = -(s * u) - w * v) :
    x = 0 ∧ y = n ∧ z = 0 := by
  have key : x * u + z * v = w * (u ^ 2 - v ^ 2) := by rw [e1, e3]; ring
  have hwle : w ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos hcon (by nlinarith [mul_pos (sub_pos.mpr huv) (by linarith : (0 : ℤ) < v + u)] : (0 : ℤ) < v ^ 2 - u ^ 2),
      mul_nonneg hx hu.le, mul_nonneg hz (by linarith : (0 : ℤ) ≤ v)]
  have hwge : 0 ≤ w := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg hu.le (by linarith : (0 : ℤ) ≤ -w - 1)]
  have hw : w = 0 := le_antisymm hwle hwge
  subst hw
  have hv : 0 < v := by linarith
  have hs0 : 0 ≤ s := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -1 - s) hv.le]
  have hs1 : s ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos hcon hu]
  have : s = 0 := le_antisymm hs1 hs0
  subst this
  refine ⟨by linarith, by linarith, by linarith⟩

/-- RC, first half: `n < v` forces `w = 0`. -/
theorem rc_int_w {u v n x y z s w : ℤ} (hu : 0 < u) (huv : u < v) (hn0 : 0 ≤ n) (hnv : n < v)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (e1 : x = w * u + v * s) (e2 : y = u * w) (e3 : z - n = -(s * u) - w * v) : w = 0 := by
  have hw0 : 0 ≤ w := by
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_pos hu (neg_pos.mpr hneg)]
  by_contra hne
  have hw1 : 1 ≤ w := by omega
  have hwd : 0 < w * (v - u) := mul_pos (by omega) (sub_pos.mpr huv)
  by_cases hs : 1 ≤ s
  · nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ s - 1) hu.le, mul_nonneg (by omega : (0 : ℤ) ≤ w - 1) (by linarith : (0 : ℤ) ≤ v)]
  · have hs' : s ≤ 0 := by omega
    have hs2 : 1 - w ≤ s := by
      by_contra hcon
      push_neg at hcon
      have : s ≤ -w := by omega
      nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0 : ℤ) ≤ v)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs2) hu.le, mul_nonneg (by omega : (0 : ℤ) ≤ w - 1) (sub_nonneg.mpr huv.le)]

theorem rc_int_all {u v n x y z s w : ℤ} (hu : 0 < u) (huv : u < v) (hn0 : 0 ≤ n) (hnu : n < u)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (e1 : x = w * u + v * s) (e2 : y = u * w) (e3 : z - n = -(s * u) - w * v) :
    x = 0 ∧ y = 0 ∧ z = n := by
  have hw := rc_int_w hu huv hn0 (by linarith) hx hy hz e1 e2 e3
  subst hw
  have hv : 0 < v := by linarith
  have hs0 : 0 ≤ s := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -1 - s) hv.le]
  have hs1 : s ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ s - 1) hu.le]
  have : s = 0 := le_antisymm hs1 hs0
  subst this
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ### natural-number statements -/

section nat

variable {u v b n x y z : ℕ}

private theorem cast_b (hb : b + u * u = v * v) : (b : ℤ) = (v : ℤ) ^ 2 - (u : ℤ) ^ 2 := by
  have : (b : ℤ) + u * u = v * v := by exact_mod_cast hb
  linear_combination this

private theorem cop (hcop : Nat.Coprime u v) : IsCoprime (u : ℤ) (v : ℤ) :=
  Nat.isCoprime_iff_coprime.mpr hcop

/-- **RA.**  `n a = x a + y b + z c` with `n < v` is the pure decomposition. -/
theorem rigid_a (hcop : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) (hb : b + u * u = v * v)
    (hn : n < v) (h : n * (u * u) = x * (u * u) + y * b + z * (u * v)) :
    x = n ∧ y = 0 ∧ z = 0 := by
  have hb' := cast_b hb
  have h' : ((x : ℤ) - n) * (u : ℤ) ^ 2 + (y : ℤ) * ((v : ℤ) ^ 2 - (u : ℤ) ^ 2) + (z : ℤ) * ((u : ℤ) * v) = 0 := by
    have : (n : ℤ) * (u * u) = x * (u * u) + y * b + z * (u * v) := by exact_mod_cast h
    rw [hb'] at this
    linear_combination (-1 : ℤ) * this
  obtain ⟨s, w, e1, e2, e3⟩ := rel_param (cop hcop) (by exact_mod_cast hu.ne') (by omega) h'
  obtain ⟨hx, hy, hz⟩ := ra_int (u := u) (v := v) (n := n) (x := x) (y := y) (z := z) (s := s) (w := w)
    (by exact_mod_cast hu) (by exact_mod_cast huv) (by positivity) (by exact_mod_cast hn)
    (by positivity) (by positivity) (by positivity) e1 e2 e3
  exact ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hz⟩

/-- **RB.**  `n b = x a + y b + z c` with `n < u` is the pure decomposition. -/
theorem rigid_b (hcop : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) (hb : b + u * u = v * v)
    (hn : n < u) (h : n * b = x * (u * u) + y * b + z * (u * v)) :
    x = 0 ∧ y = n ∧ z = 0 := by
  have hb' := cast_b hb
  have h' : (x : ℤ) * (u : ℤ) ^ 2 + ((y : ℤ) - n) * ((v : ℤ) ^ 2 - (u : ℤ) ^ 2) + (z : ℤ) * ((u : ℤ) * v) = 0 := by
    have : (n : ℤ) * b = x * (u * u) + y * b + z * (u * v) := by exact_mod_cast h
    rw [hb'] at this
    linear_combination (-1 : ℤ) * this
  obtain ⟨s, w, e1, e2, e3⟩ := rel_param (cop hcop) (by exact_mod_cast hu.ne') (by omega) h'
  obtain ⟨hx, hy, hz⟩ := rb_int (u := u) (v := v) (n := n) (x := x) (y := y) (z := z) (s := s) (w := w)
    (by exact_mod_cast hu) (by exact_mod_cast huv) (by positivity) (by exact_mod_cast hn)
    (by positivity) (by positivity) (by positivity) e1 e2 (by linarith)
  exact ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hz⟩

/-- **RC.**  `n c = x a + y b + z c` with `n < v` has no `b`, and with `n < u` is the pure decomposition. -/
theorem rigid_c (hcop : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) (hb : b + u * u = v * v)
    (h : n * (u * v) = x * (u * u) + y * b + z * (u * v)) :
    (n < v → y = 0) ∧ (n < u → x = 0 ∧ y = 0 ∧ z = n) := by
  have hb' := cast_b hb
  have h' : (x : ℤ) * (u : ℤ) ^ 2 + (y : ℤ) * ((v : ℤ) ^ 2 - (u : ℤ) ^ 2) + ((z : ℤ) - n) * ((u : ℤ) * v) = 0 := by
    have : (n : ℤ) * (u * v) = x * (u * u) + y * b + z * (u * v) := by exact_mod_cast h
    rw [hb'] at this
    linear_combination (-1 : ℤ) * this
  obtain ⟨s, w, e1, e2, e3⟩ := rel_param (cop hcop) (by exact_mod_cast hu.ne') (by omega) h'
  have hu' : (0 : ℤ) < u := by exact_mod_cast hu
  have huv' : (u : ℤ) < v := by exact_mod_cast huv
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have hw := rc_int_w (u := u) (v := v) (n := n) (x := x) (y := y) (z := z) (s := s) (w := w) hu' huv'
      (by positivity) (by exact_mod_cast hn) (by positivity) (by positivity) (by positivity) e1 e2 (by linarith)
    subst hw
    have : (y : ℤ) = 0 := by rw [e2]; ring
    exact_mod_cast this
  · obtain ⟨hx, hy, hz⟩ := rc_int_all (u := u) (v := v) (n := n) (x := x) (y := y) (z := z) (s := s) (w := w) hu' huv'
      (by positivity) (by exact_mod_cast hn) (by positivity) (by positivity) (by positivity) e1 e2 (by linarith)
    exact ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hz⟩

end nat

/-! ### sharpness (the minima `(v, u, v)` are attained) and a concrete witness -/

theorem ra_sharp (u v : ℕ) : v * (u * u) = 0 * (u * u) + 0 * (v * v - u * u) + u * (u * v) := by
  ring

theorem rc_sharp (u v : ℕ) : u * (u * v) = v * (u * u) + 0 * (v * v - u * u) + 0 * (u * v) := by ring

/-- `u b = d (a + c)` with `d = v − u`: the `b`-rigidity bound `u` is attained. -/
theorem rb_sharp (u d : ℕ) :
    u * (d * (u + (u + d))) = d * (u * u) + 0 * (d * (u + (u + d))) + d * (u * (u + d)) := by ring

/-- witness: `(u, v) = (3, 5)`, tile `(9, 16, 15)`: RA at `n = 4`, mixed relation at `n = 5`. -/
example : (4 : ℕ) = 4 ∧ (0 : ℕ) = 0 ∧ (0 : ℕ) = 0 :=
  rigid_a (u := 3) (v := 5) (b := 16) (n := 4) (x := 4) (y := 0) (z := 0)
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : 5 * (3 * 3) = 0 * (3 * 3) + 0 * 16 + 3 * (3 * 5) := by norm_num

end Erdos634.Draft.ThmC

#print axioms Erdos634.Draft.ThmC.rigid_a
#print axioms Erdos634.Draft.ThmC.rigid_b
#print axioms Erdos634.Draft.ThmC.rigid_c
