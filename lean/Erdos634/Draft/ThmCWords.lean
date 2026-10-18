import Mathlib.Tactic

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem C, module 2: the word bound (Lemma L at general `g` and the counting step)  

Tile `(a, b, c) = (u², d(2u + d), u(u + d))` with `v = u + d`, `d > 0`, `gcd(u, v) = 1`.
A leg of `T(g)` has length `g u b`, the base `g v b`.  If `p a + q b + r c` is such a length (naturals)
and `⌊g v / u⌋ · d < u`, then `r < u`:  **no side of `T(g)` can carry `u` edges of type `c`.**

* `word_core`   : `p u + r v = X (u + v)`, `X < u`  ⟹  `r ≤ X`  (mod-`v` argument; `v` coprime to `u`).
* `leg_word_bound`, `base_word_bound` : the two sides.
Pure arithmetic; hand statement `conjV.md` §2 "Lemma L at general g" (audit point 3).
-/

namespace Erdos634.Draft.ThmC

/-- the core: `p u + r (u+d) = X (2u + d)` with `X < u` gives `r ≤ X`. -/
theorem word_core {u d p r X : ℕ} (hcop : Nat.Coprime u (u + d)) (hX : X < u)
    (h : p * u + r * (u + d) = X * (u + (u + d))) : r ≤ X := by
  have hdiv : ((u + d : ℕ) : ℤ) ∣ ((p : ℤ) - X) * u := by
    refine ⟨(X : ℤ) - r, ?_⟩
    have : (p : ℤ) * u + r * (u + d) = X * (u + (u + d)) := by exact_mod_cast h
    push_cast
    linear_combination this
  have hc : IsCoprime ((u + d : ℕ) : ℤ) (u : ℤ) := (Nat.isCoprime_iff_coprime.mpr hcop).symm
  have hdiv2 : ((u + d : ℕ) : ℤ) ∣ (p : ℤ) - X := hc.dvd_of_dvd_mul_right hdiv
  have hpX : X ≤ p := by
    by_contra hcon
    push_neg at hcon
    have h1 : ((u + d : ℕ) : ℤ) ∣ (X : ℤ) - p := by
      have := dvd_neg.mpr hdiv2
      simpa using this
    have h2 := Int.le_of_dvd (by omega) h1
    push_cast at h2
    omega
  have h3 : r * (u + d) ≤ X * (u + d) := by nlinarith [Nat.mul_le_mul_right u hpX]
  exact Nat.le_of_mul_le_mul_right h3 (by omega : 0 < u + d)

/-- **Leg words.**  `p a + q b + r c = g u b`, `b = d(u+v)`, `v = u + d`, `⌊g v / u⌋ d < u` ⟹ `r < u`. -/
theorem leg_word_bound {u d g p q r : ℕ} (hd : 0 < d) (hu : 0 < u) (hcop : Nat.Coprime u (u + d))
    (hcond : (g * (u + d) / u) * d < u)
    (h : p * (u * u) + q * (d * (u + (u + d))) + r * (u * (u + d)) = g * u * (d * (u + (u + d)))) :
    r < u := by
  set b := d * (u + (u + d)) with hb
  have hbpos : 0 < b := by positivity
  have hcb : Nat.Coprime u b := by
    have hd' : Nat.Coprime u d := by
      have := hcop
      rw [Nat.coprime_self_add_right] at this
      exact this
    have h2 : Nat.Coprime u (u + (u + d)) := by
      rw [Nat.coprime_self_add_right]; exact hcop
    exact Nat.Coprime.mul_right hd' h2
  -- u ∣ q
  have h1 : u ∣ (p * (u * u) + r * (u * (u + d))) + q * b := by
    have : (p * (u * u) + r * (u * (u + d))) + q * b = g * u * b := by linarith
    rw [this]; exact ⟨g * b, by ring⟩
  have h2 : u ∣ p * (u * u) + r * (u * (u + d)) :=
    ⟨p * u + r * (u + d), by ring⟩
  have h3 : u ∣ q * b := (Nat.dvd_add_right h2).mp h1
  have h4 : u ∣ q := hcb.dvd_of_dvd_mul_right h3
  obtain ⟨q', rfl⟩ := h4
  have h5 : p * u + q' * b + r * (u + d) = g * b := by
    have : u * (p * u + q' * b + r * (u + d)) = u * (g * b) := by
      have := h
      nlinarith [this]
    exact Nat.eq_of_mul_eq_mul_left hu this
  have hq'g : q' ≤ g := by
    have : q' * b ≤ g * b := by linarith [h5, Nat.zero_le (p * u), Nat.zero_le (r * (u + d))]
    exact Nat.le_of_mul_le_mul_right this hbpos
  obtain ⟨m, hm⟩ : ∃ m, g = q' + m := ⟨g - q', by omega⟩
  have h6 : p * u + r * (u + d) = (m * d) * (u + (u + d)) := by
    have : p * u + r * (u + d) + q' * b = m * b + q' * b := by
      rw [hm] at h5; nlinarith [h5]
    have := Nat.add_right_cancel this
    rw [this, hb]; ring
  have hX : m * d < u := by
    have hgle : g ≤ g * (u + d) / u := by
      rw [Nat.le_div_iff_mul_le hu]; nlinarith
    have : m * d ≤ (g * (u + d) / u) * d := Nat.mul_le_mul_right _ (le_trans (by omega : m ≤ g) hgle)
    exact lt_of_le_of_lt this hcond
  exact lt_of_le_of_lt (word_core hcop hX h6) hX

/-- **Base words.**  `p a + q b + r c = g v b` ⟹ `r < u` under the same condition. -/
theorem base_word_bound {u d g p q r : ℕ} (hd : 0 < d) (hu : 0 < u) (hcop : Nat.Coprime u (u + d))
    (hcond : (g * (u + d) / u) * d < u)
    (h : p * (u * u) + q * (d * (u + (u + d))) + r * (u * (u + d)) = g * (u + d) * (d * (u + (u + d)))) :
    r < u := by
  set b := d * (u + (u + d)) with hb
  have hbpos : 0 < b := by positivity
  have hcb : Nat.Coprime u b := by
    have hd' : Nat.Coprime u d := by
      have := hcop
      rw [Nat.coprime_self_add_right] at this
      exact this
    have h2 : Nat.Coprime u (u + (u + d)) := by
      rw [Nat.coprime_self_add_right]; exact hcop
    exact Nat.Coprime.mul_right hd' h2
  have hqle : q ≤ g * (u + d) := by
    have : q * b ≤ g * (u + d) * b := by
      nlinarith [h, Nat.zero_le (p * (u * u)), Nat.zero_le (r * (u * (u + d)))]
    exact Nat.le_of_mul_le_mul_right this hbpos
  obtain ⟨e, he⟩ : ∃ e, g * (u + d) = q + e := ⟨g * (u + d) - q, by omega⟩
  have h1 : p * (u * u) + r * (u * (u + d)) = e * b := by
    rw [he] at h
    have : p * (u * u) + r * (u * (u + d)) + q * b = e * b + q * b := by nlinarith [h]
    exact Nat.add_right_cancel this
  have h2 : u ∣ e * b := by rw [← h1]; exact ⟨p * u + r * (u + d), by ring⟩
  have h3 : u ∣ e := hcb.dvd_of_dvd_mul_right h2
  obtain ⟨M, rfl⟩ := h3
  have h4 : p * u + r * (u + d) = (M * d) * (u + (u + d)) := by
    have : u * (p * u + r * (u + d)) = u * ((M * d) * (u + (u + d))) := by
      rw [hb] at h1; nlinarith [h1]
    exact Nat.eq_of_mul_eq_mul_left hu this
  have hX : M * d < u := by
    have hMle : M ≤ g * (u + d) / u := by
      rw [Nat.le_div_iff_mul_le hu]; nlinarith [he]
    have : M * d ≤ (g * (u + d) / u) * d := Nat.mul_le_mul_right _ hMle
    exact lt_of_le_of_lt this hcond
  exact lt_of_le_of_lt (word_core hcop hX h4) hX

/-- witness (non-vacuity): `(u, d) = (5, 1)`, `g = 4`: condition `⌊4·6/5⌋·1 = 4 < 5`; the leg `4·5·11 = 220`
has the word `(p,q,r) = (0, 20, 0)`, and e.g. `r = 0 < 5`. -/
example : (4 * (5 + 1) / 5) * 1 < 5 := by norm_num
example : 0 * (5 * 5) + 20 * (1 * (5 + (5 + 1))) + 0 * (5 * (5 + 1)) = 4 * 5 * (1 * (5 + (5 + 1))) := by norm_num

end Erdos634.Draft.ThmC

#print axioms Erdos634.Draft.ThmC.leg_word_bound
#print axioms Erdos634.Draft.ThmC.base_word_bound
