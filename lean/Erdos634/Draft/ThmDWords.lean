import Erdos634.Draft.ThmCWords

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D', module 1: the word bound at the alpha-apex leg  

Tile `(a, b, c) = (u², d(2u + d), u(u + d))`, `v = u + d`.  A leg of `T(g)` has length `g u b`.
If its word `p a + q b + r c` has `q ≥ 1` (the alpha-apex leg: counting identity `μ_β = q - 1 + ε_β`,
`ε_β = 0` there) and `(g - 1) d < u`, then `r ≤ (g - 1) d < u`: the leg cannot carry `u` edges `c`.
Hand statement: the written proof of Theorem D' in the paper.
-/

namespace Erdos634.Draft.ThmD

open Erdos634.Draft.ThmC

theorem leg_word_bound_D {u d g p q r : ℕ} (hd : 0 < d) (hu : 0 < u) (hcop : Nat.Coprime u (u + d))
    (hcond : (g - 1) * d < u) (hq : 1 ≤ q)
    (h : p * (u * u) + q * (d * (u + (u + d))) + r * (u * (u + d)) = g * u * (d * (u + (u + d)))) :
    r ≤ (g - 1) * d := by
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
  have h1 : u ∣ (p * (u * u) + r * (u * (u + d))) + q * b := by
    have : (p * (u * u) + r * (u * (u + d))) + q * b = g * u * b := by linarith
    rw [this]; exact ⟨g * b, by ring⟩
  have h2 : u ∣ p * (u * u) + r * (u * (u + d)) :=
    ⟨p * u + r * (u + d), by ring⟩
  have h3 : u ∣ q * b := (Nat.dvd_add_right h2).mp h1
  have h4 : u ∣ q := hcb.dvd_of_dvd_mul_right h3
  obtain ⟨q', rfl⟩ := h4
  have hq' : 1 ≤ q' := by
    rcases Nat.eq_zero_or_pos q' with h0 | h0
    · subst h0; simp at hq
    · exact h0
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
  have hmg : m ≤ g - 1 := by omega
  have hX : m * d < u := lt_of_le_of_lt (Nat.mul_le_mul_right _ hmg) hcond
  exact le_trans (word_core hcop hX h6) (Nat.mul_le_mul_right _ hmg)

theorem leg_word_bound_D_lt {u d g p q r : ℕ} (hd : 0 < d) (hu : 0 < u) (hcop : Nat.Coprime u (u + d))
    (hcond : (g - 1) * d < u) (hq : 1 ≤ q)
    (h : p * (u * u) + q * (d * (u + (u + d))) + r * (u * (u + d)) = g * u * (d * (u + (u + d)))) :
    r < u :=
  lt_of_le_of_lt (leg_word_bound_D hd hu hcop hcond hq h) hcond

/-- witness (non-vacuity): tile `(3,5)` (`u = 3, d = 2`), `g = 2`: `(g-1) d = 2 < 3`; the leg `2·3·16 = 96` has the word
`(p,q,r) = (0,6,0)` with `q ≥ 1`, `r = 0 ≤ (g-1)d`. -/
example : (2 - 1) * 2 < 3 := by norm_num
example : 0 * (3 * 3) + 6 * (2 * (3 + (3 + 2))) + 0 * (3 * (3 + 2)) = 2 * 3 * (2 * (3 + (3 + 2))) := by norm_num
/-- negative control: the hypothesis `(g-1) d < u` is needed: `(u,d,g) = (3,2,3)` has `(g-1)d = 4 ≥ 3` and the leg
`3·3·16 = 144` has the word `(4,3,4)` with `q ≥ 1` and `r = 4 ≥ u`. -/
example : ¬ ((3 - 1) * 2 < 3) := by norm_num
example : 4 * (3 * 3) + 3 * (2 * (3 + (3 + 2))) + 4 * (3 * (3 + 2)) = 3 * 3 * (2 * (3 + (3 + 2))) := by norm_num

end Erdos634.Draft.ThmD

#print axioms Erdos634.Draft.ThmD.leg_word_bound_D
