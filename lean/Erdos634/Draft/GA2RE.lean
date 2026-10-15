/-
GA2R-E: the consumer.  From `star` (CaseALemmaVDissection) + the angle bookkeeping, a `CongruentDissection 15` whose model
has angles a_k pi / n yields the identity `IdFin n a B0 B1 B2 c` (target angles B_k pi/n, B_k >= 1, sum n, c in N^3).
`no_dissection_n`: if `chkAll sl sh n = true` and (T) holds then no such dissection exists.
(`oppLen_word` is used inside `star`: `star` is stated with the side word c of target side 0.)
-/
import Mathlib
import Erdos634.Draft.GA2RC
import Erdos634.Draft.CaseALemmaVDissection
import Erdos634.Draft.CaseAR0c

namespace Erdos634.GA2R

open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV

/-- **The identity that the kill consumes.**  Exactly: there are `B : Fin 3 -> N` (target angles in units pi/n, each >= 1,
sum n) and `c : Fin 3 -> N` with  (sum c_k sin(a_k pi/n))^2 sin(B_1 pi/n) sin(B_2 pi/n) = 15 sin(B_0 pi/n) prod_k sin(a_k pi/n). -/
theorem identity_of_dissection (D : CongruentDissection 15) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    (∀ k, 1 ≤ a k) ∧ ∑ k, a k = n ∧
    ∃ (b c : Fin 3 → ℕ), (∀ k, 1 ≤ b k) ∧ ∑ k, b k = n ∧ IdFin n a (b 0) (b 1) (b 2) c := by
  choose b hb using target_angle_nat D hn a ha
  obtain ⟨c, hc⟩ := star D
  refine ⟨fun k => (nat_bounds hn (ha k) (angle_pos _ k) (angle_lt_pi _ k)).1,
    Erdos634.CaseA.R0c.sum_of_angles hn ha, b, c,
    fun k => (nat_bounds hn (hb k) (angle_pos _ k) (angle_lt_pi _ k)).1,
    Erdos634.CaseA.R0c.sum_of_angles hn hb, ?_⟩
  simp only [ha, hb] at hc
  unfold IdFin
  rw [Fin.prod_univ_three]
  push_cast at hc
  linear_combination (-1 : ℝ) * hc

theorem no_dissection_n {n : ℕ} {sl sh : ℕ → ℕ} (hn : 0 < n) (htab : Tab n sl sh)
    (hchk : chkAll sl sh n = true) (D : CongruentDissection 15) (a : Fin 3 → ℕ)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    False := by
  obtain ⟨ha1, hsum, b, c, hb1, hbs, hid⟩ := identity_of_dissection D hn a ha
  have hbs' := hbs
  rw [Fin.sum_univ_three] at hbs'
  exact no_tile_of_chkAll hn htab hchk a ha1 hsum hgcd (hb1 0) (hb1 1) (hb1 2) hbs' c hid

#print axioms identity_of_dissection
#print axioms no_dissection_n

end Erdos634.GA2R
