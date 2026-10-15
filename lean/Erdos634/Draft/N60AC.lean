/-
N60A-C: the constant-60 consumer: `identity60` from `CaseALemmaVDissection.star` at N = 60 (analogue of `N30K.identity30`) and `no_dissection60_n`
(reuses the constant-general `N30K.chkAllF`, `N30K.no_tile_of_chkAllF`, `N30K.IdFinF`).  No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.N30KC

namespace Erdos634.N60A

open Finset Erdos634.GA2R Erdos634.N30K
open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV

/-- **The identity with the constant 60.** -/
theorem identity60 (D : CongruentDissection 60) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    (∀ k, 1 ≤ a k) ∧ ∑ k, a k = n ∧
    ∃ (b c : Fin 3 → ℕ), (∀ k, 1 ≤ b k) ∧ ∑ k, b k = n ∧ IdFinF 60 n a (b 0) (b 1) (b 2) c := by
  choose b hb using target_angle_nat D hn a ha
  obtain ⟨c, hc⟩ := star D
  refine ⟨fun k => (nat_bounds hn (ha k) (angle_pos _ k) (angle_lt_pi _ k)).1,
    Erdos634.CaseA.R0c.sum_of_angles hn ha, b, c,
    fun k => (nat_bounds hn (hb k) (angle_pos _ k) (angle_lt_pi _ k)).1,
    Erdos634.CaseA.R0c.sum_of_angles hn hb, ?_⟩
  simp only [ha, hb] at hc
  unfold IdFinF
  rw [Fin.prod_univ_three]
  push_cast at hc
  linear_combination (-1 : ℝ) * hc

theorem no_dissection60_n {n : ℕ} {sl sh : ℕ → ℕ} (hn : 0 < n) (htab : Tab n sl sh)
    (hchk : chkAllF 60 sl sh n = true) (D : CongruentDissection 60) (a : Fin 3 → ℕ)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    False := by
  obtain ⟨ha1, hsum, b, c, hb1, hbs, hid⟩ := identity60 D hn a ha
  have hbs' := hbs
  rw [Fin.sum_univ_three] at hbs'
  exact no_tile_of_chkAllF 60 hn htab hchk a ha1 hsum hgcd (hb1 0) (hb1 1) (hb1 2) hbs' c hid

#print axioms identity60
#print axioms no_dissection60_n

end Erdos634.N60A
