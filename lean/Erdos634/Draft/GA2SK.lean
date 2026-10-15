/-
Prop K-b with an entry divisible by 3 (i = 0, n = 5^r * 3^j, r >= 2, j >= 2): primitive-eta3 top step + `A1` for the hidden entry.

For primitive eta3 (conductor 3^j) the entry T with 3 | T, 5 !| T is invisible (`bracket_hidden0`), so for each primitive eta the 5-adic Lemma N
(`GA2SJ.pointwise5_small`, |N_5| = 5 > 4 points) makes the two visible tokens eps-odd; the 3-adic constancy lemma over primitive
characters (`GA2SJ.const_prim3`, j >= 2) then forces aY = aX (eX + eY = 0) or the two weights vanish.  The hidden entry is killed by one
character of conductor 3^j / gcd (`kb_T`).
  `five_eval2` / `const_ratio3` / `exists_L1char0` / `bracket_hidden0` : the tools
  `kb_top`, `kb_T`, `kb_lab` : the labelled theorem (T, X, Y).
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2SD
import Erdos634.Draft.GA2SJ
import Erdos634.Draft.GA2QK1

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2SK

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi
open Erdos634.GA2PA Erdos634.GA2PC Erdos634.GA2PD Erdos634.GA2PE Erdos634.GA2PG
open Erdos634.GA2SD Erdos634.GA2SJ

theorem five_eval2 (r : ℕ) (hr : 2 ≤ r) (aX aY : ℕ) (cX cY : ℂ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (hX5 : ¬ 5 ∣ aX)
    (horth : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      cX * ψ (aX : ZMod (5 ^ r)) + (if 5 ∣ aY then 0 else cY * ψ (aY : ZMod (5 ^ r))) = 0) :
    cX + (if 5 ∣ aY then 0 else cY * ((if (aY : ZMod (5 ^ r)) = (aX : ZMod (5 ^ r)) then 1 else 0) +
        ε * (if (aY : ZMod (5 ^ r)) = -(aX : ZMod (5 ^ r)) then 1 else 0))) = 0 := by
  haveI : NeZero (5 ^ r) := ⟨pow_ne_zero _ (by norm_num)⟩
  set a2 : Fin 2 → ℕ := ![aX, aY] with ha2
  set c2 : Fin 2 → ℂ := ![cX, cY] with hc2
  set V : Finset (Fin 2) := univ.filter (fun t => ¬ 5 ∣ a2 t) with hV
  have hu : ∀ t ∈ V, IsUnit (a2 t : ZMod (5 ^ r)) := fun t ht => unit5r r _ (mem_filter.1 ht).2
  have hVc : V.card ≤ 4 := (Finset.card_le_univ _).trans (by simp)
  have hsumV : ∀ g : ℕ → ℂ → ℂ, ∑ t ∈ V, c2 t * g (a2 t) 0 = cX * g aX 0 +
      (if 5 ∣ aY then 0 else cY * g aY 0) := by
    intro g
    rw [hV, Finset.sum_filter, Fin.sum_univ_two]
    simp only [ha2, hc2, Matrix.cons_val_zero, Matrix.cons_val_one, if_neg hX5]
    split_ifs <;> simp
  have hpt := pointwise5_small r hr a2 c2 V hVc hu hε (by
    intro ψ hψ h1
    have := horth ψ hψ h1
    have h := hsumV (fun x _ => ψ (x : ZMod (5 ^ r)))
    simp only at h
    rw [h]; exact this)
  have h0 : (0 : Fin 2) ∈ V := mem_filter.2 ⟨mem_univ _, hX5⟩
  have := pointwise_form (5 ^ r) a2 c2 V hu ε hpt 0 h0
  rw [hV, Finset.sum_filter, Fin.sum_univ_two] at this
  simp only [ha2, hc2, Matrix.cons_val_zero, Matrix.cons_val_one, if_neg hX5, if_true] at this
  have hne : ¬ ((aX : ZMod (5 ^ r)) = -(aX : ZMod (5 ^ r))) := by
    intro h
    have h2 := (natcast_neg_iff (5 ^ r) aX aX).1 h
    have h3 : 5 ∣ aX + aX := (dvd_pow_self 5 (by omega)).trans h2
    omega
  rw [if_neg hne] at this
  by_cases hY5 : 5 ∣ aY
  · rw [if_pos hY5]
    simp [hX5, hY5] at this
    simpa using this
  · rw [if_neg hY5]
    simp [hX5, hY5] at this
    split_ifs at this ⊢ <;> linear_combination this

theorem const_ratio3 (j : ℕ) (hj : 2 ≤ j) (u v : (ZMod (3 ^ j))ˣ) (c : ℂ)
    (hc : ∀ η : DirichletCharacter ℂ (3 ^ j), η.IsPrimitive → η (v : ZMod (3 ^ j)) = c * η (u : ZMod (3 ^ j))) :
    v = u := by
  have h := const_prim3 j hj (v * u⁻¹) c (by
    intro η hη
    have e1 : η (((v * u⁻¹ : (ZMod (3 ^ j))ˣ) : ZMod (3 ^ j))) = η (v : ZMod (3 ^ j)) * η ((u⁻¹ : (ZMod (3 ^ j))ˣ) : ZMod (3 ^ j)) := by
      rw [Units.val_mul, map_mul]
    have e2 : η (u : ZMod (3 ^ j)) * η ((u⁻¹ : (ZMod (3 ^ j))ˣ) : ZMod (3 ^ j)) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    rw [e1, hc η hη]
    linear_combination c * e2)
  exact mul_inv_eq_one.1 h

theorem bracket_hidden0 (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (ψ : DirichletCharacter ℂ (5 ^ r)) (hψ : ψ.IsPrimitive)
    (η : DirichletCharacter ℂ (3 ^ j)) (hη : η.IsPrimitive) (a : ℕ) (h5 : ¬ 5 ∣ a) (h3 : 3 ∣ a) :
    bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) a = 0 := by
  haveI : NeZero (2 ^ 0) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [bracket_gen2 r 0 j ψ hψ 1 η a h5, if_neg]
  have hc1 : (1 : DirichletCharacter ℂ (2 ^ 0)).conductor = 1 := DirichletCharacter.conductor_one
  have hc3 : η.conductor = 3 ^ j := hη
  rw [hc1, hc3, one_mul]
  intro hdv
  have hMpos : 0 < 2 ^ 0 * 3 ^ j := by positivity
  have hg3 : 3 ∣ (2 ^ 0 * 3 ^ j).gcd a := Nat.dvd_gcd (Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _) h3
  have hgpos : 0 < (2 ^ 0 * 3 ^ j).gcd a := Nat.gcd_pos_of_pos_left _ hMpos
  have hd0 : 0 < dm (2 ^ 0 * 3 ^ j) a := Nat.div_pos (Nat.le_of_dvd hMpos (Nat.gcd_dvd_left _ _)) hgpos
  have hle := Nat.le_of_dvd hd0 hdv
  unfold dm at hle
  have : (2 ^ 0 * 3 ^ j) / (2 ^ 0 * 3 ^ j).gcd a < 3 ^ j := by
    have h2 : 2 ≤ (2 ^ 0 * 3 ^ j).gcd a := by
      have : 3 ≤ (2 ^ 0 * 3 ^ j).gcd a := Nat.le_of_dvd hgpos hg3
      omega
    calc (2 ^ 0 * 3 ^ j) / (2 ^ 0 * 3 ^ j).gcd a < 2 ^ 0 * 3 ^ j := Nat.div_lt_self hMpos (by omega)
      _ = 3 ^ j := by simp
  omega

theorem exists_L1char0 (r : ℕ) (hr : 1 ≤ r) (j : ℕ) (D : ℕ) (hD : D ∣ 3 ^ j) :
    ∃ (ψ : DirichletCharacter ℂ (5 ^ r)) (η3 : DirichletCharacter ℂ (3 ^ j)),
      ψ.IsPrimitive ∧ η3.conductor = D ∧ ψ (-1) * η3 (-1) = -1 := by
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨l, hl, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hD
  rcases Nat.eq_zero_or_pos l with rfl | hlp
  · obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 r hr (-1) (Or.inr rfl)
    obtain ⟨hψp, hψs⟩ := Erdos634.GA2LCore.mem_PrimPar.1 hψ
    refine ⟨ψ, 1, hψp, by simpa using (DirichletCharacter.conductor_one : (1 : DirichletCharacter ℂ (3 ^ j)).conductor = 1), ?_⟩
    rw [hψs, MulChar.one_apply (isUnit_one.neg)]; norm_num
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hodd3 : 3 ^ l % 2 = 1 := by
      have : Odd (3 ^ l) := Odd.pow (by decide)
      exact Nat.odd_iff.1 this
    obtain ⟨ω, hωp, hωo⟩ := (Erdos634.LemmaSParity.exists_odd_primitive_iff
      (d := 3 ^ l) (pow_ne_zero _ (by norm_num)) (by omega)).2
      ⟨by
        intro h
        have : 3 ^ 1 ≤ 3 ^ l := Nat.pow_le_pow_right (by norm_num) hlp
        omega, by omega⟩
    haveI : NeZero (3 ^ l) := ⟨pow_ne_zero _ (by norm_num)⟩
    obtain ⟨ψ, hψ⟩ := Erdos634.GA2NR1.nonempty5 r hr 1 (Or.inl rfl)
    obtain ⟨hψp, hψs⟩ := Erdos634.GA2LCore.mem_PrimPar.1 hψ
    refine ⟨ψ, changeLevel (pow_dvd_pow 3 hl) ω, hψp,
      Erdos634.LemmaSIso.conductor_changeLevel_of_isPrimitive (pow_dvd_pow 3 hl) hωp, ?_⟩
    have hω1 : ω (-1) = -1 := hωo
    rw [Erdos634.GA2NB2.changeLevel_neg_one, hω1, hψs]; norm_num

end Erdos634.GA2SK

#print axioms Erdos634.GA2SK.five_eval2
#print axioms Erdos634.GA2SK.const_ratio3
#print axioms Erdos634.GA2SK.bracket_hidden0
#print axioms Erdos634.GA2SK.exists_L1char0
