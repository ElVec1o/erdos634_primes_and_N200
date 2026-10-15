/-
GA2Q, Prop D, part 2: the abstract Fourier / support-counting lemma on (Z/(5 * 3^j))^x.

Let N = 5^1 * 3^j and F(g) = sum_{t in V} [g = y_t] c_t  (y_t units mod N).  If
  (A)  for all primitive psi mod 5 and all eta mod 3^j with psi(-1) eta(-1) = -1:  sum_t c_t psi(y_t) eta(y_t) = 0, and
  (B)  every fibre of g -> g mod 3^j meets P (a set containing all +-y_t) in at most 3 points,
then F is EVEN:  F(g) = F(-g) for every g.        (`even_of_top`)
Proof: D(g) = F(g) - F(-g) is orthogonal to every character psi x eta with psi != 1 (even characters trivially), hence invariant under
G_5 = ker((Z/N)^x -> (Z/3^j)^x) (`D_inv`); a nonzero D would have a full G_5-orbit (4 points of one fibre) in the support (`card_ker`).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.DirichletCRT
import Erdos634.Draft.GA2PC
import Erdos634.Draft.LemmaSC

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.GA2QD2

open DirichletCharacter Erdos634.DirichletCRT Erdos634.GA2PC

instance instNeZeroN (j : ℕ) : NeZero (5 ^ 1 * 3 ^ j) := ⟨by positivity⟩
instance instNeZero3 (j : ℕ) : NeZero (3 ^ j) := ⟨by positivity⟩

theorem cop5 (j : ℕ) : (5 ^ 1).Coprime (3 ^ j) := Nat.Coprime.pow _ _ (by norm_num)

def c5 (j : ℕ) : ZMod (5 ^ 1 * 3 ^ j) →+* ZMod (5 ^ 1) := ZMod.castHom (Nat.dvd_mul_right _ _) _
def c3 (j : ℕ) : ZMod (5 ^ 1 * 3 ^ j) →+* ZMod (3 ^ j) := ZMod.castHom (Nat.dvd_mul_left _ _) _

/-- the CRT product character psi x eta on (Z/(5 * 3^j))^x -/
noncomputable def pc (j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ 1)) (η : DirichletCharacter ℂ (3 ^ j)) :
    DirichletCharacter ℂ (5 ^ 1 * 3 ^ j) :=
  changeLevel (Nat.dvd_mul_right (5 ^ 1) (3 ^ j)) ψ * changeLevel (Nat.dvd_mul_left (3 ^ j) (5 ^ 1)) η

theorem pc_apply (j : ℕ) (ψ : DirichletCharacter ℂ (5 ^ 1)) (η : DirichletCharacter ℂ (3 ^ j))
    (g : (ZMod (5 ^ 1 * 3 ^ j))ˣ) :
    pc j ψ η (g : ZMod (5 ^ 1 * 3 ^ j)) =
      ψ (c5 j (g : ZMod (5 ^ 1 * 3 ^ j))) * η (c3 j (g : ZMod (5 ^ 1 * 3 ^ j))) := by
  unfold pc
  rw [prod_unit (cop5 j), unitsCRT_fst, unitsCRT_snd, ZMod.unitsMap_val, ZMod.unitsMap_val]
  rfl

theorem decomp5 (j : ℕ) (χ : DirichletCharacter ℂ (5 ^ 1 * 3 ^ j)) :
    χ = pc j (comp₁ (cop5 j) χ) (comp₂ (cop5 j) χ) := decomp (cop5 j) χ

/-- the function F -/
noncomputable def Fv {ι : Type*} (j : ℕ) (V : Finset ι) (y : ι → ZMod (5 ^ 1 * 3 ^ j)) (c : ι → ℂ)
    (g : ZMod (5 ^ 1 * 3 ^ j)) : ℂ := ∑ t ∈ V, if g = y t then c t else 0

theorem sum_Fv {ι : Type*} (j : ℕ) (V : Finset ι) (y : ι → ZMod (5 ^ 1 * 3 ^ j)) (c : ι → ℂ)
    (hy : ∀ t ∈ V, c t ≠ 0 → IsUnit (y t)) (χ : DirichletCharacter ℂ (5 ^ 1 * 3 ^ j)) :
    ∑ u : (ZMod (5 ^ 1 * 3 ^ j))ˣ, χ (u : ZMod (5 ^ 1 * 3 ^ j)) * Fv j V y c u =
      ∑ t ∈ V, c t * χ (y t) := by
  unfold Fv
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  by_cases hct : c t = 0
  · simp [hct]
  obtain ⟨u0, hu0⟩ := hy t ht hct
  rw [Finset.sum_eq_single u0]
  · rw [if_pos hu0, hu0]; ring
  · intro u _ hne
    rw [if_neg, mul_zero]
    intro hh
    apply hne
    apply Units.ext
    rw [hh, hu0]
  · simp


theorem neg_sum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (Φ : ZMod N → ℂ) :
    ∑ u : (ZMod N)ˣ, χ (u : ZMod N) * Φ (-(u : ZMod N)) = χ (-1) * ∑ u : (ZMod N)ˣ, χ (u : ZMod N) * Φ (u : ZMod N) := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun u => ?_)
  simp only [Equiv.neg_apply, Units.val_neg]
  have : χ (u : ZMod N) = χ (-1) * χ (-(u : ZMod N)) := by
    rw [← map_mul]; congr 1; ring
  rw [this]
  ring

theorem S_formula {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (Φ : ZMod N → ℂ) :
    ∑ u : (ZMod N)ˣ, χ (u : ZMod N) * (Φ (u : ZMod N) - Φ (-(u : ZMod N))) =
      (1 - χ (-1)) * ∑ u : (ZMod N)ˣ, χ (u : ZMod N) * Φ (u : ZMod N) := by
  have := neg_sum χ Φ
  have e : ∀ u : (ZMod N)ˣ, χ (u : ZMod N) * (Φ (u : ZMod N) - Φ (-(u : ZMod N))) =
      χ (u : ZMod N) * Φ (u : ZMod N) - χ (u : ZMod N) * Φ (-(u : ZMod N)) := fun u => by ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, this]
  ring


/-- D(g) = F(g) - F(-g) on units -/
noncomputable def Dd {ι : Type*} (j : ℕ) (V : Finset ι) (y : ι → ZMod (5 ^ 1 * 3 ^ j)) (c : ι → ℂ)
    (g : (ZMod (5 ^ 1 * 3 ^ j))ˣ) : ℂ :=
  Fv j V y c (g : ZMod (5 ^ 1 * 3 ^ j)) - Fv j V y c (-(g : ZMod (5 ^ 1 * 3 ^ j)))

theorem five_prim_of_ne_one' (η : DirichletCharacter ℂ (5 ^ 1)) (h : η ≠ 1) : η.IsPrimitive :=
  five_prim_of_ne_one η h

theorem D_inv {ι : Type*} (j : ℕ) (V : Finset ι) (y : ι → ZMod (5 ^ 1 * 3 ^ j)) (c : ι → ℂ)
    (hy : ∀ t ∈ V, c t ≠ 0 → IsUnit (y t))
    (hA : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      ∑ t ∈ V, c t * (ψ (c5 j (y t)) * η (c3 j (y t))) = 0)
    (n : (ZMod (5 ^ 1 * 3 ^ j))ˣ) (hn : ZMod.unitsMap (Nat.dvd_mul_left (3 ^ j) (5 ^ 1)) n = 1)
    (g : (ZMod (5 ^ 1 * 3 ^ j))ˣ) : Dd j V y c (g * n) = Dd j V y c g := by
  refine sub_eq_zero.1 (fourier_zero (fun u => Dd j V y c (u * n) - Dd j V y c u) ?_ g)
  intro χ
  set ψ := comp₁ (cop5 j) χ with hψ
  set η := comp₂ (cop5 j) χ with hη
  have e := decomp5 j χ
  have hχ : ∀ u : (ZMod (5 ^ 1 * 3 ^ j))ˣ, χ (u : ZMod (5 ^ 1 * 3 ^ j)) =
      ψ (c5 j (u : ZMod (5 ^ 1 * 3 ^ j))) * η (c3 j (u : ZMod (5 ^ 1 * 3 ^ j))) := by
    intro u
    have := congrArg (fun χ' : DirichletCharacter ℂ (5 ^ 1 * 3 ^ j) => χ' (u : ZMod (5 ^ 1 * 3 ^ j))) e
    simp only at this
    rw [pc_apply] at this
    exact this
  set S : ℂ := ∑ u : (ZMod (5 ^ 1 * 3 ^ j))ˣ, χ (u : ZMod (5 ^ 1 * 3 ^ j)) * Dd j V y c u with hS
  set A : ℂ := ∑ u : (ZMod (5 ^ 1 * 3 ^ j))ˣ, χ (u : ZMod (5 ^ 1 * 3 ^ j)) * Dd j V y c (u * n) with hA'
  have hshift : χ (n : ZMod (5 ^ 1 * 3 ^ j)) * A = S := by
    rw [hS, ← Equiv.sum_comp (Equiv.mulRight n) (fun u : (ZMod (5 ^ 1 * 3 ^ j))ˣ =>
      χ (u : ZMod (5 ^ 1 * 3 ^ j)) * Dd j V y c u), hA', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    simp only [Equiv.coe_mulRight, Units.val_mul, map_mul]
    ring
  have hgoal : ∑ u : (ZMod (5 ^ 1 * 3 ^ j))ˣ, χ (u : ZMod (5 ^ 1 * 3 ^ j)) *
      (Dd j V y c (u * n) - Dd j V y c u) = A - S := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rfl
  rw [hgoal]
  have hχn : χ (n : ZMod (5 ^ 1 * 3 ^ j)) ≠ 0 := unit_val_ne_zero χ n
  by_cases hψ1 : ψ = 1
  · have hc3n : c3 j (n : ZMod (5 ^ 1 * 3 ^ j)) = 1 := by
      have := congrArg (fun w : (ZMod (3 ^ j))ˣ => (w : ZMod (3 ^ j))) hn
      simp only [ZMod.unitsMap_val, Units.val_one] at this
      exact this
    have h1 : χ (n : ZMod (5 ^ 1 * 3 ^ j)) = 1 := by
      rw [hχ n, hc3n, MulChar.map_one, hψ1,
        MulChar.one_apply ((Units.isUnit n).map (c5 j)), one_mul]
    rw [h1, one_mul] at hshift
    rw [hshift]; ring
  · have hprim := five_prim_of_ne_one ψ hψ1
    have hSz : S = 0 := by
      have hS2 : S = (1 - χ (-1)) * ∑ u : (ZMod (5 ^ 1 * 3 ^ j))ˣ, χ (u : ZMod (5 ^ 1 * 3 ^ j)) *
          Fv j V y c (u : ZMod (5 ^ 1 * 3 ^ j)) := S_formula χ (Fv j V y c)
      have hT : ∑ u : (ZMod (5 ^ 1 * 3 ^ j))ˣ, χ (u : ZMod (5 ^ 1 * 3 ^ j)) *
          Fv j V y c (u : ZMod (5 ^ 1 * 3 ^ j)) = ∑ t ∈ V, c t * (ψ (c5 j (y t)) * η (c3 j (y t))) := by
        rw [sum_Fv j V y c hy χ]
        refine Finset.sum_congr rfl (fun t ht => ?_)
        by_cases hct : c t = 0
        · simp [hct]
        obtain ⟨u, hu⟩ := hy t ht hct
        rw [← hu, hχ u]
      have hneg1 : χ (-1) = ψ (-1) * η (-1) := by
        have := hχ (-1)
        simp only [Units.val_neg, Units.val_one, map_neg, map_one] at this
        exact this
      rw [hS2, hT]
      rcases DirichletCharacter.even_or_odd ψ with h1 | h1 <;>
        rcases DirichletCharacter.even_or_odd η with h2 | h2
      · rw [hneg1, h1, h2]; ring
      · have hA0 := hA ψ hprim η (by rw [h1, h2]; norm_num)
        rw [hA0]; ring
      · have hA0 := hA ψ hprim η (by rw [h1, h2]; norm_num)
        rw [hA0]; ring
      · rw [hneg1, h1, h2]; ring
    rw [hSz] at hshift
    have : A = 0 := (mul_eq_zero.1 hshift).resolve_left hχn
    rw [this, hSz]; ring


theorem card_ker (j : ℕ) :
    (Finset.univ.filter (fun n : (ZMod (5 ^ 1 * 3 ^ j))ˣ =>
      ZMod.unitsMap (Nat.dvd_mul_left (3 ^ j) (5 ^ 1)) n = 1)).card = 4 := by
  have h := Erdos634.LemmaSC.fiber_card (n := 5 ^ 1 * 3 ^ j) (d := 3 ^ j) (Nat.dvd_mul_left (3 ^ j) (5 ^ 1))
  rw [Nat.totient_mul (cop5 j)] at h
  have h3 : ((3 ^ j).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (by positivity)).ne'
  have h4 : ((Nat.totient 5 : ℕ) : ℂ) = 4 := by
    norm_num [Nat.totient_prime (by norm_num : Nat.Prime 5)]
  push_cast at h
  rw [h4, mul_div_assoc, div_self h3, mul_one] at h
  exact_mod_cast h

theorem even_of_top {ι : Type*} (j : ℕ) (V : Finset ι) (y : ι → ZMod (5 ^ 1 * 3 ^ j)) (c : ι → ℂ)
    (hy : ∀ t ∈ V, c t ≠ 0 → IsUnit (y t))
    (hA : ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      ∑ t ∈ V, c t * (ψ (c5 j (y t)) * η (c3 j (y t))) = 0)
    (P : Finset (ZMod (5 ^ 1 * 3 ^ j))) (hP : ∀ t ∈ V, c t ≠ 0 → y t ∈ P ∧ -(y t) ∈ P)
    (hcount : ∀ k : ZMod (3 ^ j), (P.filter (fun g => c3 j g = k)).card ≤ 3) :
    ∀ g : ZMod (5 ^ 1 * 3 ^ j), Fv j V y c g = Fv j V y c (-g) := by
  intro g
  by_cases hg : IsUnit g
  · obtain ⟨u, rfl⟩ := hg
    by_contra hne
    have hD : Dd j V y c u ≠ 0 := fun h => hne (sub_eq_zero.1 h)
    set K := Finset.univ.filter (fun n : (ZMod (5 ^ 1 * 3 ^ j))ˣ =>
      ZMod.unitsMap (Nat.dvd_mul_left (3 ^ j) (5 ^ 1)) n = 1) with hK
    have hinj : K.card ≤ (P.filter (fun g => c3 j g = c3 j (u : ZMod (5 ^ 1 * 3 ^ j)))).card := by
      refine Finset.card_le_card_of_injOn (fun n => ((u * n : (ZMod (5 ^ 1 * 3 ^ j))ˣ) : ZMod (5 ^ 1 * 3 ^ j))) ?_ ?_
      · intro n hn
        have hn' := (Finset.mem_filter.1 hn).2
        have hc3n : c3 j (n : ZMod (5 ^ 1 * 3 ^ j)) = 1 := by
          have := congrArg (fun w : (ZMod (3 ^ j))ˣ => (w : ZMod (3 ^ j))) hn'
          simp only [ZMod.unitsMap_val, Units.val_one] at this
          exact this
        have hDn : Dd j V y c (u * n) ≠ 0 := by rw [D_inv j V y c hy hA n hn' u]; exact hD
        simp only [Finset.mem_coe, Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · by_cases h1 : Fv j V y c ((u * n : (ZMod (5 ^ 1 * 3 ^ j))ˣ) : ZMod (5 ^ 1 * 3 ^ j)) = 0
          · have h2 : Fv j V y c (-((u * n : (ZMod (5 ^ 1 * 3 ^ j))ˣ) : ZMod (5 ^ 1 * 3 ^ j))) ≠ 0 := by
              intro h2
              apply hDn
              unfold Dd
              rw [h1, h2]; ring
            obtain ⟨t, ht, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
            have hcond : -((u * n : (ZMod (5 ^ 1 * 3 ^ j))ˣ) : ZMod (5 ^ 1 * 3 ^ j)) = y t ∧ c t ≠ 0 := by
              by_cases hh : -((u * n : (ZMod (5 ^ 1 * 3 ^ j))ˣ) : ZMod (5 ^ 1 * 3 ^ j)) = y t
              · rw [if_pos hh] at hne2; exact ⟨hh, hne2⟩
              · rw [if_neg hh] at hne2; exact absurd rfl hne2
            have := (hP t ht hcond.2).2
            rw [← hcond.1, neg_neg] at this
            exact this
          · obtain ⟨t, ht, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
            have hcond : ((u * n : (ZMod (5 ^ 1 * 3 ^ j))ˣ) : ZMod (5 ^ 1 * 3 ^ j)) = y t ∧ c t ≠ 0 := by
              by_cases hh : ((u * n : (ZMod (5 ^ 1 * 3 ^ j))ˣ) : ZMod (5 ^ 1 * 3 ^ j)) = y t
              · rw [if_pos hh] at hne2; exact ⟨hh, hne2⟩
              · rw [if_neg hh] at hne2; exact absurd rfl hne2
            rw [hcond.1]; exact (hP t ht hcond.2).1
        · rw [Units.val_mul, map_mul, hc3n, mul_one]
      · intro n _ n' _ h
        have := mul_left_cancel (Units.ext h : u * n = u * n')
        exact this
    have := hcount (c3 j (u : ZMod (5 ^ 1 * 3 ^ j)))
    rw [hK, card_ker j] at hinj
    omega
  · have hz : ∀ x : ZMod (5 ^ 1 * 3 ^ j), ¬ IsUnit x → Fv j V y c x = 0 := by
      intro x hx
      unfold Fv
      refine Finset.sum_eq_zero (fun t ht => ?_)
      by_cases hct : c t = 0
      · simp [hct]
      rw [if_neg]
      intro hh; exact hx (hh ▸ hy t ht hct)
    rw [hz g hg, hz (-g) (fun h => hg (by simpa using h))]

end Erdos634.GA2QD2

#print axioms Erdos634.GA2QD2.D_inv
#print axioms Erdos634.GA2QD2.card_ker
#print axioms Erdos634.GA2QD2.even_of_top
