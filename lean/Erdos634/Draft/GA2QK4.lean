/-
GA2Q, K-b (no entry of I divisible by 3): the i = 0 labelled theorem for n = 5^r * 3^j, ALL r, j >= 1.

`theoremK0_lab` : n = 5^r 3^j (r, j >= 1), three entries P, Q, S >= 1 summing to n, every entry prime to 5 is prime to 3,
  the weights (eP, eQ, eS) orthogonal to all odd characters psi (1 x eta), psi primitive mod 5^r, eta any mod 3^j:
  then every class sum over the entries prime to 5 vanishes.
Proof: product-group method (GA2QK2.even_of_top: Phi^- is invariant under N_5 = ker((Z/5^r 3^j)^x -> (Z/5^(r-1) 3^j)^x), whose orbits have >= 4 points,
while each of the three columns contributes at most one of +-a to each fibre), then evenness of sum_t c_t [a_t] forces the class sums to vanish
(a_s + a_t = n is impossible: the third entry would be 0; 2 a_s = n is impossible: n odd).  NO use of the pattern lemma.
For r = 1 (Theorem C) the tiles with an entry divisible by 3 are covered by GA2PD; this file does not cover them (nor for r >= 2).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2QK3

open scoped BigOperators
open Finset
open scoped Classical

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Erdos634.GA2QK4

theorem cof_eq_K (x : ℕ) (e : ℂ) (h : ¬ 5 ∣ x) : Erdos634.GA2QK3.cof x e = e := by simp [Erdos634.GA2QK3.cof, h]

open DirichletCharacter Erdos634.GA2QK2 Erdos634.GA2QK3
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (chi)

/-- the family of an entry in the i = 0 case: {x, -x} -/
def famI {M : ℕ} (x : ZMod M) : Finset (ZMod M) := {x, -x}

theorem famI_card_le_one (r j : ℕ) (hj : 1 ≤ j) (x : ZMod (5 ^ r * 3 ^ j)) (hx : IsUnit (cM r j x))
    (k : ZMod (5 ^ (r - 1) * 3 ^ j)) :
    ((famI x).filter (fun g => cM r j g = k)).card ≤ 1 := by
  haveI : Fact (1 < 5 ^ (r - 1) * 3 ^ j) := ⟨by
    have h3 : 3 ≤ 3 ^ j := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have : 1 ≤ 5 ^ (r - 1) := Nat.one_le_pow _ _ (by norm_num)
    nlinarith⟩
  have hodd : (5 ^ (r - 1) * 3 ^ j) % 2 = 1 := by
    have : (5 ^ (r - 1) * 3 ^ j) % 2 = ((5 ^ (r - 1) % 2) * (3 ^ j % 2)) % 2 := Nat.mul_mod _ _ _
    rw [this]
    have h1 : 5 ^ (r - 1) % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    have h2 : 3 ^ j % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [h1, h2]
  obtain ⟨h, hh⟩ := (Erdos634.GA2QP.two_unit hodd).exists_right_inv
  rw [Finset.card_le_one]
  intro g hg g' hg'
  have e1 := (Finset.mem_filter.1 hg).2
  have e2 := (Finset.mem_filter.1 hg').2
  have heq : cM r j g = cM r j g' := e1.trans e2.symm
  have m1 := (Finset.mem_filter.1 hg).1
  have m2 := (Finset.mem_filter.1 hg').1
  simp only [famI, Finset.mem_insert, Finset.mem_singleton] at m1 m2
  have hX0 : cM r j x ≠ 0 := hx.ne_zero
  rcases m1 with m1 | m1 <;> rcases m2 with m2 | m2
  · rw [m1, m2]
  · exfalso
    rw [m1, m2] at heq
    simp only [map_neg] at heq
    exact hX0 (by linear_combination h * heq - (cM r j x) * hh)
  · exfalso
    rw [m1, m2] at heq
    simp only [map_neg] at heq
    exact hX0 (by linear_combination (-h) * heq - (cM r j x) * hh)
  · rw [m1, m2]


/-- positions and weights of the three tokens -/
def tokY0 (r j : ℕ) (P Q S : ℕ) : Fin 3 → ZMod (5 ^ r * 3 ^ j) :=
  ![(P : ZMod (5 ^ r * 3 ^ j)), (Q : ZMod (5 ^ r * 3 ^ j)), (S : ZMod (5 ^ r * 3 ^ j))]

def tokC0 (cP cQ cS : ℂ) : Fin 3 → ℂ := ![cP, cQ, cS]

theorem hA0_of_HD (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (P Q S : ℕ) (eP eQ eS : ℂ)
    (h3P : ¬ 5 ∣ P → ¬ 3 ∣ P) (h3Q : ¬ 5 ∣ Q → ¬ 3 ∣ Q) (h3S : ¬ 5 ∣ S → ¬ 3 ∣ S)
    (HD : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) P +
      eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) Q +
      eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) S = 0) :
    ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      ∑ t : Fin 3, tokC0 (cof P eP) (cof Q eQ) (cof S eS) t *
        (ψ (c5 r j (tokY0 r j P Q S t)) * η (c3 r j (tokY0 r j P Q S t))) = 0 := by
  intro ψ hψ η hodd
  obtain ⟨κ0, hκ0, hform⟩ := Erdos634.GA2QK1.bracket_K0 r j hr hj ψ hψ η
  have H := HD ψ hψ η hodd
  have bX : ∀ (x : ℕ) (e : ℂ), (¬ 5 ∣ x → ¬ 3 ∣ x) →
      e * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) x =
        κ0 * (cof x e * (ψ (x : ZMod (5 ^ r)) * η (x : ZMod (3 ^ j)))) := by
    intro x e h3
    by_cases h : 5 ∣ x
    · rw [Erdos634.LemmaSPhi.bracket_p_dvd (p := 5) (r := r) hr (Erdos634.GA2PA.not5_dvd' 0 j) hψ _ x h]
      simp [cof, h]
    · rw [hform x h ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (h3 h))]
      simp only [cof, h, if_false]
      ring
  have key : ∑ t : Fin 3, tokC0 (cof P eP) (cof Q eQ) (cof S eS) t *
        (ψ (c5 r j (tokY0 r j P Q S t)) * η (c3 r j (tokY0 r j P Q S t))) =
      cof P eP * (ψ (P : ZMod (5 ^ r)) * η (P : ZMod (3 ^ j))) +
      cof Q eQ * (ψ (Q : ZMod (5 ^ r)) * η (Q : ZMod (3 ^ j))) +
      cof S eS * (ψ (S : ZMod (5 ^ r)) * η (S : ZMod (3 ^ j))) := by
    simp [Fin.sum_univ_three, tokC0, tokY0]
  rw [key]
  have : κ0 * (cof P eP * (ψ (P : ZMod (5 ^ r)) * η (P : ZMod (3 ^ j))) +
      cof Q eQ * (ψ (Q : ZMod (5 ^ r)) * η (Q : ZMod (3 ^ j))) +
      cof S eS * (ψ (S : ZMod (5 ^ r)) * η (S : ZMod (3 ^ j)))) = 0 := by
    rw [mul_add, mul_add, ← bX P eP h3P, ← bX Q eQ h3Q, ← bX S eS h3S]
    exact H
  exact (mul_eq_zero.1 this).resolve_left hκ0

theorem even_tokens0 (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (P Q S : ℕ) (eP eQ eS : ℂ)
    (h3P : ¬ 5 ∣ P → ¬ 3 ∣ P) (h3Q : ¬ 5 ∣ Q → ¬ 3 ∣ Q) (h3S : ¬ 5 ∣ S → ¬ 3 ∣ S)
    (HD : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) P +
      eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) Q +
      eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) S = 0) :
    ∀ g : ZMod (5 ^ r * 3 ^ j),
      Fv r j Finset.univ (tokY0 r j P Q S) (tokC0 (cof P eP) (cof Q eQ) (cof S eS)) g =
      Fv r j Finset.univ (tokY0 r j P Q S) (tokC0 (cof P eP) (cof Q eQ) (cof S eS)) (-g) := by
  have uP : ¬ 5 ∣ P → IsUnit (P : ZMod (5 ^ r * 3 ^ j)) := fun h => unit_of_not r j P h (h3P h)
  have uQ : ¬ 5 ∣ Q → IsUnit (Q : ZMod (5 ^ r * 3 ^ j)) := fun h => unit_of_not r j Q h (h3Q h)
  have uS : ¬ 5 ∣ S → IsUnit (S : ZMod (5 ^ r * 3 ^ j)) := fun h => unit_of_not r j S h (h3S h)
  have hy : ∀ t ∈ (Finset.univ : Finset (Fin 3)),
      tokC0 (cof P eP) (cof Q eQ) (cof S eS) t ≠ 0 → IsUnit (tokY0 r j P Q S t) := by
    intro t _ hct
    fin_cases t
    · have : ¬ 5 ∣ P := fun h => hct (by simp [tokC0, cof, h])
      simpa [tokY0] using uP this
    · have : ¬ 5 ∣ Q := fun h => hct (by simp [tokC0, cof, h])
      simpa [tokY0] using uQ this
    · have : ¬ 5 ∣ S := fun h => hct (by simp [tokC0, cof, h])
      simpa [tokY0] using uS this
  have hA := hA0_of_HD r j hr hj P Q S eP eQ eS h3P h3Q h3S HD
  set Pset : Finset (ZMod (5 ^ r * 3 ^ j)) :=
    (if 5 ∣ P then ∅ else famI (P : ZMod (5 ^ r * 3 ^ j))) ∪
    (if 5 ∣ Q then ∅ else famI (Q : ZMod (5 ^ r * 3 ^ j))) ∪
    (if 5 ∣ S then ∅ else famI (S : ZMod (5 ^ r * 3 ^ j))) with hPset
  refine even_of_top r j hr Finset.univ (tokY0 r j P Q S) (tokC0 (cof P eP) (cof Q eQ) (cof S eS)) hy hA Pset ?_ ?_
  · intro t _ hct
    fin_cases t
    · have h5 : ¬ 5 ∣ P := fun h => hct (by simp [tokC0, cof, h])
      simp [hPset, tokY0, h5, famI]
    · have h5 : ¬ 5 ∣ Q := fun h => hct (by simp [tokC0, cof, h])
      simp [hPset, tokY0, h5, famI]
    · have h5 : ¬ 5 ∣ S := fun h => hct (by simp [tokC0, cof, h])
      simp [hPset, tokY0, h5, famI]
  · intro k
    rw [hPset, Finset.filter_union, Finset.filter_union]
    have c1 : ((if 5 ∣ P then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famI (P : ZMod (5 ^ r * 3 ^ j))).filter
        (fun g => cM r j g = k)).card ≤ 1 := by
      by_cases h : 5 ∣ P
      · simp [h]
      · simp only [h, if_false]
        exact famI_card_le_one r j hj _ (natcast_unitM r j P h (h3P h)) k
    have c2 : ((if 5 ∣ Q then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famI (Q : ZMod (5 ^ r * 3 ^ j))).filter
        (fun g => cM r j g = k)).card ≤ 1 := by
      by_cases h : 5 ∣ Q
      · simp [h]
      · simp only [h, if_false]
        exact famI_card_le_one r j hj _ (natcast_unitM r j Q h (h3Q h)) k
    have c3' : ((if 5 ∣ S then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famI (S : ZMod (5 ^ r * 3 ^ j))).filter
        (fun g => cM r j g = k)).card ≤ 1 := by
      by_cases h : 5 ∣ S
      · simp [h]
      · simp only [h, if_false]
        exact famI_card_le_one r j hj _ (natcast_unitM r j S h (h3S h)) k
    have := Finset.card_union_le ((if 5 ∣ P then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famI (P : ZMod (5 ^ r * 3 ^ j))).filter
        (fun g => cM r j g = k)) ((if 5 ∣ Q then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famI (Q : ZMod (5 ^ r * 3 ^ j))).filter
        (fun g => cM r j g = k))
    have h2 := Finset.card_union_le (((if 5 ∣ P then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famI (P : ZMod (5 ^ r * 3 ^ j))).filter
        (fun g => cM r j g = k)) ∪ ((if 5 ∣ Q then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famI (Q : ZMod (5 ^ r * 3 ^ j))).filter
        (fun g => cM r j g = k))) ((if 5 ∣ S then (∅ : Finset (ZMod (5 ^ r * 3 ^ j))) else famI (S : ZMod (5 ^ r * 3 ^ j))).filter
        (fun g => cM r j g = k))
    omega


theorem neg_cast_ne (N : ℕ) (hN2 : N % 2 = 1) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (ha' : a < N) (hb' : b < N)
    (hab : a ≠ b → a + b ≠ N) : (-(a : ZMod N)) ≠ (b : ZMod N) := by
  intro h
  have h1 : (((a + b : ℕ) : ℤ) : ZMod N) = 0 := by
    push_cast
    linear_combination -h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  obtain ⟨k, hk⟩ := h1
  have hNpos : (0 : ℤ) < N := by exact_mod_cast (by omega : 0 < N)
  have hk1 : 0 < k := by
    by_contra hh
    push Not at hh
    have : (N : ℤ) * k ≤ 0 := by nlinarith
    have : (0 : ℤ) < ((a + b : ℕ) : ℤ) := by exact_mod_cast (by omega : 0 < a + b)
    omega
  have hk2 : k < 3 := by
    by_contra hh
    push Not at hh
    have : (N : ℤ) * 3 ≤ N * k := by nlinarith
    have : ((a + b : ℕ) : ℤ) < 2 * N := by
      have : a + b < 2 * N := by omega
      exact_mod_cast this
    omega
  have hN2' : (N : ℤ) % 2 = 1 := by omega
  interval_cases k
  · have h2 : a + b = N := by
      have : ((a + b : ℕ) : ℤ) = N := by omega
      exact_mod_cast this
    by_cases hab' : a = b
    · subst hab'; omega
    · exact hab hab' h2
  · have : ((a + b : ℕ) : ℤ) = 2 * N := by omega
    have : a + b = 2 * N := by exact_mod_cast this
    omega

theorem theoremK0_lab (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (P Q S : ℕ) (eP eQ eS : ℂ)
    (gP : 0 < P) (gQ : 0 < Q) (gS : 0 < S) (hsum : P + Q + S = 5 ^ r * 3 ^ j)
    (h3P : ¬ 5 ∣ P → ¬ 3 ∣ P) (h3Q : ¬ 5 ∣ Q → ¬ 3 ∣ Q) (h3S : ¬ 5 ∣ S → ¬ 3 ∣ S)
    (HD : ∀ ψ : DirichletCharacter ℂ (5 ^ r), ψ.IsPrimitive → ∀ η : DirichletCharacter ℂ (3 ^ j),
      ψ (-1) * η (-1) = -1 →
      eP * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) P +
      eQ * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) Q +
      eS * bracket (chi ψ (chi (1 : DirichletCharacter ℂ (2 ^ 0)) η)) S = 0) :
    ∀ x : ℕ, ¬ 5 ∣ x →
      (if P = x then eP else 0) + (if Q = x then eQ else 0) + (if S = x then eS else 0) = 0 := by
  intro x hx5
  have hev := even_tokens0 r j hr hj P Q S eP eQ eS h3P h3Q h3S HD
  have hN2 := N_odd r j
  have hPN : P < 5 ^ r * 3 ^ j := by omega
  have hQN : Q < 5 ^ r * 3 ^ j := by omega
  have hSN : S < 5 ^ r * 3 ^ j := by omega
  have hinj : ∀ a b : ℕ, a < 5 ^ r * 3 ^ j → b < 5 ^ r * 3 ^ j →
      (a : ZMod (5 ^ r * 3 ^ j)) = (b : ZMod (5 ^ r * 3 ^ j)) → a = b := by
    intro a b ha hb h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  have hF : ∀ g : ZMod (5 ^ r * 3 ^ j),
      Fv r j Finset.univ (tokY0 r j P Q S) (tokC0 (cof P eP) (cof Q eQ) (cof S eS)) g =
        (if g = (P : ZMod (5 ^ r * 3 ^ j)) then cof P eP else 0) +
        (if g = (Q : ZMod (5 ^ r * 3 ^ j)) then cof Q eQ else 0) +
        (if g = (S : ZMod (5 ^ r * 3 ^ j)) then cof S eS else 0) := by
    intro g
    simp [Fv, Fin.sum_univ_three, tokY0, tokC0]
  by_cases hxm : x = P ∨ x = Q ∨ x = S
  · have hxN : x < 5 ^ r * 3 ^ j := by rcases hxm with rfl | rfl | rfl <;> assumption
    have e1 := hev (x : ZMod (5 ^ r * 3 ^ j))
    rw [hF, hF] at e1
    have hneg : ∀ y : ℕ, 0 < y → y < 5 ^ r * 3 ^ j → (y = P ∨ y = Q ∨ y = S) →
        ∀ z : ℕ, 0 < z → z < 5 ^ r * 3 ^ j → (z = P ∨ z = Q ∨ z = S) →
        (-(y : ZMod (5 ^ r * 3 ^ j))) ≠ (z : ZMod (5 ^ r * 3 ^ j)) := by
      intro y hy hyN hyc z hz hzN hzc
      refine neg_cast_ne _ hN2 y z hy hz hyN hzN ?_
      intro hne
      rcases hyc with rfl | rfl | rfl <;> rcases hzc with rfl | rfl | rfl <;> omega
    have hxpos : 0 < x := by rcases hxm with rfl | rfl | rfl <;> assumption
    have n1 := hneg x hxpos hxN hxm P gP hPN (Or.inl rfl)
    have n2 := hneg x hxpos hxN hxm Q gQ hQN (Or.inr (Or.inl rfl))
    have n3 := hneg x hxpos hxN hxm S gS hSN (Or.inr (Or.inr rfl))
    rw [if_neg n1, if_neg n2, if_neg n3] at e1
    simp only [add_zero] at e1
    have hP' : (if (x : ZMod (5 ^ r * 3 ^ j)) = (P : ZMod (5 ^ r * 3 ^ j)) then cof P eP else 0) =
        (if P = x then eP else 0) := by
      by_cases h : P = x
      · subst h
        rw [if_pos rfl, if_pos rfl, cof_eq_K P eP hx5]
      · rw [if_neg h, if_neg (fun hh => h (hinj _ _ hPN hxN hh.symm))]
    have hQ' : (if (x : ZMod (5 ^ r * 3 ^ j)) = (Q : ZMod (5 ^ r * 3 ^ j)) then cof Q eQ else 0) =
        (if Q = x then eQ else 0) := by
      by_cases h : Q = x
      · subst h
        rw [if_pos rfl, if_pos rfl, cof_eq_K Q eQ hx5]
      · rw [if_neg h, if_neg (fun hh => h (hinj _ _ hQN hxN hh.symm))]
    have hS' : (if (x : ZMod (5 ^ r * 3 ^ j)) = (S : ZMod (5 ^ r * 3 ^ j)) then cof S eS else 0) =
        (if S = x then eS else 0) := by
      by_cases h : S = x
      · subst h
        rw [if_pos rfl, if_pos rfl, cof_eq_K S eS hx5]
      · rw [if_neg h, if_neg (fun hh => h (hinj _ _ hSN hxN hh.symm))]
    rw [hP', hQ', hS'] at e1
    exact e1
  · push Not at hxm
    rw [if_neg (fun h => hxm.1 h.symm), if_neg (fun h => hxm.2.1 h.symm), if_neg (fun h => hxm.2.2 h.symm)]
    simp

end Erdos634.GA2QK4

#print axioms Erdos634.GA2QK4.theoremK0_lab
