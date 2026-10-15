/-
GA2M, atom (g3): **chaining**.  For n = 2^(k+3) 3^j 5, j >= 2: the Lemma-A3 hypothesis on two odd entries
ap, aq (psi(ap) eta2(ap) eta3(ap) = c psi(aq) eta2(aq) eta3(aq) for every odd admissible chi = psi eta2 eta3,
c = -E_q/E_p), with ap, aq coprime to 2, 3, 5 (i.e. both in I with level j), ap != aq, 0 < ap, aq, ap+aq < n,
implies  e = 1 and (shape A: s = 0, |ap - aq| = n/2) or (shape B: s = 1, ap + aq = n/2),  and c = (-1)^(s+e) = -(-1)^s.
Route: h := ap * u, u = aq^-1 mod n; `HypP` -> `Hyp k j h h h c` -> `group_core` (ZMod) -> Int.ModEq -> `shape_arith`.
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2LGroup
import Erdos634.Draft.GA2LShape

namespace Erdos634.GA2MChain

open Erdos634.GA2LGroup Erdos634.GA2LShape

def HypP (k j : ℕ) (ap aq : ℤ) (c : ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ (5 ^ 1), ψ.IsPrimitive →
  ∀ η2 : DirichletCharacter ℂ (2 ^ (k + 3)), η2.IsPrimitive →
  ∀ η3 : DirichletCharacter ℂ (3 ^ j), η3 ≠ 1 →
    ψ (-1) * η2 (-1) * η3 (-1) = -1 →
    ψ (ap : ZMod (5 ^ 1)) * η2 (ap : ZMod (2 ^ (k + 3))) * η3 (ap : ZMod (3 ^ j)) =
      c * (ψ (aq : ZMod (5 ^ 1)) * η2 (aq : ZMod (2 ^ (k + 3))) * η3 (aq : ZMod (3 ^ j)))

theorem unit_of_coprime (a : ℤ) (m : ℕ) (h : IsCoprime a (m : ℤ)) : IsUnit (a : ZMod m) := by
  obtain ⟨u, v, huv⟩ := h
  have := congrArg (Int.cast : ℤ → ZMod m) huv
  push_cast at this
  rw [ZMod.natCast_self, mul_zero, add_zero] at this
  exact IsUnit.of_mul_eq_one (u : ZMod m) (by rw [mul_comm]; exact this)

theorem hyp_h (k j : ℕ) (ap aq u : ℤ) (c : ℂ) (H : HypP k j ap aq c)
    (e5 : ((aq * u : ℤ) : ZMod (5 ^ 1)) = 1) (e2 : ((aq * u : ℤ) : ZMod (2 ^ (k + 3))) = 1)
    (e3 : ((aq * u : ℤ) : ZMod (3 ^ j)) = 1) :
    Hyp k j (ap * u) (ap * u) (ap * u) c := by
  intro ψ hψ η2 hη2 η3 hη3 hodd
  have h := H ψ hψ η2 hη2 η3 hη3 hodd
  have k5 : ψ (aq * u : ℤ) = ψ (aq : ZMod (5 ^ 1)) * ψ (u : ZMod (5 ^ 1)) := by
    rw [← map_mul]; push_cast; rfl
  have k2 : η2 (aq * u : ℤ) = η2 (aq : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3))) := by
    rw [← map_mul]; push_cast; rfl
  have k3 : η3 (aq * u : ℤ) = η3 (aq : ZMod (3 ^ j)) * η3 (u : ZMod (3 ^ j)) := by
    rw [← map_mul]; push_cast; rfl
  rw [e5, map_one] at k5
  rw [e2, map_one] at k2
  rw [e3, map_one] at k3
  have m5 : ψ ((ap * u : ℤ) : ZMod (5 ^ 1)) = ψ (ap : ZMod (5 ^ 1)) * ψ (u : ZMod (5 ^ 1)) := by
    rw [← map_mul]; push_cast; rfl
  have m2 : η2 ((ap * u : ℤ) : ZMod (2 ^ (k + 3))) =
      η2 (ap : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3))) := by
    rw [← map_mul]; push_cast; rfl
  have m3 : η3 ((ap * u : ℤ) : ZMod (3 ^ j)) = η3 (ap : ZMod (3 ^ j)) * η3 (u : ZMod (3 ^ j)) := by
    rw [← map_mul]; push_cast; rfl
  rw [m5, m2, m3]
  -- (A*B*C) with A B C = values at ap, times u-values = c * (aq stuff)(u stuff) = c
  have := congrArg (fun x => x * (ψ (u : ZMod (5 ^ 1)) * η2 (u : ZMod (2 ^ (k + 3))) *
      η3 (u : ZMod (3 ^ j)))) h
  simp only at this
  calc _ = (ψ (ap : ZMod (5 ^ 1)) * η2 (ap : ZMod (2 ^ (k + 3))) * η3 (ap : ZMod (3 ^ j))) *
        (ψ (u : ZMod (5 ^ 1)) * η2 (u : ZMod (2 ^ (k + 3))) * η3 (u : ZMod (3 ^ j))) := by ring
    _ = _ := this
    _ = c * ((ψ (aq : ZMod (5 ^ 1)) * ψ (u : ZMod (5 ^ 1))) *
        (η2 (aq : ZMod (2 ^ (k + 3))) * η2 (u : ZMod (2 ^ (k + 3)))) *
        (η3 (aq : ZMod (3 ^ j)) * η3 (u : ZMod (3 ^ j)))) := by ring
    _ = c := by rw [← k5, ← k2, ← k3]; simp

theorem top_shape (k j : ℕ) (hj : 2 ≤ j) (ap aq : ℤ) (c : ℂ)
    (hpo : Odd ap) (hqo : Odd aq) (hp : 0 < ap) (hq : 0 < aq)
    (hp3 : IsCoprime ap 3) (hq3 : IsCoprime aq 3) (hp5 : IsCoprime ap 5) (hq5 : IsCoprime aq 5)
    (hsum : ap + aq < 2 ^ (k + 3) * (3 ^ j * 5)) (hne : ap ≠ aq)
    (H : HypP k j ap aq c) :
    ∃ s e : ℕ, s < 2 ∧ e = 1 ∧ c = (-1) ^ (s + e) ∧
      ((s = 0 ∧ (ap = aq + 2 ^ (k + 2) * (3 ^ j * 5) ∨ aq = ap + 2 ^ (k + 2) * (3 ^ j * 5))) ∨
        (s = 1 ∧ ap + aq = 2 ^ (k + 2) * (3 ^ j * 5))) := by
  -- coprimality to each modulus
  have cp2 : ∀ a : ℤ, Odd a → IsCoprime a ((2 ^ (k + 3) : ℕ) : ℤ) := fun a ha => by
    have := odd_cop a ha (k + 3); push_cast; exact this
  have cp3 : ∀ a : ℤ, IsCoprime a 3 → IsCoprime a ((3 ^ j : ℕ) : ℤ) := fun a ha => by
    have := ha.pow_right (n := j); push_cast; exact this
  have cp5 : ∀ a : ℤ, IsCoprime a 5 → IsCoprime a ((5 ^ 1 : ℕ) : ℤ) := fun a ha => by
    simpa using ha
  -- inverse of aq modulo each modulus, glued by CRT through n = 2^(k+3) * 3^j * 5
  have cpn : IsCoprime aq (((2 ^ (k + 3) * (3 ^ j * 5) : ℕ)) : ℤ) := by
    have h1 := (cp2 aq hqo)
    have h2 : IsCoprime aq (((3 ^ j * 5 : ℕ)) : ℤ) := by
      have := (hq3.pow_right (n := j)).mul_right hq5
      push_cast; exact this
    push_cast at h1 h2 ⊢
    exact h1.mul_right h2
  obtain ⟨u, v, huv⟩ := cpn
  have dvd_n : ∀ m : ℕ, (m : ℤ) ∣ ((2 ^ (k + 3) * (3 ^ j * 5) : ℕ) : ℤ) → ((aq * u : ℤ) : ZMod m) = 1 := by
    intro m hm
    have h1 : (aq * u : ℤ) = 1 - v * ((2 ^ (k + 3) * (3 ^ j * 5) : ℕ) : ℤ) := by linarith
    have : (((2 ^ (k + 3) * (3 ^ j * 5) : ℕ) : ℤ) : ZMod m) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hm
    rw [h1]; push_cast at this ⊢; rw [this]; simp
  have e5 := dvd_n (5 ^ 1) ⟨2 ^ (k + 3) * 3 ^ j, by push_cast; ring⟩
  have e2 := dvd_n (2 ^ (k + 3)) ⟨3 ^ j * 5, by push_cast; ring⟩
  have e3 := dvd_n (3 ^ j) ⟨2 ^ (k + 3) * 5, by push_cast; ring⟩
  have Hh := hyp_h k j ap aq u c H e5 e2 e3
  have unit_h : ∀ (m : ℕ), ((aq * u : ℤ) : ZMod m) = 1 → IsCoprime ap (m : ℤ) →
      IsUnit ((ap * u : ℤ) : ZMod m) := by
    intro m em hc
    have hu : IsUnit (u : ZMod m) := by
      push_cast at em
      exact IsUnit.of_mul_eq_one (aq : ZMod m) (by rw [mul_comm]; exact em)
    push_cast
    exact (unit_of_coprime ap m hc).mul hu
  have rel : ∀ (m : ℕ), ((aq * u : ℤ) : ZMod m) = 1 →
      (ap : ZMod m) = ((ap * u : ℤ) : ZMod m) * (aq : ZMod m) := by
    intro m em
    push_cast at em ⊢
    linear_combination (-(ap : ZMod m)) * em
  obtain ⟨s, e, hs, he, g5, g3, g2, gc⟩ := group_core k j hj (ap * u) (ap * u) (ap * u) c
    (unit_h (5 ^ 1) e5 (cp5 ap hp5)) (unit_h (2 ^ (k + 3)) e2 (cp2 ap hpo))
    (unit_h (3 ^ j) e3 (cp3 ap hp3)) Hh
  have c5 : ap ≡ (-1) ^ s * aq [ZMOD 5] := by
    have := (ZMod.intCast_eq_intCast_iff ap (((-1) ^ s * aq : ℤ)) (5 ^ 1)).1 (by
      rw [rel _ e5, g5]; push_cast; ring)
    simpa using this
  have c3 : ap ≡ (-1) ^ s * aq [ZMOD 3 ^ j] := by
    have := (ZMod.intCast_eq_intCast_iff ap (((-1) ^ s * aq : ℤ)) (3 ^ j)).1 (by
      rw [rel _ e3, g3]; push_cast; ring)
    simpa using this
  have c2 : ap ≡ (-1) ^ s * aq * (1 + 2 ^ (k + 2)) ^ e [ZMOD 2 ^ (k + 3)] := by
    have := (ZMod.intCast_eq_intCast_iff ap (((-1) ^ s * aq * (1 + 2 ^ (k + 2)) ^ e : ℤ))
      (2 ^ (k + 3))).1 (by
      rw [rel _ e2, g2]; push_cast; ring)
    simpa using this
  obtain ⟨he1, hshape⟩ := shape_arith k j s e hs he ap aq hpo hqo hp hq hsum hne c5 c3 c2
  subst he1
  refine ⟨s, 1, hs, rfl, gc, hshape⟩

/-- Converse (non-vacuity of `HypP`): if the group-core output congruences hold then `HypP` holds with
c = (-1)^(s+e).  Combined with the concrete instance below this exhibits a witness for `top_shape`. -/
theorem hypP_converse (k j s e : ℕ) (ap aq : ℤ)
    (e5 : (ap : ZMod (5 ^ 1)) = (-1) ^ s * aq) (e3 : (ap : ZMod (3 ^ j)) = (-1) ^ s * aq)
    (e2 : (ap : ZMod (2 ^ (k + 3))) = (-1) ^ s * (1 + 2 ^ (k + 2)) ^ e * aq) :
    HypP k j ap aq ((-1) ^ (s + e)) := by
  intro ψ _ η2 hη2 η3 _ hodd
  rw [e5, e2, e3]
  simp only [map_mul, map_pow]
  rw [eta2_val k η2 hη2]
  have key : ψ (-1) ^ s * ψ (aq : ZMod (5 ^ 1)) *
      ((η2 (-1) ^ s * (-1) ^ e) * η2 (aq : ZMod (2 ^ (k + 3)))) *
      (η3 (-1) ^ s * η3 (aq : ZMod (3 ^ j))) =
      (ψ (-1) * η2 (-1) * η3 (-1)) ^ s * (-1) ^ e *
      (ψ (aq : ZMod (5 ^ 1)) * η2 (aq : ZMod (2 ^ (k + 3))) * η3 (aq : ZMod (3 ^ j))) := by ring
  rw [key, hodd, pow_add (-1 : ℂ) s e]

/-- Concrete instance (k = 0, j = 2, n = 360): shape A pair (187, 7), s = 0, e = 1. -/
theorem hypP_187_7 : HypP 0 2 187 7 ((-1) ^ (0 + 1)) :=
  hypP_converse 0 2 0 1 187 7 (by decide) (by decide) (by decide)

/-- Concrete `top_shape` instance, all side hypotheses discharged: it applies to (187, 7). -/
theorem top_shape_187_7 : ∃ s e : ℕ, s < 2 ∧ e = 1 ∧ ((-1 : ℂ) ^ (0 + 1)) = (-1) ^ (s + e) ∧
      ((s = 0 ∧ ((187 : ℤ) = 7 + 2 ^ (0 + 2) * (3 ^ 2 * 5) ∨ (7 : ℤ) = 187 + 2 ^ (0 + 2) * (3 ^ 2 * 5))) ∨
        (s = 1 ∧ (187 : ℤ) + 7 = 2 ^ (0 + 2) * (3 ^ 2 * 5))) :=
  top_shape 0 2 le_rfl 187 7 _ (by decide) (by decide) (by norm_num) (by norm_num)
    ⟨1, -62, by norm_num⟩ ⟨1, -2, by norm_num⟩ ⟨3, -112, by norm_num⟩ ⟨3, -4, by norm_num⟩
    (by norm_num) (by norm_num) hypP_187_7

end Erdos634.GA2MChain

#print axioms Erdos634.GA2MChain.top_shape
#print axioms Erdos634.GA2MChain.hypP_converse
#print axioms Erdos634.GA2MChain.top_shape_187_7
