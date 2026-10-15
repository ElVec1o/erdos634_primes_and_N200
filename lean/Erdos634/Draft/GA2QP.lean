/-
GA2Q, item (2): the **pattern lemma**, in the form proved in Lean.

Setting.  M odd, M >= 13, u v units of Z/M, kappa != 0 ANY complex number, eps = +-1, (a, b, c) complex scalars,
  F(g) = a([g = 2u] - kappa [g = u]) + b([g = 2v] - kappa [g = v]) + c [g = -u - v],
  c = 0 or -u - v a unit (the third column is present only if its entry is prime to M).
`pattern_lemma`:  if F(g) + eps F(-g) = 0 for all g (i.e. Phi + eps [-1] Phi = 0) then
  (a = b = c = 0)  or  (v = u, b = -a, c = 0)  or  (v = -u, c = 0, b = -eps a).
This holds for every kappa != 0 (not only roots of unity of order in {1,2,3,4,6,8,9,12,18}) and for every odd
M >= 13 (not only M in {15,25,45,75,125,135,405,625}).  The proof is the case analysis on
v/u in {1,-1,2,-2,1/2,-1/2,-3,-1/3} (every coincidence between the ten points +-2u, +-u, +-2v, +-v, +-(u+v) forces one of these)
versus the generic case (no coincidence, every coefficient is the value of F at an unmatched point).  Needs M >= 13 only so that the
integers in [-12, 12] are distinct nonzero residues.  The statement is false for M = 5 (an exact computation).
No sorry / native_decide.
-/
import Mathlib

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace Erdos634.GA2QP

variable {M : ℕ}

theorem intcast_ne_zero (hM : 13 ≤ M) {m : ℤ} (hm0 : m ≠ 0) (hm : |m| ≤ 12) : (m : ZMod M) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have := Int.eq_zero_of_abs_lt_dvd h (by omega)
  exact hm0 this

theorem two_unit (hodd : M % 2 = 1) : IsUnit (2 : ZMod M) := by
  have : (2 : ZMod M) * (((M + 1) / 2 : ℕ) : ZMod M) = 1 := by
    have h : 2 * ((M + 1) / 2) = M + 1 := by omega
    have := congrArg (fun n : ℕ => (n : ZMod M)) h
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add] at this
    simpa using this
  exact IsUnit.of_mul_eq_one _ this

/-- a unit times a nonzero small integer is nonzero -/
theorem mulne (hM : 13 ≤ M) {x : ZMod M} (hx : IsUnit x) (m : ℤ) (h0 : m ≠ 0) (hb : |m| ≤ 12)
    (e : (m : ZMod M) * x = 0) : False := by
  exact intcast_ne_zero hM h0 hb (hx.mul_left_eq_zero.1 e)

theorem lab_iff (hM : 13 ≤ M) {h : ZMod M} (hh : IsUnit h) (m l : ℤ) (hb : |m - l| ≤ 12) :
    ((m : ZMod M) * h = (l : ZMod M) * h) ↔ m = l := by
  rw [hh.mul_left_inj]
  constructor
  · intro e
    by_contra hne
    exact intcast_ne_zero hM (sub_ne_zero.2 hne) hb (by push_cast; rw [sub_eq_zero]; exact e)
  · rintro rfl; rfl

/-- five-point form -/
def Fq (p1 p2 p3 p4 p5 : ZMod M) (κ a b c : ℂ) (g : ZMod M) : ℂ :=
  a * ((if g = p1 then 1 else 0) - κ * (if g = p2 then 1 else 0)) +
  b * ((if g = p3 then 1 else 0) - κ * (if g = p4 then 1 else 0)) + c * (if g = p5 then 1 else 0)

/-- the element Phi of Prop K-c as a function on Z/M -/
def Fp (u v : ZMod M) (κ a b c : ℂ) (g : ZMod M) : ℂ := Fq (2 * u) u (2 * v) v (-u - v) κ a b c g

/-- integer-labelled version -/
def Gl (A1 A2 B1 B2 C : ℤ) (κ a b c : ℂ) (m : ℤ) : ℂ :=
  a * ((if m = A1 then 1 else 0) - κ * (if m = A2 then 1 else 0)) +
  b * ((if m = B1 then 1 else 0) - κ * (if m = B2 then 1 else 0)) + c * (if m = C then 1 else 0)

theorem Fq_lab (hM : 13 ≤ M) {h : ZMod M} (hh : IsUnit h) (A1 A2 B1 B2 C m : ℤ)
    (b1 : |m - A1| ≤ 12) (b2 : |m - A2| ≤ 12) (b3 : |m - B1| ≤ 12) (b4 : |m - B2| ≤ 12) (b5 : |m - C| ≤ 12)
    (κ a b c : ℂ) :
    Fq ((A1 : ZMod M) * h) ((A2 : ZMod M) * h) ((B1 : ZMod M) * h) ((B2 : ZMod M) * h) ((C : ZMod M) * h) κ a b c
      ((m : ZMod M) * h) = Gl A1 A2 B1 B2 C κ a b c m := by
  unfold Fq Gl
  have i1 := lab_iff hM hh m A1 b1
  have i2 := lab_iff hM hh m A2 b2
  have i3 := lab_iff hM hh m B1 b3
  have i4 := lab_iff hM hh m B2 b4
  have i5 := lab_iff hM hh m C b5
  simp only [i1, i2, i3, i4, i5]

/-- Branch principle: if all five points are integer multiples of a unit h, the system reduces to the integer-labelled one. -/
theorem branch_G (hM : 13 ≤ M) {h u v : ZMod M} (hh : IsUnit h) (A1 A2 B1 B2 C : ℤ)
    (bA1 : |A1| ≤ 6) (bA2 : |A2| ≤ 6) (bB1 : |B1| ≤ 6) (bB2 : |B2| ≤ 6) (bC : |C| ≤ 6)
    (e1 : 2 * u = (A1 : ZMod M) * h) (e2 : u = (A2 : ZMod M) * h) (e3 : 2 * v = (B1 : ZMod M) * h)
    (e4 : v = (B2 : ZMod M) * h) (e5 : -u - v = (C : ZMod M) * h)
    {κ ε a b c : ℂ} (H : ∀ g, Fp u v κ a b c g + ε * Fp u v κ a b c (-g) = 0) :
    ∀ m : ℤ, |m| ≤ 6 → Gl A1 A2 B1 B2 C κ a b c m + ε * Gl A1 A2 B1 B2 C κ a b c (-m) = 0 := by
  intro m hm
  have hFp : Fp u v κ a b c = Fq ((A1 : ZMod M) * h) ((A2 : ZMod M) * h) ((B1 : ZMod M) * h)
      ((B2 : ZMod M) * h) ((C : ZMod M) * h) κ a b c := by
    unfold Fp
    rw [e1, e3, e5, e2, e4]
  have := H ((m : ZMod M) * h)
  rw [hFp] at this
  have hneg : -((m : ZMod M) * h) = ((-m : ℤ) : ZMod M) * h := by push_cast; ring
  rw [hneg] at this
  rw [Fq_lab hM hh A1 A2 B1 B2 C m (by rw [abs_le] at *; omega) (by rw [abs_le] at *; omega)
      (by rw [abs_le] at *; omega) (by rw [abs_le] at *; omega) (by rw [abs_le] at *; omega)] at this
  rw [Fq_lab hM hh A1 A2 B1 B2 C (-m) (by rw [abs_le] at *; omega) (by rw [abs_le] at *; omega)
      (by rw [abs_le] at *; omega) (by rw [abs_le] at *; omega) (by rw [abs_le] at *; omega)] at this
  exact this


theorem mulz {κ a : ℂ} (hκ : κ ≠ 0) (h : κ * a = 0) : a = 0 := (mul_eq_zero.1 h).resolve_left hκ

theorem eps_ne {ε : ℂ} (hε : ε = 1 ∨ ε = -1) : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num

theorem eps_sq {ε : ℂ} (hε : ε = 1 ∨ ε = -1) : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num

/-- the conclusion of the pattern lemma -/
def Concl (u v : ZMod M) (ε a b c : ℂ) : Prop :=
  (a = 0 ∧ b = 0 ∧ c = 0) ∨ (v = u ∧ b = -a ∧ c = 0) ∨ (v = -u ∧ c = 0 ∧ b = -ε * a)

/-! ### the eight exceptional branches (v/u in {1, -1, 2, -2, 1/2, -1/2, -3, -1/3}) -/

section branches
variable (hM : 13 ≤ M) {u v : ZMod M} {κ ε a b c : ℂ} (hκ : κ ≠ 0) (hε : ε = 1 ∨ ε = -1)
  (H : ∀ g, Fp u v κ a b c g + ε * Fp u v κ a b c (-g) = 0)
include hM hκ hε H

theorem br_E1 (hu : IsUnit u) (hv : v = u) : v = u ∧ b = -a ∧ c = 0 := by
  have hG := branch_G hM hu 2 1 2 1 (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; linear_combination 2 * hv)
    (by push_cast; linear_combination hv) (by push_cast; linear_combination (-1) * hv) H
  have g1 := hG 1 (by norm_num)
  have g2 := hG 2 (by norm_num)
  simp only [Gl, Int.reduceEq, Int.reduceNeg, ↓reduceIte] at g1 g2
  have hab : a + b = 0 := mulz hκ (by linear_combination (-1) * g1)
  have hc : ε * c = 0 := by linear_combination g2 - hab
  refine ⟨hv, by linear_combination hab, (mul_eq_zero.1 hc).resolve_left (eps_ne hε)⟩

theorem br_E2 (hu : IsUnit u) (hv : v = -u) (hc0 : c = 0 ∨ IsUnit (-u - v)) : v = -u ∧ c = 0 ∧ b = -ε * a := by
  have hG := branch_G hM hu 2 1 (-2) (-1) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; linear_combination 2 * hv)
    (by push_cast; linear_combination hv) (by push_cast; linear_combination (-1) * hv) H
  have g2 := hG 2 (by norm_num)
  simp only [Gl, Int.reduceEq, Int.reduceNeg, ↓reduceIte] at g2
  have hc : c = 0 := by
    rcases hc0 with h | h
    · exact h
    · exfalso
      have : (-u - v) = 0 := by rw [hv]; ring
      rw [this] at h
      haveI : Fact (1 < M) := ⟨by omega⟩
      exact h.ne_zero rfl
  refine ⟨hv, hc, ?_⟩
  linear_combination ε * g2 - b * (eps_sq hε)

theorem br_E3 (hu : IsUnit u) (hv : v = 2 * u) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hG := branch_G hM hu 2 1 4 2 (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; linear_combination 2 * hv)
    (by push_cast; linear_combination hv) (by push_cast; linear_combination (-1) * hv) H
  have g1 := hG 1 (by norm_num)
  have g4 := hG 4 (by norm_num)
  have g3 := hG (-3) (by norm_num)
  simp only [Gl, Int.reduceEq, Int.reduceNeg, ↓reduceIte] at g1 g4 g3
  exact ⟨mulz hκ (by linear_combination (-1) * g1), by linear_combination g4, by linear_combination g3⟩

theorem br_E4 (hu : IsUnit u) (hv : v = -2 * u) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hG := branch_G hM hu 2 1 (-4) (-2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; linear_combination 2 * hv)
    (by push_cast; linear_combination hv) (by push_cast; linear_combination (-1) * hv) H
  have g4 := hG 4 (by norm_num)
  have g2 := hG 2 (by norm_num)
  have g1 := hG 1 (by norm_num)
  simp only [Gl, Int.reduceEq, Int.reduceNeg, ↓reduceIte] at g4 g2 g1
  have hb : b = 0 := (mul_eq_zero.1 (show ε * b = 0 by linear_combination g4)).resolve_left (eps_ne hε)
  have ha : a = 0 := by subst hb; linear_combination g2
  refine ⟨ha, hb, ?_⟩
  subst hb; subst ha; linear_combination g1

theorem br_E5 (hv' : IsUnit v) (hu : u = 2 * v) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hG := branch_G hM hv' 4 2 2 1 (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linear_combination 2 * hu) (by push_cast; linear_combination hu) (by push_cast; ring)
    (by push_cast; ring) (by push_cast; linear_combination (-1) * hu) H
  have g1 := hG 1 (by norm_num)
  have g4 := hG 4 (by norm_num)
  have g3 := hG (-3) (by norm_num)
  simp only [Gl, Int.reduceEq, Int.reduceNeg, ↓reduceIte] at g1 g4 g3
  exact ⟨by linear_combination g4, mulz hκ (by linear_combination (-1) * g1), by linear_combination g3⟩

theorem br_E6 (hv' : IsUnit v) (hu : u = -2 * v) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hG := branch_G hM hv' (-4) (-2) 2 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linear_combination 2 * hu) (by push_cast; linear_combination hu) (by push_cast; ring)
    (by push_cast; ring) (by push_cast; linear_combination (-1) * hu) H
  have g4 := hG 4 (by norm_num)
  have g2 := hG 2 (by norm_num)
  have g1 := hG 1 (by norm_num)
  simp only [Gl, Int.reduceEq, Int.reduceNeg, ↓reduceIte] at g4 g2 g1
  have ha : a = 0 := (mul_eq_zero.1 (show ε * a = 0 by linear_combination g4)).resolve_left (eps_ne hε)
  have hb : b = 0 := by subst ha; linear_combination g2
  refine ⟨ha, hb, ?_⟩
  subst hb; subst ha; linear_combination g1

theorem br_E7 (hu : IsUnit u) (hv : v = -3 * u) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hG := branch_G hM hu 2 1 (-6) (-3) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; linear_combination 2 * hv)
    (by push_cast; linear_combination hv) (by push_cast; linear_combination (-1) * hv) H
  have g1 := hG 1 (by norm_num)
  have g6 := hG 6 (by norm_num)
  have g2 := hG 2 (by norm_num)
  simp only [Gl, Int.reduceEq, Int.reduceNeg, ↓reduceIte] at g1 g6 g2
  have ha : a = 0 := mulz hκ (by linear_combination (-1) * g1)
  have hb : b = 0 := by
    subst ha
    exact (mul_eq_zero.1 (show ε * b = 0 by linear_combination g6)).resolve_left (eps_ne hε)
  refine ⟨ha, hb, ?_⟩
  subst hb; subst ha; linear_combination g2

theorem br_E8 (hv' : IsUnit v) (hu : u = -3 * v) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hG := branch_G hM hv' (-6) (-3) 2 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linear_combination 2 * hu) (by push_cast; linear_combination hu) (by push_cast; ring)
    (by push_cast; ring) (by push_cast; linear_combination (-1) * hu) H
  have g6 := hG 6 (by norm_num)
  have g1 := hG 1 (by norm_num)
  have g2 := hG 2 (by norm_num)
  simp only [Gl, Int.reduceEq, Int.reduceNeg, ↓reduceIte] at g6 g1 g2
  have ha : a = 0 := (mul_eq_zero.1 (show ε * a = 0 by linear_combination g6)).resolve_left (eps_ne hε)
  have hb : b = 0 := mulz hκ (by subst ha; linear_combination (-1) * g1)
  refine ⟨ha, hb, ?_⟩
  subst hb; subst ha; linear_combination g2

end branches


/-! ### the generic case: none of the eight relations holds -/

theorem generic (hM : 13 ≤ M) (hodd : M % 2 = 1) {u v : ZMod M} (hu : IsUnit u) (hv : IsUnit v)
    {κ ε a b c : ℂ} (hκ : κ ≠ 0) (hε : ε = 1 ∨ ε = -1) (hc : c = 0 ∨ IsUnit (-u - v))
    (H : ∀ g, Fp u v κ a b c g + ε * Fp u v κ a b c (-g) = 0)
    (n1 : v ≠ u) (n2 : v ≠ -u) (n3 : v ≠ 2 * u) (n4 : v ≠ -2 * u) (n5 : u ≠ 2 * v) (n6 : u ≠ -2 * v)
    (n7 : v ≠ -3 * u) (n8 : u ≠ -3 * v) : a = 0 ∧ b = 0 ∧ c = 0 := by
  haveI : Fact (1 < M) := ⟨by omega⟩
  have c2 : ∀ x y : ZMod M, 2 * x = 2 * y → x = y := fun x y h => (two_unit hodd).mul_left_cancel h
  have mu : ∀ (x : ZMod M) (m : ℤ), IsUnit x → m ≠ 0 → |m| ≤ 12 → (m : ZMod M) * x = 0 → False :=
    fun x m hx h0 hb e => mulne hM hx m h0 hb e
  -- a = 0 : evaluate at g = 2u
  have q1 : ¬ (2 * u = u) := fun h => mu u 1 hu (by norm_num) (by norm_num) (by push_cast; linear_combination h)
  have q2 : ¬ (2 * u = 2 * v) := fun h => n1 (c2 v u h.symm)
  have q3 : ¬ (2 * u = v) := fun h => n3 h.symm
  have q4 : ¬ (2 * u = -u - v) := fun h => n7 (by linear_combination h)
  have q5 : ¬ (-(2 * u) = 2 * u) := fun h => mu u 4 hu (by norm_num) (by norm_num) (by push_cast; linear_combination (-1) * h)
  have q6 : ¬ (-(2 * u) = u) := fun h => mu u 3 hu (by norm_num) (by norm_num) (by push_cast; linear_combination (-1) * h)
  have q7 : ¬ (-(2 * u) = 2 * v) := fun h => n2 (c2 v (-u) (by linear_combination (-1) * h))
  have q8 : ¬ (-(2 * u) = v) := fun h => n4 (by linear_combination (-1) * h)
  have q9 : ¬ (-(2 * u) = -u - v) := fun h => n1 (by linear_combination h)
  have Ha := H (2 * u)
  simp only [Fp, Fq, q1, q2, q3, q4, q5, q6, q7, q8, q9, eq_self_iff_true, ↓reduceIte] at Ha
  have ha : a = 0 := by linear_combination Ha
  -- b = 0 : evaluate at g = 2v
  have r1 : ¬ (2 * v = 2 * u) := fun h => n1 (c2 v u h)
  have r2 : ¬ (2 * v = u) := fun h => n5 h.symm
  have r3 : ¬ (2 * v = v) := fun h => mu v 1 hv (by norm_num) (by norm_num) (by push_cast; linear_combination h)
  have r4 : ¬ (2 * v = -u - v) := fun h => n8 (by linear_combination h)
  have r5 : ¬ (-(2 * v) = 2 * u) := fun h => n2 (c2 v (-u) (by linear_combination (-1) * h))
  have r6 : ¬ (-(2 * v) = u) := fun h => n6 (by linear_combination (-1) * h)
  have r7 : ¬ (-(2 * v) = 2 * v) := fun h => mu v 4 hv (by norm_num) (by norm_num) (by push_cast; linear_combination (-1) * h)
  have r8 : ¬ (-(2 * v) = v) := fun h => mu v 3 hv (by norm_num) (by norm_num) (by push_cast; linear_combination (-1) * h)
  have r9 : ¬ (-(2 * v) = -u - v) := fun h => n1 (by linear_combination (-1) * h)
  have Hb := H (2 * v)
  simp only [Fp, Fq, r1, r2, r3, r4, r5, r6, r7, r8, r9, eq_self_iff_true, ↓reduceIte] at Hb
  have hb : b = 0 := by linear_combination Hb
  refine ⟨ha, hb, ?_⟩
  rcases hc with h0 | hw
  · exact h0
  · have s1 : ¬ (-(-u - v) = -u - v) := fun h => by
      have h2 : (-u - v) = 0 := c2 _ 0 (by linear_combination (-1) * h)
      exact hw.ne_zero h2
    have Hc := H (-u - v)
    subst ha; subst hb
    simp only [Fp, Fq, s1, eq_self_iff_true, ↓reduceIte] at Hc
    linear_combination Hc

/-- **The pattern lemma** (GA2Y_NOTES, Prop K-c / D).  See the file header. -/
theorem pattern_lemma (hM : 13 ≤ M) (hodd : M % 2 = 1) {u v : ZMod M} (hu : IsUnit u) (hv : IsUnit v)
    {κ ε a b c : ℂ} (hκ : κ ≠ 0) (hε : ε = 1 ∨ ε = -1) (hc : c = 0 ∨ IsUnit (-u - v))
    (H : ∀ g, Fp u v κ a b c g + ε * Fp u v κ a b c (-g) = 0) : Concl u v ε a b c := by
  unfold Concl
  by_cases e1 : v = u
  · exact Or.inr (Or.inl (br_E1 hM hκ hε H hu e1))
  by_cases e2 : v = -u
  · exact Or.inr (Or.inr (br_E2 hM hκ hε H hu e2 hc))
  by_cases e3 : v = 2 * u
  · exact Or.inl (br_E3 hM hκ hε H hu e3)
  by_cases e4 : v = -2 * u
  · exact Or.inl (br_E4 hM hκ hε H hu e4)
  by_cases e5 : u = 2 * v
  · exact Or.inl (br_E5 hM hκ hε H hv e5)
  by_cases e6 : u = -2 * v
  · exact Or.inl (br_E6 hM hκ hε H hv e6)
  by_cases e7 : v = -3 * u
  · exact Or.inl (br_E7 hM hκ hε H hu e7)
  by_cases e8 : u = -3 * v
  · exact Or.inl (br_E8 hM hκ hε H hv e8)
  exact Or.inl (generic hM hodd hu hv hκ hε hc H e1 e2 e3 e4 e5 e6 e7 e8)


/-- The statement as written in GA2Y_NOTES: kappa a root of unity (any order), any odd M >= 13 (in particular all M in
{15, 25, 45, 75, 125, 135, 405, 625}).  A corollary of `pattern_lemma`. -/
theorem pattern_lemma_rootsofunity (hM : 13 ≤ M) (hodd : M % 2 = 1) {u v : ZMod M} (hu : IsUnit u) (hv : IsUnit v)
    {κ ε a b c : ℂ} {d : ℕ} (hd : 0 < d) (hκd : κ ^ d = 1) (hε : ε = 1 ∨ ε = -1) (hc : c = 0 ∨ IsUnit (-u - v))
    (H : ∀ g, Fp u v κ a b c g + ε * Fp u v κ a b c (-g) = 0) : Concl u v ε a b c := by
  have hκ : κ ≠ 0 := by
    rintro rfl
    rw [zero_pow hd.ne'] at hκd
    exact zero_ne_one hκd
  exact pattern_lemma hM hodd hu hv hκ hε hc H

/-! ### Witnesses (the hypotheses are satisfiable with a NONZERO solution in both exceptional cases) and a counterexample at M = 5 -/

/-- v = u, M = 15, solution (1, -1, 0): hypotheses hold for every kappa and eps = +-1, and a != 0. -/
theorem witness_v_eq_u (κ ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    (∀ g : ZMod 15, Fp (1 : ZMod 15) 1 κ 1 (-1) 0 g + ε * Fp (1 : ZMod 15) 1 κ 1 (-1) 0 (-g) = 0) ∧
    IsUnit (1 : ZMod 15) ∧ ((0 : ℂ) = 0 ∨ IsUnit (-(1 : ZMod 15) - 1)) ∧ (1 : ℂ) ≠ 0 := by
  refine ⟨fun g => ?_, isUnit_one, Or.inl rfl, one_ne_zero⟩
  simp [Fp, Fq]

/-- v = -u, M = 15 (u = 1, v = 14), solution (1, -eps, 0). -/
theorem witness_v_eq_neg_u (κ ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    (∀ g : ZMod 15, Fp (1 : ZMod 15) 14 κ 1 (-ε) 0 g + ε * Fp (1 : ZMod 15) 14 κ 1 (-ε) 0 (-g) = 0) ∧
    IsUnit (14 : ZMod 15) ∧ ((0 : ℂ) = 0 ∨ IsUnit (-(1 : ZMod 15) - 14)) ∧ (1 : ℂ) ≠ 0 ∧ (14 : ZMod 15) = -1 := by
  refine ⟨fun g => ?_, by decide, Or.inl rfl, one_ne_zero, by decide⟩
  have h14 : (14 : ZMod 15) = -1 := by decide
  have h2 : (2 * 1 : ZMod 15) = 2 := by ring
  simp only [Fp, Fq, h14, h2, neg_eq_iff_eq_neg, neg_neg, mul_neg]
  rcases hε with rfl | rfl <;> split_ifs <;> ring

/-- integer mirror of the M = 5 control (decidable) -/
def Fz (u v g : ZMod 5) : ℤ := ((if g = 2 * u then 1 else 0) - (if g = u then 1 else 0)) +
  ((if g = 2 * v then 1 else 0) - (if g = v then 1 else 0))

/-- The lemma is false for M = 5 (u = 1, v = 2, kappa = eps = 1, solution (1, 1, 0)): a nonzero solution
exists with v != +-u.  So a lower bound on M (the hypothesis `13 <= M`) cannot be dropped altogether. -/
theorem pattern_fails_M5 :
    (∀ g : ZMod 5, Fp (1 : ZMod 5) 2 (1 : ℂ) 1 1 0 g + (1 : ℂ) * Fp (1 : ZMod 5) 2 (1 : ℂ) 1 1 0 (-g) = 0) ∧
    ¬ Concl (1 : ZMod 5) 2 (1 : ℂ) 1 1 0 := by
  refine ⟨?_, ?_⟩
  · have key : ∀ g : ZMod 5, Fp (1 : ZMod 5) 2 (1 : ℂ) 1 1 0 g = ((Fz 1 2 g : ℤ) : ℂ) := by
      intro g; simp only [Fp, Fq, Fz]; push_cast; split_ifs <;> simp
    have hz : ∀ g : ZMod 5, Fz 1 2 g + Fz 1 2 (-g) = 0 := by decide
    intro g
    rw [key, key, one_mul]
    exact_mod_cast hz g
  · unfold Concl
    rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)
    · exact one_ne_zero h
    · exact absurd h (by decide)
    · exact absurd h (by decide)

end Erdos634.GA2QP

#print axioms Erdos634.GA2QP.pattern_lemma
#print axioms Erdos634.GA2QP.pattern_lemma_rootsofunity
#print axioms Erdos634.GA2QP.witness_v_eq_u
#print axioms Erdos634.GA2QP.witness_v_eq_neg_u
#print axioms Erdos634.GA2QP.pattern_fails_M5
#print axioms Erdos634.GA2QP.mulne
