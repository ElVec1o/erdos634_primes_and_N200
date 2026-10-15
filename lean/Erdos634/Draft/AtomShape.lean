/-
Draft/AtomShape.lean -- the tile count of a dissected `(α+β, α+β, α)` target is `t² (f² − e²)` with `f ≤ t e`.

* `s5word_te`: a base word with a `c`-edge, `t e (f²−e²) = P·ef + Q·(f²−e²) + R·f²`, `R ≥ 1`, forces `f ≤ t e`
  (reduce modulo `f² − e²`: it divides `P e + R f > 0`, and `f (P e + R f) ≤ t e (f² − e²)`).  This contains
  `RATrap.s5word_e1` (`e = 1`, `f > t`) and `B3Prime.s5word_1_k` (`t = 1`).
* `atom_shape_te`: with `B3Prime.s5_shape` (γ-trap on the base), every dissection of that target has
  `N = t² (f² − e²)`, coprime `0 < e < f ≤ t e`; in particular `t ≥ 2`.
* `atom_not_squarefree`: hence `N` is not squarefree.  `prop:b3prime` (`N` not prime) is the special case.
* `s5inst_of_te_lt`: an S5 instance `(t, e, f)` with `t e < f` has no dissection.
All of these use only the γ-trap (`RATrap.s5_words`), not the two-`c`-edges theorem.

Composite-N and classification-branch statement; not prime-case progress in the sense of outcome (2).
No sorry, no native_decide.
-/
import Erdos634.Draft.B3Prime
import Erdos634.Draft.S5Family

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.NSQM

/-- a base word with a `c`-edge forces `f ≤ t e` -/
theorem s5word_te {t e f : ℤ} (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f) (h : S5Word t e f e) :
    f ≤ t * e := by
  obtain ⟨P, Q, R, hR, hw⟩ := h
  have hP0 : (0 : ℤ) ≤ (P : ℤ) := Int.natCast_nonneg _
  have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg _
  have hR1 : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast hR
  have hf : 0 < f := by linarith
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hc : IsCoprime (f ^ 2 - e ^ 2) f :=
    ((Erdos634.Draft.S5PinArith.coprime_ab hcop).of_mul_left_right).symm
  have hdvd : (f ^ 2 - e ^ 2) ∣ ((P : ℤ) * e + R * f) := by
    have h1 : (f ^ 2 - e ^ 2) ∣ ((P : ℤ) * e + R * f) * f := ⟨t * e - Q, by linear_combination -hw⟩
    exact hc.dvd_of_dvd_mul_right h1
  obtain ⟨j, hj⟩ := hdvd
  have hpos : 0 < (P : ℤ) * e + R * f := by
    have := mul_nonneg hP0 he.le
    have := mul_pos (by linarith : (0 : ℤ) < (R : ℤ)) hf
    linarith
  have hj1 : 1 ≤ j := by
    by_contra hlt
    have hj0 : j ≤ 0 := by omega
    have := mul_nonpos_of_nonneg_of_nonpos hb.le hj0
    linarith
  have hfj : f * j + Q = t * e := by
    have h2 : (f * j + Q - t * e) * (f ^ 2 - e ^ 2) = 0 := by
      have h3 : ((P : ℤ) * e + R * f) * f = (f ^ 2 - e ^ 2) * j * f := by rw [hj]
      linear_combination -hw - h3
    have := (mul_eq_zero.mp h2).resolve_right hb.ne'
    linarith
  nlinarith

/-- **The atom shape with `f ≤ t e`.** -/
theorem atom_shape_te {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : IrrPi α) (hrel : 3 * α + 2 * β = Real.pi) (hmod : D.model.ThreeAlphaData α β a b c)
    (htgt : TgtAngles D (α + β) (α + β) α) :
    ∃ t e f : ℤ, 2 ≤ t ∧ 0 < e ∧ e < f ∧ f ≤ t * e ∧ IsCoprime e f ∧ (N : ℤ) = t ^ 2 * (f ^ 2 - e ^ 2) := by
  obtain ⟨t, e, f, ht, he, hef, hcop, hNt, hwb, -⟩ := s5_shape D hα hrel hmod htgt
  have hte := s5word_te he hef hcop hwb
  refine ⟨t, e, f, ?_, he, hef, hte, hcop, hNt⟩
  by_contra hlt
  have ht1 : t = 1 := by omega
  rw [ht1] at hte
  linarith

/-- **The tile count of a dissected `(α+β, α+β, α)` target is not squarefree** (it is `t² (f² − e²)`, `t ≥ 2`). -/
theorem atom_not_squarefree {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : IrrPi α) (hrel : 3 * α + 2 * β = Real.pi) (hmod : D.model.ThreeAlphaData α β a b c)
    (htgt : TgtAngles D (α + β) (α + β) α) : ¬ Squarefree N := by
  obtain ⟨t, e, f, ht, he, hef, -, -, hNt⟩ := atom_shape_te D hα hrel hmod htgt
  intro hsq
  have h2 : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg (by omega)
  have hdvd : t.toNat * t.toNat ∣ N := by
    have h1 : (t * t : ℤ) ∣ (N : ℤ) := ⟨f ^ 2 - e ^ 2, by rw [hNt]; ring⟩
    rw [← h2] at h1
    exact_mod_cast h1
  have hu := hsq (t.toNat) hdvd
  rw [Nat.isUnit_iff] at hu
  rw [hu] at h2
  omega

/-- **An S5 instance with `t e < f` has no dissection** (no certificate, no search). -/
theorem s5inst_of_te_lt {t e f : ℤ} (ht : 0 < t) (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f)
    (hlt : t * e < f) : S5Inst t e f := by
  intro N D h0 h1 h2 hm
  obtain ⟨σ, hm0, hm1, hm2⟩ := hm
  obtain ⟨hirr, hrel, hmod, hP0, hP1⟩ := s5_angles ht he hef D h0 h1 h2 σ hm0 hm1 hm2
  -- the γ-trap word of the base
  obtain ⟨⟨P, Q, R, hR, hw⟩, -⟩ := s5_words (by have := D.pos; omega) D hirr hrel hmod hP0 hP1
  have hword : S5Word t e f e := by
    refine ⟨P, Q, R, hR, ?_⟩
    rw [h2] at hw
    exact_mod_cast hw
  have := s5word_te he hef hcop hword
  linarith

open Erdos634.Draft.FDBBaseBetaE1 in
/-- `s5inst_of_te_lt`, with target and tile given by their side lengths in any vertex order -/
theorem s5_te_lt_hasSides {t e f : ℤ} (ht : 0 < t) (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f)
    (hlt : t * e < f) {N : ℕ} (D : CongruentDissection N)
    (hT : HasSides D.target ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ((t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      ((t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hM : HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) : False :=
  s5inst_hasSides (s5inst_of_te_lt ht he hef hcop hlt) D hT hM

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.s5_te_lt_hasSides
#print axioms Erdos634.Draft.NSQM.s5word_te
#print axioms Erdos634.Draft.NSQM.atom_shape_te
#print axioms Erdos634.Draft.NSQM.atom_not_squarefree
#print axioms Erdos634.Draft.NSQM.s5inst_of_te_lt
