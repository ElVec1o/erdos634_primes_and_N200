-- Draft/ChainParams.lean -- CHAIN LEMMA, stage 2b: Lemma H and the canonical parameters.  From the threshold hypotheses
-- `f <= M e`, `f <= (M-1)(f-e)` (coprime `2 <= e`, `e+2 <= f`) the canonical triple `t = n - [rho = 0]`, `r = n+1`, `q = n`
-- (`n = e M / f`) satisfies the five conditions `WC`.  UNAUDITED.  No sorry.
-- Credit: Lemma H and the reparametrisation `u = g n - e - 1 >= 0`: Ramanujan-rows session / the AI assistant (Section 6 of PROPOSALS.md);
-- Paliy (W/beta framework); Beeson-Rosu.
import Erdos634.Draft.ChainW

namespace Erdos634.Draft.Chain.W

/-- **Lemma H (=>).**  Integer form: `e,g >= 2`, `f = e+g`, `e M = f n + rho` with `0 <= rho <= f-1`, `e,g` coprime,
`f <= M e` and `f <= (M-1) g` force `e + 1 <= g n`. -/
theorem lemmaH (e g M n ρ : ℤ) (he : 2 ≤ e) (hg : 2 ≤ g) (hn : 0 ≤ n) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ e + g - 1)
    (hE : e * M = (e + g) * n + ρ) (hco : IsCoprime e g) (h1 : e + g ≤ M * e) (h2 : e + g ≤ (M - 1) * g) :
    e + 1 ≤ g * n := by
  by_contra hcon
  rw [not_le] at hcon
  have hle : g * n ≤ e := by linarith
  have hne : g * n ≠ e := by
    intro heq
    have hd : g ∣ e := ⟨n, by linarith⟩
    have : IsUnit g := hco.symm.isUnit_of_dvd' (dvd_refl g) hd
    have h1' : g = 1 ∨ g = -1 := Int.isUnit_iff.mp this
    omega
  have hlt : g * n ≤ e - 1 := by omega
  rcases lt_trichotomy g e with hge | hge | hge
  · -- g < e
    have es : e * (M - n) = g * n + ρ := by linarith
    have hs3 : M - n < 3 := by
      by_contra hh; rw [not_lt] at hh
      nlinarith [mul_le_mul_of_nonneg_left hh (by linarith : (0:ℤ) ≤ e)]
    have hgs : g * (M - n) ≤ g * 2 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  · -- g = e: coprime forces e = 1
    subst hge
    have : IsUnit g := hco.isUnit_of_dvd' (dvd_refl g) (dvd_refl g)
    have h1' : g = 1 ∨ g = -1 := Int.isUnit_iff.mp this
    omega
  · -- g > e: n = 0
    have hn0 : n = 0 := by
      by_contra hh
      have : 1 ≤ n := by omega
      nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0:ℤ) ≤ g)]
    subst hn0
    nlinarith

/-- The canonical parameters satisfy `WC`, in the two cases `rho = 0` (`t = n - 1`) and `rho > 0` (`t = n`), from the integer data. -/
theorem wc_of_int (e g M n ρ : ℤ) (he : 2 ≤ e) (hg : 2 ≤ g) (hn : 0 ≤ n) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ e + g - 1)
    (hE : e * M = (e + g) * n + ρ) (hco : IsCoprime e g) (h1 : e + g ≤ M * e) (h2 : e + g ≤ (M - 1) * g)
    (hdiv : ρ = 0 → e ∣ n) :
    (ρ = 0 → WC (e : ℝ) ((e + g : ℤ) : ℝ) (M : ℝ) ((n : ℝ) - 1) ((n : ℝ) + 1) (n : ℝ)) ∧
    (0 < ρ → WC (e : ℝ) ((e + g : ℤ) : ℝ) (M : ℝ) (n : ℝ) ((n : ℝ) + 1) (n : ℝ)) := by
  have hH := lemmaH e g M n ρ he hg hn hρ0 hρ hE hco h1 h2
  have hn1 : 1 ≤ n := by
    by_contra hh; have : n = 0 := by omega
    subst this; nlinarith
  have hef : (e : ℝ) < ((e + g : ℤ) : ℝ) := by exact_mod_cast (by omega : e < e + g)
  have he0 : (0 : ℝ) < e := by exact_mod_cast (by omega : (0:ℤ) < e)
  refine ⟨fun hρz => ?_, fun hρp => ?_⟩
  · subst hρz
    obtain ⟨m, hm⟩ := hdiv rfl
    have hm1 : 1 ≤ m := by
      by_contra hh
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ e) (by omega : (0:ℤ) ≤ -m)]
    have hge : e + g + 1 ≤ g * n := by
      have : e * g ≥ e + g + 1 := by
        by_contra hh; rw [not_le] at hh
        have h22 : e = 2 ∧ g = 2 := by
          by_contra h22
          rcases not_and_or.mp h22 with a | a
          · have : 3 ≤ e := by omega
            nlinarith
          · have : 3 ≤ g := by omega
            nlinarith
        obtain ⟨rfl, rfl⟩ := h22
        have := hco.isUnit_of_dvd' (dvd_refl (2:ℤ)) (dvd_refl (2:ℤ))
        have h1' := Int.isUnit_iff.mp this
        omega
      rw [hm]; nlinarith
    have hn2 : 2 ≤ n := by rw [hm]; nlinarith
    have c3 : 0 < e * M - (e + g) * (n - 1) := by nlinarith
    have c4 : 0 < (e + g) * (n + 1) - e * M := by nlinarith
    have c6 : 0 < (e + g) * n - e * (n + 1) := by nlinarith
    have c7 : 0 < (e + g) * (n - 1) - e * n := by nlinarith
    refine ⟨he0, hef, ?_, by linarith, ?_, ?_, ?_, ?_⟩
    · have : (1:ℝ) < n := by exact_mod_cast (by omega : (1:ℤ) < n)
      linarith
    · exact_mod_cast c3
    · exact_mod_cast c4
    · exact_mod_cast c6
    · exact_mod_cast c7
  · have c3 : 0 < e * M - (e + g) * n := by nlinarith
    have c4 : 0 < (e + g) * (n + 1) - e * M := by nlinarith
    have c6 : 0 < (e + g) * n - e * (n + 1) := by nlinarith
    have c7 : 0 < (e + g) * n - e * n := by nlinarith
    refine ⟨he0, hef, ?_, by linarith, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast (by omega : (0:ℤ) < n)
    · exact_mod_cast c3
    · exact_mod_cast c4
    · exact_mod_cast c6
    · exact_mod_cast c7

/-- **The five conditions hold for the canonical parameters** (natural-number form).  For coprime `2 <= e`, `e + 2 <= f`,
`f <= M e`, `f <= (M-1)(f-e)` there are naturals `t r q` with `WC e f M t r q`. -/
theorem wc_nat (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f) (h1 : f ≤ M * e)
    (h2 : f ≤ (M - 1) * (f - e)) : ∃ t r q : ℕ, WC (e : ℝ) (f : ℝ) (M : ℝ) (t : ℝ) (r : ℝ) (q : ℝ) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = e + g := ⟨f - e, by omega⟩
  have hg : 2 ≤ g := by omega
  have hfpos : 0 < e + g := by omega
  have hM1 : 1 ≤ M := by
    by_contra hh; have : M = 0 := by omega
    subst this; simp at h1; omega
  have hE : (e + g) * (e * M / (e + g)) + e * M % (e + g) = e * M := Nat.div_add_mod _ _
  have hρlt : e * M % (e + g) < e + g := Nat.mod_lt _ hfpos
  generalize e * M / (e + g) = n at hE
  generalize e * M % (e + g) = ρ at hE hρlt
  have hcoNat : Nat.Coprime e g := (Nat.coprime_add_self_right.mp (by rwa [add_comm] at hco))
  have hcoZ : IsCoprime (e : ℤ) (g : ℤ) := Nat.isCoprime_iff_coprime.mpr hcoNat
  have h2' : e + g ≤ (M - 1) * g := by simpa using h2
  have hdiv : ρ = 0 → e ∣ n := by
    intro hρ0
    have : e ∣ (e + g) * n := ⟨M, by rw [hρ0] at hE; omega⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left hco this
  have hint := wc_of_int (e : ℤ) (g : ℤ) (M : ℤ) (n : ℤ) (ρ : ℤ) (by exact_mod_cast he) (by exact_mod_cast hg) (by positivity)
    (by positivity) (by omega) (by exact_mod_cast hE.symm) hcoZ (by exact_mod_cast h1)
    (by have : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
        have h' : ((e + g : ℕ) : ℤ) ≤ (((M - 1) * g : ℕ) : ℤ) := by exact_mod_cast h2'
        push_cast [Nat.cast_mul, this] at h' ⊢; linarith)
    (fun h0 => by exact_mod_cast hdiv (by exact_mod_cast h0))
  by_cases hρ0 : ρ = 0
  · have hn1 : 1 ≤ n := by
      by_contra hh; have : n = 0 := by omega
      rw [this, hρ0] at hE; nlinarith
    refine ⟨n - 1, n + 1, n, ?_⟩
    have := hint.1 (by exact_mod_cast hρ0)
    push_cast [Nat.cast_sub hn1] at this ⊢
    exact this
  · refine ⟨n, n + 1, n, ?_⟩
    have := hint.2 (by exact_mod_cast Nat.pos_of_ne_zero hρ0)
    push_cast at this ⊢
    exact this

/-- non-vacuity: `W_3(2,5)` (tile count 414). -/
example : ∃ t r q : ℕ, WC ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) ((3 : ℕ) : ℝ) (t : ℝ) (r : ℝ) (q : ℝ) :=
  wc_nat 2 5 3 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- non-vacuity: `W_4(3,5)` (tile count 656), explicit `(t,r,q) = (2,3,2)`. -/
theorem wc_W4_3_5 : WC (3 : ℝ) 5 4 2 3 2 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- non-vacuity: `W_3(2,5)`, explicit `(t,r,q) = (1,2,1)`. -/
theorem wc_W3_2_5 : WC (2 : ℝ) 5 3 1 2 1 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Theorem W placement, threshold form.**  For coprime `2 <= e`, `e+2 <= f`, `f <= M e`, `f <= (M-1)(f-e)` there are naturals
`t r q` such that the ten triangles of the template have pairwise disjoint interiors, lie in the target `A,O,B`, and cover its
interior (all in Fable's integer skew frame, affine-invariant statement). -/
theorem w_placement_threshold (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f) (h1 : f ≤ M * e)
    (h2 : f ≤ (M - 1) * (f - e)) :
    ∃ t r q : ℕ,
      (∀ i j, i ≠ j → Disjoint (tris (e : ℝ) f M t r q i).op (tris (e : ℝ) f M t r q j).op) ∧
      (∀ i, (tris (e : ℝ) f M t r q i).cl ⊆ (tgt (e : ℝ) f M).cl) ∧
      (∀ z ∈ (tgt (e : ℝ) f M).op, ∃ i, z ∈ (tris (e : ℝ) f M t r q i).cl) := by
  obtain ⟨t, r, q, h⟩ := wc_nat e f M hco he hef h1 h2
  exact ⟨t, r, q, w_placement h⟩

/-- instances (non-vacuity): `W_3(2,5)` (tile count 414) and `W_4(3,5)` (656). -/
theorem placement_W3_2_5 :
    (∀ i j, i ≠ j → Disjoint (tris (2 : ℝ) 5 3 1 2 1 i).op (tris (2 : ℝ) 5 3 1 2 1 j).op) ∧
    (∀ i, (tris (2 : ℝ) 5 3 1 2 1 i).cl ⊆ (tgt (2 : ℝ) 5 3).cl) := (w_placement wc_W3_2_5).imp_right (fun h => h.1)

theorem placement_W4_3_5 :
    (∀ i j, i ≠ j → Disjoint (tris (3 : ℝ) 5 4 2 3 2 i).op (tris (3 : ℝ) 5 4 2 3 2 j).op) ∧
    (∀ i, (tris (3 : ℝ) 5 4 2 3 2 i).cl ⊆ (tgt (3 : ℝ) 5 4).cl) := (w_placement wc_W4_3_5).imp_right (fun h => h.1)

end Erdos634.Draft.Chain.W

#print axioms Erdos634.Draft.Chain.W.w_placement_threshold
#print axioms Erdos634.Draft.Chain.W.placement_W3_2_5
#print axioms Erdos634.Draft.Chain.W.placement_W4_3_5
#print axioms Erdos634.Draft.Chain.W.wc_nat
#print axioms Erdos634.Draft.Chain.W.wc_W4_3_5
