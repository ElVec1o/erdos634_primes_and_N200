/-
Draft/E60Mod9C.lean — `E60Pair 87 29 9` by the mod-9 obstruction of the direction-class cancellation.
Mathematics (, derived and checked by computer lattice computations, then formalized here):
  * `Dissection.flux_cancel` holds for EVERY odd weight `Dir → ℝ`; the weights `d ↦ g(pos d)` (`E60Mod9A`) with `g0, g1`
    (`E60Mod9B`) are odd.  Every tile (of either chirality, in any coset of the direction lattice) has flux
    `a P + b Q + c R` with `(P,Q,R) = coef g t pos` of a type `(t, o, x)`.
  * At `N = 87`, `(m₁,m₂) = (29,9)`: `a + b = 19S/87`, `c = 10S/87`, `(87(a−b))² = 13 S²` (`13` not a square), so for integers
    `P,Q,R,w`: `P a + Q b + R c = S w` forces `P = Q` and `19(P+Q) + 20 R = 174 w` (`split87`).
  * Summing the `g0`-identity and the `g1`-identity: `Σ_i ν_i = 38 Σ(P₀+Q₀) + 40 ΣR₀ + Σ(P₁−Q₁) = 348 · 1` (boundary value
    `g0(0,0)+g0(2,0)+g0(4,0) = 1`), but each `ν_i` is divisible by 9 (`nu_div`, a finite check over all 216 tile types) and
    `9 ∤ 348`.
No sorry, no native_decide.
-/
import Erdos634.Draft.E60Mod9B

open scoped Classical

namespace Erdos634.Draft.E60Mod9

open Erdos634.Geometry Erdos634.Draft.CompositeE5Gen

section W

variable (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (anc : Real.Angle)

theorem tile_type (T : Tri) {a b c : ℝ} (hS : T.SixtyData α a b c)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L) :
    ∃ t : Fin 3 → Fin 3, Function.Injective t ∧ (∀ k, T.oppLen k = ![a, b, c] (t k)) ∧
      ∀ k, ext α hα anc T h k = E3 (t k) := by
  obtain ⟨ρ, h0, o0, h1, o1, h2, o2⟩ := hS
  refine ⟨ρ.symm, ρ.symm.injective, ?_, ?_⟩
  · intro k
    obtain ⟨m, rfl⟩ := ρ.surjective k
    rw [Equiv.symm_apply_apply]
    have hm : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
    rcases hm with rfl | rfl | rfl
    · simpa using o0
    · simpa using o1
    · simpa using o2
  · intro k
    obtain ⟨m, rfl⟩ := ρ.surjective k
    rw [Equiv.symm_apply_apply]
    have hm : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
    unfold ext
    rcases hm with rfl | rfl | rfl
    · have := Lam_of_eq α hα anc (Real.pi - T.angleAt (ρ 0)) 3 (-1)
        (by rw [h0]; push_cast; ring) (T.pi_sub_angleAt_mem (Gc α hα anc) h (ρ 0))
      rw [this]; decide
    · have := Lam_of_eq α hα anc (Real.pi - T.angleAt (ρ 1)) 1 1
        (by rw [h1]; push_cast; ring) (T.pi_sub_angleAt_mem (Gc α hα anc) h (ρ 1))
      rw [this]; decide
    · have := Lam_of_eq α hα anc (Real.pi - T.angleAt (ρ 2)) 2 0
        (by rw [h2]; push_cast; ring) (T.pi_sub_angleAt_mem (Gc α hα anc) h (ρ 2))
      rw [this]; decide

/-- **Every tile has a coefficient-triple flux**, for every weight `g` simultaneously. -/
theorem tile_flux_coef (T : Tri) {a b c : ℝ} (hS : T.SixtyData α a b c)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L) :
    ∃ t : Fin 3 → Fin 3, Function.Injective t ∧ ∃ (o : Bool) (x : GZ), ∀ g : GZ → ℤ,
      T.flux (fW α hα anc g) =
        a * (coef g t (pk o t x) 0 : ℝ) + b * (coef g t (pk o t x) 1 : ℝ)
          + c * (coef g t (pk o t x) 2 : ℝ) := by
  obtain ⟨t, ht, hlen, hext⟩ := tile_type α hα anc T hS h
  refine ⟨t, ht, ?_⟩
  rcases T.det_pos_or_neg with hT | hT
  · refine ⟨true, pos α hα anc (T.leftUnit 0).angle, fun g => ?_⟩
    rw [tile_flux_pos α hα anc g T hT h, ← sum_coef a b c t (pk true t _) g]
    simp only [Fin.sum_univ_three, pk, if_true, posP, show (0 : Fin 3) + 2 = 2 from rfl,
      show (1 : Fin 3) + 2 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hlen, hext]
    simp
  · refine ⟨false, pos α hα anc (T.leftUnit 2).angle, fun g => ?_⟩
    rw [tile_flux_neg α hα anc g T hT h, ← sum_coef a b c t (pk false t _) g]
    simp only [Fin.sum_univ_three, pk, posM, show (0 : Fin 3) + 2 = 2 from rfl,
      show (1 : Fin 3) + 2 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hlen, hext]
    simp
    ring

end W

/-- The target flux of the weight `g` (anchored at side `01` of an equilateral target). -/
theorem target_flux_W {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (g : GZ → ℤ) :
    D.target.flux (fW α hα (D.target.leftUnit 0).angle g) =
      D.target.oppLen 0 * ((g (0, 0) + g (2, 0) + g (4, 0) : ℤ) : ℝ) := by
  set anc := (D.target.leftUnit 0).angle with hanc
  have e3 : Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α := by push_cast; ring
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L := by
    intro k; rw [hP k, e3]; exact wAt_mem _ _ _ _ _ _
  obtain ⟨e1, e2, -⟩ := Row5.equilateral_boundary D hα 0
    (fun k => D.model.sixty_angles_mem hα h 0 _ k) hP
  have hext : ∀ k, ext α hα anc D.target htarget k = (2, 0) := by
    intro k
    unfold ext
    have := Lam_of_eq α hα anc (Real.pi - D.target.angleAt k) 2 0
      (by rw [hP k]; push_cast; ring) (D.target.pi_sub_angleAt_mem (Gc α hα anc) htarget k)
    rw [this]; decide
  rcases D.target.det_pos_or_neg with hT | hT
  · rw [tile_flux_pos α hα anc g D.target hT htarget, pos_anchor, hext 1, hext 2, e1, e2]
    have h1 : ((0 : GZ) + (2, 0)) = (2, 0) := by decide
    have h2 : ((0 : GZ) + (2, 0) + (2, 0)) = (4, 0) := by decide
    rw [h2, h1]
    have h0 : (0 : GZ) = (0, 0) := rfl
    rw [h0]
    push_cast; ring
  · have hrel := pos_rel_neg α hα anc D.target hT htarget
    rw [pos_anchor, hext 1, hext 2] at hrel
    have hy : pos α hα anc (D.target.leftUnit 2).angle = (2, 0) := by
      revert hrel
      generalize pos α hα anc (D.target.leftUnit 2).angle = y
      revert y
      decide
    rw [tile_flux_neg α hα anc g D.target hT htarget, hy, hext 2, hext 1, e1, e2]
    have h1 : (((2 : ZMod 6), (0 : ZMod 3)) + (2, 0)) = (4, 0) := by decide
    have h2 : (((2 : ZMod 6), (0 : ZMod 3)) + (2, 0) + (2, 0)) = (0, 0) := by decide
    rw [h2, h1]
    push_cast; ring

/-- **The irrational split.**  At `N = 87`, `(m₁,m₂) = (29,9)`: an integer identity `P a + Q b + R c = S w` forces
`P = Q` and `19(P+Q) + 20 R = 174 w`. -/
theorem split87 {a b c S : ℝ} (hS0 : 0 < S) (h1 : (29 : ℝ) * (a + b - c) = 3 * S)
    (h2 : (9 : ℝ) * (a + b + c) = 3 * S) (harea : S ^ 2 = (87 : ℝ) * a * b)
    (P Q R w : ℤ) (h : (P : ℝ) * a + Q * b + R * c = S * w) :
    P = Q ∧ 19 * (P + Q) + 20 * R = 174 * w := by
  have e1 : 87 * (a + b) = 19 * S := by linarith
  have e2 : 87 * c = 10 * S := by linarith
  have hu : (87 * (a - b)) ^ 2 = 13 * S ^ 2 := by
    have : (87 * (a - b)) ^ 2 = (87 * (a + b)) ^ 2 - 4 * 87 * (87 * a * b) := by ring
    rw [this, e1]
    nlinarith [harea]
  have hK : ((P : ℝ) - Q) * (87 * (a - b)) = S * ((174 * w - 19 * (P + Q) - 20 * R : ℤ) : ℝ) := by
    push_cast
    linear_combination 174 * h - ((P : ℝ) + Q) * e1 - 2 * (R : ℝ) * e2
  have hPQ : P = Q := by
    by_contra hne
    have hL : ((P - Q : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
    have hK2 : (((174 * w - 19 * (P + Q) - 20 * R : ℤ) : ℝ) / ((P - Q : ℤ) : ℝ)) ^ 2 = ((13 : ℤ) : ℝ) := by
      have hS2 : S ^ 2 ≠ 0 := by positivity
      push_cast at hL hK ⊢
      field_simp
      have h3 : ((P : ℝ) - Q) ^ 2 * (87 * (a - b)) ^ 2
          = S ^ 2 * ((174 * w - 19 * (P + Q) - 20 * R : ℤ) : ℝ) ^ 2 := by
        rw [← mul_pow, hK, mul_pow]; push_cast; ring
      rw [hu] at h3
      push_cast at h3
      apply mul_left_cancel₀ hS2
      push_cast
      linear_combination -h3
    have hsq := isSquare_of_rat_sq 13 (174 * w - 19 * (P + Q) - 20 * R) (P - Q) (sub_ne_zero.mpr hne) hK2
    exact absurd hsq (by decide +kernel)
  refine ⟨hPQ, ?_⟩
  subst hPQ
  have hz : S * ((174 * w - 19 * (P + P) - 20 * R : ℤ) : ℝ) = 0 := by
    rw [← hK]; ring
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact absurd h0 hS0.ne'
  · have : (174 * w - 19 * (P + P) - 20 * R : ℤ) = 0 := by exact_mod_cast h0
    omega

/-- **`E60Pair 87 29 9`.**  () -/
theorem e60Pair_87 : E60Pair 87 29 9 := by
  intro D α a b c hα h hE hS1 hS2
  have hP : ∀ k, D.target.angleAt k = Real.pi / 3 := hE
  set anc := (D.target.leftUnit 0).angle with hanc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, harea, -⟩ := Row5.theoremE_sixty D hα h hP
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have hS1' : (29 : ℝ) * (a + b - c) = 3 * D.target.oppLen 0 := by exact_mod_cast hS1
  have hS2' : (9 : ℝ) * (a + b + c) = 3 * D.target.oppLen 0 := by exact_mod_cast hS2
  have harea' : D.target.oppLen 0 ^ 2 = (87 : ℝ) * a * b := by exact_mod_cast harea
  have hmem : ∀ i k, (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L :=
    fun i => Row5Hr0.tile_angles_mem D hα h i
  -- tile data
  have hdata : ∀ i, ∃ t : Fin 3 → Fin 3, Function.Injective t ∧ ∃ (o : Bool) (x : GZ), ∀ g : GZ → ℤ,
      (D.tile i).flux (fW α hα anc g) =
        a * (coef g t (pk o t x) 0 : ℝ) + b * (coef g t (pk o t x) 1 : ℝ)
          + c * (coef g t (pk o t x) 2 : ℝ) := by
    intro i
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
    have hS : (D.tile i).SixtyData α a b c := by
      obtain ⟨τ, h0, o0, h1, o1, h2, o2⟩ := h
      refine ⟨σ.symm * τ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Equiv.Perm.mul_apply, (hσ _).1, (hσ _).2, Equiv.apply_symm_apply] <;> assumption
    exact tile_flux_coef α hα anc (D.tile i) hS (hmem i)
  choose t ht o x hflux using hdata
  -- the two cancellation identities
  have hcancel : ∀ g : GZ → ℤ, (∀ y, g (y + (3, 0)) = - g y) →
      ∑ i, (D.tile i).flux (fW α hα anc g) = D.target.flux (fW α hα anc g) :=
    fun g hg => D.flux_cancel (fW α hα anc g) (fW_odd α hα anc g hg)
  have hI : ∀ g : GZ → ℤ, (∀ y, g (y + (3, 0)) = - g y) →
      ((∑ i, coef g (t i) (pk (o i) (t i) (x i)) 0 : ℤ) : ℝ) * a
        + ((∑ i, coef g (t i) (pk (o i) (t i) (x i)) 1 : ℤ) : ℝ) * b
        + ((∑ i, coef g (t i) (pk (o i) (t i) (x i)) 2 : ℤ) : ℝ) * c
        = D.target.oppLen 0 * ((g (0, 0) + g (2, 0) + g (4, 0) : ℤ) : ℝ) := by
    intro g hg
    have := hcancel g hg
    rw [target_flux_W D hα h hP g] at this
    rw [← this, Finset.sum_congr rfl fun i _ => hflux i g]
    push_cast
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  -- split
  have s0 := split87 hS0 hS1' hS2' harea'
    (∑ i, coef g0 (t i) (pk (o i) (t i) (x i)) 0) (∑ i, coef g0 (t i) (pk (o i) (t i) (x i)) 1)
    (∑ i, coef g0 (t i) (pk (o i) (t i) (x i)) 2) (g0 (0, 0) + g0 (2, 0) + g0 (4, 0))
    (by have := hI g0 g0_odd; linarith)
  have s1 := split87 hS0 hS1' hS2' harea'
    (∑ i, coef g1 (t i) (pk (o i) (t i) (x i)) 0) (∑ i, coef g1 (t i) (pk (o i) (t i) (x i)) 1)
    (∑ i, coef g1 (t i) (pk (o i) (t i) (x i)) 2) (g1 (0, 0) + g1 (2, 0) + g1 (4, 0))
    (by have := hI g1 g1_odd; linarith)
  rw [boundary_g0] at s0
  obtain ⟨-, hr0⟩ := s0
  obtain ⟨hpq1, -⟩ := s1
  -- Σ ν_i = 348
  have hsumnu : ∑ i, nu (t i) (pk (o i) (t i) (x i)) = 348 := by
    unfold nu
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    omega
  have hdvd : (9 : ℤ) ∣ ∑ i, nu (t i) (pk (o i) (t i) (x i)) :=
    Finset.dvd_sum fun i _ => nu_div (t i) (ht i) (o i) (x i)
  rw [hsumnu] at hdvd
  exact absurd hdvd (by decide)

end Erdos634.Draft.E60Mod9

#print axioms Erdos634.Draft.E60Mod9.tile_flux_coef
#print axioms Erdos634.Draft.E60Mod9.target_flux_W
#print axioms Erdos634.Draft.E60Mod9.split87
#print axioms Erdos634.Draft.E60Mod9.e60Pair_87
