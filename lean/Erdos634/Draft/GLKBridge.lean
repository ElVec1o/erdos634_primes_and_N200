import Mathlib.Tactic
import Erdos634.Draft.GLIFinal
import Erdos634.Draft.NSQLegs

/-!
# GLK(a): `CaseGClosed N` for `N = 4(2k+1)` whenever the arithmetic forces the leaf scale (`N = 60, 76`)

`Row4.P5` gives integers `M, M'` with `M·M' = N`, `M ≡ M' ≡ N (2)`, `3M < M'`, `M(a+c) = X = M'(c-a)`, `ab = c²-a²`
(`X` = leg of the target).  If these force `(M, M') = (2, 2(2k+1))` then `c/a = (k+1)/k`, so with `s = a/k²`
`(a,b,c) = s(k², 2k+1, k(k+1))` and `X = s·2k(2k+1)`: exactly the hypotheses of `GLI.leafG_of_dissection`.
-/

namespace Erdos634.GLK

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.ChainComposite

/-- oriented bridge (base angles at vertices 0,1) -/
theorem caseG_oriented {N : ℕ} (k : ℕ) (hk : 3 ≤ k)
    (harith : ∀ M M' : ℤ, 0 < M → 0 < M' → (N : ℤ) = M * M' → (2 : ℤ) ∣ M - N → (2 : ℤ) ∣ M' - N →
      3 * M < M' → M = 2 ∧ M' = 2 * (2 * k + 1))
    (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) : False := by
  obtain ⟨M, M', hM, hM', hX1, hX2, hNM, hp, hp', hlt, -, -, hab⟩ := Row4.P5 D hα h hA hB
  obtain ⟨rfl, rfl⟩ := harith M M' hM hM' hNM hp hp' hlt
  obtain ⟨κ, -, -, ha, -, -, -, -, -⟩ := Row4.sides D h hA hB
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  push_cast at hX1 hX2
  have hc : c = (k + 1) / k * a := by
    field_simp
    nlinarith [hX1, hX2]
  obtain ⟨s, hs0, has⟩ : ∃ s : ℝ, 0 < s ∧ a = s * (k : ℝ) ^ 2 :=
    ⟨a / (k : ℝ) ^ 2, by positivity, by field_simp⟩
  have hcs : c = s * (k * (k + 1)) := by rw [hc, has]; field_simp
  have hbs : b = s * (2 * k + 1) := by
    have h1 : (s * (k : ℝ) ^ 2) * (b - s * (2 * k + 1)) = 0 := by
      rw [hcs, has] at hab; linear_combination hab
    have h2 : s * (k : ℝ) ^ 2 ≠ 0 := by positivity
    have := (mul_eq_zero.mp h1).resolve_left h2
    linarith
  refine Erdos634.GLI.leafG_of_dissection D k hk hs0 has hbs hcs hα h hA hB ?_
  have hX : D.target.oppLen 0 = 2 * (a + c) := hX1.symm
  rw [show dist (D.target.pts 1) (D.target.pts 2) = D.target.oppLen 0 from rfl, hX, hcs, has]
  push_cast; ring

private theorem cA'' (p q r : Plane) : cornerAngle p q r = cornerAngle r q p :=
  EuclideanGeometry.angle_comm (V := Plane) p q r

/-- any-label form of an oriented statement. -/
theorem caseG_of_oriented (N : ℕ)
    (key0 : ∀ D : CongruentDissection N, ∀ {α a b c : ℝ}, IrrPi α → D.model.TwoAlphaData α a b c →
      D.target.angleAt 0 = α → D.target.angleAt 1 = α → False) : CaseGClosed N := by
  intro D α a b c hα h i j hij hi hj
  have key : ∀ σ : Equiv.Perm (Fin 3),
      (D.relabelTarget' σ).target.angleAt 0 = α → (D.relabelTarget' σ).target.angleAt 1 = α → False :=
    fun σ h0 h1 => key0 (D.relabelTarget' σ) hα h h0 h1
  have p01 : D.target.angleAt 0 = α → D.target.angleAt 1 = α → False := fun h0 h1 => key0 D hα h h0 h1
  have p02 : D.target.angleAt 0 = α → D.target.angleAt 2 = α → False := fun h0 h2 =>
    key (Equiv.swap 1 2)
      (by
        have := h0; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA'']; simpa using this)
      (by
        have := h2; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA'']; simpa using this)
  have p12 : D.target.angleAt 1 = α → D.target.angleAt 2 = α → False := fun h1 h2 =>
    key (Equiv.swap 0 2)
      (by
        have := h2; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA'']; simpa using this)
      (by
        have := h1; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA'']; simpa using this)
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals first
    | exact p01 hi hj | exact p01 hj hi | exact p02 hi hj | exact p02 hj hi
    | exact p12 hi hj | exact p12 hj hi

theorem caseG_of_leafOnly (N k : ℕ) (hk : 3 ≤ k)
    (harith : ∀ M M' : ℤ, 0 < M → 0 < M' → (N : ℤ) = M * M' → (2 : ℤ) ∣ M - N → (2 : ℤ) ∣ M' - N →
      3 * M < M' → M = 2 ∧ M' = 2 * (2 * k + 1)) : CaseGClosed N :=
  caseG_of_oriented N (fun D _ _ _ _ hα h hA hB => caseG_oriented k hk harith D hα h hA hB)

theorem arith_60 : ∀ M M' : ℤ, 0 < M → 0 < M' → ((60 : ℕ) : ℤ) = M * M' → (2 : ℤ) ∣ M - ((60 : ℕ) : ℤ) →
    (2 : ℤ) ∣ M' - ((60 : ℕ) : ℤ) → 3 * M < M' → M = 2 ∧ M' = 2 * (2 * ((7 : ℕ) : ℤ) + 1) := by
  intro M M' hM hM' hN h1 h2 h3
  push_cast at *
  have : M ≤ 4 := by nlinarith
  interval_cases M <;> omega

theorem arith_76 : ∀ M M' : ℤ, 0 < M → 0 < M' → ((76 : ℕ) : ℤ) = M * M' → (2 : ℤ) ∣ M - ((76 : ℕ) : ℤ) →
    (2 : ℤ) ∣ M' - ((76 : ℕ) : ℤ) → 3 * M < M' → M = 2 ∧ M' = 2 * (2 * ((9 : ℕ) : ℤ) + 1) := by
  intro M M' hM hM' hN h1 h2 h3
  push_cast at *
  have : M ≤ 5 := by nlinarith
  interval_cases M <;> omega

/-- `CaseGClosed 60`: the whole branch (all scales, shapes: M=2 is forced). -/
theorem caseG_60 : CaseGClosed 60 := caseG_of_leafOnly 60 7 (by norm_num) arith_60
theorem caseG_76 : CaseGClosed 76 := caseG_of_leafOnly 76 9 (by norm_num) arith_76

end Erdos634.GLK

#print axioms Erdos634.GLK.caseG_60
#print axioms Erdos634.GLK.caseG_76
