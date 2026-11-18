/-
Draft/WCornerStruct2.lean -- written 16 November 2026 (work item LEAN_CORNERSTRUCT_2026-11-16).  UNAUDITED beyond internal checks.  Not imported by any aggregate.  New leaf module (imports `WCornerStruct1`).
**The quantitative consequence of `w_corner_run_long` in the bottom rung of `W_M(e,f)`** and the non-vacuity controls.
* `rung_arith`: pure arithmetic.  Natural numbers `x y z` with `x e f + y (f²-e²) + z f² = M f (f²-e²)` and `f <= z`, where `(M-1)(f-e) < f <= M(f-e)`, `f <= M e`, `2 <= e`, coprime `e < f`, satisfy `y = 0` and
  `(x, z) = (M(f-e), M(f-e))` or `(M(f-e) - f, M(f-e) + e)`.  Proof: `C_AQ'` (`f | y`), `C_AQ'` again at `M - y/f` (a positive `y/f` would force `z < f`), then the congruence `f | x - M(f-e)` (coprimality), and `g = f - e < e` (a consequence of the window hypotheses).
* `w_bottom_rung_words`: for EVERY dissection `D₀` of `W_M(e,f)` in this rung, the word `(x,y,z)` of the side `AQ` (letter counts of the chain of `WLongRunWord`) has `y = 0` and is `c^{f+r} a^{f+r}` or `c^{f+r+e} a^r`, `r = M(f-e) - f`.
  It is the count dichotomy of the port analysis (WGAP_PORT_2026-11-16, B.2, internal notes); Lean gives exactly this (not less).  It decides NO value of `N` and is not a step across the rung.
* controls: `WTilable 2 3 3`, `6 11 11`, `6 11 17` (from `WGapRung6b`) satisfy `w_corner_run_long` (`z >= 3, 11, 11`); `(2,3,3)` lies in the rung (`r = 0`, `g = 1`) and the dichotomy holds there.
No sorry, no native_decide.
-/
import Erdos634.Draft.WCornerStruct1

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WCornerStruct

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Erdos634.Draft.FDBBaseBetaE1 Set
  Erdos634.Draft.WGapStmt Erdos634.Draft.WGapRung Erdos634.Draft.CollarG

/-- `(M-1)(f-e) < f <= M(f-e)`, `f <= M e`, `2 <= e`, coprime  imply  `f - e < e` -/
theorem rung_g_lt_e {e f M : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f) (hfM : f ≤ M * e)
    (hlow : (M - 1) * (f - e) < f) (hup : f ≤ M * (f - e)) : f - e < e := by
  obtain ⟨g, hg⟩ : ∃ g, f = e + g := ⟨f - e, by omega⟩
  have hgf : f - e = g := by omega
  rw [hgf] at hlow hup ⊢
  rcases Nat.lt_or_ge M 3 with hM3 | hM3
  · have hM : M = 0 ∨ M = 1 ∨ M = 2 := by omega
    rcases hM with rfl | rfl | rfl
    · omega
    · simp at hup; omega
    · -- `2 e >= e + g`, so `g <= e`; `g = e` contradicts coprimality
      have hle : g ≤ e := by omega
      rcases Nat.lt_or_ge g e with h | h
      · exact h
      · have hge : g = e := by omega
        have : e ∣ f := ⟨2, by omega⟩
        have := Nat.Coprime.eq_one_of_dvd hco this
        omega
  · -- `M >= 3`: `(M-2) g < e`, `g <= (M-2) g`
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 3 := ⟨M - 3, by omega⟩
    have h1 : (M' + 3 - 1) * g = (M' + 2) * g := by congr 1
    rw [h1] at hlow
    nlinarith [Nat.zero_le (M' * g)]

theorem rung_arith {e f M x y z : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f) (hfM : f ≤ M * e)
    (hlow : (M - 1) * (f - e) < f) (hup : f ≤ M * (f - e))
    (hnat : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2)) (hz : f ≤ z) :
    y = 0 ∧ ((x = M * (f - e) ∧ z = M * (f - e)) ∨ (x = M * (f - e) - f ∧ z = M * (f - e) + e)) := by
  have hgE := rung_g_lt_e hco he hef hfM hlow hup
  have hdiv := (SplusThick.C_AQ' (by omega) hef hco hnat).1
  obtain ⟨m, hm⟩ := hdiv
  have hb0 : 0 < f ^ 2 - e ^ 2 := Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hef (by norm_num))
  have hf0 : 0 < f := by omega
  have hmM : m ≤ M := by
    by_contra h
    push_neg at h
    have h1 : f * (M + 1) * (f ^ 2 - e ^ 2) ≤ f * m * (f ^ 2 - e ^ 2) := by
      apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; omega
    have h2 := Nat.mul_pos hf0 hb0
    rw [hm] at hnat
    nlinarith [Nat.zero_le (x * (e * f)), Nat.zero_le (z * f ^ 2)]
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + m := ⟨M - m, by omega⟩
  have h0 : x * (e * f) + 0 * (f ^ 2 - e ^ 2) + z * f ^ 2 = M' * f * (f ^ 2 - e ^ 2) := by
    rw [hm] at hnat; nlinarith [hnat]
  have hC := (SplusThick.C_AQ' (by omega) hef hco h0).2
  have hm0 : m = 0 := by
    by_contra hmne
    have h1 : M' * (f - e) ≤ (M' + m - 1) * (f - e) := Nat.mul_le_mul_right _ (by omega)
    have := hC (by omega)
    have h2 : z ≤ M' * (f - e) := this
    omega
  subst hm0
  simp only [Nat.add_zero, Nat.mul_zero] at hm hnat hlow hup hfM ⊢
  refine ⟨hm, ?_⟩
  subst hm
  clear hC h0 hmM
  obtain ⟨g, hg⟩ : ∃ g, f = e + g := ⟨f - e, by omega⟩
  have hgf : f - e = g := by omega
  rw [hgf] at hlow hup hgE ⊢
  -- the word: `x e + z f = P (f + e)` with `P = M' g`
  obtain ⟨P, hP⟩ : ∃ P, P = M' * g := ⟨_, rfl⟩
  rw [← hP] at hup ⊢
  have hP2 : P < f + g := by
    rcases Nat.eq_zero_or_pos M' with h0' | h0'
    · subst h0'; simp at hP; omega
    · obtain ⟨M'', rfl⟩ : ∃ M'', M' = M'' + 1 := ⟨M' - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hlow
      have : P = M'' * g + g := by rw [hP]; ring
      omega
  have hbz : ((f ^ 2 - e ^ 2 : ℕ) : ℤ) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2)]; push_cast; ring
  have hZ : (x : ℤ) * e * f + z * f ^ 2 = (M' : ℤ) * f * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hnat
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hbz, Nat.cast_zero, zero_mul, add_zero] at this
    linarith
  have hgZ : (f : ℤ) = e + g := by exact_mod_cast hg
  have hPZ : (P : ℤ) = M' * g := by exact_mod_cast hP
  have hf0z : (f : ℤ) ≠ 0 := by exact_mod_cast hf0.ne'
  have hZ2 : (x : ℤ) * e + z * f = P * (f + e) := by
    apply mul_left_cancel₀ hf0z
    rw [hPZ]
    have : (f : ℤ) ^ 2 - (e : ℤ) ^ 2 = g * (f + e) := by rw [hgZ]; ring
    rw [this] at hZ
    linear_combination hZ
  have hdvd : (f : ℤ) ∣ ((x : ℤ) - P) * e := ⟨P - z, by linear_combination hZ2⟩
  have hcop : IsCoprime (f : ℤ) (e : ℤ) := Nat.isCoprime_iff_coprime.2 hco.symm
  obtain ⟨s, hs⟩ := hcop.dvd_of_dvd_mul_right hdvd
  have hes : (e : ℤ) * s = P - z := by
    apply mul_left_cancel₀ hf0z
    linear_combination hZ2 - (e : ℤ) * hs
  have hPf : (f : ℤ) ≤ P := by exact_mod_cast hup
  have hPf2 : (P : ℤ) < f + g := by exact_mod_cast hP2
  have hzf : (f : ℤ) ≤ z := by exact_mod_cast hz
  have hgeZ : (g : ℤ) < e := by exact_mod_cast hgE
  have h0e : (0 : ℤ) < e := by exact_mod_cast (show 0 < e by omega)
  have hgfZ : (g : ℤ) < f := by rw [hgZ]; linarith
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hs1 : s ≤ 0 := by
    by_contra h
    have h1 : 1 ≤ s := by omega
    have h2 : (e : ℤ) * 1 ≤ e * s := mul_le_mul_of_nonneg_left h1 h0e.le
    linarith
  have hs2 : -1 ≤ s := by
    by_contra h
    have h1 : s ≤ -2 := by omega
    have h2 : (f : ℤ) * s ≤ f * (-2) := mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hs3 : s = 0 ∨ s = -1 := by omega
  rcases hs3 with rfl | rfl
  · left
    refine ⟨by omega, by omega⟩
  · right
    refine ⟨by omega, by omega⟩

/-- **THE BOTTOM RUNG, COUNT DICHOTOMY (a statement about every tiling).**  Let `e < f` be coprime, `2 <= e`, `f <= M e` and `(M-1)(f-e) < f <= M(f-e)` (put `r = M(f-e) - f`).  For every congruent dissection `D₀`
of the triangle `W_M(e,f)` by the tile `(e f, f² - e², f²)`, the side `AQ` has the long-run chain of `WLongRunWord` with counts `(x, y, z)` satisfying `y = 0` and either `x = z = f + r` (`c^{f+r} a^{f+r}`)
or `x = r`, `z = f + r + e` (`c^{f+r+e} a^r`).  A COUNT statement; decides no `N`. -/
theorem w_bottom_rung_words {N e f M : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f) (hfM : f ≤ M * e)
    (hlow : (M - 1) * (f - e) < f) (hup : f ≤ M * (f - e))
    (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ x y z : ℕ, WLongRunWord D₀ M e f x y z ∧ y = 0 ∧
      ((x = M * (f - e) ∧ z = M * (f - e)) ∨ (x = M * (f - e) - f ∧ z = M * (f - e) + e)) := by
  have hM : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hup; omega
    · exact h
  obtain ⟨x, y, z, hw, hnat, hz⟩ := w_corner_run_long hco (by omega) hef hM D₀ hT hMod
  exact ⟨x, y, z, hw, rung_arith hco he hef hfM hlow hup hnat hz⟩

/-! ## Controls on the three Lean tilings of `WGapRung6b` -/

theorem ctl_2_3_3 : ∃ (N : ℕ) (D₀ : CongruentDissection N) (x y z : ℕ), WLongRunWord D₀ 3 2 3 x y z ∧ 3 ≤ z ∧
    y = 0 ∧ ((x = 3 ∧ z = 3) ∨ (x = 0 ∧ z = 5)) := by
  obtain ⟨D₀, hT, hMod⟩ := wt_2_3_3
  obtain ⟨x, y, z, hw, hnat, hz⟩ := w_corner_run_long (e := 2) (f := 3) (M := 3) (by decide) (by omega) (by omega) (by omega) D₀ hT hMod
  have := rung_arith (e := 2) (f := 3) (M := 3) (x := x) (y := y) (z := z) (by decide) le_rfl (by omega) (by omega) (by omega) (by omega) hnat hz
  exact ⟨_, D₀, x, y, z, hw, hz, this.1, by simpa using this.2⟩

theorem ctl_6_11_11 : ∃ (N : ℕ) (D₀ : CongruentDissection N) (x y z : ℕ), WLongRunWord D₀ 11 6 11 x y z ∧ 11 ≤ z := by
  obtain ⟨D₀, hT, hMod⟩ := wt_6_11_11
  obtain ⟨x, y, z, hw, hnat, hz⟩ := w_corner_run_long (e := 6) (f := 11) (M := 11) (by decide) (by omega) (by omega) (by omega) D₀ hT hMod
  exact ⟨_, D₀, x, y, z, hw, hz⟩

theorem ctl_6_11_17 : ∃ (N : ℕ) (D₀ : CongruentDissection N) (x y z : ℕ), WLongRunWord D₀ 17 6 11 x y z ∧ 11 ≤ z := by
  obtain ⟨D₀, hT, hMod⟩ := wt_6_11_17
  obtain ⟨x, y, z, hw, hnat, hz⟩ := w_corner_run_long (e := 6) (f := 11) (M := 17) (by decide) (by omega) (by omega) (by omega) D₀ hT hMod
  exact ⟨_, D₀, x, y, z, hw, hz⟩

/-- the hypotheses of `w_bottom_rung_words` are satisfiable (at `(e,f,M) = (2,3,3)`, a real Lean tiling, above) and pure arithmetic instances exist beyond the tilings: `(3,5,3)`, `(5,8,3)`, `(4,7,3)` -/
example : (Nat.Coprime 2 3 ∧ 2 ≤ 2 ∧ 2 < 3 ∧ 3 ≤ 3 * 2 ∧ (3 - 1) * (3 - 2) < 3 ∧ 3 ≤ 3 * (3 - 2)) := by decide
example : (Nat.Coprime 3 5 ∧ 2 ≤ 3 ∧ 3 < 5 ∧ 5 ≤ 3 * 3 ∧ (3 - 1) * (5 - 3) < 5 ∧ 5 ≤ 3 * (5 - 3)) := by decide
example : (Nat.Coprime 5 8 ∧ 2 ≤ 5 ∧ 5 < 8 ∧ 8 ≤ 3 * 5 ∧ (3 - 1) * (8 - 5) < 8 ∧ 8 ≤ 3 * (8 - 5)) := by decide

#print axioms w_corner_run_long
#print axioms no_tiling_W_gap'
#print axioms rung_g_lt_e
#print axioms rung_arith
#print axioms w_bottom_rung_words
#print axioms ctl_2_3_3
#print axioms ctl_6_11_11
#print axioms ctl_6_11_17

end Erdos634.Draft.WCornerStruct
