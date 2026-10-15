import Mathlib
import Erdos634.Draft.FDDShapes
import Erdos634.Draft.RSBSine
import Erdos634.Draft.RSBCorner
import Erdos634.Draft.ThmIso
import Erdos634.Draft.ThmIsoShBridge
import Erdos634.Draft.FluxCRow2
import Erdos634.TriLawSin
import Erdos634.EdgeWordConversion

/-!
# RSB, part 3: sides, scale and the area identity of a REAL dissection in the table's form.

Setting (the paper's normalization, with a similarity scale `K > 0` as in `ADMCore`): the tile is
`K·(a,b,c)`, `(a,b,c) ∈ ℕ³` a primitive `120°`-triple (`gcd(a,b)=1`, `c² = a²+ab+b²`), with angles
`(α, π/3 − α, 2π/3)`, `α ∉ ℚπ`.

`bridge`: for ANY `CongruentDissection N` of any triangle by that tile there are a shape `s`, a vertex
labelling `σ` of the target, and an integer `k ≥ 1` with
  (i)   corner `σ j` has angle `m_j α + k_j π/3`, `(m_j,k_j) = s.triple j` (one of the eleven shapes);
  (ii)  the side opposite corner `σ j` is `K · k · D_j`, `D = s.sideVec a b c` (primitive vector): so
        `ABC = k·D` in units of `K`, the integrality of `k` coming from `EdgeWordConversion.side_walk_congruent`
        (each target side is a ℕ-combination of whole tile edges) and `vecGcd_one`;
  (iii) `s.AreaEq a b k N`, i.e. `N · den = k² · num` (the area equation), from `|det target| = N |det model|`.
-/

open scoped Classical

namespace Erdos634.Draft.RSBArea

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.FDDShapes
  Erdos634.Draft.RSBSine Erdos634.Draft.RSBCorner

variable {N : ℕ}

/-! ## Arithmetic: a proportional integer vector over a primitive one is an integer multiple -/

theorem prop_int (D n : Fin 3 → ℕ) (hg : Nat.gcd (Nat.gcd (D 0) (D 1)) (D 2) = 1) (hD0 : 0 < D 0)
    (h : ∀ j, n j * D 0 = n 0 * D j) : ∃ k : ℕ, ∀ j, n j = k * D j := by
  set g := Nat.gcd (n 0) (D 0) with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hD0
  obtain ⟨p, hp⟩ : g ∣ n 0 := Nat.gcd_dvd_left _ _
  obtain ⟨q, hq⟩ : g ∣ D 0 := Nat.gcd_dvd_right _ _
  have hcop : Nat.Coprime p q := by
    have := Nat.coprime_div_gcd_div_gcd (m := n 0) (n := D 0) hgpos
    have e1 : n 0 / g = p := by rw [hp]; exact Nat.mul_div_cancel_left _ hgpos
    have e2 : D 0 / g = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hgpos
    rwa [e1, e2] at this
  have hrel : ∀ j, p * D j = q * n j := by
    intro j
    have := h j
    rw [hp, hq] at this
    have h2 : g * (p * D j) = g * (q * n j) := by
      calc g * (p * D j) = (g * p) * D j := by ring
        _ = n j * (g * q) := by rw [← hp] at *; rw [← hq] at *; linarith [this]
        _ = g * (q * n j) := by ring
    exact Nat.eq_of_mul_eq_mul_left hgpos h2
  have hqD : ∀ j, q ∣ D j := by
    intro j
    have : q ∣ p * D j := ⟨n j, by rw [hrel j]⟩
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
  have hq1 : q = 1 := by
    have : q ∣ Nat.gcd (Nat.gcd (D 0) (D 1)) (D 2) :=
      Nat.dvd_gcd (Nat.dvd_gcd (hqD 0) (hqD 1)) (hqD 2)
    rw [hg] at this
    exact Nat.dvd_one.mp this
  refine ⟨p, fun j => ?_⟩
  have := hrel j
  rw [hq1] at this
  linarith

/-! ## Geometry -/

/-- Every side of the target of a `CongruentDissection` by the tile `K(a,b,c)` is `K · n`, `n ∈ ℕ`. -/
theorem target_side_nat (D : CongruentDissection N) {α K : ℝ} {a b c : ℕ}
    (hm : D.model.TwoPiThreeData α (K * a) (K * b) (K * c)) (i : Fin 3) :
    ∃ n : ℕ, D.target.oppLen i = K * n := by
  have hside : ∀ t : Fin 3, ∃ n : ℕ, Erdos634.EdgeWordConversion.sideLen D t = K * n := by
    intro t
    have e : Erdos634.EdgeWordConversion.sideLen D t = D.model.oppLen (t + 2) := by
      unfold Erdos634.EdgeWordConversion.sideLen Tri.oppLen
      fin_cases t <;> rfl
    rw [e]
    obtain ⟨σ, -, ha, -, hb, -, hc⟩ := hm
    obtain ⟨j, hj⟩ := σ.surjective (t + 2)
    rw [← hj]
    fin_cases j
    · exact ⟨a, ha⟩
    · exact ⟨b, hb⟩
    · exact ⟨c, hc⟩
  obtain ⟨P, Q, R, hPQR, -⟩ := Erdos634.EdgeWordConversion.side_walk_congruent D (i + 1)
  have e : D.target.oppLen i = dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) := by
    unfold Tri.oppLen
    fin_cases i <;> rfl
  obtain ⟨n0, h0⟩ := hside 0
  obtain ⟨n1, h1⟩ := hside 1
  obtain ⟨n2, h2⟩ := hside 2
  refine ⟨P * n0 + Q * n1 + R * n2, ?_⟩
  rw [e, ← hPQR, h0, h1, h2]
  push_cast; ring

/-- The pairwise law of sines on the target, in `oppLen`/`angleAt` form. -/
theorem law_sines (T : Tri) (i j : Fin 3) :
    T.oppLen i * Real.sin (T.angleAt j) = T.oppLen j * Real.sin (T.angleAt i) := by
  have h : ∀ x : Fin 3, Real.sin (T.angleAt (x + 1)) * T.oppLen x
      = Real.sin (T.angleAt x) * T.oppLen (x + 1) := fun x =>
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T x
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  have e12 : (1 : Fin 3) + 1 = 2 := rfl
  have e20 : (2 : Fin 3) + 1 = 0 := rfl
  rw [e01] at h0; rw [e12] at h1; rw [e20] at h2
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases fin3 i with rfl | rfl | rfl <;> rcases fin3 j with rfl | rfl | rfl <;>
    first | rfl | linarith

/-- `sin α = (√3/2) a / c` for a `120°` tile (positive branch). -/
theorem sin_alpha (α a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hcos : Real.cos α = (a + 2 * b) / (2 * c))
    (hsin0 : 0 ≤ Real.sin α) : Real.sin α * c = Real.sqrt 3 / 2 * a := by
  have hcne : c ≠ 0 := hc.ne'
  have hsq : (Real.sin α * c) ^ 2 = (Real.sqrt 3 / 2 * a) ^ 2 := by
    have h1 : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by rw [Real.sin_sq]
    have : (Real.sin α * c) ^ 2 = c ^ 2 - (a + 2 * b) ^ 2 / 4 := by
      rw [mul_pow, h1, hcos]; field_simp; ring
    rw [this]
    have : (Real.sqrt 3 / 2 * a) ^ 2 = 3 * a ^ 2 / 4 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; ring
    rw [this, hc2]; ring
  have hl : 0 ≤ Real.sin α * c := mul_nonneg hsin0 hc.le
  have hr : 0 ≤ Real.sqrt 3 / 2 * a := by positivity
  exact (pow_left_inj₀ hl hr two_ne_zero).mp hsq

/-- **The bridge.**  See the file header. -/
theorem bridge (D : CongruentDissection N) {α K : ℝ} (hK : 0 < K) (a b c : ℕ)
    (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α (K * a) (K * b) (K * c)) :
    ∃ (s : Shape) (σ : Equiv.Perm (Fin 3)) (k : ℕ), 0 < k ∧
      (∀ j, D.target.angleAt (σ j) = (s.triple j).1 * α + (s.triple j).2 * (Real.pi / 3)) ∧
      (∀ j, D.target.oppLen (σ j) = K * k * (s.sideV a b c j)) ∧
      s.AreaEq a b k N := by
  obtain ⟨s, σ, hang⟩ := corner_shape D hα hm
  obtain ⟨hcosK, hcK, haK, hbK⟩ := cos_alpha_of_TwoPiThree D.model hm
  have ha : 0 < a := by
    have : (0 : ℝ) < a := (pos_iff_pos_of_mul_pos haK).mp hK
    exact_mod_cast this
  have hb : 0 < b := by
    have : (0 : ℝ) < b := (pos_iff_pos_of_mul_pos hbK).mp hK
    exact_mod_cast this
  have hc0 : 0 < c := by
    have : (0 : ℝ) < c := (pos_iff_pos_of_mul_pos hcK).mp hK
    exact_mod_cast this
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc0
  have hcR2 : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + a * b + (b : ℝ) ^ 2 := by exact_mod_cast hc
  -- cos α, sin α in the unscaled coordinates
  have hKne : K ≠ 0 := hK.ne'
  have hcne : (c : ℝ) ≠ 0 := hcR.ne'
  have hcos : Real.cos α = ((a : ℝ) + 2 * b) / (2 * c) := by
    rw [hcosK]; field_simp
  have hcosc : Real.cos α * c = b + (a : ℝ) / 2 := by rw [hcos]; field_simp; ring
  have hα0 : 0 ≤ Real.sin α := by
    obtain ⟨σm, h0, -⟩ := hm
    have p1 : 0 < D.model.angleAt (σm 0) := Erdos634.MarchFlank.cornerAngle_pos D.model (σm 0)
    have p2 : D.model.angleAt (σm 0) < Real.pi :=
      Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model (σm 0)
    rw [h0] at p1 p2
    exact Real.sin_nonneg_of_nonneg_of_le_pi p1.le p2.le
  have hsinc : Real.sin α * c = Real.sqrt 3 / 2 * a :=
    sin_alpha α a b c haR hbR hcR hcR2 hcos hα0
  -- positivity of target angle sines
  have hsinpos : ∀ i, 0 < Real.sin (D.target.angleAt i) := fun i =>
    Real.sin_pos_of_pos_of_lt_pi (Erdos634.MarchFlank.cornerAngle_pos D.target i)
      (Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target i)
  -- sines of the shape's corners
  have hsc : ∀ j, Real.sin (D.target.angleAt (σ j)) * (c : ℝ) ^ (s.triple j).1.natAbs
      = Real.sqrt 3 / 2 * Wz a b (s.triple j).1 (s.triple j).2 := by
    intro j
    rw [hang j]
    obtain ⟨-, hk0, hk3⟩ := triple_realizable s j
    exact sin_corner α a b c hcosc hsinc _ _ hk0 hk3
  -- W_0 > 0
  have hW0 : 0 < Wz a b (s.triple 0).1 (s.triple 0).2 := by
    have h := hsc 0
    have hpos : 0 < Real.sin (D.target.angleAt (σ 0)) * (c : ℝ) ^ (s.triple 0).1.natAbs :=
      mul_pos (hsinpos _) (pow_pos hcR _)
    rw [h] at hpos
    have h3 : 0 < Real.sqrt 3 / 2 := by positivity
    exact (pos_iff_pos_of_mul_pos hpos).mp h3
  -- proportionality of sides
  have hprop : ∀ j, D.target.oppLen (σ j) * (s.sideV a b c 0 : ℝ)
      = D.target.oppLen (σ 0) * (s.sideV a b c j : ℝ) := by
    intro j
    have hl := law_sines D.target (σ j) (σ 0)
    have hr := ratio_table s a b c j
    have e0 := hsc 0
    have ej := hsc j
    have hpe0 : 0 < (c : ℝ) ^ (s.triple 0).1.natAbs := pow_pos hcR _
    have hpej : 0 < (c : ℝ) ^ (s.triple j).1.natAbs := pow_pos hcR _
    have hW : (Wz a b (s.triple 0).1 (s.triple 0).2) * (c : ℝ) ^ (s.triple j).1.natAbs ≠ 0 :=
      (mul_pos hW0 hpej).ne'
    have h3 : 0 < Real.sqrt 3 / 2 := by positivity
    apply mul_left_cancel₀ (mul_ne_zero hW (h3.ne'))
    -- ℓ_j sinA_0 = ℓ_0 sinA_j, multiply by c^{e_0} c^{e_j}
    have key : D.target.oppLen (σ j) * (Real.sqrt 3 / 2 * Wz a b (s.triple 0).1 (s.triple 0).2)
        * (c : ℝ) ^ (s.triple j).1.natAbs
        = D.target.oppLen (σ 0) * (Real.sqrt 3 / 2 * Wz a b (s.triple j).1 (s.triple j).2)
          * (c : ℝ) ^ (s.triple 0).1.natAbs := by
      rw [← e0, ← ej]
      have := congrArg (fun x => x * ((c : ℝ) ^ (s.triple 0).1.natAbs * (c : ℝ) ^ (s.triple j).1.natAbs)) hl
      simp only at this
      linear_combination this
    linear_combination ((s.sideV a b c 0 : ℕ) : ℝ) * key
      + (Real.sqrt 3 / 2 * D.target.oppLen (σ 0)) * hr
  -- integer sides
  have hn : ∀ j, ∃ n : ℕ, D.target.oppLen (σ j) = K * n := fun j => target_side_nat D hm (σ j)
  choose n hn using hn
  have hD0 : 0 < s.sideV a b c 0 := by
    cases s <;> simp only [Shape.sideV, Shape.sideVec, Matrix.cons_val_zero] <;> positivity
  have hnD : ∀ j, n j * s.sideV a b c 0 = n 0 * s.sideV a b c j := by
    intro j
    have := hprop j
    rw [hn j, hn 0] at this
    have h2 : K * ((n j * s.sideV a b c 0 : ℕ) : ℝ) = K * ((n 0 * s.sideV a b c j : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast mul_left_cancel₀ hK.ne' h2
  have hgcd : Nat.gcd (Nat.gcd (s.sideV a b c 0) (s.sideV a b c 1)) (s.sideV a b c 2) = 1 := by
    have := vecGcd_one s a b c hcop hc
    simpa [Shape.sideV] using this
  obtain ⟨k, hk⟩ := prop_int (s.sideV a b c) n hgcd hD0 hnD
  have hside : ∀ j, D.target.oppLen (σ j) = K * k * (s.sideV a b c j) := by
    intro j; rw [hn j, hk j]; push_cast; ring
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      have := hside 0
      have hl : 0 < D.target.oppLen (σ 0) := Tri.oppLen_pos _ _
      rw [h0] at this; simp at this; linarith
    · exact h0
  refine ⟨s, σ, k, hkpos, hang, hside, ?_⟩
  -- area identity
  have hdet := D.abs_detTri_target
  have hdet2 : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hdet
    simp only [mul_pow, sq_abs] at h
    exact h
  have hmod := Erdos634.Draft.ThmIso.model_four_det_sq D.model hm
  have htg := D.target.four_detTri_sq_sym
  rw [D.target.sum_perm 2 σ, D.target.sum_perm 4 σ] at htg
  rw [hside 0, hside 1, hside 2] at htg
  set Dv := s.sideV a b c with hDv
  -- heron_table
  have hh := heron_table s a b c hc
  have hHR : (4 * ((s.sideVec a b c).1 : ℝ) ^ 2 * ((s.sideVec a b c).2.1 : ℝ) ^ 2
      - (((s.sideVec a b c).1 : ℝ) ^ 2 + ((s.sideVec a b c).2.1 : ℝ) ^ 2
          - ((s.sideVec a b c).2.2 : ℝ) ^ 2) ^ 2) * (s.den a b : ℝ) ^ 2
      = (s.num a b : ℝ) ^ 2 * (3 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2) := by exact_mod_cast hh
  have e0 : (Dv 0 : ℝ) = ((s.sideVec a b c).1 : ℝ) := rfl
  have e1 : (Dv 1 : ℝ) = ((s.sideVec a b c).2.1 : ℝ) := rfl
  have e2 : (Dv 2 : ℝ) = ((s.sideVec a b c).2.2 : ℝ) := rfl
  rw [← e0, ← e1, ← e2] at hHR
  -- k^4 * H(D) * K^4 = 3 N² K⁴ a² b²
  have hKK : (K * k) ^ 4 * (4 * (Dv 0 : ℝ) ^ 2 * (Dv 1 : ℝ) ^ 2
      - ((Dv 0 : ℝ) ^ 2 + (Dv 1 : ℝ) ^ 2 - (Dv 2 : ℝ) ^ 2) ^ 2)
      = 3 * (N : ℝ) ^ 2 * ((K * a) ^ 2 * (K * b) ^ 2) := by
    have h1 : 4 * Erdos634.AreaDet.detTri D.target ^ 2
        = (K * k) ^ 4 * (4 * (Dv 0 : ℝ) ^ 2 * (Dv 1 : ℝ) ^ 2
            - ((Dv 0 : ℝ) ^ 2 + (Dv 1 : ℝ) ^ 2 - (Dv 2 : ℝ) ^ 2) ^ 2) := by
      rw [htg]; ring
    rw [← h1]
    linear_combination 4 * hdet2 + (N : ℝ) ^ 2 * hmod
  have hK4 : 0 < K ^ 4 := pow_pos hK 4
  have hab : 0 < (a : ℝ) ^ 2 * (b : ℝ) ^ 2 := mul_pos (pow_pos haR 2) (pow_pos hbR 2)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hdenN : 0 < s.den a b := by
    cases s <;> simp only [Shape.den] <;> positivity
  have hnumN : 0 < s.num a b := by
    cases s <;> simp only [Shape.num] <;> positivity
  have hden : 0 < (s.den a b : ℝ) := by exact_mod_cast hdenN
  have hnum : 0 < (s.num a b : ℝ) := by exact_mod_cast hnumN
  -- (k² num)² = (N den)²
  have hsq : ((k : ℝ) ^ 2 * (s.num a b : ℝ)) ^ 2 = ((N : ℝ) * (s.den a b : ℝ)) ^ 2 := by
    apply mul_left_cancel₀ (mul_pos (by norm_num : (0:ℝ) < 3) (mul_pos hK4 hab)).ne'
    linear_combination (s.den a b : ℝ) ^ 2 * hKK - (k : ℝ) ^ 4 * K ^ 4 * hHR
  have hpos1 : 0 ≤ (k : ℝ) ^ 2 * (s.num a b : ℝ) := by positivity
  have hpos2 : 0 ≤ (N : ℝ) * (s.den a b : ℝ) := by positivity
  have hfin := (pow_left_inj₀ hpos1 hpos2 two_ne_zero).mp hsq
  unfold Shape.AreaEq
  have hcast : ((N * s.den a b : ℕ) : ℝ) = ((k ^ 2 * s.num a b : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast hcast

end Erdos634.Draft.RSBArea

#print axioms Erdos634.Draft.RSBArea.bridge
#print axioms Erdos634.Draft.RSBArea.target_side_nat
#print axioms Erdos634.Draft.RSBArea.prop_int
