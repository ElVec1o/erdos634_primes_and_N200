/-
Draft/OpenReductions143.lean -- the open value `143` reduced to one instance.

`143 = 11 · 13` is not decided here.  Every leaf of the squarefree chain is closed in Lean except one instance of the
scalene target `F₂`, carried as a hypothesis:

    theorem not_tile_143_of (h : F2Inst143) (D : CongruentDissection 143) : False

where `F2Inst143` says that no triangle with sides `39, 55, 49` can be cut into congruent copies, in any number, of
a triangle with sides `3, 5, 7`.

The scalene leaf was formalized only as an arithmetic condition (`R8Gen2.NoF2`), whose lemmas are private.  The
section `F2x` below is a copy of that proof (`ChainCompositeR8b`, namespace `R8Gen2.F2`) in which the arithmetic
hypothesis is replaced by three handlers that also receive the geometric meaning of the integers:
`x = ν |a − b|` and `y = 3 ν b` (or `3 ν a`).  At `N = 143` the handlers find `(ν a, ν b, ν c) = (5, 3, 7)` or
`(3, 5, 7)`, and the dissection scaled by `ν` is an instance of `F2Inst143`.

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.OpenReductions
import Erdos634.Draft.R8ZFLeaf
import Erdos634.Draft.IsoInst

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.OpenRed.F2x

open Erdos634.Geometry
open Erdos634.Row8Arith
open Erdos634.Draft.R8F2AreaFormula (F2_area_formula)
open Erdos634.Draft.R8CompositeArg (no_prime_F4_form)
open Erdos634.Draft.R8Gen2 (rat_pos_int)

theorem c_sq (T : Erdos634.Geometry.Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

-- Factor identities
theorem F2_factor_alpha {ν a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (a - b - c) * (c + a - b) = -(3 * ν * a * b) := by linear_combination -ν * hc2

theorem F2_factor_beta {ν a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    -(ν * (a - b + c)) * (c + b - a) = -(3 * ν * a * b) := by linear_combination -ν * hc2

-- Flux value rewritten as -(3νab) — pure arithmetic
theorem flux_eq_neg3ab {ν a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - a * (a + 2 * b) - b * (2 * a + b)) = -(3 * ν * a * b) := by
  linear_combination ν * hc2

/-! ## N = 3z² − δ² -/

theorem f2_N_eq {N : ℕ} {a b c ν : ℝ} {δ z : ℤ}
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b))
    (hδ : (δ : ℝ) = ν * (a - b)) (hz : (z : ℝ) = ν * c) :
    (N : ℤ) = 3 * z ^ 2 - δ ^ 2 := by
  have hR : (N : ℝ) = 3 * (z : ℝ) ^ 2 - (δ : ℝ) ^ 2 := by
    rw [hδ, hz, hNreal]; nlinarith [hc2]
  exact_mod_cast hR

/-! ## δ = 0 case -/

theorem f2_delta_zero_False {N : ℕ} (h3 : ¬ (3 : ℤ) ∣ (N : ℤ))
    {z : ℤ} (hNeq : (N : ℤ) = 3 * z ^ 2) : False := by
  exact h3 ⟨z ^ 2, hNeq⟩
theorem f2_unused_old (z : ℤ) (hNeq : (15 : ℤ) = 3 * z ^ 2) : False := by
  have h5 : z ^ 2 = 5 := by linarith
  have h1 : z ≤ 2 := by nlinarith
  have h2 : -2 ≤ z := by nlinarith
  interval_cases z <;> omega

/-! ## toNat helper -/

theorem toNat_pos_of_pos {k : ℤ} (hk : 0 < k) : 0 < k.toNat := by
  have h : 0 < (k.toNat : ℤ) := by rw [Int.toNat_of_nonneg hk.le]; exact hk
  exact_mod_cast h

theorem toNat_cast_real {k : ℤ} (hk : 0 < k) : (k.toNat : ℝ) = (k : ℝ) := by
  have h : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.le
  exact_mod_cast h

/-! ## w ∈ ℚ cases — reuse no_prime_F4_form -/

-- δ > 0: N = (δ + 3νb)(2δ + 3νb), apply no_prime_F4_form with x=δ.toNat, y=3νb
theorem f2_wQ_pos {N : ℕ} {a b ν : ℝ}
    (Hpos : ∀ (x : ℕ) (y : ℚ) (z : ℤ), 0 < x → 0 < y → (N : ℚ) = ((x : ℚ) + y) * (2 * (x : ℚ) + y) →
      (N : ℤ) = 3 * z ^ 2 - (x : ℤ) ^ 2 → (x : ℝ) = ν * (a - b) → (y : ℝ) = 3 * (ν * b) → False)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b))
    {δ : ℤ} (hδ : (δ : ℝ) = ν * (a - b)) (hδ_pos : 0 < δ)
    (w_q : ℚ) (hw : (w_q : ℝ) = ν * (a + b))
    {z : ℤ} (hNeq : (N : ℤ) = 3 * z ^ 2 - δ ^ 2) : False := by
  -- y_q = (w_q - δ)/2 = νb ∈ ℚ
  set y_q : ℚ := (w_q - (δ : ℚ)) / 2
  have hy_R : (y_q : ℝ) = ν * b := by
    have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
    have : (y_q : ℝ) * 2 = ν * b * 2 := by
      push_cast [y_q]; field_simp; linarith [hw, hδ]
    linarith
  have hy_pos : 0 < y_q := by
    have : (0 : ℝ) < (y_q : ℝ) := by rw [hy_R]; exact mul_pos hν hb
    exact_mod_cast this
  -- δ.toNat as ℝ = ν(a-b)
  have hdn_R : (δ.toNat : ℝ) = ν * (a - b) := by
    rw [toNat_cast_real hδ_pos]; exact hδ
  have hdn_pos : 0 < δ.toNat := toNat_pos_of_pos hδ_pos
  -- N = (δ.toNat + 3*y_q)(2*δ.toNat + 3*y_q) in ℚ
  have hNq : (N : ℚ) = ((δ.toNat : ℚ) + 3 * y_q) * (2 * (δ.toNat : ℚ) + 3 * y_q) := by
    have hNR : (N : ℝ) = ((δ.toNat : ℝ) + 3 * (y_q : ℝ)) * (2 * (δ.toNat : ℝ) + 3 * (y_q : ℝ)) := by
      rw [hy_R, hdn_R, hNreal]; ring
    exact_mod_cast show ((N : ℚ) : ℝ) =
        (((δ.toNat : ℚ) + 3 * y_q) * (2 * (δ.toNat : ℚ) + 3 * y_q) : ℚ) by
      push_cast; linarith [hNR]
  exact Hpos δ.toNat (3 * y_q) z hdn_pos (by positivity) hNq
    (by rw [Int.toNat_of_nonneg hδ_pos.le]; exact hNeq) hdn_R (by push_cast; rw [hy_R])

-- δ < 0: N = (-δ + 3νa)(2*(-δ) + 3νa), apply no_prime_F4_form with x=(-δ).toNat, y=3νa
theorem f2_wQ_neg {N : ℕ} {a b ν : ℝ}
    (Hneg : ∀ (x : ℕ) (y : ℚ) (z : ℤ), 0 < x → 0 < y → (N : ℚ) = ((x : ℚ) + y) * (2 * (x : ℚ) + y) →
      (N : ℤ) = 3 * z ^ 2 - (x : ℤ) ^ 2 → (x : ℝ) = ν * (b - a) → (y : ℝ) = 3 * (ν * a) → False)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b))
    {δ : ℤ} (hδ : (δ : ℝ) = ν * (a - b)) (hδ_neg : δ < 0)
    (w_q : ℚ) (hw : (w_q : ℝ) = ν * (a + b))
    {z : ℤ} (hNeq : (N : ℤ) = 3 * z ^ 2 - δ ^ 2) : False := by
  -- x_q = (w_q + δ)/2 = νa ∈ ℚ
  set x_q : ℚ := (w_q + (δ : ℚ)) / 2
  have hx_R : (x_q : ℝ) = ν * a := by
    have : (x_q : ℝ) * 2 = ν * a * 2 := by push_cast [x_q]; field_simp; linarith [hw, hδ]
    linarith
  have hx_pos : 0 < x_q := by
    have : (0 : ℝ) < (x_q : ℝ) := by rw [hx_R]; exact mul_pos hν ha
    exact_mod_cast this
  set δ' := -δ
  have hδ'_pos : 0 < δ' := by omega
  have hd'n_pos : 0 < δ'.toNat := toNat_pos_of_pos hδ'_pos
  have hd'n_R : (δ'.toNat : ℝ) = ν * (b - a) := by
    rw [toNat_cast_real hδ'_pos]
    simp only [δ']; push_cast; linarith [hδ]
  have hNq : (N : ℚ) = ((δ'.toNat : ℚ) + 3 * x_q) * (2 * (δ'.toNat : ℚ) + 3 * x_q) := by
    have hNR : (N : ℝ) = ((δ'.toNat : ℝ) + 3 * (x_q : ℝ)) * (2 * (δ'.toNat : ℝ) + 3 * (x_q : ℝ)) := by
      rw [hx_R, hd'n_R, hNreal]; ring
    exact_mod_cast show ((N : ℚ) : ℝ) =
        (((δ'.toNat : ℚ) + 3 * x_q) * (2 * (δ'.toNat : ℚ) + 3 * x_q) : ℚ) by
      push_cast; linarith [hNR]
  exact Hneg δ'.toNat (3 * x_q) z hd'n_pos (by positivity) hNq
    (by rw [Int.toNat_of_nonneg hδ'_pos.le]
        have h2 : δ' ^ 2 = δ ^ 2 := by simp only [δ']; ring
        rw [h2]; exact hNeq) hd'n_R (by push_cast; rw [hx_R])

/-! ## Walk argument: δ ≠ 0 → ν(a+b) ∈ ℚ -/

-- When δ = ν(a−b) ≠ 0, the side-word walk on the target forces ν(a+b) ∈ ℚ.
-- δ < 0: use walk on target.oppLen(τ 0) = ν·a·(a+2b);  coefficient na+nb−δ > 0.
-- δ > 0: use walk on target.oppLen(τ 1) = ν·b·(2a+b);  coefficient na+nb+δ > 0.
-- Key algebraic identity (verified by ring): from na·u+nb·v+nc·z = u·(u+2v) (or v·(2u+v))
-- and u²+uv+v² = z², one derives (na+nb∓δ)·w = integer, giving w ∈ ℚ.
theorem f2_w_rational {N : ℕ} (D : CongruentDissection N) {α a b c ν : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F2Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    {δ : ℤ} (hδ : (δ : ℝ) = ν * (a - b)) (hδ0 : δ ≠ 0)
    {z : ℤ} (hz : (z : ℝ) = ν * c) :
    ∃ w_q : ℚ, (w_q : ℝ) = ν * (a + b) := by
  obtain ⟨σ_m, -, hm_a, -, hm_b, -, hm_c⟩ := hm
  obtain ⟨-, hgrid⟩ := ht
  obtain ⟨τ, -, ht0, -, ht1, -, -⟩ := hgrid
  -- (νa)²+(νa)(νb)+(νb)² = (νc)² = z²
  have hc2_nuv : (ν * a) ^ 2 + (ν * a) * (ν * b) + (ν * b) ^ 2 = (z : ℝ) ^ 2 := by
    rw [hz]; linear_combination -ν ^ 2 * hc2
  -- δ = νa − νb
  have hδ_uv : (δ : ℝ) = ν * a - ν * b := by linarith [hδ]
  rcases lt_or_gt_of_ne (show (δ : ℝ) ≠ 0 by exact_mod_cast hδ0) with hδ_neg | hδ_pos
  · -- δ < 0: walk on target.oppLen(τ 0) = ν·a·(a+2b)
    obtain ⟨na, nb, nc, hwalk⟩ := D.side_word σ_m hm_a hm_b hm_c (τ 0)
    have hwalkR : (na : ℝ) * a + nb * b + nc * c = ν * (a * (a + 2 * b)) :=
      hwalk.symm.trans ht0
    -- Multiply by ν: na·(νa) + nb·(νb) + nc·(νc) = (νa)·((νa)+2(νb))
    have h5 : (na : ℝ) * (ν * a) + nb * (ν * b) + nc * (z : ℝ) =
        (ν * a) * (ν * a + 2 * (ν * b)) := by
      rw [hz]; linear_combination ν * hwalkR
    -- (na+nb−δ)·w = 2z²−δ²−(na−nb)·δ−2nc·z
    have hW_eq : ((na : ℝ) + nb - (δ : ℝ)) * (ν * (a + b)) =
        2 * (z : ℝ) ^ 2 - (δ : ℝ) ^ 2 - ((na : ℝ) - nb) * (δ : ℝ) - 2 * nc * (z : ℝ) := by
      rw [show ν * (a + b) = ν * a + ν * b from by ring, hδ_uv]
      linear_combination 2 * h5 + 2 * hc2_nuv
    have hδ_neg_int : δ < 0 := by exact_mod_cast hδ_neg
    have hden_pos : (0 : ℤ) < (na : ℤ) + nb - δ := by
      have h1 : (0 : ℤ) ≤ (na : ℤ) := Int.natCast_nonneg na
      have h2 : (0 : ℤ) ≤ (nb : ℤ) := Int.natCast_nonneg nb
      omega
    set num_z : ℤ := 2 * z ^ 2 - δ ^ 2 - ((na : ℤ) - nb) * δ - 2 * nc * z
    set den_z : ℤ := (na : ℤ) + nb - δ
    refine ⟨(num_z : ℚ) / (den_z : ℚ), ?_⟩
    have hden_ne_r : (den_z : ℝ) ≠ 0 := by exact_mod_cast hden_pos.ne'
    have hW' : (den_z : ℝ) * (ν * (a + b)) = (num_z : ℝ) := by
      simp only [den_z, num_z]; push_cast; linarith [hW_eq]
    simp only [Rat.cast_div, Rat.cast_intCast]
    rw [div_eq_iff hden_ne_r]; linear_combination -hW'
  · -- δ > 0: walk on target.oppLen(τ 1) = ν·b·(2a+b)
    obtain ⟨na, nb, nc, hwalk⟩ := D.side_word σ_m hm_a hm_b hm_c (τ 1)
    have hwalkR : (na : ℝ) * a + nb * b + nc * c = ν * (b * (2 * a + b)) :=
      hwalk.symm.trans ht1
    have h5 : (na : ℝ) * (ν * a) + nb * (ν * b) + nc * (z : ℝ) =
        (ν * b) * (2 * (ν * a) + (ν * b)) := by
      rw [hz]; linear_combination ν * hwalkR
    -- (na+nb+δ)·w = 2z²−δ²+(na−nb)·δ−2nc·z
    have hW_eq : ((na : ℝ) + nb + (δ : ℝ)) * (ν * (a + b)) =
        2 * (z : ℝ) ^ 2 - (δ : ℝ) ^ 2 - ((na : ℝ) - nb) * (δ : ℝ) - 2 * nc * (z : ℝ) := by
      rw [show ν * (a + b) = ν * a + ν * b from by ring, hδ_uv]
      linear_combination 2 * h5 + 2 * hc2_nuv
    have hδ_pos_int : (0 : ℤ) < δ := by exact_mod_cast hδ_pos
    have hden_pos : (0 : ℤ) < (na : ℤ) + nb + δ := by
      have h1 : (0 : ℤ) ≤ (na : ℤ) := Int.natCast_nonneg na
      have h2 : (0 : ℤ) ≤ (nb : ℤ) := Int.natCast_nonneg nb
      omega
    set num_z : ℤ := 2 * z ^ 2 - δ ^ 2 - ((na : ℤ) - nb) * δ - 2 * nc * z
    set den_z : ℤ := (na : ℤ) + nb + δ
    refine ⟨(num_z : ℚ) / (den_z : ℚ), ?_⟩
    have hden_ne_r : (den_z : ℝ) ≠ 0 := by exact_mod_cast hden_pos.ne'
    have hW' : (den_z : ℝ) * (ν * (a + b)) = (num_z : ℝ) := by
      simp only [den_z, num_z]; push_cast; linarith [hW_eq]
    simp only [Rat.cast_div, Rat.cast_intCast]
    rw [div_eq_iff hden_ne_r]; linear_combination -hW'

/-! ## Core: given δ=(ν(a-b):ℤ) and z=(νc:ℤ), derive False -/

theorem f2_core {N : ℕ} (D : CongruentDissection N) {α a b c ν : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F2Data α a b c ν)
    (H1 : ∀ z : ℤ, (N : ℤ) ≠ 3 * z ^ 2)
    (Hpos : ∀ (x : ℕ) (y : ℚ) (z : ℤ), 0 < x → 0 < y → (N : ℚ) = ((x : ℚ) + y) * (2 * (x : ℚ) + y) →
      (N : ℤ) = 3 * z ^ 2 - (x : ℤ) ^ 2 → (x : ℝ) = ν * (a - b) → (y : ℝ) = 3 * (ν * b) → False)
    (Hneg : ∀ (x : ℕ) (y : ℚ) (z : ℤ), 0 < x → 0 < y → (N : ℚ) = ((x : ℚ) + y) * (2 * (x : ℚ) + y) →
      (N : ℤ) = 3 * z ^ 2 - (x : ℤ) ^ 2 → (x : ℝ) = ν * (b - a) → (y : ℝ) = 3 * (ν * a) → False)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b))
    (δ : ℤ) (hδ : (δ : ℝ) = ν * (a - b))
    (z : ℤ) (hz : (z : ℝ) = ν * c) : False := by
  by_cases hδ0 : δ = 0
  · exact H1 z (by
      have hNeq : (N : ℤ) = 3 * z ^ 2 - δ ^ 2 := f2_N_eq hc2 hNreal hδ hz
      simp [hδ0] at hNeq; exact hNeq)
  · obtain ⟨w_q, hw⟩ := f2_w_rational D hm ht ha hb hν hc2 hδ hδ0 hz
    have hNeq : (N : ℤ) = 3 * z ^ 2 - δ ^ 2 := f2_N_eq hc2 hNreal hδ hz
    rcases lt_trichotomy δ 0 with hn | h0 | hp
    · exact f2_wQ_neg Hneg ha hb hν hNreal hδ hn w_q hw hNeq
    · exact absurd h0 hδ0
    · exact f2_wQ_pos Hpos ha hb hν hNreal hδ hp w_q hw hNeq

/-! ## Main theorem: 4 sign-cases for lemmaW -/

/-- No prime `N > 3` admits a 2π/3-model `CongruentDissection` with an F2Data target. -/
theorem f2_elim {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F2Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (H1 : ∀ z : ℤ, (N : ℤ) ≠ 3 * z ^ 2)
    (Hpos : ∀ (x : ℕ) (y : ℚ) (z : ℤ), 0 < x → 0 < y → (N : ℚ) = ((x : ℚ) + y) * (2 * (x : ℚ) + y) →
      (N : ℤ) = 3 * z ^ 2 - (x : ℤ) ^ 2 → (x : ℝ) = ν * (a - b) → (y : ℝ) = 3 * (ν * b) → False)
    (Hneg : ∀ (x : ℕ) (y : ℚ) (z : ℤ), 0 < x → 0 < y → (N : ℚ) = ((x : ℚ) + y) * (2 * (x : ℚ) + y) →
      (N : ℤ) = 3 * z ^ 2 - (x : ℤ) ^ 2 → (x : ℝ) = ν * (b - a) → (y : ℝ) = 3 * (ν * a) → False) : False := by
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  have hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b) :=
    F2_area_formula D hm ht ha hb hν
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  have hW_α := Row8.lemmaW_F2_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F2_beta D.target hα ht
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hc0
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hc0
  -- Abbreviate the common flux scalar
  set V : ℝ := ν * (c ^ 2 - a * (a + 2 * b) - b * (2 * a + b))
  have hV : V = -(3 * ν * a * b) := flux_eq_neg3ab hc2
  have hfact_α : ν * (a - b - c) * (c + a - b) = V := by rw [hV]; exact F2_factor_alpha hc2
  have hfact_β : -(ν * (a - b + c)) * (c + b - a) = V := by rw [hV]; exact F2_factor_beta hc2
  -- Mα+Mβ and Mα-Mβ are even
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mα - Mβ := by omega
  obtain ⟨d, hd⟩ := hdiff_even  -- Mα - Mβ = 2d
  obtain ⟨s, hs⟩ := hsum_even   -- Mα + Mβ = 2s
  -- Dispatch on the 4 sign combinations from lemmaW
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++) Mα = ν(a-b-c), Mβ = -(ν(a-b+c))
    -- flux_α = V, flux_β = V
    have hMα_eq : (Mα : ℝ) * (c + a - b) = ν * (a - b - c) * (c + a - b) := by
      have hV : (Mα : ℝ) * (c + a - b) = V := hflux_α.symm.trans hα_pos
      linarith [hfact_α]
    have hMβ_eq : (Mβ : ℝ) * (c + b - a) = -(ν * (a - b + c)) * (c + b - a) := by
      have hV : (Mβ : ℝ) * (c + b - a) = V := hflux_β.symm.trans hβ_pos
      linarith [hfact_β]
    have hMα_val : (Mα : ℝ) = ν * (a - b - c) := mul_right_cancel₀ hdiv_α.ne' hMα_eq
    have hMβ_val : (Mβ : ℝ) = -(ν * (a - b + c)) := mul_right_cancel₀ hdiv_β.ne' hMβ_eq
    -- Mα - Mβ = 2ν(a-b), Mα + Mβ = -2νc
    have h2d : (d : ℝ) = ν * (a - b) := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; linarith
    have h2s : (-s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    exact f2_core D hm ht H1 Hpos Hneg ha hb hν hc2 hNreal d h2d (-s) (by push_cast; linarith [h2s])
  · -- (+-) Mα = ν(a-b-c), Mβ = ν(a-b+c)
    -- flux_α = V, flux_β = -V
    have hMα_eq : (Mα : ℝ) * (c + a - b) = ν * (a - b - c) * (c + a - b) := by
      have hV : (Mα : ℝ) * (c + a - b) = V := hflux_α.symm.trans hα_pos
      linarith [hfact_α]
    have hMβ_neg_eq : (Mβ : ℝ) * (c + b - a) = ν * (a - b + c) * (c + b - a) := by
      have hMβV : (Mβ : ℝ) * (c + b - a) = -V := hflux_β.symm.trans hβ_neg
      have hfact : ν * (a - b + c) * (c + b - a) = -V := by linarith [hfact_β]
      linarith [hMβV, hfact]
    have hMα_val : (Mα : ℝ) = ν * (a - b - c) := mul_right_cancel₀ hdiv_α.ne' hMα_eq
    have hMβ_val : (Mβ : ℝ) = ν * (a - b + c) := mul_right_cancel₀ hdiv_β.ne' hMβ_neg_eq
    -- Mα - Mβ = -2νc, Mα + Mβ = 2ν(a-b)
    have h2d : (-d : ℝ) = ν * c := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    have h2s : (s : ℝ) = ν * (a - b) := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; linarith
    exact f2_core D hm ht H1 Hpos Hneg ha hb hν hc2 hNreal s h2s (-d) (by push_cast; linarith [h2d])
  · -- (-+) Mα = -(ν(a-b-c)), Mβ = -(ν(a-b+c))
    -- flux_α = -V, flux_β = V
    have hMα_neg_eq : (Mα : ℝ) * (c + a - b) = -(ν * (a - b - c)) * (c + a - b) := by
      have hMαV : (Mα : ℝ) * (c + a - b) = -V := hflux_α.symm.trans hα_neg
      have hfact : -(ν * (a - b - c)) * (c + a - b) = -V := by linarith [hfact_α]
      linarith [hMαV, hfact]
    have hMβ_eq : (Mβ : ℝ) * (c + b - a) = -(ν * (a - b + c)) * (c + b - a) := by
      have hV : (Mβ : ℝ) * (c + b - a) = V := hflux_β.symm.trans hβ_pos
      linarith [hfact_β]
    have hMα_val : (Mα : ℝ) = -(ν * (a - b - c)) := mul_right_cancel₀ hdiv_α.ne' hMα_neg_eq
    have hMβ_val : (Mβ : ℝ) = -(ν * (a - b + c)) := mul_right_cancel₀ hdiv_β.ne' hMβ_eq
    -- Mα - Mβ = 2νc, Mα + Mβ = -2ν(a-b)
    have h2d : (d : ℝ) = ν * c := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; linarith
    have h2s : (-s : ℝ) = ν * (a - b) := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    exact f2_core D hm ht H1 Hpos Hneg ha hb hν hc2 hNreal (-s) (by push_cast; linarith [h2s]) d h2d
  · -- (--) Mα = -(ν(a-b-c)), Mβ = ν(a-b+c)
    -- flux_α = -V, flux_β = -V
    have hMα_neg_eq : (Mα : ℝ) * (c + a - b) = -(ν * (a - b - c)) * (c + a - b) := by
      have hMαV : (Mα : ℝ) * (c + a - b) = -V := hflux_α.symm.trans hα_neg
      have hfact : -(ν * (a - b - c)) * (c + a - b) = -V := by linarith [hfact_α]
      linarith [hMαV, hfact]
    have hMβ_neg_eq : (Mβ : ℝ) * (c + b - a) = ν * (a - b + c) * (c + b - a) := by
      have hMβV : (Mβ : ℝ) * (c + b - a) = -V := hflux_β.symm.trans hβ_neg
      have hfact : ν * (a - b + c) * (c + b - a) = -V := by linarith [hfact_β]
      linarith [hMβV, hfact]
    have hMα_val : (Mα : ℝ) = -(ν * (a - b - c)) := mul_right_cancel₀ hdiv_α.ne' hMα_neg_eq
    have hMβ_val : (Mβ : ℝ) = ν * (a - b + c) := mul_right_cancel₀ hdiv_β.ne' hMβ_neg_eq
    -- Mα - Mβ = -2ν(a-b), Mα + Mβ = 2νc
    have h2d : (-d : ℝ) = ν * (a - b) := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    have h2s : (s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; linarith
    exact f2_core D hm ht H1 Hpos Hneg ha hb hν hc2 hNreal (-d) (by push_cast; linarith [h2d]) s h2s


end Erdos634.Draft.OpenRed.F2x

namespace Erdos634.Draft.OpenRed

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2 Erdos634.Draft.R8ZF Erdos634.Draft.E60Irr
open Erdos634.Draft.IsoInst Erdos634.Draft.ChainIso Erdos634.Draft.AllN3 Erdos634.Draft.R8F2to4Bridge
open Erdos634.Draft.R8Gen2 (rat_pos_int NoF4z)

/-- **The `F₂` instance of `143`**: no triangle with sides `39, 55, 49` is cut into congruent copies (any number)
of a triangle with sides `3, 5, 7`. -/
def F2Inst143 : Prop :=
  ∀ {N' : ℕ} (D' : CongruentDissection N'),
    (∃ τ : Equiv.Perm (Fin 3), D'.target.oppLen (τ 0) = 39 ∧ D'.target.oppLen (τ 1) = 55 ∧
      D'.target.oppLen (τ 2) = 49) →
    (∃ σ : Equiv.Perm (Fin 3), D'.model.oppLen (σ 0) = 3 ∧ D'.model.oppLen (σ 1) = 5 ∧
      D'.model.oppLen (σ 2) = 7) → False

open Erdos634.Realizable in
/-- scale the dissection by `ν` and apply the instance -/
theorem f2_scaled_apply {N : ℕ} (D : CongruentDissection N) {ν : ℝ} (hν : 0 < ν) (h : F2Inst143)
    (τ σ : Equiv.Perm (Fin 3))
    (ht0 : ν * D.target.oppLen (τ 0) = 39) (ht1 : ν * D.target.oppLen (τ 1) = 55)
    (ht2 : ν * D.target.oppLen (τ 2) = 49)
    (hm0 : ν * D.model.oppLen (σ 0) = 3) (hm1 : ν * D.model.oppLen (σ 1) = 5)
    (hm2 : ν * D.model.oppLen (σ 2) = 7) : False := by
  set Ds := scaleDissection (D.model.pts 0) ν hν.ne' D with hDs
  have htd : ∀ i j : Fin 3, dist (Ds.target.pts i) (Ds.target.pts j) = ν * dist (D.target.pts i) (D.target.pts j) := by
    intro i j
    rw [hDs, scaleDissection_target_pts, scaleDissection_target_pts, homothetyEquiv_dist, abs_of_pos hν]
  have hmd : ∀ i j : Fin 3, dist (Ds.model.pts i) (Ds.model.pts j) = ν * dist (D.model.pts i) (D.model.pts j) := by
    intro i j
    rw [hDs, scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist, abs_of_pos hν]
  have hto : ∀ j : Fin 3, Ds.target.oppLen j = ν * D.target.oppLen j := fun j => by
    unfold Tri.oppLen; exact htd _ _
  have hmo : ∀ j : Fin 3, Ds.model.oppLen j = ν * D.model.oppLen j := fun j => by
    unfold Tri.oppLen; exact hmd _ _
  exact h Ds ⟨τ, by rw [hto]; exact ht0, by rw [hto]; exact ht1, by rw [hto]; exact ht2⟩
    ⟨σ, by rw [hmo]; exact hm0, by rw [hmo]; exact hm1, by rw [hmo]; exact hm2⟩

/-- the factorization `143 = (x + r)(2x + r)` -/
theorem fact_143 {x r : ℕ} (hx : 0 < x) (hr : 0 < r) (h : 143 = (x + r) * (2 * x + r)) : x = 2 ∧ r = 9 := by
  have h11 : x + r ≤ 11 := by nlinarith
  have hx10 : x ≤ 10 := by omega
  have hr10 : r ≤ 10 := by omega
  interval_cases x <;> interval_cases r <;> omega

/-- the swap of the first two indices under a permutation -/
theorem swap_vals (σ : Equiv.Perm (Fin 3)) :
    ((Equiv.swap (0 : Fin 3) 1).trans σ) 0 = σ 1 ∧ ((Equiv.swap (0 : Fin 3) 1).trans σ) 1 = σ 0 ∧
      ((Equiv.swap (0 : Fin 3) 1).trans σ) 2 = σ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · show σ (Equiv.swap (0 : Fin 3) 1 0) = σ 1
    rw [Equiv.swap_apply_left]
  · show σ (Equiv.swap (0 : Fin 3) 1 1) = σ 0
    rw [Equiv.swap_apply_right]
  · show σ (Equiv.swap (0 : Fin 3) 1 2) = σ 2
    rw [show Equiv.swap (0 : Fin 3) 1 2 = 2 by decide]

/-- **The scalene leaf of `143` from its one instance.** -/
theorem gapR8_143_of (h : F2Inst143) : GapR8 143 := by
  have h3 : NoF3z 143 := noF3z_of_chk (noF3zChk_of_sq (by decide +kernel))
  have h4 : NoF4z 143 := noF4z_of_chk (noF4zChk_of_sq (by decide +kernel))
  intro D α a b c hirr hm hshape
  obtain ⟨_, _, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  rcases hshape with hF2 | hF3 | hF3' | hF4s | hF4'
  · obtain ⟨ν, hνpos, hd⟩ := f2_data_of_shape D hm hF2
    have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := F2x.c_sq D.model hm
    have hm' := hm
    obtain ⟨σm, -, oa, -, ob, -, oc⟩ := hm'
    have hd' := hd
    obtain ⟨-, σt, -, t0, -, t1, -, t2⟩ := hd'
    have hcpos : 0 < c := by rw [← oc]; exact D.model.oppLen_pos _
    have hνc : 0 < ν * c := mul_pos hνpos hcpos
    refine F2x.f2_elim D hirr hm hd ha0 hb0 hνpos ?_ ?_ ?_
    · intro z hz
      push_cast at hz
      omega
    · -- `a > b`: `(ν a, ν b, ν c) = (5, 3, 7)`
      intro x y z hx hy hNq hNz hxR hyR
      obtain ⟨r, hr, rfl, hNn⟩ := rat_pos_int 143 x y hy hNq
      obtain ⟨rfl, rfl⟩ := fact_143 hx hr hNn
      have hB : ν * b = 3 := by push_cast at hyR; linarith
      have hA : ν * a = 5 := by push_cast at hxR; linarith
      have hC : ν * c = 7 := by
        have h49 : (ν * c) ^ 2 = 49 := by
          have : (ν * c) ^ 2 = (ν * a) ^ 2 + (ν * a) * (ν * b) + (ν * b) ^ 2 := by linear_combination ν ^ 2 * hc2
          rw [this, hA, hB]; norm_num
        have h7 : (ν * c - 7) * (ν * c + 7) = 0 := by linear_combination h49
        rcases mul_eq_zero.mp h7 with h' | h'
        · linarith
        · linarith
      obtain ⟨s0, s1, s2⟩ := swap_vals σt
      obtain ⟨m0, m1, m2⟩ := swap_vals σm
      refine f2_scaled_apply D hνpos h ((Equiv.swap (0 : Fin 3) 1).trans σt) ((Equiv.swap (0 : Fin 3) 1).trans σm)
        ?_ ?_ ?_ ?_ ?_ ?_
      · rw [s0, t1]; linear_combination (2 * (ν * a) + ν * b + 3) * hB + (6 : ℝ) * hA
      · rw [s1, t0]; linear_combination (ν * a + 2 * (ν * b) + 5) * hA + (10 : ℝ) * hB
      · rw [s2, t2]; linear_combination (ν * c + 7) * hC
      · rw [m0, ob]; exact hB
      · rw [m1, oa]; exact hA
      · rw [m2, oc]; exact hC
    · -- `a < b`: `(ν a, ν b, ν c) = (3, 5, 7)`
      intro x y z hx hy hNq hNz hxR hyR
      obtain ⟨r, hr, rfl, hNn⟩ := rat_pos_int 143 x y hy hNq
      obtain ⟨rfl, rfl⟩ := fact_143 hx hr hNn
      have hA : ν * a = 3 := by push_cast at hyR; linarith
      have hB : ν * b = 5 := by push_cast at hxR; linarith
      have hC : ν * c = 7 := by
        have h49 : (ν * c) ^ 2 = 49 := by
          have : (ν * c) ^ 2 = (ν * a) ^ 2 + (ν * a) * (ν * b) + (ν * b) ^ 2 := by linear_combination ν ^ 2 * hc2
          rw [this, hA, hB]; norm_num
        have h7 : (ν * c - 7) * (ν * c + 7) = 0 := by linear_combination h49
        rcases mul_eq_zero.mp h7 with h' | h'
        · linarith
        · linarith
      refine f2_scaled_apply D hνpos h σt σm ?_ ?_ ?_ ?_ ?_ ?_
      · rw [t0]; linear_combination (ν * a + 2 * (ν * b) + 3) * hA + (6 : ℝ) * hB
      · rw [t1]; linear_combination (2 * (ν * a) + ν * b + 5) * hB + (10 : ℝ) * hA
      · rw [t2]; linear_combination (ν * c + 7) * hC
      · rw [oa]; exact hA
      · rw [ob]; exact hB
      · rw [oc]; exact hC
  · obtain ⟨ν, hνpos, hd⟩ := f3_data_of_shape D hm hF3
    exact F3.f3_prime_contradiction D hirr hm hd ha0 hb0 hνpos h3
  · obtain ⟨ν, hνpos, hd⟩ := f3prime_data_of_shape D hm hF3'
    exact F3Prime.f3prime_contradiction D hirr hm hd ha0 hb0 hνpos h3
  · obtain ⟨ν, hνpos, hd⟩ := f4_data_of_shape D hm hF4s
    exact Erdos634.Draft.R8Gen2.F4.f4_prime_contradiction D hirr hm hd ha0 hb0 hνpos h4
  · obtain ⟨ν, hνpos, hd⟩ := f4prime_data_of_shape D hm hF4'
    exact Erdos634.Draft.R8Gen2.F4Prime.f4prime_prime_contradiction D hirr hm hd ha0 hb0 hνpos h4

/-- **`143` is not a tile count, given its one remaining instance**: the tile `(3, 5, 7)` on the triangle with
sides `39, 55, 49`. -/
theorem not_tile_143_of (h : F2Inst143) (D : CongruentDissection 143) : False :=
  not_tile_sqf_full 143 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (leafNSq_of_sq (by decide +kernel)) (leafHAr_of_sq (by decide +kernel)) (by decide +kernel)
    (leafS2_of_sq (by decide +kernel)) (s3Closed_of_chkD (by norm_num) (s3ChkD_of_sq (by decide +kernel)))
    (isoClosed_of_chk (by norm_num) (by decide +kernel))
    (gapE60_of_chk_sq (by norm_num) [] (by decide +kernel) (by intro p hp; cases hp))
    (gapE120_of_chk (by norm_num) (by decide +kernel))
    (gapF1_of_chksq (by norm_num) (by decide +kernel))
    (gapR8_143_of h) D

end Erdos634.Draft.OpenRed

#print axioms Erdos634.Draft.OpenRed.not_tile_143_of
