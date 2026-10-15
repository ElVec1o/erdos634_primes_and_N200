/-
Draft/F1PairCert.lean -- the `F₁` leaf pair by pair, with certificates for the rational pairs.

`F1MaGt1 N` (what `GapF1 N` needs beyond the pin `Ma = 1`, `CompositeF1Gen.gapF1_of_MaGt1`) quantifies over the pairs
`(Ma, Mb)`, `1 < Ma`, `Ma Mb = N`, of the invariants `Ma b = μ (c − a)`, `Mb b = μ (c + a)`.  `F1Pair N Ma Mb` is the
statement for one pair.
* `f1Pair_of_arith`: the pair is dead when `(Ma + Mb)² + 12 N` is not a square (`F1KappaSide.f1_pair_false`).
* `f1Pair_of_cert`: a pair with a square discriminant pins the tile up to scale, `(a, b, c) = l (x, y, z)` with
  `z (Mb − Ma) = x (Mb + Ma)`, `z² = x² + x y + y²`, and the target, `μ = m` with `Ma y = m (z − x)`, sides
  `l m (x, z, x + y)`; a refutation of that instance (a kernel-checked search certificate) kills the pair.

Composite-N statement; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.F1KappaSide3
import Erdos634.Draft.GPairCert

open scoped Classical

namespace Erdos634.Draft.F1PairCert

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeF1Gen Erdos634.Draft.F1KappaSide
open Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.GPairCert

private lemma c_sq4 (T : Erdos634.Geometry.Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

/-- **The `F₁` pair `(Ma, Mb)` has no dissection into `N` tiles.** -/
def F1Pair (N Ma Mb : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (α a b c μ : ℝ), IrrPi α → D.model.TwoPiThreeData α a b c →
    D.target.F1Data α a b c μ → 0 < μ → (Ma : ℝ) * b = μ * (c - a) → (Mb : ℝ) * b = μ * (c + a) → False

/-- **`F1MaGt1 N` from the pairs.** -/
theorem f1MaGt1_of_pairs (N : ℕ) (h : ∀ Ma Mb : ℕ, 1 < Ma → Ma < Mb → Ma * Mb = N → F1Pair N Ma Mb) :
    F1MaGt1 N := by
  intro D α a b c μ hirr hm hF1 hμ Ma Mb h1 hp e1 e2
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hlt : Ma < Mb := by
    have : (Ma : ℝ) * b < (Mb : ℝ) * b := by rw [e1, e2]; nlinarith
    have := lt_of_mul_lt_mul_right this hb0.le
    exact_mod_cast this
  exact h Ma Mb h1 hlt hp D α a b c μ hirr hm hF1 hμ e1 e2

/-- a pair with a non-square discriminant -/
theorem f1Pair_of_arith (N Ma Mb κ : ℕ) (hMa : 0 < Ma) (hκ0 : 0 < κ) (hprod : Ma * Mb = N) (hκ : Mb = Ma + 2 * κ)
    (hns : ¬ IsSquare (((Ma : ℤ) + Mb) ^ 2 + 12 * (N : ℤ))) (hne : Ma ^ 2 + Mb ^ 2 ≠ 4 * Ma * Mb) : F1Pair N Ma Mb :=
  fun D _ _ _ _ _ hirr hm hF1 hμ e1 e2 => f1_pair_false D hirr hm hF1 hμ Ma Mb κ hMa hκ0 hprod hκ hns hne e1 e2

/-- **`F1Pair N Ma Mb` from a certificate** of the pinned instance: tile `(x, y, z)` (opposite the angles `α`,
`π/3 − α`, `2π/3`), target with sides `m (x, z, x + y)`. -/
theorem f1Pair_of_cert (N Ma Mb : ℕ) (hlt : Ma < Mb) (x y z m : ℝ) (hx : 0 < x) (hy : 0 < y) (hxz : x < z)
    (hz : z * ((Mb : ℝ) - Ma) = x * ((Mb : ℝ) + Ma)) (hyz : z ^ 2 = x ^ 2 + x * y + y ^ 2)
    (hm' : (Ma : ℝ) * y = m * (z - x))
    (TGT MODEL : Erdos634.Geometry.Tri)
    (cT : ∀ T : Erdos634.Geometry.Tri, HasSides T (m * x) (m * z) (m * (x + y)) → T.Congruent TGT)
    (cM : ∀ T : Erdos634.Geometry.Tri, HasSides T x y z → T.Congruent MODEL)
    (hno : ∀ D' : CongruentDissection N, D'.target.Congruent TGT → D'.model.Congruent MODEL → False) :
    F1Pair N Ma Mb := by
  intro D α a b c μ hirr hm hF1 hμ e1 e2
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq4 D.model hm
  have hMM : (0 : ℝ) < (Mb : ℝ) - Ma := by
    have : (Ma : ℝ) < Mb := by exact_mod_cast hlt
    linarith
  have hca : c * ((Mb : ℝ) - Ma) = a * ((Mb : ℝ) + Ma) := by
    have : μ * ((Mb : ℝ) * (c - a) - Ma * (c + a)) = 0 := by
      linear_combination (-(Mb : ℝ)) * e1 + (Ma : ℝ) * e2
    have h0 := (mul_eq_zero.mp this).resolve_left hμ.ne'
    linarith
  set l := a / x with hldef
  have hl : 0 < l := div_pos ha0 hx
  have hax : a = x * l := by rw [hldef]; field_simp
  have hcz : c = z * l := by
    have h1 : (c - z * l) * ((Mb : ℝ) - Ma) = 0 := by rw [hax] at hca; linear_combination hca - l * hz
    have := (mul_eq_zero.mp h1).resolve_right hMM.ne'
    linarith
  have hby : b = y * l := by
    have h1 : (b - y * l) * (b + y * l + x * l) = 0 := by
      rw [hax, hcz] at hc2; linear_combination l ^ 2 * hyz - hc2
    have h2 : b + y * l + x * l ≠ 0 := by
      have := mul_pos hy hl
      have := mul_pos hx hl
      linarith
    have := (mul_eq_zero.mp h1).resolve_right h2
    linarith
  have hμm : μ = m := by
    have h1 : (μ - m) * ((z - x) * l) = 0 := by
      rw [hax, hcz, hby] at e1; linear_combination l * hm' - e1
    have h2 : (z - x) * l ≠ 0 := (mul_pos (by linarith) hl).ne'
    have := (mul_eq_zero.mp h1).resolve_right h2
    linarith
  obtain ⟨-, τ, -, t0, -, t1, -, t2⟩ := hF1
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := hm
  exact refute_scaled D TGT MODEL (m * x) (m * z) (m * (x + y)) x y z l hl
    (hasSides_of_sigma τ (by rw [t0, hμm, hax]; ring) (by rw [t1, hμm, hcz]; ring)
      (by rw [t2, hμm, hax, hby]; ring))
    (hasSides_of_sigma σ (by rw [o0, hax]) (by rw [o1, hby]) (by rw [o2, hcz])) cT cM hno

end Erdos634.Draft.F1PairCert

#print axioms Erdos634.Draft.F1PairCert.f1MaGt1_of_pairs
#print axioms Erdos634.Draft.F1PairCert.f1Pair_of_cert
