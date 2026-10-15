import Mathlib
import Erdos634.Draft.RSBArea

/-!
# RSB, part 4: the reduction at the level of a REAL dissection.

Statement: tile `(α,β,2π/3)`, `α/π` irrational; `N` prime => `ABC`
isosceles and not equilateral.  The proof of the equilateral case cites Beeson (BeesonEq Thm 6), so the
Lean statement below is the conclusion MINUS that case:

  `N` prime  =>  `ABC` is equilateral, OR (`ABC` isosceles and not equilateral).

Everything else (`ABC` one of the eleven corner types, `N = k² N₀` with `k` an integer, the composite-ness
of `N` for `F₁..F₄`, `F₁'..F₄'`, tile-similar) is proved: `RSBArea.bridge` + `FDDShapes.prime_forces_iso_or_equi`.
-/

namespace Erdos634.Draft.RSBReduce

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.FDDShapes
  Erdos634.Draft.RSBSine Erdos634.Draft.RSBCorner Erdos634.Draft.RSBArea

variable {N : ℕ}

/-- The paper's normalization `gcd(a,b,c) = 1` (`eq:tile`) gives the `gcd(a,b) = 1` that the bridge uses. -/
theorem coprime_of_gcd3 (a b c : ℕ) (h3 : Nat.gcd (Nat.gcd a b) c = 1)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) : Nat.Coprime a b := by
  set g := Nat.gcd a b with hg
  obtain ⟨a', ha'⟩ : g ∣ a := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : g ∣ b := Nat.gcd_dvd_right a b
  have hg2 : g ^ 2 ∣ c ^ 2 := ⟨a' ^ 2 + a' * b' + b' ^ 2, by
    rw [hc]; conv_lhs => rw [ha', hb']
    ring⟩
  have hgc : g ∣ c := (Nat.pow_dvd_pow_iff (by norm_num)).mp hg2
  have : g ∣ Nat.gcd g c := Nat.dvd_gcd dvd_rfl hgc
  rw [h3] at this
  exact Nat.dvd_one.mp this

theorem reduction_tiling (D : CongruentDissection N) {α K : ℝ} (hK : 0 < K) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hα : IrrPi α) (hm : D.model.TwoPiThreeData α (K * a) (K * b) (K * c)) (hN : N.Prime) :
    (∀ i, D.target.angleAt i = Real.pi / 3) ∨
    ((∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j) ∧
      ¬ (∀ i, D.target.angleAt i = Real.pi / 3)) := by
  obtain ⟨s, σ, k, hk, hang, -, harea⟩ := bridge D hK a b c hcop hc hα hm
  have hshape := prime_forces_iso_or_equi s a b c k N ha hb hcop hc hk harea hN
  have hne01 : σ 0 ≠ σ 1 := fun h => absurd (σ.injective h) (by decide)
  rcases hshape with rfl | rfl | rfl
  · left
    intro i
    obtain ⟨j, rfl⟩ := σ.surjective i
    rw [hang j]
    have : ∀ j, (Shape.equilateral.triple j) = (0, 1) := by decide
    rw [this j]; push_cast; ring
  · right
    have h0 := hang 0
    have h1 := hang 1
    have e0 : Shape.isoAlpha.triple 0 = (1, 0) := by decide
    have e1 : Shape.isoAlpha.triple 1 = (1, 0) := by decide
    rw [e0] at h0; rw [e1] at h1
    refine ⟨⟨σ 0, σ 1, hne01, by rw [h0, h1]⟩, ?_⟩
    intro hall
    have := hall (σ 0)
    rw [h0] at this
    exact hα ⟨1 / 3, by push_cast at this ⊢; linarith⟩
  · right
    have h0 := hang 0
    have h1 := hang 1
    have e0 : Shape.isoBeta.triple 0 = (-1, 1) := by decide
    have e1 : Shape.isoBeta.triple 1 = (-1, 1) := by decide
    rw [e0] at h0; rw [e1] at h1
    refine ⟨⟨σ 0, σ 1, hne01, by rw [h0, h1]⟩, ?_⟩
    intro hall
    have := hall (σ 0)
    rw [h0] at this
    exact hα ⟨0, by push_cast at this ⊢; linarith⟩

#print axioms Erdos634.Draft.RSBReduce.reduction_tiling
#print axioms Erdos634.Draft.RSBReduce.coprime_of_gcd3

end Erdos634.Draft.RSBReduce
