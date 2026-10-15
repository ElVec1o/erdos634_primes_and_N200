/-
Draft/PI3FStatement.lean -- Theorem T, stage (a): the statements, as Lean Props.

**Theorem T.**  Equilateral target dissected by `N` copies of a `π/3`-tile (`α ∉ ℚπ`), invariant pair
`(m₁, m₂)` (`m₁ m₂ = 3N`, `m₁(a+b−c) = 3S`, `m₂(a+b+c) = 3S`), `D = (m₁+m₂)² − 16N` NOT a square, and
`ℓκ := (m₁² − m₂²)/gcd(m₁+m₂, m₁−m₂) > 2N`.  Then no such dissection exists.

Stated here in the exact shape of `CompositeE5Gen.E60Pair` (the conclusion is `E60Pair N m₁ m₂`, i.e. `False` from every
dissection with these invariants), with `ℓκ > 2N` written division-free as `2 N gcd(m₁+m₂, m₁−m₂) < m₁² − m₂²`.

The intermediate statements of the plan:

* `PI3F_Cert`            (stage b)  the finite certificate: for every tile type, the `{b, c}`-edge count of the weight `gV`
                                    (`[j = 0] − [j = 3]` on the direction class) sums to `0`; the boundary value is `1`.
                                    NOTE: a type-dependent weight `f(τ,u,w)` is not needed in this strength: the
                                    weight `τ ≠ a ? gV(w) : 0` already works (it is `coef_bc` of `E60VMod3`, which
                                    previously certified a LENGTH-weighted identity).
* `PI3F_Kernel`          (stage c0) the length-kernel floor for the length system `(a, b, c)`.
* `PI3F_ChainBalance`    (stage c)  L1: interior edge counts, per `(type, direction)`, are reversal-symmetric: the weighted
                                    sum of any type-dependent, direction-odd integer weight over the interior edges is `0`.
* `PI3F_TheoremT`        (stage d)  Theorem T.
No sorry, no native_decide.
-/
import Erdos634.Draft.CompositeE5Gen
import Erdos634.Draft.FluxCore
import Erdos634.Draft.E60VMod3

namespace Erdos634.Draft.PI3F

open Erdos634.Geometry Erdos634.Draft.CompositeE5Gen Erdos634.Draft.E60Mod9 Erdos634.Draft.E60V

/-- The type coefficient: `1` on the sides `b, c`, `0` on `a`. -/
def rhoBC (i : Fin 3) : ℤ := if i = 0 then 0 else 1

/-- **Stage (b): the finite certificate (count form).**  For every tile type `(t, o, x)` (216 of them: injective vertex-type
assignment, orientation, direction-class coset), the signed count of `{b, c}`-edges, weighted by `gV` on the edge's direction
class, vanishes; and the boundary value of an equilateral target is `1`. -/
def PI3F_Cert : Prop :=
  (∀ t : Fin 3 → Fin 3, Function.Injective t → ∀ (o : Bool) (x : GZ),
    ∑ k : Fin 3, rhoBC (t (k + 2)) * gV (pk o t x k) = 0) ∧
  gV (0, 0) + gV (2, 0) + gV (4, 0) = 1

/-- **Stage (c0): the length-kernel floor.**  For a `π/3` tile `(a,b,c)` with invariant pair `(m₁,m₂)`, non-square `D`
and `ℓκ > 2N`, every nonzero integer relation `n₀ a + n₁ b + n₂ c = 0` has one-sided length `> S`. -/
def PI3F_Kernel : Prop :=
  ∀ (N : ℕ) (a b c S : ℝ) (m₁ m₂ : ℤ), 0 < N → 0 < a → 0 < b → 0 < c →
    (m₁ : ℝ) * (a + b - c) = 3 * S → (m₂ : ℝ) * (a + b + c) = 3 * S → S ^ 2 = N * a * b →
    m₁ * m₂ = 3 * (N : ℤ) → 0 < S → ¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) →
    2 * (N : ℤ) * (Int.gcd (m₁ + m₂) (m₁ - m₂) : ℤ) < (m₁ + m₂) * (m₁ - m₂) →
    ∀ n₀ n₁ n₂ : ℤ, ¬ (n₀ = 0 ∧ n₁ = 0 ∧ n₂ = 0) → (n₀ : ℝ) * a + n₁ * b + n₂ * c = 0 →
      S < ((max n₀ 0 : ℤ) : ℝ) * a + ((max n₁ 0 : ℤ) : ℝ) * b + ((max n₂ 0 : ℤ) : ℝ) * c

/-- **Theorem T** (§80), for every `N`, every invariant pair. -/
def PI3F_TheoremT : Prop :=
  ∀ (N : ℕ) (m₁ m₂ : ℤ), 0 < N → m₁ * m₂ = 3 * (N : ℤ) →
    ¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) →
    2 * (N : ℤ) * (Int.gcd (m₁ + m₂) (m₁ - m₂) : ℤ) < (m₁ + m₂) * (m₁ - m₂) →
    E60Pair N m₁ m₂

/-- **Stage (c): the chain-balance lemma L1**, dissection level.  For a dissection whose tile edges carry a type `τ` with
`eLen = ℓ ∘ τ` (`ℓ ≥ 0`), whose target has diameter `≤ B`, and such that every nonzero integer relation among the `ℓᵢ`
has one-sided length `> B`: every direction-odd integer weight, with an arbitrary type coefficient, sums to zero over the
interior edges. -/
def PI3F_ChainBalance : Prop :=
  ∀ (N : ℕ) (D : Dissection N) (τ : Fin N × Fin 3 → Fin 3) (ℓ : Fin 3 → ℝ),
    (∀ e, D.eLen e = ℓ (τ e)) → (∀ i, 0 ≤ ℓ i) →
    ∀ B : ℝ, (∀ x ∈ D.target.carrier, ∀ y ∈ D.target.carrier, dist x y ≤ B) →
    (∀ n : Fin 3 → ℤ, (∃ i, n i ≠ 0) → ∑ i, (n i : ℝ) * ℓ i = 0 →
      B < ∑ i, ((max (n i) 0 : ℤ) : ℝ) * ℓ i) →
    ∀ (ρ : Fin 3 → ℤ) (ω : Dir → ℤ), (∀ d, ω (Dir.neg d) = - ω d) →
      ∑ e ∈ D.intEdges, ρ (τ e) * ω (D.eDir e) = 0

end Erdos634.Draft.PI3F
