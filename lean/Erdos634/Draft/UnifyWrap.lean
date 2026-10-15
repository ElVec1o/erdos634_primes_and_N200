import Erdos634.CChord
import Erdos634.MidTriangleGeneral
import Erdos634.OrderForcing

/-!
# Member-independent arithmetic identities for the chain machinery

The chain machinery is member-independent.  The identity halves of four clauses are in Lean.

Clause (i): the straight/full vertex classification is unchanged:
* `CChord.fill_beta`: the fill of β is {β}.
* `CChord.fill_alpha`: the fill of α is {α}.
* `CChord.fill_alpha_beta`: the fill of α+β is {α,β}.

Clause (ii): every reflected partner dies at a straight junction:
* `MidTriangleGeneral.two_gamma_gt_pi`: 2γ > π (angle arithmetic).

Clause (iii): b·sinγ = c·sinβ (member-independent sine rule), wrapped separately in TriLawSin.

Clause (iv): the partition of j·b is uniquely (0,j,0):
* `OrderForcing.partition_jb_gen`: for any base-β (e,f).

The geometric consequents (reflected partner's placement, a-up spanning, straight
classification for a real tiling, and the actual partition application) require the
placement layer and are not covered here.

In All.lean, 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.UnifyWrap

-- ─── Clause (i): fill identities ─────────────────────────────────────────

/-- The fill of β is a single β-corner. -/
theorem unify_fill_beta (x y z : ℕ) (h1 : x + 2 * z = 0) (h2 : y + z = 1) :
    x = 0 ∧ y = 1 ∧ z = 0 :=
  Erdos634.CChord.fill_beta x y z h1 h2

/-- The fill of α is a single α-corner. -/
theorem unify_fill_alpha (x y z : ℕ) (h1 : x + 2 * z = 1) (h2 : y + z = 0) :
    x = 1 ∧ y = 0 ∧ z = 0 :=
  Erdos634.CChord.fill_alpha x y z h1 h2

/-- The fill of α+β is {α,β}. -/
theorem unify_fill_alpha_beta (x y z : ℕ) (h1 : x + 2 * z = 1) (h2 : y + z = 1) :
    x = 1 ∧ y = 1 ∧ z = 0 :=
  Erdos634.CChord.fill_alpha_beta x y z h1 h2

-- ─── Clause (ii): 2γ > π ──────────────────────────────────────────────────

/-- 2γ > π at any base-β member: the reflected partner always dies at a straight junction. -/
theorem unify_two_gamma_gt_pi (α β γ : ℝ) (hα : 0 < α) (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) :
    Real.pi < γ + γ :=
  Erdos634.MidTriangleGeneral.two_gamma_gt_pi α β γ hα hγ hrel

-- ─── Clause (iv): partition of j·b is unique ─────────────────────────────

/-- The walk partition is uniquely (0,j,0) for any base-β (e,f) and j < f. -/
theorem unify_partition_jb_gen {e f j x y z B : ℕ}
    (he : 1 ≤ e) (hef : e < f) (hjf : j < f)
    (hco : Nat.Coprime f (e * e)) (hB : f * f = B + e * e)
    (h : x * (e * f) + y * B + z * (f * f) = j * B) :
    x = 0 ∧ y = j ∧ z = 0 :=
  Erdos634.OrderForcing.partition_jb_gen he hef hjf hco hB h

-- Non-vacuity for unify_two_gamma_gt_pi: α=π/7, β=2π/7, γ=4π/7, γ+γ=8π/7>π. ✓
-- Non-vacuity for unify_partition_jb_gen: e=1,f=3,j=1,x=0,y=1,z=0,B=8: 0+1·8+0=8=1·8. ✓

#print axioms unify_fill_beta
#print axioms unify_two_gamma_gt_pi
#print axioms unify_partition_jb_gen

end Erdos634.Draft.UnifyWrap
