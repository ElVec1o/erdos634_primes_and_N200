-- Draft/ADMLattice.lean — `thm:lattice` gap (ii): from a real CongruentDissection to the lattice form.
-- Combines `ADMCore.admissible_alpha` (tiling-level conditions) with
-- `FDDSpectrum.lattice_paper` (arithmetic set equality) to close gap (ii) of thm:lattice.
-- Only-if direction: if D is a base-α CongruentDissection, then N = d*(E*u)²*(a+2b).
-- The if direction (existence of tiling for each N = d*(E*u)²*(a+2b)) is the
-- spectral-construction half of thm:lattice and remains unformalized.

import Erdos634.Draft.ADMCore
import Erdos634.Draft.FDDSpectrumArith

namespace Erdos634.Draft.ADMLattice

open Erdos634.Geometry Erdos634.Draft Set

/-- **`thm:lattice`, only-if direction from a real tiling.**
Given a `CongruentDissection N` of a base-α isosceles target by a `3α+2β=π` tile `(a,b,c)`,
the count `N` lies in the image of the lattice map `u ↦ d*(E*u)²*(a+2b)`,
where `b = d*e²` (squarefree `d`), `g = gcd(e,a+b−c)`, `e₁ = e/g`, and
`E = e₁` or `2*e₁` according to the parity condition.

Closes gap (ii) of `thm:lattice`: previously `FDDSpectrum.lattice_paper` proved the arithmetic
set equality (over natural-number conditions only), but did not quantify over real dissections.
`ADMCore.admissible_alpha` produces exactly those conditions from a real dissection. -/
theorem lattice_onlyif {N : ℕ} (D : CongruentDissection N)
    (a b c d e : ℕ) (s α μ : ℝ)
    (ha : 0 < a) (hb0 : 0 < b)
    (hcop : Nat.Coprime a b)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hbde : b = d * e ^ 2) (hd : Squarefree d)
    (hm : D.model.TwoPiThreeData α (s * a) (s * b) (s * c))
    (hbase : D.target.BaseAlphaData α (s * a) (s * b) (s * c) μ) :
    ∃ u : ℕ, 0 < u ∧ N = d * ((if (2 : ℤ) ∣
          ((c : ℤ) - ↑a - ↑b) / ((Int.gcd (↑e : ℤ) ((c : ℤ) - ↑a - ↑b) : ℕ) : ℤ)
          + ↑d * ((↑e / ↑(Int.gcd (↑e : ℤ) ((c : ℤ) - ↑a - ↑b)) : ℤ) ^ 2) * (↑a + 2 * ↑b)
        then e / (Int.gcd (↑e : ℤ) ((c : ℤ) - ↑a - ↑b) : ℕ)
        else 2 * (e / (Int.gcd (↑e : ℤ) ((c : ℤ) - ↑a - ↑b) : ℕ))) * u) ^ 2 * (a + 2 * b) := by
  -- Derive positivity of e from b > 0 and the factorization b = d*e²
  have he0 : e ≠ 0 := by
    intro h; subst h; simp at hbde; omega
  have he : 0 < e := Nat.pos_of_ne_zero he0
  -- Apply admissible_alpha to extract arithmetic conditions from the real dissection
  obtain ⟨_k, w, _hμk, hw, _harea, _hkw, hN, hdvd, hpar⟩ :=
    ADMCore.admissible_alpha D a b c d e s α μ hcop hc hbde hd hm hbase
  -- N is in the LHS of lattice_paper
  have hLHS : N ∈ {M : ℕ | ∃ w : ℕ, 0 < w ∧ M = d * w ^ 2 * (a + 2 * b) ∧
        (e : ℤ) ∣ ↑w * ((c : ℤ) - ↑a - ↑b) ∧
        (2 : ℤ) ∣ (↑w * ((c : ℤ) - ↑a - ↑b)) / ↑e - ↑M} :=
    mem_setOf.mpr ⟨w, hw, hN, hdvd, hpar⟩
  -- Apply lattice_paper to transform to the lattice (E*u) form
  have hset := FDDSpectrum.lattice_paper a b c d e ha hb0 hcop hc hbde he
  exact mem_setOf.mp ((Set.ext_iff.mp hset N).mp hLHS)

end Erdos634.Draft.ADMLattice

#print axioms Erdos634.Draft.ADMLattice.lattice_onlyif
