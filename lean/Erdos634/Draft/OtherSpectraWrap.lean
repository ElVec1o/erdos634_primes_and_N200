import Erdos634.AdmissibleSpectrum

/-!
# Squarefree kernel clause of the spectrum statement

Several spectral forcing results.
The equilateral squarefree-kernel clause ("N and ab have the same squarefree
kernel") is stated in Lean as the general fact it is:

* `AdmissibleSpectrum.same_valuation_parity`: if x·y = z², then for every
  prime p, v_p(x) and v_p(y) have the same parity — i.e. x and y have the
  same squarefree kernel.
* Non-vacuity witness: x=8, y=2, z=4 (8·2=16=4²), v_2(8)=3, v_2(2)=1.

The F₁–F₄ and tile-similar clauses and the equilateral divisibilities (c+a−b)∣3S, which quantify
over a real dissection's boundary flux, are not part of this file.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.OtherSpectraWrap

/-- If x·y = z², then for every prime p, v_p(x) ≡ v_p(y) (mod 2). -/
theorem same_squarefree_kernel {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (heq : x * y = z ^ 2) (p : ℕ) :
    x.factorization p % 2 = y.factorization p % 2 :=
  Erdos634.AdmissibleSpectrum.same_valuation_parity hx hy heq p

/-- Non-vacuity: x=8, y=2, z=4 gives a real witness with the same v_2 parity. -/
theorem squarefree_kernel_witness :
    (8 : ℕ).factorization 2 % 2 = (2 : ℕ).factorization 2 % 2 :=
  Erdos634.AdmissibleSpectrum.same_valuation_parity_witness

#print axioms same_squarefree_kernel
#print axioms squarefree_kernel_witness

end Erdos634.Draft.OtherSpectraWrap
