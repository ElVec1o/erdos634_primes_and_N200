import Erdos634.AdmissibleSpectrum

/-!
# Squarefree-scale lemma: wrapper

Re-exports, under `as_` names, results of `AdmissibleSpectrum`:
- `sqfree_scale_dvd`: b ∣ k², b = d·e², d squarefree → d·e ∣ k
- `count_eq`: N·b = k²·(a+2b) → N = d·w²·(a+2b)
- `same_valuation_parity`: x·y = z² → v_p(x) and v_p(y) have same parity
- `chord_identity`: (c−a−b)(c+a−b) = b(2b+a−2c) for a 120°-triple

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.AdmissibleSpectrumWrap

open Erdos634.AdmissibleSpectrum

theorem as_sqfree_scale_dvd {b d e k : ℕ} (hb : b = d * e ^ 2) (hd : Squarefree d)
    (hk : k ≠ 0) (hdvd : b ∣ k ^ 2) : d * e ∣ k :=
  sqfree_scale_dvd hb hd hk hdvd

theorem as_count_eq (N a b d e w : ℕ) (hb : b = d * e ^ 2) (hbpos : 0 < b)
    (harea : N * b = (d * e * w) ^ 2 * (a + 2 * b)) :
    N = d * w ^ 2 * (a + 2 * b) :=
  count_eq N a b d e w hb hbpos harea

theorem as_same_valuation_parity {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (heq : x * y = z ^ 2) (p : ℕ) :
    x.factorization p % 2 = y.factorization p % 2 :=
  same_valuation_parity hx hy heq p

theorem as_chord_identity (a b c : ℤ) (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c - a - b) * (c + a - b) = b * (2 * b + a - 2 * c) :=
  chord_identity a b c h

-- Non-vacuity: same_valuation_parity witness
example : (8:ℕ).factorization 2 % 2 = (2:ℕ).factorization 2 % 2 :=
  as_same_valuation_parity (x := 8) (y := 2) (z := 4) (by norm_num) (by norm_num) (by norm_num) 2

#print axioms as_sqfree_scale_dvd
#print axioms as_same_valuation_parity

end Erdos634.Draft.AdmissibleSpectrumWrap
