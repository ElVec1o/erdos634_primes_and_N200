import Erdos634.OffsetForcing

/-!
# Offsets: arithmetic kernel

`OffsetForcing.forcing` is the full two-parity arithmetic core of the offsets lemma:

* Over j = p + q levels, with p the (+1)-count and q the (−1)-count, the accumulated offset
  satisfies Σεᵢ − j = −2q.
* **Odd f**: integrality gives `f ∣ 2q`; since gcd(f,2) = 1, `f ∣ q`; q ≤ j < f forces q = 0.
* **Even f**: integrality gives `2f ∣ 2q`, hence `f ∣ q`; same conclusion.

The geometric statement that the terminal-column base apex satisfies the integrality
hypothesis is not part of this file.  The arithmetic half subsumes the older even-only
`W2Core.sum_forcing_*` results.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.OffsetForcingWrap

/-- Bundle the two-parity forcing as a statement mirroring the paper's lemma.
    p = count of (+1)-oriented levels; q = count of (−1)-oriented levels; f = the scale parameter.
    Hypotheses: the j = p+q total stays below f, AND the parity-dependent divisibility condition
    (odd-f: f∣2q; even-f: 2f∣2q).  Conclusion: q = 0, i.e. every level is (+1)-oriented. -/
theorem offset_forcing_both_parities {f p q : ℕ}
    (hlt  : p + q < f)
    (hdvd : (¬ 2 ∣ f ∧ f ∣ 2 * q) ∨ (2 * f ∣ 2 * q)) :
    q = 0 :=
  Erdos634.OffsetForcing.forcing hlt hdvd

/-- Non-vacuity witness: f = 5 (odd), p = 3, q = 0 satisfies all hypotheses with q = 0. -/
theorem offset_forcing_witness : ∃ (f p q : ℕ),
    p + q < f ∧ ((¬ 2 ∣ f ∧ f ∣ 2 * q) ∨ (2 * f ∣ 2 * q)) ∧ q = 0 :=
  ⟨5, 3, 0, by norm_num, Or.inl ⟨by norm_num, by norm_num⟩, rfl⟩

#print axioms offset_forcing_both_parities
#print axioms offset_forcing_witness

end Erdos634.Draft.OffsetForcingWrap
