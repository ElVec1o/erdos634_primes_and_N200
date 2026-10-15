import Erdos634.ChordDecomp

/-!
# Area arithmetic kernel of the general straddling statement

`ChordDecomp.area_never_integral` is the arithmetic core:

For any member with gcd(e,f)=1, a junction at distance d from the apex has height fraction
m/f² with 1 ≤ m < f², and the area above its chord is N·m²/f⁴ tile areas.  Since gcd(N,f)=1
(propagated from gcd(e,f)=1), the quantity f⁴ ∣ N·m² would force f⁴ ∣ m², hence f² ∣ m,
contradicting m < f².

So the area above the chord is not an integral number of tiles, and some tile meets both open sides of the chord.  Only the area
arithmetic is proved here; the geometric clause is not stated in Lean.
The tight-subfamily coprimality is `ChordDecomp.coprime_tight`.

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.StraddleGenWrap

/-- The area arithmetic kernel of prop:straddlegen:
    for any coprime pair (N,f) with 0 < f, and any m with 1 ≤ m < f²,
    the fraction N·m²/f⁴ is not an integer, i.e. f⁴ does not divide N·m². -/
theorem straddle_area_not_integral {N f m : ℕ} (hf : 0 < f) (hcop : Nat.Coprime N f)
    (h1 : 1 ≤ m) (h2 : m < f ^ 2) : ¬ (f ^ 4 ∣ N * m ^ 2) :=
  Erdos634.ChordDecomp.area_never_integral hf hcop h1 h2

/-- On the tight subfamily (N = 3f² − e², e = 1, f = 2e+1) the coprimality is automatic.
    Abstractly: gcd(e, 2e+1) = 1 for every e. -/
theorem tight_coprime (e : ℕ) : Nat.Coprime e (2 * e + 1) :=
  Erdos634.ChordDecomp.coprime_tight e

/-- Non-vacuity witness: f = 3, N = 26 (the (1,3) tight member), m = 2.
    3 > 0, gcd(26, 3) = 1 (since 26 = 2·3²-1 and 3∤26), 1 ≤ 2 < 9, and 81 ∤ 26·4 = 104. -/
theorem straddle_gen_witness :
    ∃ (N f m : ℕ), 0 < f ∧ Nat.Coprime N f ∧ 1 ≤ m ∧ m < f ^ 2 ∧ ¬ (f ^ 4 ∣ N * m ^ 2) :=
  ⟨26, 3, 2, by norm_num, by decide, by norm_num, by norm_num,
   straddle_area_not_integral (by norm_num) (by decide) (by norm_num) (by norm_num)⟩

#print axioms straddle_area_not_integral
#print axioms tight_coprime

end Erdos634.Draft.StraddleGenWrap
