import Mathlib.Tactic

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem C, module 3: the integer parametrisation `M = g d`, `M' = g (2u + d)` of the `γ = 2α` pairs  

Resolves the audit caveat (is `g` an integer?).  In the G leaf
(`GPairCert.GPair`, `Row4.P5`) a pair `(M, M')` with `M M' = N`, `M ≡ M' (mod 2)`, `3 M < M'` is all there is; the
parity hypothesis `M ≡ M' ≡ N (mod 2)` makes `M' ± M` even, hence `g := gcd(M' − M, M' + M) / 2` is a natural number and

  `M = g d`,  `M' = g (2u + d)`,  `u = (M' − M)/(2g)`,  `d = M/g`,  `gcd(u, u + d) = 1`,  `0 < d < u`,  `N = g² b`.

So `g` is an INTEGER for every pair that can occur, and no rational-`g` extension of Theorem C is needed in the G leaf.
(The `b`-non-squarefree worry of the audit concerns the tile, not the pair: the pair fixes `(u, v)` up to the
coprime reduction, and `g` is read off the pair.)
-/

namespace Erdos634.Draft.ThmC

theorem pair_param {M M' : ℕ} (hM : 0 < M) (hlt : 3 * M < M') (hpar : M % 2 = M' % 2) :
    ∃ g u d : ℕ, g = Nat.gcd (M' - M) (M' + M) / 2 ∧ u = (M' - M) / Nat.gcd (M' - M) (M' + M) ∧
      d = 2 * M / Nat.gcd (M' - M) (M' + M) ∧ 0 < g ∧ 0 < d ∧ d < u ∧ Nat.Coprime u (u + d) ∧
      M = g * d ∧ M' = g * (u + (u + d)) := by
  obtain ⟨P, hP⟩ : ∃ P, P = M' - M := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = M' + M := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = Nat.gcd P Q := ⟨_, rfl⟩
  rw [← hP, ← hQ, ← hG]
  have hPpos : 0 < P := by omega
  have hGpos : 0 < G := by rw [hG]; exact Nat.gcd_pos_of_pos_left _ hPpos
  have hGP : G ∣ P := by rw [hG]; exact Nat.gcd_dvd_left P Q
  have hGQ : G ∣ Q := by rw [hG]; exact Nat.gcd_dvd_right P Q
  have h2P : 2 ∣ P := by omega
  have h2Q : 2 ∣ Q := by omega
  have h2G : 2 ∣ G := by rw [hG]; exact Nat.dvd_gcd h2P h2Q
  obtain ⟨g, hg⟩ := h2G
  obtain ⟨u, hu⟩ := hGP
  obtain ⟨v, hv⟩ := hGQ
  have hcop : Nat.Coprime (P / G) (Q / G) := by
    have := Nat.coprime_div_gcd_div_gcd (m := P) (n := Q) (by rw [← hG]; exact hGpos)
    rwa [← hG] at this
  have hPu : P / G = u := Nat.div_eq_of_eq_mul_right hGpos hu
  have hQv : Q / G = v := Nat.div_eq_of_eq_mul_right hGpos hv
  rw [hPu, hQv] at hcop
  have hgpos : 0 < g := by omega
  have huv : u < v := by
    have : G * u < G * v := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  obtain ⟨d, rfl⟩ : ∃ d, v = u + d := ⟨v - u, by omega⟩
  have hd : 0 < d := by omega
  have h4 : G * (u + d) = G * u + G * d := by ring
  have hGd : 2 * M = G * d := by omega
  have h1 : G * d = 2 * (g * d) := by rw [hg]; ring
  have hMd : M = g * d := by omega
  have hM'd : M' = g * (u + (u + d)) := by
    have h2 : G * u = 2 * (g * u) := by rw [hg]; ring
    have h3 : g * (u + (u + d)) = g * u + g * u + g * d := by ring
    omega
  refine ⟨g, u, d, by omega, hPu.symm, ?_, hgpos, hd, ?_, hcop, hMd, hM'd⟩
  · exact (Nat.div_eq_of_eq_mul_right hGpos hGd).symm
  · have h5 : g * (3 * d) < g * (2 * u + d) := by
      have : 3 * M < M' := hlt
      rw [hMd, hM'd] at this
      nlinarith [this]
    have := Nat.lt_of_mul_lt_mul_left h5
    omega

/-- the gcd of the pair -/
def Gd (M M' : ℕ) : ℕ := Nat.gcd (M' - M) (M' + M)

/-- **Theorem C's arithmetic condition on a pair** `⌊g v / u⌋ · d < u` (`v = u + d`). -/
def thmCChk (M M' : ℕ) : Prop :=
  (Gd M M' / 2 * ((M' - M) / Gd M M' + 2 * M / Gd M M') / ((M' - M) / Gd M M')) * (2 * M / Gd M M')
    < (M' - M) / Gd M M'

instance (M M' : ℕ) : Decidable (thmCChk M M') := by unfold thmCChk; infer_instance

theorem thmCChk_param {M M' : ℕ} (hM : 0 < M) (hlt : 3 * M < M') (hpar : M % 2 = M' % 2)
    (h : thmCChk M M') :
    ∃ g u d : ℕ, 0 < g ∧ 0 < d ∧ d < u ∧ Nat.Coprime u (u + d) ∧ M = g * d ∧ M' = g * (u + (u + d)) ∧
      (g * (u + d) / u) * d < u := by
  obtain ⟨g, u, d, hg, hu, hd, hgp, hdp, hdu, hc, hM1, hM2⟩ := pair_param hM hlt hpar
  refine ⟨g, u, d, hgp, hdp, hdu, hc, hM1, hM2, ?_⟩
  subst hg hu hd
  exact h

/-- witnesses: `(M, M') = (2, 14)` has `g = 2, u = 3, d = 1` and `⌊2·4/3⌋·1 = 2 < 3`; `(2, 30)` has `g = 2, u = 7, d = 1`. -/
example : thmCChk 2 14 := by decide
example : thmCChk 2 30 := by decide
/-- negative control: `(6, 24)` has `g = 3, u = 3, d = 2`, `⌊3·5/3⌋·2 = 10 ≥ 3`. -/
example : ¬ thmCChk 6 24 := by decide

end Erdos634.Draft.ThmC

#print axioms Erdos634.Draft.ThmC.pair_param
#print axioms Erdos634.Draft.ThmC.thmCChk_param
