/-
Draft/E120Irr.lean -- the irrational `2π/3` pairs on the equilateral triangle, for every `N`.

`E120Graph.twoPiThree_has_a_relation` (`Draft/E120Count.lean`): a tile with an angle `2π/3` and an irrational angle
that tiles an equilateral triangle satisfies `j a = p b + q c`.  Consequences:

* `twoPiThree_has_b_relation` (the two irrational angles can be exchanged) and `a_ne_b` (law of sines);
* `disc_square_of_relations`: with the invariants `s (c + a − b) = 3S`, `t (c + b − a) = 3S`, `S² = N a b`,
  `s t = 3N` of `Row5.theoremE_twoPiThree`, an `a`-relation, a `b`-relation and `a ≠ b` force
  `(t − s)² + 16N` to be a square.  (`c` and `a − b` are rational multiples of `S`; a relation with `j ≠ p` makes
  `b`, hence `a + b`, a rational multiple of `S`; if both relations are degenerate, `t = s` and `a = b`.)
* `e120Pair_of_not_isSquare`: for every `N` and every pair `(s, t)` whose discriminant `(t − s)² + 16N` is not a
  square, `E120Pair N s t`: no dissection has that pair.
* `gapE120_of_disc`: `GapE120 N` if no admissible pair has a square discriminant; `Pairs120ChkSq`,
  `gapE120_of_chk_sq`: the same from a kernel-checkable table with a list of pairs left to certify.

PRIOR ART.  That such a tile has commensurable sides is Theorem 5.2 of M. Beeson and Y. X. Zhang, Rationality of
certain triangle tilings, arXiv:2604.01314; their proof ends with the invariant `Φ` of Laczkovich.  Here the degree
count (their Lemma 3.5) is combined with the two flux invariants of `Row5.theoremE_twoPiThree` instead, which gives
the statement in the form needed by the pair tables.  A formal reproduction of a published theorem by a shorter
ending; not a new result. not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.E120Count
import Erdos634.Draft.GapE120Exc
import Erdos634.Draft.E60Parity

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.E120Irr

open Erdos634.Draft.AllNExclusion

/-- the pair table: a divisor pair `(m, 3N/m)` is listed (to be certified), of the wrong parity, or has a
non-square discriminant `(3N/m − m)² + 16N` -/
def Pairs120ChkSq (N : ℕ) (L : List (ℕ × ℕ)) : Prop :=
  ∀ m ≤ N, 1 ≤ m → m ∣ 3 * N → 3 * N / m ≤ N →
    L.contains (m, 3 * N / m) = true ∨
    (m % 2 ≠ N % 2 ∨ (3 * N / m) % 2 ≠ N % 2) ∨
    ¬ sqChk ((m + 3 * N / m) ^ 2 + 16 * N - 4 * (3 * N))

instance (N : ℕ) (L : List (ℕ × ℕ)) : Decidable (Pairs120ChkSq N L) := by
  unfold Pairs120ChkSq sqChk; infer_instance

end Erdos634.Draft.E120Irr

open scoped Classical
open Erdos634.Geometry
open Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeE5Gen
open Erdos634.Draft.AllNExclusion Erdos634.Draft.E120Graph Erdos634.Draft.GapE120Exc
open Erdos634.Pi3Tile (Irr)

namespace Erdos634.Draft.E120Irr

variable {N : ℕ}

/-- the two irrational angles of a `2π/3` tile can be exchanged -/
theorem twoPiThreeData_swap {T : Erdos634.Geometry.Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    T.TwoPiThreeData (Real.pi / 3 - α) b a c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  refine ⟨(Equiv.swap (0 : Fin 3) 1).trans σ, ?_⟩
  have e0 : ((Equiv.swap (0 : Fin 3) 1).trans σ) 0 = σ 1 := by
    show σ (Equiv.swap (0 : Fin 3) 1 0) = σ 1
    rw [Equiv.swap_apply_left]
  have e1 : ((Equiv.swap (0 : Fin 3) 1).trans σ) 1 = σ 0 := by
    show σ (Equiv.swap (0 : Fin 3) 1 1) = σ 0
    rw [Equiv.swap_apply_right]
  have e2 : ((Equiv.swap (0 : Fin 3) 1).trans σ) 2 = σ 2 := by
    show σ (Equiv.swap (0 : Fin 3) 1 2) = σ 2
    rw [show Equiv.swap (0 : Fin 3) 1 2 = 2 by decide]
  rw [e0, e1, e2]
  exact ⟨h1, o1, by rw [h0]; ring, o0, h2, o2⟩

/-- the relation for the other side -/
theorem twoPiThree_has_b_relation (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.TwoPiThreeData α a b c) (hE : ∀ k, D.target.angleAt k = Real.pi / 3) :
    ∃ j p q : ℕ, 0 < j ∧ (j : ℝ) * b = p * a + q * c :=
  twoPiThree_has_a_relation D (Erdos634.TwoPi3Tile.irr_swap hirr) (twoPiThreeData_swap hS) hE

/-- the sides opposite the two irrational angles are different -/
theorem a_ne_b {T : Erdos634.Geometry.Tri} {α a b c : ℝ} (hirr : Irr α) (hS : T.TwoPiThreeData α a b c) :
    a ≠ b := by
  obtain ⟨σ, h0, o0, h1, o1, -, -⟩ := hS
  intro hab
  have hls := T.lawSin (σ 0) (σ 1)
  rw [h0, h1, o0, o1, hab] at hls
  have hbpos : 0 < b := by rw [← o1]; exact T.oppLen_pos _
  have hsin : Real.sin α = Real.sin (Real.pi / 3 - α) := mul_right_cancel₀ hbpos.ne' hls
  have hα0 : 0 < α := by
    rw [← h0]; exact Erdos634.MarchFlank.cornerAngle_pos T (σ 0)
  have hβ0 : 0 < Real.pi / 3 - α := by
    rw [← h1]; exact Erdos634.MarchFlank.cornerAngle_pos T (σ 1)
  have hpi := Real.pi_pos
  have heq : α = Real.pi / 3 - α :=
    Real.injOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hsin
  exact hirr ⟨1 / 6, by push_cast; linarith⟩

/-- **`a/b` is rational** for a tile with an angle `2π/3` and an irrational angle that tiles an equilateral
triangle (Beeson and Zhang, Lemma 3.6). -/
theorem twoPiThree_ratio_rational (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.TwoPiThreeData α a b c) (hE : ∀ k, D.target.angleAt k = Real.pi / 3) :
    ∃ r : ℚ, a = (r : ℝ) * b := by
  obtain ⟨j, p, q, hj, h1⟩ := twoPiThree_has_a_relation D hirr hS hE
  obtain ⟨J, P, Q, hJ, h2⟩ := twoPiThree_has_b_relation D hirr hS hE
  have hS' := hS
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := hS'
  have ha : 0 < a := by rw [← o0]; exact D.model.oppLen_pos _
  have hb : 0 < b := by rw [← o1]; exact D.model.oppLen_pos _
  have hc : 0 < c := by rw [← o2]; exact D.model.oppLen_pos _
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have key : ((j : ℝ) * Q + q * P) * a = ((J : ℝ) * q + p * Q) * b := by
    linear_combination (Q : ℝ) * h1 - (q : ℝ) * h2
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    refine ⟨(p : ℚ) / j, ?_⟩
    push_cast
    field_simp
    simp only [Nat.cast_zero, zero_mul, add_zero] at h1
    linarith
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hpos : (0 : ℝ) < (j : ℝ) * Q + q * P ∨ ((Q : ℝ) = 0 ∧ (P : ℝ) = 0) := by
      rcases Nat.eq_zero_or_pos Q with hQ | hQ
      · rcases Nat.eq_zero_or_pos P with hP | hP
        · right; exact ⟨by exact_mod_cast hQ, by exact_mod_cast hP⟩
        · left
          have : (0 : ℝ) < P := by exact_mod_cast hP
          have : (0 : ℝ) ≤ (j : ℝ) * Q := by positivity
          nlinarith
      · left
        have : (0 : ℝ) < Q := by exact_mod_cast hQ
        have : (0 : ℝ) ≤ (q : ℝ) * P := by positivity
        nlinarith
    rcases hpos with hpos | ⟨hQ0, hP0⟩
    · refine ⟨((J : ℚ) * q + p * Q) / ((j : ℚ) * Q + q * P), ?_⟩
      push_cast
      rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
      linarith
    · exfalso
      rw [hQ0, hP0] at h2
      nlinarith

/-- **Commensurable sides** (Beeson and Zhang, Theorem 5.2): a tile with an angle `2π/3` and an irrational angle
that tiles an equilateral triangle has pairwise commensurable sides. -/
theorem twoPiThree_commensurable (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.TwoPiThreeData α a b c) (hE : ∀ k, D.target.angleAt k = Real.pi / 3) :
    ∃ r s : ℚ, a = (r : ℝ) * b ∧ c = (s : ℝ) * b := by
  obtain ⟨r, hr⟩ := twoPiThree_ratio_rational D hirr hS hE
  obtain ⟨s, t, -, -, hs1, -, ht1, -, hT1, hT2, -, -, -⟩ := Row5.theoremE_twoPiThree D hirr hS hE
  have hab := a_ne_b hirr hS
  have h1 : c * ((s : ℝ) - t) = (b - a) * ((s : ℝ) + t) := by linear_combination hT1 - hT2
  have hst : (s : ℝ) ≠ t := by
    intro h
    rw [h, sub_self, mul_zero] at h1
    have e2 : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have h0 : b - a = 0 := by
      rcases mul_eq_zero.mp h1.symm with h0 | h0
      · exact h0
      · linarith
    exact hab (by linarith)
  have hne : (s : ℝ) - t ≠ 0 := sub_ne_zero.mpr hst
  have h2 : c * ((s : ℝ) - t) = (1 - (r : ℝ)) * ((s : ℝ) + t) * b := by
    rw [hr] at h1
    linear_combination h1
  have h3 : c = (1 - (r : ℝ)) * ((s : ℝ) + t) * b / ((s : ℝ) - t) := by
    rw [eq_div_iff hne]; exact h2
  refine ⟨r, (1 - r) * (((s + t : ℤ) : ℚ) / ((s - t : ℤ) : ℚ)), hr, ?_⟩
  rw [h3]
  push_cast
  ring

/-- **The discriminant is a square.**  Pure algebra on the invariants and the two relations. -/
theorem disc_square_of_relations {a b c S : ℝ} {s t : ℤ} (hN : 0 < N) (hS : 0 < S)
    (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hS1 : (s : ℝ) * (c + a - b) = 3 * S) (hS2 : (t : ℝ) * (c + b - a) = 3 * S)
    (harea : S ^ 2 = N * a * b) (hprod : s * t = 3 * (N : ℤ)) (hab : a ≠ b)
    {j p q J P Q : ℕ} (hj : 0 < j) (hJ : 0 < J)
    (h1 : (j : ℝ) * a = p * b + q * c) (h2 : (J : ℝ) * b = P * a + Q * c) :
    IsSquare ((t - s) ^ 2 + 16 * (N : ℤ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hprodR : (s : ℝ) * t = 3 * N := by exact_mod_cast hprod
  have key1 : 2 * (N : ℝ) * c = S * ((s : ℝ) + t) := by
    have h3 : (s : ℝ) * t * (2 * c) = 3 * S * (s + t) := by
      linear_combination (t : ℝ) * hS1 + (s : ℝ) * hS2
    rw [hprodR] at h3; linarith
  have key2 : 2 * (N : ℝ) * (a - b) = S * ((t : ℝ) - s) := by
    have h3 : (s : ℝ) * t * (2 * (a - b)) = 3 * S * (t - s) := by
      linear_combination (t : ℝ) * hS1 - (s : ℝ) * hS2
    rw [hprodR] at h3; linarith
  have hdisc : (2 * (N : ℝ) * (a + b)) ^ 2 = S ^ 2 * (((t : ℝ) - s) ^ 2 + 16 * N) := by
    have e : (2 * (N : ℝ) * (a + b)) ^ 2 = (2 * (N : ℝ) * (a - b)) ^ 2 + 16 * (N : ℝ) * (N * a * b) := by ring
    rw [e, key2, ← harea]; ring
  -- a rational value of `2N (a + b) / S` makes the discriminant a square
  have fin : ∀ K L : ℤ, L ≠ 0 → 2 * (N : ℝ) * (a + b) * (L : ℝ) = S * (K : ℝ) →
      IsSquare ((t - s) ^ 2 + 16 * (N : ℤ)) := by
    intro K L hL hKL
    have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL
    have h5 : (K : ℝ) ^ 2 = (((t : ℝ) - s) ^ 2 + 16 * N) * (L : ℝ) ^ 2 := by
      have h6 : S ^ 2 * (K : ℝ) ^ 2 = S ^ 2 * ((((t : ℝ) - s) ^ 2 + 16 * N) * (L : ℝ) ^ 2) := by
        linear_combination (-(2 * (N : ℝ) * (a + b) * (L : ℝ) + S * (K : ℝ))) * hKL + ((L : ℝ) ^ 2) * hdisc
      exact mul_left_cancel₀ (pow_ne_zero 2 hS.ne') h6
    refine isSquare_of_rat_sq _ K L hL ?_
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hLR), h5]
    first | (push_cast; ring) | push_cast
  have hX1 : 2 * (N : ℝ) * (a + b) * ((j : ℝ) - p)
      = S * (2 * (q : ℝ) * ((s : ℝ) + t) - ((j : ℝ) + p) * ((t : ℝ) - s)) := by
    linear_combination (4 * (N : ℝ)) * h1 + (2 * (q : ℝ)) * key1 - ((j : ℝ) + p) * key2
  have hX2 : 2 * (N : ℝ) * (a + b) * ((J : ℝ) - P)
      = S * (2 * (Q : ℝ) * ((s : ℝ) + t) + ((J : ℝ) + P) * ((t : ℝ) - s)) := by
    linear_combination (4 * (N : ℝ)) * h2 + (2 * (Q : ℝ)) * key1 + ((J : ℝ) + P) * key2
  have hst : (0 : ℝ) < (s : ℝ) + t := by
    have e1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have e2 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  rcases eq_or_ne j p with hjp | hjp
  · rcases eq_or_ne J P with hJP | hJP
    · exfalso
      have hjp' : (j : ℝ) = p := by exact_mod_cast hjp
      have hJP' : (J : ℝ) = P := by exact_mod_cast hJP
      have hjR : (0 : ℝ) < j := by exact_mod_cast hj
      have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
      have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
      have e1 : 2 * (q : ℝ) * ((s : ℝ) + t) - ((j : ℝ) + p) * ((t : ℝ) - s) = 0 := by
        have h0 : S * (2 * (q : ℝ) * ((s : ℝ) + t) - ((j : ℝ) + p) * ((t : ℝ) - s)) = 0 := by
          rw [← hX1, hjp', sub_self, mul_zero]
        exact (mul_eq_zero.mp h0).resolve_left hS.ne'
      have e2 : 2 * (Q : ℝ) * ((s : ℝ) + t) + ((J : ℝ) + P) * ((t : ℝ) - s) = 0 := by
        have h0 : S * (2 * (Q : ℝ) * ((s : ℝ) + t) + ((J : ℝ) + P) * ((t : ℝ) - s)) = 0 := by
          rw [← hX2, hJP', sub_self, mul_zero]
        exact (mul_eq_zero.mp h0).resolve_left hS.ne'
      have h3 : (0 : ℝ) ≤ ((j : ℝ) + p) * ((t : ℝ) - s) := by
        have := mul_nonneg hq0 hst.le
        linarith
      have h4 : ((J : ℝ) + P) * ((t : ℝ) - s) ≤ 0 := by
        have := mul_nonneg hQ0 hst.le
        linarith
      have h5 : (0 : ℝ) ≤ (t : ℝ) - s := by
        rcases le_or_gt 0 ((t : ℝ) - s) with h | h
        · exact h
        · exfalso
          have := mul_neg_of_pos_of_neg (by linarith : (0 : ℝ) < (j : ℝ) + p) h
          linarith
      have h6 : (t : ℝ) - s ≤ 0 := by
        rcases le_or_gt ((t : ℝ) - s) 0 with h | h
        · exact h
        · exfalso
          have := mul_pos (by linarith : (0 : ℝ) < (J : ℝ) + P) h
          linarith
      have h7 : (t : ℝ) - s = 0 := le_antisymm h6 h5
      rw [h7, mul_zero] at key2
      have h8 : a - b = 0 := by
        rcases mul_eq_zero.mp key2 with h | h
        · exfalso; linarith
        · exact h
      exact hab (by linarith)
    · exact fin (2 * Q * (s + t) + ((J : ℤ) + P) * (t - s)) ((J : ℤ) - P)
        (sub_ne_zero.mpr (by exact_mod_cast hJP)) (by push_cast; linear_combination hX2)
  · exact fin (2 * q * (s + t) - ((j : ℤ) + p) * (t - s)) ((j : ℤ) - p)
      (sub_ne_zero.mpr (by exact_mod_cast hjp)) (by push_cast; linear_combination hX1)

/-- **Every irrational `2π/3` pair is excluded, for every `N`.**  If the discriminant `(t − s)² + 16N` of the
pair is not a square, no dissection has that pair. -/
theorem e120Pair_of_not_isSquare (N : ℕ) (s t : ℤ)
    (hD : ¬ IsSquare ((t - s) ^ 2 + 16 * (N : ℤ))) : E120Pair N s t := by
  intro D α a b c hα hS hE hS1 hS2 harea
  obtain ⟨s', t', -, -, hs1, -, ht1, -, hT1, hT2, -, hprod, -⟩ := Row5.theoremE_twoPiThree D hα hS hE
  have hSpos : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have e1 : s = s' := by
    have hne : c + a - b ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hT1; linarith
    have : (s : ℝ) = s' := mul_right_cancel₀ hne (hS1.trans hT1.symm)
    exact_mod_cast this
  have e2 : t = t' := by
    have hne : c + b - a ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hT2; linarith
    have : (t : ℝ) = t' := mul_right_cancel₀ hne (hS2.trans hT2.symm)
    exact_mod_cast this
  rw [← e1, ← e2] at hprod
  rw [← e1] at hs1
  rw [← e2] at ht1
  obtain ⟨j, p, q, hj, h1⟩ := twoPiThree_has_a_relation D hα hS hE
  obtain ⟨J, P, Q, hJ, h2⟩ := twoPiThree_has_b_relation D hα hS hE
  exact hD (disc_square_of_relations D.toDissection.pos hSpos hs1 ht1 hS1 hS2 harea hprod (a_ne_b hα hS)
    hj hJ h1 h2)

/-- **`GapE120 N` when no admissible pair has a square discriminant.** -/
theorem gapE120_of_disc (N : ℕ)
    (hpairs : ∀ s t : ℤ, 1 ≤ s → s ≤ N → 1 ≤ t → t ≤ N → s * t = 3 * (N : ℤ) →
      (2 : ℤ) ∣ s - N → (2 : ℤ) ∣ t - N → ¬ IsSquare ((t - s) ^ 2 + 16 * (N : ℤ))) : GapE120 N := by
  intro D α a b c hα h hE
  obtain ⟨s, t, hp1, hp2, hs1, hsN, ht1, htN, hS1, hS2, harea, hprod, -⟩ := Row5.theoremE_twoPiThree D hα h hE
  exact e120Pair_of_not_isSquare N s t (hpairs s t hs1 hsN ht1 htN hprod hp1 hp2) D α a b c hα h hE hS1 hS2 harea

/-- **`GapE120 N` from the pair table**: only the listed pairs (rational, of the right parity) need a proof. -/
theorem gapE120_of_chk_sq {N : ℕ} (L : List (ℕ × ℕ)) (h : Pairs120ChkSq N L)
    (hL : ∀ p ∈ L, E120Pair N (p.1 : ℤ) (p.2 : ℤ)) : GapE120 N := by
  intro D α a b c hα hd hE
  obtain ⟨s, t, hp1, hp2, hs1, hsN, ht1, htN, hS1, hS2, harea, hprod, -⟩ := Row5.theoremE_twoPiThree D hα hd hE
  lift s to ℕ using (by omega)
  lift t to ℕ using (by omega)
  have hp' : s * t = 3 * N := by exact_mod_cast hprod
  have h1 : 1 ≤ s := by exact_mod_cast hs1
  have h1N : s ≤ N := by exact_mod_cast hsN
  have h2N : t ≤ N := by exact_mod_cast htN
  have hdvd : s ∣ 3 * N := ⟨t, hp'.symm⟩
  have hdiv : 3 * N / s = t := by rw [← hp']; exact Nat.mul_div_cancel_left _ h1
  have hall := h s h1N h1 hdvd (by rw [hdiv]; exact h2N)
  rw [hdiv] at hall
  rcases hall with hmem | hpar | hsq
  · exact hL (s, t) (List.contains_iff_mem.mp hmem) D α a b c hα hd hE hS1 hS2 harea
  · exfalso
    rcases hpar with h | h <;> omega
  · refine e120Pair_of_not_isSquare N s t ?_ D α a b c hα hd hE hS1 hS2 harea
    have hle : 4 * (3 * N) ≤ (s + t) ^ 2 + 16 * N := by
      have : 4 * (s * t) ≤ (s + t) ^ 2 := by
        have h4 := four_mul_le_sq_add s t
        rwa [mul_assoc] at h4
      rw [hp'] at this
      omega
    exact not_isSquare_of_chk ((s + t) ^ 2 + 16 * N - 4 * (3 * N)) _
      (by
        rw [Nat.cast_sub hle]
        push_cast
        have hpZ : (s : ℤ) * t = 3 * (N : ℤ) := by exact_mod_cast hp'
        linear_combination (-4 : ℤ) * hpZ) hsq

end Erdos634.Draft.E120Irr

#print axioms Erdos634.Draft.E120Irr.twoPiThree_has_b_relation
#print axioms Erdos634.Draft.E120Irr.disc_square_of_relations
#print axioms Erdos634.Draft.E120Irr.e120Pair_of_not_isSquare
#print axioms Erdos634.Draft.E120Irr.gapE120_of_chk_sq
#print axioms Erdos634.Draft.E120Irr.twoPiThree_commensurable
