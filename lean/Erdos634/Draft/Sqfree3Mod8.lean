/-
Draft/Sqfree3Mod8.lean -- no squarefree `N ≡ 3 (mod 8)` with `3 ∤ N` is a tile count.

`not_tile_sqfree_3mod8`: for squarefree `N` with `N % 8 = 3` and `3 ∤ N`, no triangle can be cut into `N` congruent
triangles (isometries including reflections; no edge-to-edge assumption).  The set of such `N` has positive
density: `11, 19, 35, 43, 59, 67, 83, 91, 107, 115, 131, 139, 155, 163, 179, 187, 203, 211, …`.

Proof: the squarefree classification chain `ChainIso.chain_gen3_iso`, every leaf proved for the whole class.
* Commensurable angles, similar tile, right tile, `γ = 2α`: `N` squarefree, `N ≡ 3 (mod 4)`.
* `3α + 2β = π`: the base-`β` target at the scale `m = 1` has no tiling (`basebeta_full_unc`, through
  `s1Closed_of_sqfree`); `(2α, α, 2β)`: `Sqfree3Mod8.s2Arith_3mod8`; base-`α`: the count is
  `r² (f² − e²)(2f² − e²)` (`BADL2.theoremA_L2_full`, `prop:basealphadiv`), which is `≡ 1, 5 (mod 8)` when odd
  (`s3Closed_3mod8`; the weaker reduced equation `IsoQRef` alone does not suffice: `N = 46379` satisfies it).
* `2π/3` tiles: isosceles targets `isoH9b_3mod8`; scalene targets `noF2/F3z/F4z`; `F₁` and the equilateral
  triangle: every pair has a non-square discriminant (`f1Pair_3mod8`, `e120_pairs`), and for `π/3` tiles
  `e60_disc_not_sq` with `E60Irr.e60Pair_of_not_isSquare` (`prop:pi3rel`).

Relation to the literature.  The reduction of every tiling with such an
`N` to a base-`β` tiling at scale one, with `N = 3v² − u²`, `0 < u < v`, `gcd(u, v) = 1`, is the general clause of
Theorem A of D. Paliy, "Square-class obstructions and a uniform finite reduction for triangle tilings"
(unrefereed note).  He concludes the exclusion whenever that equation has no solution
(explicitly `N ≡ 19 (mod 24)`, `N ≡ 35 (mod 120)`; in general as soon as a prime `≡ ±5 (mod 12)` divides `N`).
The Lean proof of the reduction, and
the case where the equation is solvable, by `basebeta_full_unc` (`theoremP_6`), are given here.  Apart from the primes, that case is the composite `N` of the class with every prime factor
`≡ ±1 (mod 12)`: a set of density zero, first element `299 = 13 · 23 = 3·10² − 1 = 3·11² − 8²`
(`not_tileCount_299`).  `203 = 7 · 29` is excluded by the reduction alone.

The theorem contains the primes `≡ 3 (mod 8)`.  No sorry, no native_decide.
-/
import Erdos634.Draft.Sqfree3Mod8Arith
import Erdos634.Draft.S3Inst
import Erdos634.Draft.G3CAng
import Erdos634.Draft.PrimeCharacterization
import Erdos634.Draft.CompositeF1Gen
import Erdos634.BADFinal2

open scoped Classical

namespace Erdos634.Draft.Sqfree3Mod8

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.AllNExclusion Erdos634.Draft.ChainIso Erdos634.Draft.R8ZF Erdos634.Draft.R8Gen2
open Erdos634.Draft.TileCountFamilies

variable {N : ℕ}

/-! ## Base-`α` targets: the instance leaf from `b ∣ w` -/

/-- **An S3 instance whose scale is not a multiple of `f − e` has no dissection** (`prop:basealphadiv`: the
leg is `f² w` with `(f² − e²) ∣ w`). -/
theorem s3inst_of_not_dvd (m e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) (hm : 1 ≤ m)
    (hnd : ¬ (f - e) ∣ m) : S3Inst m e f := by
  intro N D h0 h1 h2 ⟨σ, m0, m1, m2⟩
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hefR : (e : ℝ) < (f : ℝ) := by exact_mod_cast hef
  have hfR : (0 : ℝ) < (f : ℝ) := heR.trans hefR
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hQ : (0 : ℝ) < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hefZ : (e : ℤ) < (f : ℤ) := by exact_mod_cast hef
  have hcopZ : IsCoprime (e : ℤ) (f : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have l0 : D.model.oppLen (σ 0) = (((e : ℤ) : ℝ)) * ((f : ℤ) : ℝ) := by push_cast; exact m0
  have l1 : D.model.oppLen (σ 1) = ((f : ℤ) : ℝ) ^ 2 - ((e : ℤ) : ℝ) ^ 2 := by push_cast; exact m1
  have l2 : D.model.oppLen (σ 2) = ((f : ℤ) : ℝ) ^ 2 := by push_cast; exact m2
  obtain ⟨hcα, -⟩ := Erdos634.BADL2.tile_angles D.model σ (e : ℤ) (f : ℤ) heZ hefZ l0 l1 l2
  push_cast at hcα
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (m : ℝ) * (f : ℝ) ^ 2 * ((f : ℝ) + e) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (m : ℝ) * ((f : ℝ) + e) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := ⟨_, rfl⟩
  rw [← hX] at h0 h1
  rw [← hY] at h2
  have hXpos : 0 < X := by rw [hX]; positivity
  have hYpos : 0 < Y := by rw [hY]; exact mul_pos (mul_pos hmR (by linarith)) hQ
  have hYX : Y * (f : ℝ) ^ 2 = X * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by rw [hX, hY]; ring
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  have e02 : (0 : Fin 3) + 2 = 2 := rfl
  have e11 : (1 : Fin 3) + 1 = 2 := rfl
  have e12 : (1 : Fin 3) + 2 = 0 := rfl
  have c0 := Erdos634.Draft.G3CAng.cos_angleAt_opp D.target 0 (by rw [e01, h1]; exact hXpos)
    (by rw [e02, h2]; exact hYpos)
  rw [e01, e02, h0, h1, h2] at c0
  have c1 := Erdos634.Draft.G3CAng.cos_angleAt_opp D.target 1 (by rw [e11, h2]; exact hYpos)
    (by rw [e12, h0]; exact hXpos)
  rw [e11, e12, h0, h1, h2] at c1
  have a0 : D.target.angleAt 0 = D.model.angleAt (σ 0) := by
    refine Erdos634.Draft.G3CAng.angle_eq_of_cos 0 (σ 0) ?_
    rw [c0, hcα, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (2 * Y) * hYX
  have a1 : D.target.angleAt 1 = D.model.angleAt (σ 0) := by
    refine Erdos634.Draft.G3CAng.angle_eq_of_cos 1 (σ 0) ?_
    rw [c1, hcα, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (2 * Y) * hYX
  obtain ⟨w, hXw, -, hdvd⟩ := Erdos634.BADL2.theoremA_L2_full D (e : ℤ) (f : ℤ) heZ hefZ hcopZ X Y σ l0 l1 l2
    (Equiv.refl _) a0 a1 h0 h1 h2
  -- `w = m (f + e)`
  have hw : (w : ℝ) = (m : ℝ) * ((f : ℝ) + e) := by
    push_cast at hXw
    have h3 : (f : ℝ) ^ 2 * (w : ℝ) = (f : ℝ) ^ 2 * ((m : ℝ) * ((f : ℝ) + e)) := by
      rw [← hXw, hX]
      ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hfR.ne') h3
  have hwZ : w = (m : ℤ) * ((f : ℤ) + e) := by exact_mod_cast hw
  rw [hwZ] at hdvd
  have hfe : ((f : ℤ) + e) ≠ 0 := by positivity
  have hdvd' : ((f : ℤ) - e) * ((f : ℤ) + e) ∣ (m : ℤ) * ((f : ℤ) + e) := by
    have h3 : ((f : ℤ) - e) * ((f : ℤ) + e) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by ring
    rw [h3]
    exact hdvd
  have hdm : ((f : ℤ) - e) ∣ (m : ℤ) := (mul_dvd_mul_iff_right hfe).mp hdvd'
  have hdm' : ((f - e : ℕ) : ℤ) ∣ (m : ℤ) := by
    rw [Nat.cast_sub hef.le]
    exact hdm
  exact hnd (Int.natCast_dvd_natCast.mp hdm')

/-- the base-`α` leaf for `N ≡ 3 (mod 8)` -/
theorem s3Closed_3mod8 (h8 : N % 8 = 3) : S3Closed N := by
  have hc := cast8 h8
  refine s3Closed_of_inst N ?_
  intro e d m he hd hcop heq
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      rw [h] at heq
      have hNd : N * d = 0 := by rw [heq]; ring
      have hN0 : 0 < N := by omega
      have := Nat.mul_pos hN0 hd
      omega
    · exact h
  rcases Classical.em (d ∣ m) with hdm | hdm
  · exfalso
    obtain ⟨r, rfl⟩ := hdm
    have h' : N = d * r ^ 2 * (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2) := by
      have h1 : d * N = d * (d * r ^ 2 * (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
        rw [mul_comm d N, heq]
        ring
      exact Nat.eq_of_mul_eq_mul_left hd h1
    have h8' := congrArg (Nat.cast : ℕ → ZMod 8) h'
    push_cast at h8'
    rw [hc] at h8'
    exact z8_s3 (e : ZMod 8) (d : ZMod 8) (r : ZMod 8) (by linear_combination h8')
  · have hnd : ¬ (e + d - e) ∣ m := by rwa [Nat.add_sub_cancel_left]
    intro N' D' a0 a1 a2 a3
    exact s3inst_of_not_dvd m e (e + d) he (by omega) hcop hm hnd D' a0 a1 a2 a3

/-! ## The equilateral and `F₁` leaves -/

theorem gapE60_3mod8 (h8 : N % 8 = 3) : GapE60 N := by
  intro D α a b c hα h hE
  obtain ⟨m₁, m₂, -, hp2, -, -, -, -, hS1, hS2, -, hprod, -, -⟩ := Row5.theoremE_sixty D hα h hE
  exact Erdos634.Draft.E60Irr.e60Pair_of_not_isSquare N m₁ m₂ (e60_disc_not_sq h8 m₁ m₂ hp2 hprod) D α a b c
    hα h hE hS1 hS2

theorem gapE120_3mod8 (hsq : Squarefree N) (h8 : N % 8 = 3) (h3 : ¬ 3 ∣ N) : GapE120 N :=
  Erdos634.Draft.CompositeE5Gen.gapE120_of_pairs N (by omega) (e120_pairs hsq h8 h3)

theorem gapF1_3mod8 (h8 : N % 8 = 3) (h7 : 6 < N) : GapF1 N :=
  Erdos634.Draft.CompositeF1Gen.gapF1_of_MaGt1 N h7
    (Erdos634.Draft.F1PairCert.f1MaGt1_of_pairs N (f1Pair_3mod8 h8))

/-! ## The theorem -/

/-- **No squarefree `N ≡ 3 (mod 8)` with `3 ∤ N` is a tile count.** -/
theorem not_tile_sqfree_3mod8 (hsq : Squarefree N) (h8 : N % 8 = 3) (h3 : ¬ 3 ∣ N)
    (D : CongruentDissection N) : False := by
  by_cases h11 : N = 11
  · subst h11
    have h := (Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff 11 (by norm_num)).mp ⟨D⟩
    omega
  have h19 : 19 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hns := nsq_3mod8 h8
  obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := exists_prime_ge7 hsq h8 h3
  exact chain_gen3_iso N hsq (s1Closed_of_sqfree N hsq hN0)
    (s2Closed_of_arith N (s2Arith_3mod8 h8))
    (s3Closed_3mod8 h8)
    (fun D α a b c hα hd hi =>
      Erdos634.Draft.ThmIsoH9b.thmIso_H9b N D (isoH9b_3mod8 h8) α a b c hα hd hi)
    (fun hS => Erdos634.CaseA.RCompositeE.gapA_of_ellE hS hsq (by omega) (Or.inl (by omega)) hns
      (harith_3mod8 h8 h3) hℓ hℓ7 hodd)
    (caseB_of_sumsq N
      (fun D μ τ hs => Row2.theoremS_perm_sqfreeE D μ τ hs hsq (by omega) (Or.inl (by omega))) hns)
    (caseR_of_odd N (by omega))
    (Erdos634.Draft.CompositeFinal10.caseG_of_squarefree N hsq)
    (gapE60_3mod8 h8) (gapE120_3mod8 hsq h8 h3) (gapF1_3mod8 h8 (by omega))
    (gapR8_of_arith_z N (noF2_3mod8 h8 h3) (noF3z_3mod8 h3) (noF4z_3mod8 h8)) D

/-- the same, as a statement about tile counts -/
theorem not_tileCount_sqfree_3mod8 (hsq : Squarefree N) (h8 : N % 8 = 3) (h3 : ¬ 3 ∣ N) : ¬ TileCount N :=
  fun ⟨D⟩ => not_tile_sqfree_3mod8 hsq h8 h3 D

/-- an instance beyond the table of values `≤ 200` (already excluded by the reduction alone: `7 ∣ 203`) -/
theorem not_tileCount_203 : ¬ TileCount 203 :=
  not_tileCount_sqfree_3mod8 (by
    have h : (203 : ℕ) = 7 * 29 := by norm_num
    rw [h]
    exact Nat.squarefree_mul_iff.mpr ⟨by norm_num, (by norm_num : Nat.Prime 7).prime.squarefree,
      (by norm_num : Nat.Prime 29).prime.squarefree⟩) (by norm_num) (by norm_num)

/-- the first composite value for which the base-`β` exclusion at scale one is needed
(`299 = 3·10² − 1² = 3·11² − 8²`) -/
theorem not_tileCount_299 : ¬ TileCount 299 :=
  not_tileCount_sqfree_3mod8 (by
    have h : (299 : ℕ) = 13 * 23 := by norm_num
    rw [h]
    exact Nat.squarefree_mul_iff.mpr ⟨by norm_num, (by norm_num : Nat.Prime 13).prime.squarefree,
      (by norm_num : Nat.Prime 23).prime.squarefree⟩) (by norm_num) (by norm_num)

end Erdos634.Draft.Sqfree3Mod8

#print axioms Erdos634.Draft.Sqfree3Mod8.s3inst_of_not_dvd
#print axioms Erdos634.Draft.Sqfree3Mod8.not_tile_sqfree_3mod8
#print axioms Erdos634.Draft.Sqfree3Mod8.not_tileCount_203
#print axioms Erdos634.Draft.Sqfree3Mod8.not_tileCount_299
