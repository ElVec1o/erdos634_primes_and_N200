/-
Draft/OpenReductions.lean -- the open values `154` and `161` reduced to one instance each.

Neither value is decided here.  For each, every leaf of the squarefree chain is closed in Lean except one instance,
which is carried as a hypothesis:

    theorem not_tile_161_of (h : S3Inst 1 3 4)      (D : CongruentDissection 161) : False
    theorem not_tile_154_of (h : IsoInst 8 7 13 7)  (D : CongruentDissection 154) : False

* `161 = 7 · 23 = (4² − 3²)(2·4² − 3²)`: the base-`α` target of the member `(3, 4)` at the smallest scale; tile
  `(12, 7, 16)`, target legs `112`, base `161`.
* `154 = 2 · 7 · 11`: the isosceles target with a `2π/3` tile; tile `(8, 7, 13)`, target legs `91`, base `154`.

Tools: `S3ChkDL`, `s3Closed_of_chkDL` (the base-`α` check with a list of open triples) and `IsoChkL`,
`isoInstHyp_of_chkL` (the isosceles check with a list of open pairs).  The second gives the first use of
`IsoInst.isoClosed_of_inst`.

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.AllN3Cond
import Erdos634.Draft.ChainIso

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.OpenRed

open Erdos634.Draft.AllNExclusion

/-- the base-`α` check with a list of triples `(e, d, r)` left open (the scale is `m = d r`) -/
def S3ChkDL (N : ℕ) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ e ≤ Nat.sqrt N, 1 ≤ e → e * e ≤ N → ∀ d ≤ Nat.sqrt (N / 2), 1 ≤ d → 2 * (d * d) ≤ N → qQ e d ∣ N →
    kK e d ∣ N * d → Nat.sqrt (N * d / kK e d) * Nat.sqrt (N * d / kK e d) = N * d / kK e d →
      d ∣ Nat.sqrt (N * d / kK e d) → L.contains (e, d, Nat.sqrt (N * d / kK e d) / d) = true

instance (N : ℕ) (L : List (ℕ × ℕ × ℕ)) : Decidable (S3ChkDL N L) := by unfold S3ChkDL qQ kK; infer_instance

/-- the isosceles check with a list of pairs `(a, b)` left open -/
def IsoChkL (N : ℕ) (L : List (ℕ × ℕ)) : Prop :=
  ∀ e < N, 3 ≤ e → e ∣ N → ∀ b < e, 0 < b → 2 * b < e → Nat.gcd b e = 1 →
    IsoBad N (e - 2 * b) b → L.contains (e - 2 * b, b) = true

instance (N : ℕ) (L : List (ℕ × ℕ)) : Decidable (IsoChkL N L) := by unfold IsoChkL; infer_instance

end Erdos634.Draft.OpenRed

open scoped Classical

namespace Erdos634.Draft.OpenRed

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2 Erdos634.Draft.R8ZF Erdos634.Draft.E60Irr
open Erdos634.Draft.IsoInst Erdos634.Draft.ChainIso Erdos634.Draft.AllN3

/-- **The base-`α` leaf, the listed triples being carried as instances.** -/
theorem s3Closed_of_chkDL {N : ℕ} (hN0 : 0 < N) (L : List (ℕ × ℕ × ℕ)) (h : S3ChkDL N L)
    (hL : ∀ p ∈ L, S3Inst (p.2.1 * p.2.2) p.1 (p.1 + p.2.1)) : S3Closed N := by
  refine s3Closed_of_inst N ?_
  intro e d m he hd hcop heq
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      rw [h0] at heq
      have hNd : N * d = 0 := by rw [heq]; ring
      have := Nat.mul_pos hN0 hd
      omega
    · exact h0
  rcases Classical.em (d ∣ m) with hdm | hdm
  · obtain ⟨r, rfl⟩ := hdm
    have hKpos : 0 < kK e d := by unfold kK qQ; positivity
    have heq' : N * d = (d * r) * (d * r) * kK e d := by unfold kK qQ; rw [heq]; ring
    have hN : N = d * r * r * kK e d := by
      have h1 : d * N = d * (d * r * r * kK e d) := by rw [mul_comm d N, heq']; ring
      exact Nat.eq_of_mul_eq_mul_left hd h1
    have hQ' : qQ e d ∣ N := ⟨d * r * r * (2 * e + d), by rw [hN]; unfold kK; ring⟩
    have hle : qQ e d ≤ N := Nat.le_of_dvd hN0 hQ'
    have he2 : e * e ≤ N := by unfold qQ at hle; nlinarith
    have hd2 : 2 * (d * d) ≤ N := by unfold qQ at hle; nlinarith
    have hdiv : N * d / kK e d = (d * r) * (d * r) := by
      rw [heq']; exact Nat.mul_div_cancel _ hKpos
    have hsq : Nat.sqrt (N * d / kK e d) = d * r := by rw [hdiv, Nat.sqrt_eq]
    have hmem := h e (Nat.le_sqrt.mpr he2) he he2
      d (Nat.le_sqrt.mpr ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith))) hd hd2 hQ'
      ⟨(d * r) * (d * r), by rw [heq']; ring⟩ (by rw [hsq, hdiv]) (by rw [hsq]; exact Dvd.intro r rfl)
    rw [hsq, Nat.mul_div_cancel_left r hd] at hmem
    intro N' D' a0 a1 a2 a3
    exact hL (e, d, r) (List.contains_iff_mem.mp hmem) D' a0 a1 a2 a3
  · have hnd : ¬ (e + d - e) ∣ m := by rwa [Nat.add_sub_cancel_left]
    intro N' D' a0 a1 a2 a3
    exact Erdos634.Draft.Sqfree3Mod8.s3inst_of_not_dvd m e (e + d) he (by omega) hcop hm hnd D' a0 a1 a2 a3

/-- **The isosceles instances an `N` must supply, the listed pairs being carried as instances.** -/
theorem isoInstHyp_of_chkL {N : ℕ} (hN : 0 < N) (L : List (ℕ × ℕ)) (h : IsoChkL N L)
    (hL : ∀ p ∈ L, ∀ c₀ k : ℤ, 0 < c₀ → 0 < k → c₀ ^ 2 = (p.1 : ℤ) ^ 2 + (p.1 : ℤ) * p.2 + (p.2 : ℤ) ^ 2 →
      (p.2 : ℤ) * (N : ℤ) = k ^ 2 * ((p.1 : ℤ) + 2 * p.2) → IsoInst (p.1 : ℤ) (p.2 : ℤ) c₀ k) :
    IsoInstHyp N := by
  intro a b c k nA ha hb hc hk hcc h3 hcop hdvd hne harea hkc hpar
  have hle : a + 2 * b ≤ (N : ℤ) := Int.le_of_dvd (by exact_mod_cast hN) hdvd
  have hlt : a + 2 * b < (N : ℤ) := lt_of_le_of_ne hle hne
  lift a to ℕ using ha.le
  lift b to ℕ using hb.le
  have hc' := hc
  have hk' := hk
  lift c to ℕ using hc.le
  lift k to ℕ using hk.le
  have hdvd' : a + 2 * b ∣ N := by exact_mod_cast hdvd
  have hcc' : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by exact_mod_cast hcc
  have hcop' : Nat.gcd b (a + 2 * b) = 1 := by
    have : IsCoprime ((b : ℕ) : ℤ) (((a + 2 * b : ℕ)) : ℤ) := by exact_mod_cast hcop
    exact Nat.isCoprime_iff_coprime.mp this
  obtain ⟨n', hn'⟩ := hdvd'
  have hepos : 0 < a + 2 * b := by omega
  have hdiv : N / (a + 2 * b) = n' := by rw [hn']; exact Nat.mul_div_cancel_left _ hepos
  have hkq : k ^ 2 = b * n' := by
    have h1 : (b : ℤ) * (N : ℤ) = (k : ℤ) ^ 2 * (a + 2 * b) := by exact_mod_cast harea
    have h2 : b * N = k ^ 2 * (a + 2 * b) := by exact_mod_cast h1
    rw [hn'] at h2
    have h3' : (a + 2 * b) * (b * n') = (a + 2 * b) * k ^ 2 := by linarith [h2]
    exact (Nat.eq_of_mul_eq_mul_left hepos h3').symm
  have hsc : Nat.sqrt (a ^ 2 + a * b + b ^ 2) = c := by rw [← hcc']; exact Nat.sqrt_eq' c
  have hsk : Nat.sqrt (b * (N / (a + 2 * b))) = k := by rw [hdiv, ← hkq]; exact Nat.sqrt_eq' k
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have hnA : ((k : ℤ) * ((c : ℤ) - a - b)) / b = nA := by
    rw [hkc]; exact Int.mul_ediv_cancel nA hb0
  have hmod : ((k : ℤ) * ((c : ℤ) - a - b)) % b = 0 := Int.emod_eq_zero_of_dvd ⟨nA, by rw [hkc]; ring⟩
  have hpar' : ((nA - (N : ℤ)) % 2 = 0) := Int.emod_eq_zero_of_dvd hpar
  have hbad : IsoBad N a b := by
    unfold IsoBad
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hsc]; nlinarith [hcc']
    · rw [hsk, hdiv, ← hkq]; ring
    · rw [hsk, hsc]; exact hmod
    · rw [hsk, hsc, hnA]; exact hpar'
  have hmem := h (a + 2 * b) (by omega) (by omega) ⟨n', hn'⟩ b (by omega) (by exact_mod_cast hb) (by omega) hcop'
  rw [Nat.add_sub_cancel] at hmem
  intro N' D' hT hM
  exact hL (a, b) (List.contains_iff_mem.mp (hmem hbad)) c k hc' hk' hcc harea D' hT hM

/-! ## `N = 161` -/

/-- the base-`α` leaf of `161` from its one instance -/
theorem s3_161_of (h : S3Inst 1 3 4) : S3Closed 161 := by
  refine s3Closed_of_chkDL (by norm_num) [(3, 1, 1)] (by decide +kernel) ?_
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact h

/-- the list is sharp: without the instance the check fails -/
theorem s3_161_sharp : ¬ S3ChkDL 161 [] := by decide +kernel

/-- **`161` is not a tile count, given its one remaining instance**: the tile `(12, 7, 16)` on the isosceles
triangle with legs `112` and base `161`. -/
theorem not_tile_161_of (h : S3Inst 1 3 4) (D : CongruentDissection 161) : False :=
  not_tile_sqf_full 161 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (leafNSq_of_sq (by decide +kernel)) (leafHAr_of_sq (by decide +kernel)) (by decide +kernel)
    (leafS2_of_sq (by decide +kernel)) (s3_161_of h)
    (isoClosed_of_chk (by norm_num) (by decide +kernel))
    (gapE60_of_chk_sq (by norm_num) [] (by decide +kernel) (by intro p hp; cases hp))
    (gapE120_of_chk (by norm_num) (by decide +kernel))
    (gapF1_of_chksq (by norm_num) (by decide +kernel))
    (gapR8_of_chk_z (noF2Chk_of_sq (by decide +kernel)) (noF3zChk_of_sq (by decide +kernel))
      (noF4zChk_of_sq (by decide +kernel))) D

/-! ## `N = 154` -/

/-- the isosceles leaf of `154` from its one instance -/
theorem iso_154_of (h : IsoInst 8 7 13 7) : IsoClosed 154 := by
  refine isoClosed_of_inst 154 (isoInstHyp_of_chkL (by norm_num) [(8, 7)] (by decide +kernel) ?_)
  intro p hp c₀ k hc hk hcc harea
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  dsimp only at hcc harea ⊢
  push_cast at hcc harea
  have hc2 : c₀ ^ 2 = 169 := by linarith
  have hk2 : k ^ 2 = 49 := by linarith
  have e1 : c₀ = 13 := by
    have h13 : (c₀ - 13) * (c₀ + 13) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp h13 with h' | h' <;> omega
  have e2 : k = 7 := by
    have h7 : (k - 7) * (k + 7) = 0 := by linear_combination hk2
    rcases mul_eq_zero.mp h7 with h' | h' <;> omega
  subst e1 e2
  first
    | exact @h
    | (intro N' D' hT hM
       exact h D' (by simpa using hT) (by simpa using hM))

/-- the list is sharp -/
theorem iso_154_sharp : ¬ IsoChkL 154 [] := by decide +kernel

/-- **`154` is not a tile count, given its one remaining instance**: the tile `(8, 7, 13)` on the isosceles
triangle with legs `91` and base `154`. -/
theorem not_tile_154_of (h : IsoInst 8 7 13 7) (D : CongruentDissection 154) : False :=
  not_tile_sqf_full 154 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (leafNSq_of_sq (by decide +kernel)) (leafHAr_of_sq (by decide +kernel)) (by decide +kernel)
    (leafS2_of_sq (by decide +kernel)) (s3Closed_of_chkD (by norm_num) (s3ChkD_of_sq (by decide +kernel)))
    (iso_154_of h)
    (gapE60_of_mod4_two 154 (by norm_num))
    (gapE120_of_mod4_two 154 (by norm_num))
    (gapF1_of_mod4_two 154 (by norm_num))
    (gapR8_of_chk_z (noF2Chk_of_sq (by decide +kernel)) (noF3zChk_of_sq (by decide +kernel))
      (noF4zChk_of_sq (by decide +kernel))) D

end Erdos634.Draft.OpenRed

#print axioms Erdos634.Draft.OpenRed.not_tile_161_of
#print axioms Erdos634.Draft.OpenRed.not_tile_154_of
