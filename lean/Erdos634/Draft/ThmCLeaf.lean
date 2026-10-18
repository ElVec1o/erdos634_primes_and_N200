import Erdos634.Draft.ThmCPair
import Erdos634.Draft.ThmCWords
import Erdos634.Draft.GPairArith
import Erdos634.Draft.NSQGammaChk

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem C, modules 4-6: skeleton, G-leaf strengthening  (; CONDITIONAL ON `ThmCStatement`)

**What is proved here.**
* `thmC_skeleton` : the logical wiring of conjV.md Theorem C, from three NAMED inputs
  (W) the side words of a real tiling, (D) the corner dichotomy, (L34) Lemma 34′.
* `ThmCStatement` : Theorem C in `GPairCert.GPair` form.  **NOT PROVED.**  Remaining: Lemma 34′ (row induction
  Lemmas 32′, 33′, 34′ over a real dissection, needing edge-level placement on interior segments) and (W).
* `caseG_of_gammaChkC` : `ThmCStatement → GammaChkC N → CaseGClosed N`, the G-leaf strengthening of
  `NSQGammaChk.GammaChk` by Theorem C.  Conditional, hence NOT used by any `CN'`; a theorem with an unproved
  hypothesis `ThmCStatement`, NOT a result.  The hypothesis is satisfiable (it is the audited-sound hand theorem; no known
  tiling satisfies the condition `thmCChk`, registry-consistent), but it is not witnessed by a formal object.
-/

open scoped Classical

namespace Erdos634.Draft.ThmC

open Erdos634.Draft.GPairCert Erdos634.Draft.ChainComposite

/-- **Skeleton of Theorem C.**  Words `(#a, #b, #c)` of the two legs and the base of `T(g)`, the corner dichotomy
(the tile at a base corner has `α` there, so its `b`-edge is on the leg or on the base), and Lemma 34′ in its two forms
(a leg whose corner tile has `b` on it carries `≥ u` edges `c`; if both corner tiles have `b` on the base, the base does). -/
theorem thmC_skeleton {u d g : ℕ} (hd : 0 < d) (hu : 0 < u) (hcop : Nat.Coprime u (u + d))
    (hcond : (g * (u + d) / u) * d < u)
    (legL legR base : ℕ × ℕ × ℕ)
    (hL : legL.1 * (u * u) + legL.2.1 * (d * (u + (u + d))) + legL.2.2 * (u * (u + d)) = g * u * (d * (u + (u + d))))
    (hR : legR.1 * (u * u) + legR.2.1 * (d * (u + (u + d))) + legR.2.2 * (u * (u + d)) = g * u * (d * (u + (u + d))))
    (hB : base.1 * (u * u) + base.2.1 * (d * (u + (u + d))) + base.2.2 * (u * (u + d)) =
      g * (u + d) * (d * (u + (u + d))))
    (bLegL bLegR bBaseL bBaseR : Prop) (hdL : bLegL ∨ bBaseL) (hdR : bLegR ∨ bBaseR)
    (L34L : bLegL → u ≤ legL.2.2) (L34R : bLegR → u ≤ legR.2.2)
    (L34B : bBaseL → bBaseR → u ≤ base.2.2) : False := by
  have rL := leg_word_bound hd hu hcop hcond hL
  have rR := leg_word_bound hd hu hcop hcond hR
  have rB := base_word_bound hd hu hcop hcond hB
  have nL : ¬ bLegL := fun h => absurd (L34L h) (by omega)
  have nR : ¬ bLegR := fun h => absurd (L34R h) (by omega)
  exact absurd (L34B (hdL.resolve_left nL) (hdR.resolve_left nR)) (by omega)

/-- **Theorem C in the G-leaf format.**  NOT PROVED (remaining: Lemma 34′ and (W); see the header). -/
noncomputable def ThmCStatement : Prop :=
  ∀ (N M M' : ℕ), 0 < M → M * M' = N → 3 * M < M' → M % 2 = M' % 2 → thmCChk M M' → GPair N (M : ℤ) (M' : ℤ)

/-- the decidable G-leaf check with Theorem C: every admissible pair is a coprime pair (`gPair_of_coprime`), a leaf-G pair
`(2, 2(2k+1))` (`gPair_of_leafG`), or satisfies Theorem C's condition. -/
def GammaChkC (N : ℕ) : Prop :=
  ∀ M ≤ N, 0 < M → M ∣ N → 3 * M < N / M → M % 2 = N % 2 → (N / M) % 2 = N % 2 →
    Nat.Coprime (((N / M) - M) / 2) N ∨ (M = 2 ∧ (N / M) % 4 = 2 ∧ 3 ≤ (N / M) / 4) ∨ thmCChk M (N / M)

noncomputable instance (N : ℕ) : Decidable (GammaChkC N) := by unfold GammaChkC; infer_instance

/-- `GammaChk N → GammaChkC N`: the new check only weakens the old one. -/
theorem gammaChkC_of_chk {N : ℕ} (h : Erdos634.Draft.NSQLegs.GammaChk N) : GammaChkC N :=
  fun M hM hM0 hdv h3 hp hp' => Or.inl (h M hM hM0 hdv h3 hp hp')

/-- **`CaseGClosed N` from Theorem C.**  CONDITIONAL on `ThmCStatement`. -/
theorem caseG_of_gammaChkC (hC : ThmCStatement) {N : ℕ} (h : GammaChkC N) : CaseGClosed N := by
  refine caseG_of_pairs N
    (((List.range (N + 1)).filter (fun M => decide (0 < M ∧ M ∣ N ∧ 3 * M < N / M ∧ M % 2 = N % 2 ∧
      (N / M) % 2 = N % 2))).map (fun (M : ℕ) => ((M : ℤ), ((N / M : ℕ) : ℤ)))) ?_ ?_
  · intro M M' hM hM' hNM hp hp' hlt
    lift M to ℕ using hM.le
    lift M' to ℕ using hM'.le
    have hNM' : M * M' = N := by exact_mod_cast hNM.symm
    have hMpos : 0 < M := by exact_mod_cast hM
    have hdiv : N / M = M' := by rw [← hNM']; exact Nat.mul_div_cancel_left _ hMpos
    have hM'0 : 0 < M' := by exact_mod_cast hM'
    have hle : M ≤ N := by rw [← hNM']; exact Nat.le_mul_of_pos_right M hM'0
    have h3 : 3 * M < N / M := by rw [hdiv]; exact_mod_cast hlt
    have h4 : M % 2 = N % 2 := by omega
    have h5 : N / M % 2 = N % 2 := by rw [hdiv]; omega
    have hdv : M ∣ N := ⟨M', hNM'.symm⟩
    have hmem : M ∈ (List.range (N + 1)).filter (fun (M : ℕ) => decide (0 < M ∧ M ∣ N ∧ 3 * M < N / M ∧ M % 2 = N % 2 ∧
      (N / M) % 2 = N % 2)) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.lt_succ_of_le hle), decide_eq_true ⟨hMpos, hdv, h3, h4, h5⟩⟩
    refine List.mem_map.mpr ⟨M, hmem, ?_⟩
    rw [hdiv]
  · intro p hp
    simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hp
    obtain ⟨M, ⟨hMle, hMpos, hMdvd, h3, hp1, hp2⟩, rfl⟩ := hp
    obtain ⟨M', hM'⟩ := hMdvd
    have hdiv : N / M = M' := by rw [hM']; exact Nat.mul_div_cancel_left _ hMpos
    have hNM : M * M' = N := hM'.symm
    show GPair N (M : ℤ) ((N / M : ℕ) : ℤ)
    rw [hdiv]
    rw [hdiv] at h3 hp2
    rcases h M (Nat.lt_succ_iff.mp hMle) hMpos ⟨M', hM'⟩ (by rw [hdiv]; exact h3) hp1 (by rw [hdiv]; exact hp2) with hc | hl | hk
    · rw [hdiv] at hc
      exact Erdos634.Draft.GPairArith.gPair_of_coprime N M M' hMpos hNM hc
    · rw [hdiv] at hl
      obtain ⟨rfl, h4, h5⟩ := hl
      have : (M' : ℤ) = 2 * (2 * ((M' / 4 : ℕ) : ℤ) + 1) := by omega
      rw [this]
      exact gPair_of_leafG N (M' / 4) h5
    · rw [hdiv] at hk
      exact hC N M M' hMpos hNM h3 (by omega) hk

end Erdos634.Draft.ThmC

#print axioms Erdos634.Draft.ThmC.thmC_skeleton
#print axioms Erdos634.Draft.ThmC.caseG_of_gammaChkC
