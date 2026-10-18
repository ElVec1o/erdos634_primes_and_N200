import Erdos634.Draft.ThmCLeaf
import Erdos634.Draft.ThmDWords
import Erdos634.Draft.ThmDPair

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D', module 3: skeleton and G-leaf strengthening  (; `ThmDStatement` is now PROVED, see `ThmDStatementGeo`)

* `thmD_skeleton` : the logical wiring of conjV2.md Theorem D': the alpha-apex leg has `q ≥ 1` (D2), carries a
  both-ends-stopped c-run of length `≥ u` (D1, from Lemma K and Lemma 34'), but its word has `r < u`.
* `ThmDStatement` : Theorem D' in `GPairCert.GPair` form.  **PROVED** (`ThmDStatementGeo.thmDStatement_geo`, unconditional).  Historical remaining list: (D1) = Lemma K (stopped half,
  K2) + Lemma 34' over a real dissection, and (D2) the construction of the alpha-apex `RealLeg`
  (`APrimeLegBuild.exists_chain_leg`, `side_leg_counting`) together with the identification of its word with `(p,q,r)`.
* `caseG_of_gammaChkD` : `ThmDStatement → GammaChkD N → CaseGClosed N`.  Its hypothesis is discharged by `thmDStatement_geo`;
  used by `CN'zETD` (`ThmDChain`) and `CN'zETWD` (`ThmDChainW`).
-/

open scoped Classical

namespace Erdos634.Draft.ThmD

open Erdos634.Draft.GPairCert Erdos634.Draft.ChainComposite Erdos634.Draft.ThmC

theorem thmD_skeleton {u d g : ℕ} (hd : 0 < d) (hu : 0 < u) (hcop : Nat.Coprime u (u + d))
    (hcond : (g - 1) * d < u) (leg : ℕ × ℕ × ℕ)
    (hL : leg.1 * (u * u) + leg.2.1 * (d * (u + (u + d))) + leg.2.2 * (u * (u + d)) =
      g * u * (d * (u + (u + d))))
    (D2 : 1 ≤ leg.2.1) (D1 : u ≤ leg.2.2) : False := by
  have := leg_word_bound_D_lt hd hu hcop hcond D2 hL
  omega

/-- **Theorem D' in the G-leaf format.**  PROVED by `ThmDStatementGeo.thmDStatement_geo`. -/
noncomputable def ThmDStatement : Prop :=
  ∀ (N M M' : ℕ), 0 < M → M * M' = N → 3 * M < M' → M % 2 = M' % 2 → thmDChk M M' → GPair N (M : ℤ) (M' : ℤ)

def GammaChkD (N : ℕ) : Prop :=
  ∀ M ≤ N, 0 < M → M ∣ N → 3 * M < N / M → M % 2 = N % 2 → (N / M) % 2 = N % 2 →
    Nat.Coprime (((N / M) - M) / 2) N ∨ (M = 2 ∧ (N / M) % 4 = 2 ∧ 3 ≤ (N / M) / 4) ∨ thmDChk M (N / M)

section
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000
instance (N : ℕ) : Decidable (GammaChkD N) := by unfold GammaChkD; infer_instance
end

theorem caseG_of_gammaChkD (hD : ThmDStatement) {N : ℕ} (h : GammaChkD N) : CaseGClosed N := by
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
      exact hD N M M' hMpos hNM h3 (by omega) hk

end Erdos634.Draft.ThmD

#print axioms Erdos634.Draft.ThmD.thmD_skeleton
#print axioms Erdos634.Draft.ThmD.caseG_of_gammaChkD
