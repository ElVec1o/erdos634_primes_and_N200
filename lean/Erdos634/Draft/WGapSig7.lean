/-
Draft/WGapSig7.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.5 (b1)).
Not imported by any aggregate.  No sorry, no native_decide.
`sigma_row_nob`: **no `b`-edge above `Λ`** (P7.5 (b1)): by the partition (P) of the row `Λ = [p(0,j+1), p(q,j+1)]` (both ends clamped, `D(i,j)` below) and Lemma A5 (`1 ≤ q ≤ f−2`) every
edge on the row line of a tile above it, contained in a unit step, has length `≠ b`.  This is `hnobstep` of the proof of `CtxJ.rowJ` (verbatim), as a lemma.
-/
import Erdos634.Draft.WGapSig6

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

variable {N : ℕ} {D : CongruentDissection N}

section sig7

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

theorem sigma_row_nob (C : CtxBase D e f α β γ L ax ay ε x) {j q : ℕ} (hq : 1 ≤ q) (hqj : q + j + 1 ≤ f)
    (hD : ∀ i' : ℕ, i' < q → DTG D (e : ℝ) (f : ℝ) ε x i' j)
    (hcl : ∃ Q' : Plane, GHG (f : ℝ) Q' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) ∧
      lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1) ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) Q' ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)))
    (hclL : ∃ P' : Plane, GHG (f : ℝ) P' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) ∧
      lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1) ∈ openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1))) :
    ∀ ρ : ℝ, 0 ≤ ρ → ρ + 1 ≤ q →
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
      (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x ρ ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) ((j : ℝ) + 1)) →
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  classical
  have S := C.S
  have hε := C.e2
  have he0 := S.e0
  have hef := S.hef'
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  -- the row segment
  have hA0q : lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1) ≠ lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1) := lpG_ne_xi he0 hef hε hqpos.ne
  have hfA0 : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) := GHG_lp _ _ _ _ _ _
  have hfAq : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) := GHG_lp _ _ _ _ _ _
  obtain ⟨P', hfP', hP', hPcl⟩ := hclL
  obtain ⟨tD0, hD0⟩ := hD 0 (by omega)
  rw [Nat.cast_zero] at hD0
  obtain ⟨tDq, hDq⟩ := hD (q - 1) (by omega)
  have hcq : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq, Nat.cast_one]
  rw [hcq] at hDq
  have hAq_mem : lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1) ∈ D.target.carrier := by
    have := hDq.mem₃
    rwa [show (q : ℝ) - 1 + 1 = q by ring] at this
  have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1))
      ⊆ interior D.target.carrier :=
    C.seg_intG hD0.mem₂ hAq_mem (Or.inl (by linarith)) (Or.inl ⟨1, one_pos, hD0.mem₃⟩)
      (Or.inr ⟨1, one_pos, hDq.mem₂⟩)
  have hwall : ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    have hy' : y ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) ε x (0 + (q : ℝ) * 1) ((j : ℝ) + 1 + (q : ℝ) * 0)) := by
      rw [show lpG (e : ℝ) (f : ℝ) ε x (0 + (q : ℝ) * 1) ((j : ℝ) + 1 + (q : ℝ) * 0) = lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1) from
        lpG_congr (by ring) (by ring)]
      exact openSegment_subset_segment ℝ _ _ hy
    obtain ⟨i', hi', hyi⟩ := seg_split_lpG hq hy'
    obtain ⟨t, k, m, j₃, hkm, hkj, hmj, hk, hm, hj⟩ := hD i' hi'
    refine seg_wall D.toDissection (t := t) hmj ?_
    rw [hm, hj]
    rw [show lpG (e : ℝ) (f : ℝ) ε x (0 + (i' : ℝ) * 1) ((j : ℝ) + 1 + (i' : ℝ) * 0) = lpG (e : ℝ) (f : ℝ) ε x i' ((j : ℝ) + 1) from
      lpG_congr (by ring) (by ring),
      show lpG (e : ℝ) (f : ℝ) ε x (0 + ((i' : ℝ) + 1) * 1) ((j : ℝ) + 1 + ((i' : ℝ) + 1) * 0)
        = lpG (e : ℝ) (f : ℝ) ε x ((i' : ℝ) + 1) ((j : ℝ) + 1) from lpG_congr (by ring) (by ring)] at hyi
    exact hyi
  obtain ⟨Q', hfQ', hQ', hQc⟩ := hcl
  have hpart := run_partition D.toDissection (GHG (f : ℝ)) (GHG_ne he0 hef) _ hA0q hfP' hfQ' hP' hQ'
    (CSlot.segment_subset_level (GHG (f : ℝ)) _ hfA0 hfAq) hint hwall
    hPcl hQc
  have hdq : dist (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) = (q : ℝ) * (f : ℝ) ^ 2 := by
    rw [dist_rowG he0 hef hε (by linarith : (0 : ℝ) ≤ q)]; ring
  have hnobΛ : ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
      (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) →
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    intro ed he hsub hb
    obtain ⟨x', y', z', hxyz⟩ := sum_split_semigroup _ _ ((e : ℝ) * (f : ℝ)) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) _
      (fun e' _ => edge_length_casesG D S.hM e'.1 e'.2) (Finset.mem_filter.mpr ⟨he, hsub⟩) hpart
    rw [hdq, hb] at hxyz
    have := SideRunGArith.A5 S.he S.hef S.hco hq (by omega)
      (rep_nat_c S.hef (x := x') (y := y' + 1) (z := z') (by push_cast; linarith))
    omega
  have hrowmem : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ q →
      lpG (e : ℝ) (f : ℝ) ε x ρ ((j : ℝ) + 1) ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) := by
    intro ρ h0 h1
    have h := lp_mem_segG (e := (e : ℝ)) (f := (f : ℝ)) (ε := ε) (x := x) (ξ := 0) (η := (j : ℝ) + 1)
      (ξ' := q) (η' := (j : ℝ) + 1) (τ := ρ / q) (div_nonneg h0 hqpos.le)
      (by rw [div_le_one hqpos]; exact h1)
    rw [show lpG (e : ℝ) (f : ℝ) ε x (0 + ρ / (q : ℝ) * ((q : ℝ) - 0))
          ((j : ℝ) + 1 + ρ / (q : ℝ) * ((j : ℝ) + 1 - ((j : ℝ) + 1)))
        = lpG (e : ℝ) (f : ℝ) ε x ρ ((j : ℝ) + 1) from
      lpG_congr (by rw [sub_zero, div_mul_cancel₀ _ hqpos.ne', zero_add]) (by ring)] at h
    exact h
  have hnobstep : ∀ ρ : ℝ, 0 ≤ ρ → ρ + 1 ≤ q →
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
      (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x ρ ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) ((j : ℝ) + 1)) →
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    intro ρ h0 h1 ed he hsub
    exact hnobΛ ed he (hsub.trans ((convex_segment _ _).segment_subset
      (hrowmem ρ h0 (by linarith)) (hrowmem (ρ + 1) (by linarith) h1)))

  exact hnobstep

end sig7

#print axioms sigma_row_nob

end Erdos634.Draft.WGapStmt
