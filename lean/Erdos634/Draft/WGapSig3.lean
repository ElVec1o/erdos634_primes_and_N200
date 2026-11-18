/-
Draft/WGapSig3.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.5 step (b), (b3)).
Not imported by any aggregate.  No sorry, no native_decide.
`sigma_rowB`: **the row `y₀+1` above `Λ`** = `SideRunGJ.CtxJ.rowJ` with the (K1) chord tile `φ` replaced by (i) the LEFT clamp of `Λ` (`hclL`, from the tile `E_{y₀}`) and (ii) the
first tile `U(0,y₀+1)` (`hU0`, from (b2): `Z*`, `U3`); the claim `K` of smaller size at the row `j+1` is the hypothesis `hA` (`AGJ ... (j+1)`: it holds when `T⁺` lays `c` (Theorem K at
`js = y₀+1`) or when `T⁺ = E_{y₀+1}` (Σ at the same apex at level `y₀+1`)).  The proof is the proof of `rowJ` for `r ≥ 1` (`row_stepG`, `row_badG`, partition `run_partition`, `A5`).
-/
import Erdos634.Draft.WGapSig2
import Erdos634.Draft.SideRunGJRow

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

section sig3

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

theorem sigma_rowB (C : CtxBase D e f α β γ L ax ay ε x) {j q : ℕ} (hq : 1 ≤ q) (hqj : q + j + 1 ≤ f)
    (hUr : ∀ i' j' : ℕ, j' ≤ j → i' + j' ≤ q + j → UTG D (e : ℝ) (f : ℝ) ε x i' j')
    (hDr : ∀ i' j' : ℕ, j' < j → i' + j' + 1 ≤ q + j → DTG D (e : ℝ) (f : ℝ) ε x i' j')
    (hD : ∀ i' : ℕ, i' < q → DTG D (e : ℝ) (f : ℝ) ε x i' j)
    (hcl : ∃ Q' : Plane, GHG (f : ℝ) Q' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) ∧
      lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1) ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) Q' ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)))
    (hclL : ∃ P' : Plane, GHG (f : ℝ) P' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) ∧
      lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1) ∈ openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)))
    (hU0 : UTG D (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1))
    (hA : ∀ m' : ℕ, 1 ≤ m' → m' < q → AGJ D e f ε x (j + 1) m') :
    ∀ r : ℕ, r < q → UTG D (e : ℝ) (f : ℝ) ε x r ((j : ℝ) + 1) := by
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
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · subst hr0
      rw [Nat.cast_zero]
      exact hU0
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [Nat.cast_add, Nat.cast_one]
      obtain ⟨t₃, h3⟩ := hD (r' + 1) hr
      rw [Nat.cast_add, Nat.cast_one] at h3
      obtain ⟨t₁, h1⟩ := hD r' (by omega)
      obtain ⟨t₂, h2⟩ := hUr (r' + 1) j le_rfl (by omega)
      rw [Nat.cast_add, Nat.cast_one] at h2
      obtain ⟨t₄, h4⟩ := ih r' (by omega) (by omega)
      have hr'0 : (0 : ℝ) ≤ r' := Nat.cast_nonneg r'
      have hr'q : (r' : ℝ) + 1 + 1 ≤ q := by
        have h' : r' + 1 + 1 ≤ q := hr
        exact_mod_cast h'
      have hclV : ∃ P'' : Plane, GHG (f : ℝ) P'' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) ∧
          lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1) ((j : ℝ) + 1) ∈ openSegment ℝ P'' (lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1 + 1) ((j : ℝ) + 1)) ∧
          ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
            ¬ Straddles ((D.tile ed.1).edge ed.2) P'' (lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1) ((j : ℝ) + 1))
              (lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1 + 1) ((j : ℝ) + 1)) := by
        have hle4 := h4.all (P := fun p => GHG (f : ℝ) p ≤ -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)))
          (GHG_le he0 hef le_rfl) (GHG_le he0 hef le_rfl) (GHG_le he0 hef (by linarith))
        obtain ⟨k4, m4, j4, hkm4, -, -, hk4, hm4, -⟩ := h4
        have hVW : lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1) ((j : ℝ) + 1) ≠ lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1 + 1) ((j : ℝ) + 1) :=
          lpG_ne_xi he0 hef hε (by linarith)
        have hP'' : lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1) ((j : ℝ) + 1)
            ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x r' ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1 + 1) ((j : ℝ) + 1)) := by
          refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
          unfold lpG
          apply plane_ext <;>
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
        exact ⟨_, GHG_lp _ _ _ _ _ _, hP'', clamp_b D.toDissection (GHG (f : ℝ)) (GHG_ne he0 hef) _ hVW
          (GHG_lp _ _ _ _ _ _) (GHG_lp _ _ _ _ _ _) (GHG_lp _ _ _ _ _ _) hP'' hkm4 hk4 hm4 hle4⟩
      rcases C.row_stepG h3 hj0 hclV (hnobstep ((r' : ℝ) + 1) (by linarith) hr'q) with
        hU | ⟨ix, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle, hθ, hno⟩
      · exact hU
      · exfalso
        refine C.row_badG h1 h2 h3 h4 ht hm hle hθ
          (fun i hi => hno i (by rw [hi]; exact lpG_congr (by ring) rfl)) (fun w hw => ?_)
        refine hA (r' + 1) (by omega) hr (r' + 1 + j + 1) (j + 1) (by omega) (by omega) (by omega) (by omega)
          ⟨?_, ?_⟩ ?_
        · intro i' j' hj' hij'
          rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
          · exact hUr i' j' (by omega) (by omega)
          · have hje : j' = j + 1 := by omega
            subst hje
            have h := ih i' (by omega) (by omega)
            rw [Nat.cast_add, Nat.cast_one]
            exact h
        · intro i' j' hj' hij'
          rcases Nat.lt_or_ge j' j with hlt | hge
          · exact hDr i' j' hlt (by omega)
          · have hje : j' = j := by omega
            subst hje
            exact hD i' (by omega)
        · have e1 : (((r' + 1 + j + 1 : ℕ)) : ℝ) = (r' : ℝ) + ((j : ℝ) + 1) + 1 := by
            push_cast; ring
          have e2 : (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
          rw [e1, e2]
          exact Or.inr ⟨w, hw⟩

end sig3

#print axioms sigma_rowB

end Erdos634.Draft.WGapStmt
