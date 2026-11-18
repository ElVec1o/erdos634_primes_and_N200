/-
Draft/WGapSig19.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.3: "if F lays `b` on `[O,Y]`, `c − b ∈ S`, against (A5) with `m = 1`").
Not imported by any aggregate.  No sorry, no native_decide.
`chord_no_b`: on a clamped chord `[X,Y]` of length `c` (both ends clamped, open part interior and wall) no tile on the chain's side has a `b`-edge `[X, X + ν (Y − X)]` starting at `X`.
(Pattern of `no_c_edge`/`sigma_row_nob`: edge into `lineChain`, `run_partition`, `sum_split_semigroup`, A5.)
-/
import Erdos634.Draft.WGapSig18

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

section sig19

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem chord_no_b (S : SetupG D e f α β γ L ax ay) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {X Y P' Q' : Plane} (hXY : X ≠ Y) (hfX : F X = c) (hfY : F Y = c) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : X ∈ openSegment ℝ P' Y) (hQ' : Y ∈ openSegment ℝ X Q')
    (hint : openSegment ℝ X Y ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ X Y, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y)
    (hQ : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q' Y X)
    (hd : dist X Y = (f : ℝ) ^ 2) {τ : Fin N} {R : Plane}
    (hV : HasV D τ X (X + nuG (e : ℝ) f • (Y - X)) R) (hR : F R < c) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hν := nuG_spec he0 hef
  have hν0 : 0 < nuG (e : ℝ) f := by
    unfold nuG; exact div_pos (by nlinarith) hf2
  have hν1 : nuG (e : ℝ) f ≤ 1 := by
    unfold nuG; rw [div_le_one hf2]; nlinarith [pow_pos he0 2]
  have hfPb : F (X + nuG (e : ℝ) f • (Y - X)) = c := by
    rw [map_add, map_smul, map_sub, hfX, hfY]; simp
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hjR⟩ := hV
  have hWle : ∀ i : Fin 3, F ((D.tile τ).pts i) ≤ c := by
    intro i
    rcases fin3_cover k m j hkm hkj hmj i with h | h | h
    · rw [h, hk]; exact hfX.le
    · rw [h, hm]; exact hfPb.le
    · rw [h, hjR]; exact hR.le
  have hlen : dist ((D.tile τ).pts k) ((D.tile τ).pts m) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hk, hm, dist_eq_norm, show X - (X + nuG (e : ℝ) f • (Y - X)) = -(nuG (e : ℝ) f • (Y - X)) by abel,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hν0, ← dist_eq_norm, dist_comm, hd]
    linarith
  have hed : ∃ ed : Fin N × Fin 3, ed ∈ D.lineChain F c ∧
      (D.tile ed.1).edge ed.2 = segment ℝ X (X + nuG (e : ℝ) f • (Y - X)) ∧
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rcases fin3_adj k m hkm with h | h
    · refine ⟨(τ, k), Dissection.mem_lineChain.mpr ⟨?_, ?_, hWle⟩, ?_, ?_⟩
      · simp only; rw [hk]; exact hfX
      · simp only; rw [← h, hm]; exact hfPb
      · show segment ℝ ((D.tile τ).pts k) ((D.tile τ).pts (k + 1)) = _
        rw [← h, hk, hm]
      · simp only; rw [← h]; exact hlen
    · refine ⟨(τ, m), Dissection.mem_lineChain.mpr ⟨?_, ?_, hWle⟩, ?_, ?_⟩
      · simp only; rw [hm]; exact hfPb
      · simp only; rw [← h, hk]; exact hfX
      · show segment ℝ ((D.tile τ).pts m) ((D.tile τ).pts (m + 1)) = _
        rw [← h, hk, hm, segment_symm]
      · simp only; rw [← h, dist_comm]; exact hlen
  obtain ⟨ed, hedm, hedseg, hedlen⟩ := hed
  have hsub : (D.tile ed.1).edge ed.2 ⊆ segment ℝ X Y := by
    rw [hedseg]
    refine (convex_segment X Y).segment_subset (left_mem_segment ℝ _ _) ?_
    rw [segment_eq_image_lineMap]
    exact ⟨nuG (e : ℝ) f, ⟨hν0.le, hν1⟩, by rw [AffineMap.lineMap_apply]; simp [add_comm]⟩
  have hpart := run_partition D.toDissection F hF c hXY hfP' hfQ' hP' hQ'
    (CSlot.segment_subset_level F _ hfX hfY) hint hwall hP hQ
  obtain ⟨x', y', z', hxyz⟩ := sum_split_semigroup _ _ ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) _
    (fun e' _ => edge_length_casesG D S.hM e'.1 e'.2) (Finset.mem_filter.mpr ⟨hedm, hsub⟩) hpart
  rw [hd, hedlen] at hxyz
  have h5 := SideRunGArith.A5 S.he S.hef S.hco (j := 1) le_rfl (by have := S.he; have := S.hef; omega)
    (rep_nat_c S.hef (x := x') (y := y' + 1) (z := z') (by push_cast; linarith))
  omega

end sig19

end Erdos634.Draft.WGapStmt
