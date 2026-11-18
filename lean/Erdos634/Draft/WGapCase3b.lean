/-
Draft/WGapCase3b.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 Case 3).
Not imported by any aggregate.  Module P-D3: `claim_S`: the far-side tile `phi0` with its `c`-edge `[X0, C0]` on `l'_c` (`FlipAt c js`, clamped at `X0` by `ClampB`) forces some far-side chain edge to
STRADDLE `Y = X0 - m u` (`m <= f-1`): otherwise the run `[X0, Y]` is clamped at both ends and by (A1) (`chain_edge_len_b`) every chain edge in it has length `b`, but `phi0`'s edge has length `c` (if `c <= m b` it lies
in the run; if `c > m b` it itself straddles `Y`).  The hypotheses `hint`, `hwall` for the open run are parameters here (discharged in `WGapCase3c`).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapCase3a

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

theorem hasV_edge_pts {t : Fin N} {A B C : Plane} (h : HasV D t A B C) :
    ∃ k : Fin 3, (D.tile t).edge k = segment ℝ A B ∧
      (((D.tile t).pts k = A ∧ (D.tile t).pts (k + 1) = B) ∨ ((D.tile t).pts k = B ∧ (D.tile t).pts (k + 1) = A)) := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  rcases fin3_adj k m hkm with h' | h'
  · refine ⟨k, ?_, Or.inl ⟨hk, by rw [← h']; exact hm⟩⟩
    simp only [Tri.edge]; rw [← h', hk, hm]
  · refine ⟨m, ?_, Or.inr ⟨hm, by rw [← h']; exact hk⟩⟩
    simp only [Tri.edge]; rw [← h', hk, hm, segment_symm]

/-- points of the line `X - t u` strictly between two of its points are in the open segment -/
theorem lin_openSeg (X u : Plane) {a b t : ℝ} (hab : a ≠ b) (h : (b < t ∧ t < a) ∨ (a < t ∧ t < b)) :
    X - t • u ∈ openSegment ℝ (X - a • u) (X - b • u) := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  refine ⟨(t - b) / (a - b), (a - t) / (a - b), ?_, ?_, ?_, ?_⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_pos (by linarith) (by linarith)
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_pos (by linarith) (by linarith)
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · field_simp; ring
  · ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp; ring

theorem lin_seg (X u : Plane) {a b t : ℝ} (hab : a ≠ b) (h : (b ≤ t ∧ t ≤ a) ∨ (a ≤ t ∧ t ≤ b)) :
    X - t • u ∈ segment ℝ (X - a • u) (X - b • u) := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  refine ⟨(t - b) / (a - b), (a - t) / (a - b), ?_, ?_, ?_, ?_⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_nonneg (by linarith) (by linarith)
    · exact div_nonneg_of_nonpos (by linarith) (by linarith)
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_nonneg (by linarith) (by linarith)
    · exact div_nonneg_of_nonpos (by linarith) (by linarith)
  · field_simp; ring
  · ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp; ring

section case3b

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 2000000 in
theorem claim_S (S : SetupG D e f α β γ L ax ay) {c js m : ℕ} (hm1 : 1 ≤ m) (hmf : m ≤ f - 1)
    (hflip : FlipAt D e f c js) (hCl : ClampB D e f c js)
    (hint : openSegment ℝ (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f c js) (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ)) ⊆
      interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f c js) (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ)),
      ∀ i, y ∉ interior (D.tile i).carrier) :
    ∃ ed ∈ D.lineChain (crossL (ub e f c js)) (cross (ub e f c js) (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ))),
      Straddles ((D.tile ed.1).edge ed.2) (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f c js - ub e f c js)
        (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f c js) (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ)) := by
  by_contra hno
  push_neg at hno
  have he0 := S.e0
  have hef := S.hef'
  have hb0 := S.b_pos
  have hf2 := S.c_pos
  have hν0 := nuG_pos he0 hef
  have hν1 := nuG_lt_one he0 hef
  have hνs := nuG_spec he0 hef
  obtain ⟨O, E1, E2, hm⟩ := mpG_affine he0 hef
  obtain ⟨φ, hφ⟩ := hflip
  set X₀ := mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) with hX₀
  set u := ub e f c js with hu
  set ν := nuG (e : ℝ) f with hν
  have hu0 : u ≠ 0 := ub_ne S c js
  set F := crossL u with hF
  set cc := cross u X₀ with hcc
  have hFX : F X₀ = cc := crossL_apply _ _
  have hFu : F u = 0 := by rw [hF, crossL_apply]; simp [cross]; ring
  have hFl : ∀ s : ℝ, F (X₀ + s • u) = cc := by
    intro s; rw [map_add, map_smul, hFu, hFX]; simp
  have hC0 : mpG (e : ℝ) f 1 0 (c : ℝ) ((js : ℝ) + 1 / ν) = X₀ - (1 / ν) • u := by
    rw [hX₀, hu]; unfold ub; simp only [hm]
    ext x; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  set C0 := mpG (e : ℝ) f 1 0 (c : ℝ) ((js : ℝ) + 1 / ν) with hC0def
  set B0 := mpG (e : ℝ) f 1 0 ((c : ℝ) + ν) (js : ℝ) with hB0
  have hFC0 : F C0 = cc := by
    have := hFl (-(1 / ν)); rw [hC0]; simpa [sub_eq_add_neg] using this
  have hFB0 : F B0 ≤ cc := by
    have hcr : cross u (B0 - X₀) < 0 := by
      rw [hu, hX₀, hB0]; unfold ub
      rw [cross_mpG he0 hef]
      have := kapG_pos he0 hef
      have e1 : ((c : ℝ) - (c : ℝ)) * ((js : ℝ) - (js : ℝ)) - ((js : ℝ) - ((js : ℝ) + 1)) * ((c : ℝ) + ν - (c : ℝ)) = ν := by ring
      rw [e1]; nlinarith
    have h1 : F B0 = cross u (B0 - X₀) + cc := by
      rw [hF, crossL_apply, hcc, ← cross_add_right]; congr 1; abel
    linarith
  -- the tile phi and its edge [X0, C0]
  obtain ⟨k, hk, hkpts⟩ := hasV_edge_pts (hφ.rot.rot.swap : HasV D φ X₀ C0 B0)
  have hmemφ : (φ, k) ∈ D.lineChain F cc := by
    rw [Dissection.mem_lineChain]
    have hall : ∀ i, F ((D.tile φ).pts i) ≤ cc :=
      hφ.all (P := fun z => F z ≤ cc) (le_of_eq hFX) hFB0 (le_of_eq hFC0)
    refine ⟨?_, ?_, hall⟩
    · rcases hkpts with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only [] <;> rw [h1] <;> [exact hFX; exact hFC0]
    · rcases hkpts with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp only [] <;> rw [h1] <;> [exact hFC0; exact hFX]
  have hdistC : dist X₀ C0 = (f : ℝ) ^ 2 :=
    dist_mpG he0 hef 0 hf2.le (qf_flip1 he0 hef (c : ℝ) (js : ℝ))
  have hdedge : dist ((D.tile φ).pts k) ((D.tile φ).pts (k + 1)) = (f : ℝ) ^ 2 := by
    rcases hkpts with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hdistC
    · rw [h1, h2, dist_comm]; exact hdistC
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hY : X₀ - (m : ℝ) • u = X₀ + (-(m : ℝ)) • u := by rw [sub_eq_add_neg, neg_smul]
  have hseg1 : (D.tile φ).edge k = segment ℝ X₀ C0 := hk
  by_cases hcase : 1 / ν ≤ (m : ℝ)
  · -- the c-edge lies inside the run: contradiction with (A1)
    have hfP : F (X₀ - (m : ℝ) • u) = cc := by rw [hY]; exact hFl _
    have hfP' : F (X₀ - (m : ℝ) • u - u) = cc := by
      have := hFl (-((m : ℝ) + 1)); convert this using 2; ext x; simp [sub_eq_add_neg]; ring
    have hfQ' : F (X₀ + u) = cc := by simpa using hFl 1
    have hPQ : X₀ - (m : ℝ) • u ≠ X₀ := by
      intro h
      have : (m : ℝ) • u = 0 := by
        have := congrArg (fun z => X₀ - z) h
        simpa using this
      rcases smul_eq_zero.mp this with h0 | h0
      · exact hmpos.ne' h0
      · exact hu0 h0
    have hP' : X₀ - (m : ℝ) • u ∈ openSegment ℝ (X₀ - (m : ℝ) • u - u) X₀ := by
      refine ⟨(m : ℝ) / (m + 1), 1 / (m + 1), by positivity, by positivity, (by first | (field_simp; done) | (field_simp; ring)), ?_⟩
      ext x
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp; ring
    have hQ' : X₀ ∈ openSegment ℝ (X₀ - (m : ℝ) • u) (X₀ + u) := by
      refine ⟨1 / (1 + m), (m : ℝ) / (1 + m), by positivity, by positivity, (by first | (field_simp; done) | (field_simp; ring)), ?_⟩
      ext x
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp; ring
    have hdPQ : dist (X₀ - (m : ℝ) • u) X₀ = (m : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hmpos, hu, ub_norm S c js]
    have hC0mem : C0 ∈ segment ℝ (X₀ - (m : ℝ) • u) X₀ := by
      rw [hC0]
      have := lin_seg X₀ u (a := (m : ℝ)) (b := 0) (t := 1 / ν) hmpos.ne' (Or.inl ⟨by linarith [one_div_pos.mpr hν0], hcase⟩)
      simpa using this
    have hsub : (D.tile φ).edge k ⊆ segment ℝ (X₀ - (m : ℝ) • u) X₀ := by
      rw [hseg1]
      exact (convex_segment _ _).segment_subset (right_mem_segment ℝ _ _) hC0mem
    have hQ := hCl (m : ℝ) hmpos
    have := chain_edge_len_b S hm1 hmf F (crossL_ne_zero hu0) cc hPQ hfP hFX hfP' hfQ' hP' hQ' hint hwall
      (hno) (by intro ed hed; exact hQ ed hed) hdPQ hmemφ hsub
    rw [hdedge] at this
    nlinarith [pow_pos he0 2]
  · -- the c-edge sticks out beyond Y: it straddles Y
    push_neg at hcase
    have hν1' : (0 : ℝ) < 1 / ν - m := by linarith
    set δ : ℝ := min 1 (1 / ν - m) / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; have := lt_min one_pos hν1'; linarith
    have hδ1 : δ < 1 := by rw [hδ]; have := min_le_left (1 : ℝ) (1 / ν - m); linarith
    have hδ2 : δ < 1 / ν - m := by rw [hδ]; have := min_le_right (1 : ℝ) (1 / ν - m); linarith [lt_min one_pos hν1']
    refine absurd ?_ (hno (φ, k) hmemφ)
    refine ⟨⟨X₀ - ((m : ℝ) + δ) • u, ?_, ?_⟩, ⟨X₀ - ((m : ℝ) / 2) • u, ?_, ?_⟩⟩
    · show _ ∈ (D.tile φ).edge k
      rw [hseg1, hC0]
      have := lin_seg X₀ u (a := 0) (b := 1 / ν) (t := (m : ℝ) + δ) (by have := one_div_pos.mpr hν0; linarith)
        (Or.inr ⟨by linarith, by linarith⟩)
      simpa using this
    · have := lin_openSeg X₀ u (a := (m : ℝ) + 1) (b := (m : ℝ)) (t := (m : ℝ) + δ) (by linarith) (Or.inl ⟨by linarith, by linarith⟩)
      convert this using 2
      ext x; simp [sub_eq_add_neg]; ring
    · show _ ∈ (D.tile φ).edge k
      rw [hseg1, hC0]
      have := lin_seg X₀ u (a := 0) (b := 1 / ν) (t := (m : ℝ) / 2) (by have := one_div_pos.mpr hν0; linarith)
        (Or.inr ⟨by linarith, by linarith⟩)
      simpa using this
    · have := lin_openSeg X₀ u (a := (m : ℝ)) (b := 0) (t := (m : ℝ) / 2) hmpos.ne' (Or.inl ⟨by linarith, by linarith⟩)
      simpa using this

end case3b

end Erdos634.Draft.WGapStmt
