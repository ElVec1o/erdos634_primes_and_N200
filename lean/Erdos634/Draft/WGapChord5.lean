/-
Draft/WGapChord5.lean -- written 15 November 2026 (session 4).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 chord facts (C); FINDINGS F8).
Not imported by any aggregate.  Module W6b: `no_c_edge`: on a clamped run `[X, X + n s]` (`‖s‖ = a`, `1 ≤ n ≤ f-1`) there is NO far-side tile with an edge `[X, P]`,
`P = X + t s`, `t > 0`, of length `f^2` (a `c`-edge) beside the run.  This is the generic form of the exclusion of the second alternative of `w1_fill`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapChord4

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

theorem par_seg (X s : Plane) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : 0 < v) :
    X + u • s ∈ segment ℝ X (X + v • s) := by
  refine ⟨1 - u / v, u / v, by rw [sub_nonneg, div_le_one hv]; exact huv, div_nonneg hu hv.le, by ring, ?_⟩
  ext j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem fin3_adj (k m : Fin 3) (h : k ≠ m) : m = k + 1 ∨ k = m + 1 := by
  revert k m; decide

section chord5

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **No `c`-edge beside a clamped run of `a`-steps.** -/
theorem no_c_edge (S : SetupG D e f α β γ L ax ay) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {X s : Plane} (hs0 : s ≠ 0) (hnorm : ‖s‖ = (e : ℝ) * f) (hFX : F X = c) (hFs : F s = 0)
    {n : ℕ} (hn1 : 1 ≤ n) (hnf : n ≤ f - 1)
    (hint : openSegment ℝ X (X + (n : ℝ) • s) ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ X (X + (n : ℝ) • s), ∀ i, y ∉ interior (D.tile i).carrier)
    (hX : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) (X + (-1 : ℝ) • s) X (X + (n : ℝ) • s))
    (hE : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) (X + ((n : ℝ) + 1) • s) (X + (n : ℝ) • s) X)
    {τ : Fin N} {t : ℝ} (ht : 0 < t) {W : Plane}
    (hV : HasV D τ X (X + t • s) W) (hW : F W < c)
    (hd : dist X (X + t • s) = (f : ℝ) ^ 2) : False := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hef' : (e : ℝ) < f := by exact_mod_cast S.hef
  have hef : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 (he0.trans hef')
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hFl : ∀ u : ℝ, F (X + u • s) = c := fun u => by rw [map_add, map_smul, hFs, hFX]; simp
  have hdist : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ → dist (X + t₁ • s) (X + t₂ • s) = (t₂ - t₁) * ((e : ℝ) * f) := by
    intro t₁ t₂ h
    rw [dist_eq_norm, show X + t₁ • s - (X + t₂ • s) = (t₁ - t₂) • s by module, norm_smul, hnorm,
      Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hne : ∀ t₁ t₂ : ℝ, t₁ < t₂ → X + t₁ • s ≠ X + t₂ • s := by
    intro t₁ t₂ h hh
    have := hdist t₁ t₂ h.le
    rw [hh, dist_self] at this
    have hp : 0 < (t₂ - t₁) * ((e : ℝ) * f) := mul_pos (by linarith) hef
    linarith
  have hX0 : X = X + (0 : ℝ) • s := by simp
  -- the data of the run
  have hPQ : X ≠ X + (n : ℝ) • s := by
    have := hne 0 n hnpos; rwa [← hX0] at this
  have hfP : F X = c := hFX
  have hfQ : F (X + (n : ℝ) • s) = c := hFl _
  have hfP' : F (X + (-1 : ℝ) • s) = c := hFl _
  have hfQ' : F (X + ((n : ℝ) + 1) • s) = c := hFl _
  have hP' : X ∈ openSegment ℝ (X + (-1 : ℝ) • s) (X + (n : ℝ) • s) := by
    have := par_mem_open X s (t₁ := -1) (t₂ := 0) (t₃ := n) (by norm_num) hnpos
    simpa using this
  have hQ' : X + (n : ℝ) • s ∈ openSegment ℝ X (X + ((n : ℝ) + 1) • s) := by
    have := par_mem_open X s (t₁ := 0) (t₂ := n) (t₃ := (n : ℝ) + 1) hnpos (by linarith)
    simpa using this
  -- the edge of τ along [X, P]
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hjW⟩ := hV
  have hPne : X ≠ X + t • s := by
    have := hne 0 t ht; rwa [← hX0] at this
  have hWle : ∀ i : Fin 3, F ((D.tile τ).pts i) ≤ c := by
    intro i
    rcases fin3_cover k m j hkm hkj hmj i with h | h | h
    · rw [h, hk]; exact hFX.le
    · rw [h, hm]; exact (hFl t).le
    · rw [h, hjW]; exact hW.le
  have hlen : dist ((D.tile τ).pts k) ((D.tile τ).pts m) = (f : ℝ) ^ 2 := by rw [hk, hm]; exact hd
  have hlen_a : ∃ ed : Fin N × Fin 3, ed ∈ D.lineChain F c ∧
      (D.tile ed.1).edge ed.2 = segment ℝ X (X + t • s) ∧
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = (f : ℝ) ^ 2 := by
    rcases fin3_adj k m hkm with h | h
    · refine ⟨(τ, k), Dissection.mem_lineChain.mpr ⟨?_, ?_, hWle⟩, ?_, ?_⟩
      · simp only; rw [hk]; exact hFX
      · simp only; rw [← h, hm]; exact hFl t
      · simp only [Tri.edge]; rw [← h, hk, hm]
      · simp only; rw [← h]; exact hlen
    · refine ⟨(τ, m), Dissection.mem_lineChain.mpr ⟨?_, ?_, hWle⟩, ?_, ?_⟩
      · simp only; rw [hm]; exact hFl t
      · simp only; rw [← h, hk]; exact hFX
      · simp only [Tri.edge]; rw [← h, hk, hm, segment_symm]
      · simp only; rw [← h, dist_comm]; exact hlen
  obtain ⟨ed, hed, hedseg, hedlen⟩ := hlen_a
  -- the edge lies in [X, E]
  have hclamp := edge_clamped F hF c hPQ hfP hfQ hfP' hfQ' hP' hQ' (p₁ := X) (p₂ := X + t • s) hFX (hFl t)
    (by have := hX ed hed; rwa [hedseg] at this) (by have := hE ed hed; rwa [hedseg] at this)
  have hsub : (D.tile ed.1).edge ed.2 ⊆ segment ℝ X (X + (n : ℝ) • s) := by
    rcases hclamp with hss | hss
    · exfalso
      have hm' : min t n > 0 := lt_min ht hnpos
      have h1 : X + (min t n) • s ∈ segment ℝ X (X + t • s) := par_seg X s hm'.le (min_le_left _ _) ht
      have h2 : X + (min t n) • s ∈ segment ℝ X (X + (n : ℝ) • s) := par_seg X s hm'.le (min_le_right _ _) hnpos
      have h3 : X ∈ segment ℝ X (X + t • s) := left_mem_segment _ _ _
      have h4 : X ∈ segment ℝ X (X + (n : ℝ) • s) := left_mem_segment _ _ _
      exact (hne 0 (min t n) hm') (by
        have := hss ⟨h3, h4⟩ ⟨h1, h2⟩
        simpa using this.symm)
    · rw [hedseg]; exact hss
  have hdE : dist X (X + (n : ℝ) • s) = (n : ℝ) * ((e : ℝ) * f) := by
    have := hdist 0 n hnpos.le
    rw [← hX0] at this; simpa using this
  have hl := chain_edge_len_a S (j := n) hn1 hnf F hF c hPQ hfP hfQ hfP' hfQ' hP' hQ' hint hwall hX hE hdE hed hsub
  rw [hedlen] at hl
  have : (f : ℝ) ^ 2 = (e : ℝ) * f := hl
  have hf0 : (0 : ℝ) < f := he0.trans hef'
  nlinarith

end chord5

#print axioms no_c_edge

end Erdos634.Draft.WGapStmt
