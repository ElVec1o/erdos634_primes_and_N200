import Mathlib.Tactic
import Erdos634.Draft.ThmDWestEdge
import Erdos634.Draft.ThmDK2Final
import Erdos634.Draft.ThmDRowFrontier

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (4): Lemma 33' for an interior start  

`lemma33_interior` : a run of `n` tiles `Δ_{i,0}` on the side `S` starting at the interior point `U = lp 0 0` (`1 ≤ n < u`), stopped at its far
end `V = lp n 0`, with a tile `T₀` west of the ray `UW` having an `a`- or `c`-edge from `U` along it (`RayTileAC`), cannot exist.
It is `lemmaK2_final_gen` with the ends `P_w` good because of `T₀` and the window `RB` (`west_edge_at_ray`, `westCover_at_ray`, `PGood_of_west`).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem FXT_apply' {u v ε : ℝ} (y : Plane) :
    FXT u v ε y = ε * hhT u v * y 0 + (uuT u v - u * v) * y 1 := by
  unfold FXT; rw [lin_apply]

theorem exists_lp_of_FXT (C : CtxBaseT D u v α β γ L ax ay ε x) {y : Plane}
    (hy : FXT (u : ℝ) (v : ℝ) ε y = lvT (u : ℝ) (v : ℝ) ε x 0) :
    ∃ η : ℝ, y = lpT (u : ℝ) (v : ℝ) ε x 0 η := by
  have S := C.S
  have hε := C.e2
  have hh := hhT_pos S.u0 S.uv' S.v2
  set η : ℝ := y 1 / hhT (u : ℝ) (v : ℝ) with hηdef
  refine ⟨η, ?_⟩
  have h1 : y 1 = η * hhT (u : ℝ) (v : ℝ) := by rw [hηdef]; field_simp
  rw [FXT_apply'] at hy
  unfold lvT at hy
  refine plane_ext ?_ ?_
  · simp only [lpT, mkPt_zero]
    have hne : ε * hhT (u : ℝ) (v : ℝ) ≠ 0 := mul_ne_zero (eps_neT hε) hh.ne'
    apply mul_left_cancel₀ hne
    linear_combination hy + ((u : ℝ) * v - uuT (u : ℝ) (v : ℝ)) * h1
      - (((u : ℝ) * v - uuT (u : ℝ) (v : ℝ)) * η * hhT (u : ℝ) (v : ℝ)) * hε
  · simp only [lpT, mkPt_one]
    exact h1

theorem PGood_at_ray_int (C : CtxBaseT D u v α β γ L ax ay ε x) {w : ℕ} (hw1 : 1 ≤ w) (hwu : w < u)
    (hray : ∀ j : ℕ, j < w → UTT D (u : ℝ) (v : ℝ) ε x 0 (j : ℝ))
    (hch : ∀ j : ℕ, 1 ≤ j → lpT (u : ℝ) (v : ℝ) ε x 0 (j : ℝ) ∈ D.target.carrier →
      openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 0) (lpT (u : ℝ) (v : ℝ) ε x 0 (j : ℝ)) ⊆
        interior D.target.carrier)
    (hT0 : ∃ (e : Fin N) (k m : Fin 3) (t : ℝ), k ≠ m ∧ (D.tile e).pts k = lpT (u : ℝ) (v : ℝ) ε x 0 0 ∧ 0 < t ∧
        (D.tile e).pts m = lpT (u : ℝ) (v : ℝ) ε x 0 t ∧
        (dist ((D.tile e).pts k) ((D.tile e).pts m) = (u : ℝ) ^ 2 ∨
          dist ((D.tile e).pts k) ((D.tile e).pts m) = (u : ℝ) * v) ∧
        (∀ i, FXT (u : ℝ) (v : ℝ) ε ((D.tile e).pts i) ≤ lvT (u : ℝ) (v : ℝ) ε x 0)) :
    lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ∈ interior D.target.carrier ∧ PGood D (u : ℝ) (v : ℝ) ε x α (w : ℝ) := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw1
  set P := lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) with hPdef
  have hPmem : P ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := hray (w - 1) (by omega)
    have := ht.mem₃
    have e : ((w - 1 : ℕ) : ℝ) + 1 = (w : ℝ) := by rw [Nat.cast_sub hw1]; simp
    rwa [e] at this
  have hint := hch w hw1 hPmem
  obtain ⟨tE, k, m, hkm, hk, hm, hle, hP⟩ := west_edge_at_ray C hw1 hwu hray hint hT0
  obtain ⟨j, hjk, hjm⟩ := fin3_third k m hkm
  have hkj : k ≠ j := Ne.symm hjk
  have hmj : m ≠ j := Ne.symm hjm
  have hFP : FXT (u : ℝ) (v : ℝ) ε P = lvT (u : ℝ) (v : ℝ) ε x 0 := FXT_lp hε 0 (w : ℝ)
  -- the third vertex is strictly west
  have hj' : FXT (u : ℝ) (v : ℝ) ε ((D.tile tE).pts j) < FXT (u : ℝ) (v : ℝ) ε P := by
    rw [hFP]
    refine lt_of_le_of_ne (hle j) ?_
    intro heq
    refine two_vertices_on_line (D.tile tE) (FXT (u : ℝ) (v : ℝ) ε) (lvT (u : ℝ) (v : ℝ) ε x 0)
      (FXT_ne hu huv hv2 hε) (fun i => ?_)
    rcases fin3_cover k m j hkm hkj hmj i with rfl | rfl | rfl
    · exact hk
    · exact hm
    · exact heq
  have hW : WestCover D.toDissection (FXT (u : ℝ) (v : ℝ) ε) P :=
    westCover_of_edge (D := D.toDissection) (FXT (u : ℝ) (v : ℝ) ε) tE hkm hkj hmj hP (by rw [hk, hFP])
      (by rw [hm, hFP]) (fun i => by rw [hFP]; exact hle i) hj'
  -- `P` is interior to the target
  obtain ⟨ηA, hA⟩ := exists_lp_of_FXT C hk
  obtain ⟨ηB, hB⟩ := exists_lp_of_FXT C hm
  have hPint : P ∈ interior D.target.carrier := by
    rw [hA, hB, openSegment_eq_image_lineMap] at hP
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := hP
    rw [lineMap_lpT] at hs
    have hsw := lpT_eta_eq hu huv hv2 hs
    have hAm : lpT (u : ℝ) (v : ℝ) ε x 0 ηA ∈ D.target.carrier := by
      rw [← hA]; exact pts_mem_target D.toDissection tE k
    have hBm : lpT (u : ℝ) (v : ℝ) ε x 0 ηB ∈ D.target.carrier := by
      rw [← hB]; exact pts_mem_target D.toDissection tE m
    have hM : lpT (u : ℝ) (v : ℝ) ε x 0 ((w : ℝ) / 2) ∈ interior D.target.carrier := by
      apply hint
      rw [openSegment_eq_image_lineMap]
      refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [lineMap_lpT]
      refine lpT_congr (by ring) ?_
      ring
    -- the upper endpoint
    have key : ∀ ηU : ℝ, (w : ℝ) < ηU → lpT (u : ℝ) (v : ℝ) ε x 0 ηU ∈ D.target.carrier →
        P ∈ interior D.target.carrier := by
      intro ηU hU hUm
      have hopen := D.target.convex.openSegment_interior_closure_subset_interior hM (subset_closure hUm)
      apply hopen
      rw [openSegment_eq_image_lineMap]
      have hden : 0 < ηU - (w : ℝ) / 2 := by linarith
      refine ⟨((w : ℝ) / 2) / (ηU - (w : ℝ) / 2), ⟨div_pos (by linarith) hden, ?_⟩, ?_⟩
      · rw [div_lt_one hden]; linarith
      · rw [lineMap_lpT, hPdef]
        refine lpT_congr (by ring) ?_
        rw [div_mul_cancel₀ _ hden.ne']; ring
    have hAB : ηA ≠ ηB := by
      intro h; apply hkm; apply (D.tile tE).indep.injective; rw [hA, hB, h]
    by_cases hAw : (w : ℝ) < ηA
    · exact key ηA hAw hAm
    · push_neg at hAw
      by_cases hBw : (w : ℝ) < ηB
      · exact key ηB hBw hBm
      · push_neg at hBw
        exfalso
        rcases lt_or_gt_of_ne hAB with h | h <;> nlinarith
  exact ⟨hPint, PGood_of_west C (by positivity) hPint hW⟩

theorem lemma33_interior (C : CtxBaseT D u v α β γ L ax ay ε x) {n : ℕ} (hn1 : 1 ≤ n) (hnu : n < u)
    (hrun : ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) ε x (i : ℝ) 0)
    (hch : ∀ j : ℕ, 1 ≤ j → lpT (u : ℝ) (v : ℝ) ε x 0 (j : ℝ) ∈ D.target.carrier →
      openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 0) (lpT (u : ℝ) (v : ℝ) ε x 0 (j : ℝ)) ⊆
        interior D.target.carrier)
    (hT0 : ∃ (e : Fin N) (k m : Fin 3) (t : ℝ), k ≠ m ∧ (D.tile e).pts k = lpT (u : ℝ) (v : ℝ) ε x 0 0 ∧ 0 < t ∧
        (D.tile e).pts m = lpT (u : ℝ) (v : ℝ) ε x 0 t ∧
        (dist ((D.tile e).pts k) ((D.tile e).pts m) = (u : ℝ) ^ 2 ∨
          dist ((D.tile e).pts k) ((D.tile e).pts m) = (u : ℝ) * v) ∧
        (∀ i, FXT (u : ℝ) (v : ℝ) ε ((D.tile e).pts i) ≤ lvT (u : ℝ) (v : ℝ) ε x 0))
    (hVnv : (∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) →
      lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∉ Set.range D.target.pts)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∈ Set.range D.target.pts ∨
      ∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) : False := by
  have S := C.S
  have hnv : n < v := lt_trans hnu S.huv
  have hQmem : ∀ w : ℕ, 1 ≤ w → w ≤ n → lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ D.target.carrier := by
    intro w hw1 hwn
    obtain ⟨t, ht⟩ := hrun (w - 1) (by omega)
    have := ht.mem₂
    have e : ((w - 1 : ℕ) : ℝ) + 1 = (w : ℝ) := by rw [Nat.cast_sub hw1]; simp
    rwa [e] at this
  have hQf : ∀ w : ℕ, 1 ≤ w → w ≤ n → lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ frontier D.target.carrier := by
    intro w hw1 hwn
    exact S.frontier_y0 (hQmem w hw1 hwn) (by rw [lpT_snd]; ring)
  refine lemmaK2_final_gen C hn1 hnv hrun
    (fun w h1 h2 hr => (PGood_at_ray_int C h1 (by omega) hr hch hT0).2) hQf
    (fun w h1 h2 hr => ?_) hVnv hnoγ hstop
  have hPi := (PGood_at_ray_int C h1 (by omega) hr hch hT0).1
  exact D.target.convex.openSegment_interior_closure_subset_interior hPi (subset_closure (hQmem w h1 h2))

#print axioms lemma33_interior

end Erdos634.Draft.ThmDRun

