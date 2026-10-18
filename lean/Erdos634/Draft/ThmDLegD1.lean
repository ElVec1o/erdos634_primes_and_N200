import Mathlib.Tactic
import Erdos634.Draft.ThmDLegBig
import Erdos634.Draft.ThmDLegIdx

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (5)): D1 for a positioned leg  

`leg_D1` : a positioned leg `[Q, B]` of a `SetupT` frame has at least `u` edges `c`, GIVEN the two endpoint statements `hQ` (no stopped
`c>` block of length `n < u` starts at the first edge) and `hBe` (no stopped `c<` block of length `n < u` ends at the last edge).  The proof is the
pigeonhole `pig` (a `c`-run `cm^j cp^i` stopped at both ends) and, for an interior start, `T0_stop_cp/cm`, `T0_aa` with `east_big/west_big`
(Lemma 33' with the window `u`).  The endpoint statements are `leg_K2_start/end` at an `α`-corner (even with window `v`) and the apex
lemma at an apex.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.Draft.APrimeLegBuild
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Erdos634.MarchSlots Erdos634.Draft.ThmD Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem leg_D1 (S : SetupT D u v α β γ L ax ay) {r : List (LegStep N)} {t : Fin N} {e : OE}
    (hRL : RealLeg D.toDissection α t e r)
    (hLP : LegPos D.toDissection D.model (mkPt 0 0) (mkPt L 0) t e 0 r)
    (hLE : LegEnd D.toDissection α (mkPt L 0) t e r)
    (hang : (D.tile t).localAngle (mkPt 0 0) = angVal α e.l)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hQ : ∀ n : ℕ, 1 ≤ n → n < u → (∀ j < n, (legEdges e r)[j]? = some OE.cp) →
      (n = (legEdges e r).length ∨ ∃ o, (legEdges e r)[n]? = some o ∧ o.l = Ang.ga) → False)
    (hBe : ∀ n : ℕ, 1 ≤ n → n < u → n ≤ (legEdges e r).length →
      (∀ j < n, (legEdges e r)[(legEdges e r).length - 1 - j]? = some OE.cm) →
      (n < (legEdges e r).length →
        ∃ o, (legEdges e r)[(legEdges e r).length - 1 - n]? = some o ∧ o.r = Ang.ga) → False) :
    u ≤ cntLetter isC (legEdges e r) := by
  classical
  by_contra hlt
  push Not at hlt
  have hcong : ∀ i, D.model.Congruent (D.tile i) := fun i => (D.tiles_congruent i).symm
  have hA0 := S.hM.hα'
  have hA1 := S.hM.hβ'
  have hA2 := S.hM.hγ'
  rw [S.hβ] at hA1
  rw [S.hγ] at hA2
  have h3α : 3 * α < Real.pi := by
    have hβpos : 0 < Real.pi - 3 * α := by
      have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
      have e' : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = Real.pi - 3 * α := hA1
      rw [e'] at h; exact h
    linarith
  obtain ⟨f, hB⟩ := brk_of_leg S hRL hLP hLE hang
  set W := legEdges e r with hWdef
  have hCh : Ch W := by
    obtain ⟨steps, hmap, hval⟩ := RealLeg.toValid D.toDissection D.model hcong α S.hirr hA0 hA1 hA2 S.hα h3α
      r t e hRL
    have : edges e steps = W := by simp [edges, hWdef, legEdges, hmap]
    rw [← this]; exact ch_of_valid e steps hval
  have hne : W ≠ [] := by simp [hWdef, legEdges]
  have h0 : 0 < W.length := List.length_pos_of_ne_nil hne
  have hgam : angVal α Ang.ga = γ := by rw [S.hγ]; simp [angVal]
  have hh : ∀ e' t', W = e' :: t' → e'.l ≠ Ang.ga := by
    intro e' t' hW hga
    obtain ⟨t', j, k, hjk, hj, hk, hjang, hkang, hw⟩ := hB.step 0 h0
    have hge : W[0]'h0 = e' := by simp [hW]
    rw [hge, hga, hgam] at hjang
    have hmem : (D.tile t').pts j ∈ Set.range D.target.pts := by
      refine ⟨0, ?_⟩
      rw [hj, hB.f0, (target_pts01 S).1]; simp
    exact hnoγ t' j hmem hjang
  have hl : ∀ q e', W = q ++ [e'] → e'.r ≠ Ang.ga := by
    intro q e' hW hga
    have hlen : W.length = q.length + 1 := by rw [hW]; simp
    obtain ⟨t', j, k, hjk, hj, hk, hjang, hkang, hw⟩ := hB.step (W.length - 1) (by omega)
    have hge : W[W.length - 1]'(by omega) = e' := by
      simp [hW]
    rw [hge, hga, hgam] at hkang
    have hmem : (D.tile t').pts k ∈ Set.range D.target.pts := by
      refine ⟨1, ?_⟩
      rw [hk, show W.length - 1 + 1 = W.length by omega, hB.fl, (target_pts01 S).2.1]; simp
    exact hnoγ t' k hmem hkang
  obtain ⟨pre, run, post, hW, hrne, hrc, hpre, hpost⟩ := pig W hne hCh hh hl
  obtain ⟨j, i, hrun⟩ := run_shape run hrc (ch_middle pre run post (hW ▸ hCh))
  have hcnt := cnt_ge pre run post hrc
  rw [← hW] at hcnt
  rw [hrun] at hcnt hW
  simp only [List.length_append, List.length_replicate] at hcnt
  have hji : j + i < u := by omega
  have hju : j < u := by omega
  have hiu : i < u := by omega
  have hlen : W.length = pre.length + (j + i) + post.length := by rw [hW]; exact len_decomp pre post j i
  have hcm : ∀ k < j, W[pre.length + k]? = some OE.cm := by
    intro k hk; rw [hW]; exact idx_cm pre post j i hk
  have hcp : ∀ k < i, W[pre.length + j + k]? = some OE.cp := by
    intro k hk; rw [hW]; exact idx_cp pre post j i hk
  have hrne' : j + i ≠ 0 := by
    intro h0'; apply hrne
    rw [hrun]
    have hj0 : j = 0 := by omega
    have hi0 : i = 0 := by omega
    subst hj0 hi0; simp
  -- the stop on the right of the run
  have hR : pre.length + j + i = W.length ∨ ∃ o, W[pre.length + j + i]? = some o ∧ o.l = Ang.ga := by
    rcases hpost with hp | ⟨o, q, hpo, hol⟩
    · left; subst hp; simp at hlen; omega
    · right
      refine ⟨o, ?_, hol⟩
      have := idx_post pre (List.replicate j OE.cm ++ List.replicate i OE.cp) (o := o) (q := q)
      simp only [List.length_append, List.length_replicate] at this
      rw [hW, hpo]
      rw [show pre.length + j + i = pre.length + (j + i) by ring]
      exact this
  -- the stop on the left of the run
  have hLs : pre.length = 0 ∨ (1 ≤ pre.length ∧ ∃ o, W[pre.length - 1]? = some o ∧ o.r = Ang.ga) := by
    rcases hpre with hp | ⟨q, o, hpo, hor⟩
    · left; subst hp; simp
    · right
      refine ⟨by rw [hpo]; simp, o, ?_, hor⟩
      rw [hW]
      have := idx_pre pre post (List.replicate j OE.cm ++ List.replicate i OE.cp) hpo
      exact this
  rcases Nat.eq_zero_or_pos i with hi0 | hi1
  · -- no `cp`: the run is `cm^j`, `j ≥ 1`
    have hj1 : 1 ≤ j := by omega
    subst hi0
    have hcm' : ∀ k < j, W[pre.length + j - 1 - k]? = some OE.cm := by
      intro k hk
      have := hcm (j - 1 - k) (by omega)
      rwa [show pre.length + (j - 1 - k) = pre.length + j - 1 - k by omega] at this
    have hstopW : j = pre.length + j ∨ (j < pre.length + j ∧ ∃ o, W[pre.length + j - 1 - j]? = some o ∧
        o.r = Ang.ga) := by
      rcases hLs with hz | ⟨hp1, o, ho, hor⟩
      · left; omega
      · right
        refine ⟨by omega, o, ?_, hor⟩
        rwa [show pre.length + j - 1 - j = pre.length - 1 by omega]
    rcases hR with hR | ⟨o, ho, hol⟩
    · -- the east end is `B`
      have hb : pre.length + j = W.length := by omega
      refine hBe j hj1 hju (by omega) ?_ ?_
      · intro k hk
        rw [← hb]; exact hcm' k hk
      · intro hjl
        rcases hLs with hz | ⟨hp1, o, ho, hor⟩
        · exfalso; omega
        · exact ⟨o, by rwa [show W.length - 1 - j = pre.length - 1 by omega], hor⟩
    · have hbw : pre.length + j < W.length := by
        by_contra hnot
        rw [List.getElem?_eq_none (by omega)] at ho
        exact absurd ho (by simp)
      have hcm0 : W[pre.length + j - 1]? = some OE.cm := by simpa using hcm' 0 hj1
      obtain ⟨t1, hT0⟩ := T0_stop_cm S hB (b := pre.length + j) (by omega) hbw hcm0 ⟨o, by simpa using ho, hol⟩
      exact west_big S hB (b := pre.length + j) (n := j) hj1 hju hbw (by omega) hcm' ⟨t1, hT0⟩ hnoγ hstopW
  · rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · -- no `cm`: the run is `cp^i`
      subst hj0
      have haw : pre.length < W.length := by omega
      have hcp' : ∀ k < i, W[pre.length + k]? = some OE.cp := by
        intro k hk; simpa using hcp k hk
      have hR' : pre.length + i = W.length ∨ ∃ o, W[pre.length + i]? = some o ∧ o.l = Ang.ga := by
        simpa using hR
      rcases hLs with hz | ⟨hp1, o, ho, hor⟩
      · refine hQ i hi1 hiu ?_ ?_
        · intro k hk; simpa [hz] using hcp' k hk
        · simpa [hz] using hR'
      · have hcp0 : W[pre.length]? = some OE.cp := by simpa using hcp' 0 hi1
        obtain ⟨t1, hT0⟩ := T0_stop_cp S hB hp1 haw hcp0 ⟨o, ho, hor⟩
        exact east_big S hB (a := pre.length) hp1 hi1 hiu (by omega) haw hcp' ⟨t1, hT0⟩ hnoγ hR'
    · -- both: the `α | α` junction at `a = |pre| + j`
      have haw : pre.length + j < W.length := by omega
      have hcp0 : W[pre.length + j]? = some OE.cp := by simpa using hcp 0 hi1
      have hcm0 : W[pre.length + j - 1]? = some OE.cm := by
        have := hcm (j - 1) (by omega)
        rwa [show pre.length + (j - 1) = pre.length + j - 1 by omega] at this
      have hcm' : ∀ k < j, W[pre.length + j - 1 - k]? = some OE.cm := by
        intro k hk
        have := hcm (j - 1 - k) (by omega)
        rwa [show pre.length + (j - 1 - k) = pre.length + j - 1 - k by omega] at this
      have hstopW : j = pre.length + j ∨ (j < pre.length + j ∧ ∃ o, W[pre.length + j - 1 - j]? = some o ∧
          o.r = Ang.ga) := by
        rcases hLs with hz | ⟨hp1, o, ho, hor⟩
        · left; omega
        · right
          refine ⟨by omega, o, ?_, hor⟩
          rwa [show pre.length + j - 1 - j = pre.length - 1 by omega]
      rcases T0_aa S hB (a := pre.length + j) (by omega) haw hcp0 hcm0 with h | h
      · obtain ⟨t1, hT0⟩ := h
        exact east_big S hB (a := pre.length + j) (by omega) hi1 hiu (by omega) haw hcp ⟨t1, hT0⟩ hnoγ hR
      · obtain ⟨t2, hT0⟩ := h
        exact west_big S hB (b := pre.length + j) (n := j) hj1 hju haw (by omega) hcm' ⟨t2, hT0⟩ hnoγ hstopW

#print axioms leg_D1
end Erdos634.Draft.ThmDRun
