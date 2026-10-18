import Mathlib.Tactic
import Erdos634.Draft.ThmDRowStep
import Erdos634.Draft.ThmDRowFrontier

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: Lemma K, which is ours (it uses the window v at the base corners).
# Theorem D' (R6 anchor): Lemma K, (K2) for a run of length `n = 1`  

`lemmaK2_one` : a corner tile `Δ_{0,0}` with its `c`-edge on the base side `S`, whose run `n = 1` is *stopped* at `V = lp 1 0`
(`V` a vertex of the target, or the tile on `S` beyond `V` has `γ` at `V`), cannot exist.  Proof: `row_orient_full` (`w = 1`, the
H2 theorem) gives `∇_{0,0}` across the `a`-edge `PV`; it has `γ` at `V` (`D_anglesT`); a `γ` at a target vertex is excluded by the
standing assumption (`hnoγ`), two `γ` at a frontier non-vertex by the fan (`no_two_gamma`).

This is the first rung of (K2): the induction `H(w) => H(w+1)` (Lemmas 32', 33' of `conjV.md`) is NOT proved; `lemmaK2_one` is its
case `w = n = 1`, where no sector has to be filled.  It is witnessed on `Dk 2`-type data by nothing (the hypotheses are
contradictory by the lemma itself); the pieces it uses are witnessed in `ThmDRowFarWitness`.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.ThmDHalf
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **(K2), `n = 1`.** -/
theorem lemmaK2_one (C : CtxBaseT D u v α β γ L ax ay ε x) (hwv : 1 < v)
    (h00 : UTT D (u : ℝ) (v : ℝ) ε x 0 0)
    (hP : lpT (u : ℝ) (v : ℝ) ε x 0 1 ∈ frontier D.target.carrier)
    (hPnv : lpT (u : ℝ) (v : ℝ) ε x 0 1 ∉ Set.range D.target.pts)
    (hVnv : (∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x 1 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x 1 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x 1 0) = γ) →
      lpT (u : ℝ) (v : ℝ) ε x 1 0 ∉ Set.range D.target.pts)
    (hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 1) (lpT (u : ℝ) (v : ℝ) ε x 1 0) ⊆ interior D.target.carrier)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : lpT (u : ℝ) (v : ℝ) ε x 1 0 ∈ Set.range D.target.pts ∨
      ∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x 1 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x 1 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x 1 0) = γ) : False := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  obtain ⟨t0, ht0⟩ := h00
  have e10 : lpT (u : ℝ) (v : ℝ) ε x (0 + 1) 0 = lpT (u : ℝ) (v : ℝ) ε x 1 0 := lpT_congr (by ring) rfl
  have e01 : lpT (u : ℝ) (v : ℝ) ε x 0 (0 + 1) = lpT (u : ℝ) (v : ℝ) ε x 0 1 := lpT_congr rfl (by ring)
  have ht0' : HasV D t0 (lpT (u : ℝ) (v : ℝ) ε x 0 0) (lpT (u : ℝ) (v : ℝ) ε x 1 0) (lpT (u : ℝ) (v : ℝ) ε x 0 1) :=
    hasV_congr ht0 rfl e10 e01
  -- V is a frontier point (on the base line y = 0)
  have hVmem : lpT (u : ℝ) (v : ℝ) ε x 1 0 ∈ D.target.carrier := by
    obtain ⟨k, m, j, -, -, -, -, hm, -⟩ := ht0'
    rw [← hm]; exact pts_mem_target D.toDissection t0 m
  have hV1 : (lpT (u : ℝ) (v : ℝ) ε x 1 0) 1 = 0 := by
    unfold lpT; rw [mkPt_one]; ring
  have hVf : lpT (u : ℝ) (v : ℝ) ε x 1 0 ∈ frontier D.target.carrier := S.frontier_y0 hVmem hV1
  -- the row step with w = 1
  have hnear : ∀ i : ℕ, i < 1 → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw 1 i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw 1 i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw 1 i + 1)) := by
    intro i hi
    have : i = 0 := by omega
    subst this
    refine ⟨t0, hasV_congr ht0' ?_ ?_ ?_⟩
    · exact lpT_congr (by simp) (by unfold ηw; simp)
    · exact lpT_congr (by simp) (by unfold ηw; simp)
    · exact lpT_congr (by simp) (by unfold ηw; simp)
  have hP1 : lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw 1 0 + 1) = lpT (u : ℝ) (v : ℝ) ε x 0 1 :=
    lpT_congr (by simp) (by unfold ηw; simp)
  have hQ1 : lpT (u : ℝ) (v : ℝ) ε x ((1 : ℕ) : ℝ) 0 = lpT (u : ℝ) (v : ℝ) ε x 1 0 := lpT_congr (by simp) rfl
  have hint1 : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 ((1 : ℕ) : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x ((1 : ℕ) : ℝ) 0) ⊆
      interior D.target.carrier := by
    rw [show ((1 : ℕ) : ℝ) = 1 by simp]; exact hint
  obtain ⟨tD, hD⟩ := row_orient_full C 1 one_pos hwv hnear (by rw [hP1]; exact hP) (by rw [hP1]; exact hPnv)
    (by rw [hQ1]; exact hVf) hint1 0 (by norm_num)
  have e1 : lpT (u : ℝ) (v : ℝ) ε x (((0 : ℕ) : ℝ) + 1) (ηw 1 0) = lpT (u : ℝ) (v : ℝ) ε x (0 + 1) 0 :=
    lpT_congr (by simp) (by unfold ηw; simp)
  have e2 : lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw 1 0 + 1) = lpT (u : ℝ) (v : ℝ) ε x 0 (0 + 1) :=
    lpT_congr (by simp) (by unfold ηw; simp)
  have e3 : lpT (u : ℝ) (v : ℝ) ε x (((0 : ℕ) : ℝ) + 1) (ηw 1 0 + 1) = lpT (u : ℝ) (v : ℝ) ε x (0 + 1) (0 + 1) :=
    lpT_congr (by simp) (by unfold ηw; simp)
  have hD' : HasV D tD (lpT (u : ℝ) (v : ℝ) ε x (0 + 1) 0) (lpT (u : ℝ) (v : ℝ) ε x 0 (0 + 1))
      (lpT (u : ℝ) (v : ℝ) ε x (0 + 1) (0 + 1)) := hasV_congr hD e1 e2 e3
  have hgam := (D_anglesT hu huv hv2 hε S.tile.hab S.tile.ac S.tile.bc S.hM hD').1
  rw [e10] at hgam
  -- the stop
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hD'
  have hkV : (D.tile tD).pts k = lpT (u : ℝ) (v : ℝ) ε x 1 0 := by rw [hk, e10]
  rcases hstop with hvert | ⟨t', k', m', hk'm', hk', hm1, hmV, hang⟩
  · exact hnoγ tD k (by rw [hkV]; exact hvert) (by rw [hkV]; exact hgam)
  · have hβpos : 0 < β := by
      have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
      have e : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
      rw [e] at h; exact h
    have h3α : 3 * α < Real.pi := by have := S.hβ; linarith
    have hne : tD ≠ t' := by
      rintro rfl
      -- the vertices of `tD` other than `V` are off the base line
      have hy : ∀ i, (D.tile tD).pts i 1 = 0 → (D.tile tD).pts i = lpT (u : ℝ) (v : ℝ) ε x 1 0 := by
        intro i hi
        rcases fin3_cover k m j hkm hkj hmj i with h | h | h
        · rw [h, hkV]
        · exfalso
          rw [h, hm] at hi
          have : (lpT (u : ℝ) (v : ℝ) ε x 0 (0 + 1)) 1 = ((0 : ℝ) + 1) * hhT (u : ℝ) (v : ℝ) := lp_snd_eq
          rw [this] at hi
          have := hhT_pos hu huv hv2
          linarith
        · exfalso
          rw [h, hj] at hi
          have : (lpT (u : ℝ) (v : ℝ) ε x (0 + 1) (0 + 1)) 1 = ((0 : ℝ) + 1) * hhT (u : ℝ) (v : ℝ) := lp_snd_eq
          rw [this] at hi
          have := hhT_pos hu huv hv2
          linarith
      exact hmV (hy m' hm1)
    obtain ⟨mm, hfan⟩ := pinfan_ang D S.hirr S.hM.hα' (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α
      hVf (hVnv ⟨t', k', m', hk'm', hk', hm1, hmV, hang⟩) tD t' hne Ang.ga Ang.ga (by rw [hgam, S.hγ]; simp [angVal]) (by rw [hang, S.hγ]; simp [angVal])
    exact no_two_gamma _ _ mm hfan ⟨rfl, rfl⟩

#print axioms lemmaK2_one
end Erdos634.Draft.ThmDRun
