import Mathlib.Tactic
import Erdos634.Draft.ThmDStep33c
import Erdos634.Draft.ThmDK2One

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: Lemma K, which is ours (it uses the window v at the base corners).
# Theorem D' (R6): Lemma K (K2) from Lemma 32  (; CONDITIONAL on `L32Hyp`)

`lemmaK2` : a run of `n` tiles `Δ_{i,0}` (`1 ≤ n < v`) on the base side, stopped at `V = lp n 0`, cannot exist.  `H(1)` holds, `H(w) => H(w+1)`
is `step33` (conditional on Lemma 32, `L32Hyp`), so `H(n)` occurs; then `∇_{n-1,0}` (from `row_orient_full`) has `γ` at `V`, against the stop
(a `γ` at a target vertex, or two `γ` at a frontier non-vertex).  `lemmaK2_one` is the case `n = 1`, which needs no Lemma 32.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.ThmDHalf
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem lemmaK2_gen (C : CtxBaseT D u v α β γ L ax ay ε x) {n : ℕ} (hn1 : 1 ≤ n) (hnv : n < v)
    (L32 : L32Hyp D (u : ℝ) (v : ℝ) ε x α n)
    (hrun : ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) ε x (i : ℝ) 0)
    (hPG : ∀ w : ℕ, 1 ≤ w → w ≤ n → (∀ j : ℕ, j < w → UTT D (u : ℝ) (v : ℝ) ε x 0 (j : ℝ)) →
      PGood D (u : ℝ) (v : ℝ) ε x α (w : ℝ))
    (hQf : ∀ w : ℕ, 1 ≤ w → w ≤ n → lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ frontier D.target.carrier)
    (hint : ∀ w : ℕ, 1 ≤ w → w ≤ n → (∀ j : ℕ, j < w → UTT D (u : ℝ) (v : ℝ) ε x 0 (j : ℝ)) →
      openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
        interior D.target.carrier)
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
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hnvR : n < v := hnv
  -- H(w) for all 1 ≤ w ≤ n
  have hH : ∀ w : ℕ, 1 ≤ w → w ≤ n → HT D (u : ℝ) (v : ℝ) ε x w := by
    intro w hw1 hwn
    induction w with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · refine ⟨fun i j hj hij => ?_, fun i j hj hij => ?_⟩
        · have hj0 : j = 0 := by omega
          have hi0 : i = 0 := by omega
          subst hj0 hi0
          simpa using hrun 0 (by omega)
        · omega
      · exact step33_gen C L32 hk (by omega) hnv (ih hk (by omega)) (hrun k (by omega))
          (hPG k hk (by omega) (fun j hj => by simpa using (ih hk (by omega)).1 0 j hj (by omega)))
          (hQf k hk (by omega)) (hint k hk (by omega) (fun j hj => by simpa using (ih hk (by omega)).1 0 j hj (by omega)))
  have HTn := hH n hn1 le_rfl
  -- the far row at w = n
  have hnear : ∀ i : ℕ, i < n → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw n i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw n i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw n i + 1)) := by
    intro i hi
    have hU := HTn.1 i (n - 1 - i) (by omega) (by omega)
    have hj : ((n - 1 - i : ℕ) : ℝ) = ηw n i := by
      unfold ηw; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    obtain ⟨t, ht⟩ := hU
    exact ⟨t, hasV_congr ht (lpT_congr rfl hj) (lpT_congr rfl hj) (lpT_congr rfl (by rw [hj]))⟩
  have hPn := hPG n hn1 le_rfl (fun j hj => by simpa using HTn.1 0 j hj (by omega))
  have hP1 : lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw n 0 + 1) = lpT (u : ℝ) (v : ℝ) ε x 0 (n : ℝ) :=
    lpT_congr (by simp) (by unfold ηw; simp)
  have hfar := row_orient_full_gen C n (by omega) hnv hnear hPn
    (hQf n hn1 le_rfl) (hint n hn1 le_rfl (fun j hj => by simpa using HTn.1 0 j hj (by omega)))
  obtain ⟨tD, hD⟩ := hfar (n - 1) (by omega)
  -- ∇_{n-1,0}: lp (n) 0, lp (n-1) 1, lp n 1
  have e0 : ηw n (n - 1) = 0 := by
    unfold ηw; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e1 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hD' : HasV D tD (lpT (u : ℝ) (v : ℝ) ε x (((n - 1 : ℕ) : ℝ) + 1) 0)
      (lpT (u : ℝ) (v : ℝ) ε x ((n - 1 : ℕ) : ℝ) (0 + 1))
      (lpT (u : ℝ) (v : ℝ) ε x (((n - 1 : ℕ) : ℝ) + 1) (0 + 1)) :=
    hasV_congr hD (lpT_congr rfl e0) (lpT_congr rfl (by rw [e0])) (lpT_congr rfl (by rw [e0]))
  have hgam := (D_anglesT hu huv hv2 hε S.tile.hab S.tile.ac S.tile.bc S.hM hD').1
  rw [e1] at hgam
  -- the stop
  have hVmem : lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∈ D.target.carrier := by
    have := (hQf n hn1 le_rfl).1
    exact D.target.isCompact.isClosed.closure_eq ▸ this
  have hVf : lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∈ frontier D.target.carrier := hQf n hn1 le_rfl
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hD'
  have hkV : (D.tile tD).pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 := by rw [hk, e1]
  rcases hstop with hvert | ⟨t', k', m', hk'm', hk', hm1, hmV, hang⟩
  · exact hnoγ tD k (by rw [hkV]; exact hvert) (by rw [hkV]; exact hgam)
  · have hβpos : 0 < β := by
      have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
      have e : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
      rw [e] at h; exact h
    have h3α : 3 * α < Real.pi := by have := S.hβ; linarith
    have hne : tD ≠ t' := by
      rintro rfl
      have hy : ∀ i, (D.tile tD).pts i 1 = 0 → (D.tile tD).pts i = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 := by
        intro i hi
        rcases fin3_cover k m j hkm hkj hmj i with h | h | h
        · rw [h, hkV]
        · exfalso
          rw [h, hm] at hi
          have : (lpT (u : ℝ) (v : ℝ) ε x ((n - 1 : ℕ) : ℝ) (0 + 1)) 1 = ((0 : ℝ) + 1) * hhT (u : ℝ) (v : ℝ) := lp_snd_eq
          rw [this] at hi
          have := hhT_pos hu huv hv2
          linarith
        · exfalso
          rw [h, hj] at hi
          have : (lpT (u : ℝ) (v : ℝ) ε x (((n - 1 : ℕ) : ℝ) + 1) (0 + 1)) 1 = ((0 : ℝ) + 1) * hhT (u : ℝ) (v : ℝ) := lp_snd_eq
          rw [this] at hi
          have := hhT_pos hu huv hv2
          linarith
      exact hmV (hy m' hm1)
    obtain ⟨mm, hfan⟩ := pinfan_ang D S.hirr S.hM.hα' (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α
      hVf (hVnv ⟨t', k', m', hk'm', hk', hm1, hmV, hang⟩) tD t' hne Ang.ga Ang.ga (by rw [hgam, S.hγ]; simp [angVal]) (by rw [hang, S.hγ]; simp [angVal])
    exact no_two_gamma _ _ mm hfan ⟨rfl, rfl⟩

theorem lemmaK2 (C : CtxBaseT D u v α β γ L ax ay ε x) {n : ℕ} (hn1 : 1 ≤ n) (hnv : n < v)
    (L32 : L32Hyp D (u : ℝ) (v : ℝ) ε x α n)
    (hrun : ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) ε x (i : ℝ) 0)
    (hPf : ∀ w : ℕ, 1 ≤ w → w ≤ n → lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ∈ frontier D.target.carrier ∧
      lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ∉ Set.range D.target.pts ∧
      ((ε = 1 ∧ gA ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) = 0) ∨
        (ε = -1 ∧ gB L ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) = 0)))
    (hQf : ∀ w : ℕ, 1 ≤ w → w ≤ n → lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ frontier D.target.carrier)
    (hint : ∀ w : ℕ, 1 ≤ w → w ≤ n →
      openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
        interior D.target.carrier)
    (hVnv : (∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) →
      lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∉ Set.range D.target.pts)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∈ Set.range D.target.pts ∨
      ∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) : False :=
  lemmaK2_gen C hn1 hnv L32 hrun
    (fun w h1 h2 _ => PGood_of_frontier C (by exact_mod_cast (by omega : 0 < w)) (hPf w h1 h2).1 (hPf w h1 h2).2.1
      (hPf w h1 h2).2.2 (hint w h1 h2)) hQf (fun w h1 h2 _ => hint w h1 h2) hVnv hnoγ hstop

#print axioms lemmaK2_gen
#print axioms lemmaK2
end Erdos634.Draft.ThmDRun
