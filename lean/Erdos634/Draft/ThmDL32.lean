import Mathlib.Tactic
import Erdos634.Draft.ThmDL32B
import Erdos634.Draft.ThmDK2

/-!
# Theorem D' (Lemma 32): the trapezoid lemma  

`lemma32` : `L32Hyp D u v ε x α n`, by downward induction on `s` (Beeson-Rosu Lemma 32, pp. 26-27), from
* step A (`L32_A`): `R = x(s-r,r)` is interior to a north chain edge (rigidity window `RC`);
* step B (`L32_B`): the east chain of `σ = q_0 R` is the column `∇_{s-1-j,j}`, `j < r`;
* the stop: `∇_{s-1,0}` has `γ` at `q_0`, so `s < n` (`stop_contra`);
* the `α`-tiles `G_j` at the interior diagonal vertices (`sector_dichotomy_UD`): `Δ_{s-j,j}` or a `b`-edge east;
* `T(s+1, r)` or `T(s+1, j*)` occurs, against the induction hypothesis.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.ThmDHalf
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **The stop**: `∇_{n-1,0}` has `γ` at `V = lp n 0`, against the stop at `V`. -/
theorem stop_contra (C : CtxBaseT D u v α β γ L ax ay ε x) {n : ℕ} (hn1 : 1 ≤ n)
    (hD : DTT D (u : ℝ) (v : ℝ) ε x ((n - 1 : ℕ) : ℝ) 0)
    (hVf : lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∈ frontier D.target.carrier)
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
  obtain ⟨tD, hD'⟩ := hD
  have e1 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by rw [Nat.cast_sub hn1]; simp
  have hgam := (D_anglesT hu huv hv2 hε S.tile.hab S.tile.ac S.tile.bc S.hM hD').1
  rw [e1] at hgam
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hD'
  have hkV : (D.tile tD).pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 := by rw [hk, e1]
  rcases hstop with hvert | ⟨t', k', m', hk'm', hk', hm1, hmV, hang⟩
  · exact hnoγ tD k (by rw [hkV]; exact hvert) (by rw [hkV]; exact hgam)
  · have h3α : 3 * α < Real.pi := by
      have hβpos : 0 < β := by
        have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
        have e : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
        rw [e] at h; exact h
      have := S.hβ; linarith
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

#print axioms stop_contra

/-- **Lemma 32 (the trapezoid lemma).** -/
theorem lemma32_gen (C : CtxBaseT D u v α β γ L ax ay ε x) {n : ℕ} (hn1 : 1 ≤ n) (hnv : n < v)
    (hrun : ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) ε x (i : ℝ) 0)
    (hPR : ∀ w : ℕ, 1 ≤ w → w ≤ n → (∀ j : ℕ, j < w → UTT D (u : ℝ) (v : ℝ) ε x 0 (j : ℝ)) →
      PRow D (u : ℝ) (v : ℝ) ε x (w : ℝ))
    (hVf : lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∈ frontier D.target.carrier)
    (hVnv : (∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) →
      lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∉ Set.range D.target.pts)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∈ Set.range D.target.pts ∨
      ∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) :
    L32Hyp D (u : ℝ) (v : ℝ) ε x α n := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  intro s0 r0 i00
  have key : ∀ k : ℕ, ∀ s r i0 : ℕ, n - s = k → 1 ≤ r → r < s → s ≤ n → i0 + r < s →
      TrapT D (u : ℝ) (v : ℝ) ε x s r → BEastT D (u : ℝ) (v : ℝ) ε x α (i0 : ℝ) (r : ℝ) → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s r i0 hk h1r hrs hsn hi0 Tt hB
      obtain ⟨tN, kN, mN, hkm, hk', hm', hle', hR'⟩ :=
        L32_A_gen C hnv h1r hrs hsn hi0 Tt hB (hPR r h1r (by omega) (fun j hj => by simpa using Tt.1 0 j hj (by omega)))
      obtain ⟨hcol, hintσ⟩ := L32_B C hnv h1r hrs hsn Tt ⟨tN, kN, mN, hkm, hk', hm', hle', hR'⟩
      -- the run does not stop at `q_0`
      have hsn' : s < n := by
        by_contra hge
        have hs : s = n := by omega
        subst hs
        refine stop_contra C hn1 ?_ hVf hVnv hnoγ hstop
        have := hcol 0 (by omega)
        simpa using this
      -- the `α`-tiles at the interior diagonal vertices
      have hG : ∀ j : ℕ, j < r → UTT D (u : ℝ) (v : ℝ) ε x ((s - j : ℕ) : ℝ) (j : ℝ) ∨
          BEastT D (u : ℝ) (v : ℝ) ε x α ((s - j : ℕ) : ℝ) (j : ℝ) := by
        intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · left
          simpa using hrun s hsn'
        · have hξ : ((s - j : ℕ) : ℝ) = (s : ℝ) - j := Nat.cast_sub (by omega)
          have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
          have hjr : (j : ℝ) < r := by exact_mod_cast hj
          have haR : ((s - r : ℕ) : ℝ) + (r : ℝ) = (s : ℝ) := by rw [Nat.cast_sub hrs.le]; ring
          have hrpos : (0 : ℝ) < r := by linarith
          have hx : lpT (u : ℝ) (v : ℝ) ε x ((s - j : ℕ) : ℝ) (j : ℝ) ∈ interior D.target.carrier := by
            apply hintσ
            rw [openSegment_eq_image_lineMap]
            refine ⟨((r : ℝ) - j) / r, ⟨by apply div_pos <;> linarith, ?_⟩, ?_⟩
            · rw [div_lt_one hrpos]; linarith
            · rw [lineMap_lpT, hξ]
              refine lpT_congr ?_ ?_
              · rw [← haR]; field_simp; ring
              · field_simp; ring
          have e1 : ((s - j - 1 : ℕ) : ℝ) = ((s - j : ℕ) : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega), hξ]; simp
          have ej : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj0]; simp
          have u1 : UTT D (u : ℝ) (v : ℝ) ε x (((s - j : ℕ) : ℝ) - 1) (j : ℝ) :=
            UTT_congr (Tt.1 (s - j - 1) j (by omega) (by omega)) e1 rfl
          have u2 : UTT D (u : ℝ) (v : ℝ) ε x ((s - j : ℕ) : ℝ) ((j : ℝ) - 1) :=
            UTT_congr (Tt.1 (s - j) (j - 1) (by omega) (by omega)) rfl ej
          have d3 : DTT D (u : ℝ) (v : ℝ) ε x (((s - j : ℕ) : ℝ) - 1) ((j : ℝ) - 1) :=
            DTT_congr (Tt.2 (s - j - 1) (j - 1) (by omega) (by omega)) e1 ej
          have d4 : DTT D (u : ℝ) (v : ℝ) ε x (((s - j : ℕ) : ℝ) - 1) (j : ℝ) := by
            have := hcol j hj
            have e2 : ((s - 1 - j : ℕ) : ℝ) = ((s - j : ℕ) : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hξ]; simp; ring
            exact DTT_congr this e2 rfl
          have d5 : DTT D (u : ℝ) (v : ℝ) ε x ((s - j : ℕ) : ℝ) ((j : ℝ) - 1) := by
            have := hcol (j - 1) (by omega)
            have e2 : ((s - 1 - (j - 1) : ℕ) : ℝ) = ((s - j : ℕ) : ℝ) := by
              congr 1; omega
            exact DTT_congr this e2 ej
          exact sector_dichotomy_UD C hx u1 u2 d3 d4 d5
      -- conclusion
      by_cases hall : ∀ j : ℕ, j < r → UTT D (u : ℝ) (v : ℝ) ε x ((s - j : ℕ) : ℝ) (j : ℝ)
      · have hT : TrapT D (u : ℝ) (v : ℝ) ε x (s + 1) r := by
          refine ⟨fun i j hj hij => ?_, fun i j hj hij => ?_⟩
          · by_cases hlt : i + j + 1 ≤ s
            · exact Tt.1 i j hj hlt
            · have hij' : i = s - j := by omega
              have := hall j hj
              rw [← hij'] at this
              exact this
          · by_cases hlt : i + j + 2 ≤ s
            · exact Tt.2 i j hj hlt
            · have hij' : i = s - 1 - j := by omega
              have := hcol j hj
              rw [← hij'] at this
              exact this
        exact ih (n - (s + 1)) (by omega) (s + 1) r i0 rfl h1r (by omega) (by omega) (by omega) hT hB
      · push_neg at hall
        have hex : ∃ j : ℕ, j < r ∧ ¬ UTT D (u : ℝ) (v : ℝ) ε x ((s - j : ℕ) : ℝ) (j : ℝ) := hall
        obtain ⟨js, hjsr, hjsU, hmin⟩ : ∃ js : ℕ, js < r ∧ ¬ UTT D (u : ℝ) (v : ℝ) ε x ((s - js : ℕ) : ℝ) (js : ℝ) ∧
            ∀ j : ℕ, j < js → UTT D (u : ℝ) (v : ℝ) ε x ((s - j : ℕ) : ℝ) (j : ℝ) := by
          refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j hj => ?_⟩
          by_contra hn
          exact Nat.find_min hex hj ⟨by have := (Nat.find_spec hex).1; omega, hn⟩
        have hjs1 : 1 ≤ js := by
          rcases Nat.eq_zero_or_pos js with h0 | h0
          · exfalso; apply hjsU; rw [h0]; simpa using hrun s hsn'
          · exact h0
        have hBE := (hG js hjsr).resolve_left hjsU
        have hT : TrapT D (u : ℝ) (v : ℝ) ε x (s + 1) js := by
          refine ⟨fun i j hj hij => ?_, fun i j hj hij => ?_⟩
          · by_cases hlt : i + j + 1 ≤ s
            · exact Tt.1 i j (by omega) hlt
            · have hij' : i = s - j := by omega
              have := hmin j hj
              rw [← hij'] at this
              exact this
          · by_cases hlt : i + j + 2 ≤ s
            · exact Tt.2 i j (by omega) hlt
            · have hij' : i = s - 1 - j := by omega
              have := hcol j (by omega)
              rw [← hij'] at this
              exact this
        exact ih (n - (s + 1)) (by omega) (s + 1) js (s - js) rfl hjs1 (by omega) (by omega) (by omega) hT hBE
  intro hr0 hrs0 hsn0 hi0 Tt hB
  exact key (n - s0) s0 r0 i00 rfl hr0 hrs0 hsn0 hi0 Tt hB

theorem lemma32 (C : CtxBaseT D u v α β γ L ax ay ε x) {n : ℕ} (hn1 : 1 ≤ n) (hnv : n < v)
    (hrun : ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) ε x (i : ℝ) 0)
    (hPf : ∀ w : ℕ, 1 ≤ w → w ≤ n → lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ∈ frontier D.target.carrier ∧
      lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ∉ Set.range D.target.pts ∧
      ((ε = 1 ∧ gA ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) = 0) ∨
        (ε = -1 ∧ gB L ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) = 0)))
    (hVf : lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∈ frontier D.target.carrier)
    (hVnv : (∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) →
      lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∉ Set.range D.target.pts)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∈ Set.range D.target.pts ∨
      ∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) :
    L32Hyp D (u : ℝ) (v : ℝ) ε x α n :=
  lemma32_gen C hn1 hnv hrun
    (fun w h1 h2 _ => PRow_of_frontier C (hPf w h1 h2).1 (hPf w h1 h2).2.2) hVf hVnv hnoγ hstop

#print axioms lemma32_gen
#print axioms lemma32
end Erdos634.Draft.ThmDRun
