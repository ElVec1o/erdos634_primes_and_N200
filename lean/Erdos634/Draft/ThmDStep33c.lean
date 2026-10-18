import Mathlib.Tactic
import Erdos634.Draft.ThmDStep33b
import Erdos634.Draft.ThmDPGoodCorner
import Erdos634.Draft.ThmDPGoodSector

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: 'how not to start a run' (their Lemma 33, p. 28).
# Theorem D' (R5): `step33`  (; CONDITIONAL on Lemma 32 `L32Hyp`)
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg Erdos634.Draft.ThmDRowFar

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem step33_gen (C : CtxBaseT D u v α β γ L ax ay ε x) {n : ℕ} (L32 : L32Hyp D (u : ℝ) (v : ℝ) ε x α n)
    {w : ℕ} (hw1 : 1 ≤ w) (hwn : w < n) (hnv : n < v)
    (HTw : HT D (u : ℝ) (v : ℝ) ε x w)
    (hrun : UTT D (u : ℝ) (v : ℝ) ε x (w : ℝ) 0)
    (hPG : PGood D (u : ℝ) (v : ℝ) ε x α (w : ℝ))
    (hQf : lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ frontier D.target.carrier)
    (hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
      interior D.target.carrier) :
    HT D (u : ℝ) (v : ℝ) ε x (w + 1) := by
  have S := C.S
  have hε := C.e2
  have hwv : w < v := by omega
  have hw0 : 0 < w := by omega
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw0
  have hcast : ∀ a b : ℕ, b ≤ a → ((a - b : ℕ) : ℝ) = (a : ℝ) - b := fun a b h => Nat.cast_sub h
  -- the near towers
  have hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)) := by
    intro i hi
    have hU := HTw.1 i (w - 1 - i) (by omega) (by omega)
    have hj : ((w - 1 - i : ℕ) : ℝ) = ηw w i := by
      unfold ηw; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    obtain ⟨t, ht⟩ := hU
    exact ⟨t, hasV_congr ht (lpT_congr rfl hj) (lpT_congr rfl hj) (lpT_congr rfl (by rw [hj]))⟩
  -- the far row
  have hP1 : lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) = lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) :=
    lpT_congr (by simp) (by unfold ηw; simp)
  have hfar := row_orient_full_gen C w hw0 hwv hnear hPG hQf hint
  -- nabla row as `DTT`
  have hDN : ∀ i : ℕ, i < w → DTT D (u : ℝ) (v : ℝ) ε x (i : ℝ) ((w - 1 - i : ℕ) : ℝ) := by
    intro i hi
    have hj : ((w - 1 - i : ℕ) : ℝ) = ηw w i := by
      unfold ηw; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [hj]
    exact hfar i hi
  -- the alpha tiles G_j
  have hG : ∀ j : ℕ, j ≤ w → UTT D (u : ℝ) (v : ℝ) ε x ((w - j : ℕ) : ℝ) (j : ℝ) ∨
      BEastT D (u : ℝ) (v : ℝ) ε x α ((w - j : ℕ) : ℝ) (j : ℝ) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · left
      simpa using hrun
    · rcases Nat.lt_or_ge j w with hjw | hjw
      · -- interior diagonal vertex
        have hjR : (j : ℝ) < w := by exact_mod_cast hjw
        have hj0R : (0 : ℝ) < j := by exact_mod_cast hj0
        have hξ : ((w - j : ℕ) : ℝ) = (w : ℝ) - j := hcast w j hj
        have hxi := diag_vertex_interior S hε hw0 hj0R hjR hint
        have e1 : ((w - j - 1 : ℕ) : ℝ) = ((w - j : ℕ) : ℝ) - 1 := by
          rw [hξ]; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
        have e5 : ((w - 1 - (w - j) : ℕ) : ℝ) = (j : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
        have e4 : ((w - 1 - (w - j - 1) : ℕ) : ℝ) = (j : ℝ) := by
          have : w - 1 - (w - j - 1) = j := by omega
          rw [this]
        have u1 : UTT D (u : ℝ) (v : ℝ) ε x (((w - j : ℕ) : ℝ) - 1) (j : ℝ) :=
          UTT_congr (HTw.1 (w - j - 1) j (by omega) (by omega)) e1 rfl
        have u2 : UTT D (u : ℝ) (v : ℝ) ε x ((w - j : ℕ) : ℝ) ((j : ℝ) - 1) := by
          have := HTw.1 (w - j) (j - 1) (by omega) (by omega)
          exact UTT_congr this rfl (by rw [Nat.cast_sub (by omega)]; simp)
        have d3 : DTT D (u : ℝ) (v : ℝ) ε x (((w - j : ℕ) : ℝ) - 1) ((j : ℝ) - 1) := by
          have := HTw.2 (w - j - 1) (j - 1) (by omega) (by omega)
          exact DTT_congr this e1 (by rw [Nat.cast_sub (by omega)]; simp)
        have d4 : DTT D (u : ℝ) (v : ℝ) ε x (((w - j : ℕ) : ℝ) - 1) (j : ℝ) :=
          DTT_congr (hDN (w - j - 1) (by omega)) e1 e4
        have d5 : DTT D (u : ℝ) (v : ℝ) ε x ((w - j : ℕ) : ℝ) ((j : ℝ) - 1) :=
          DTT_congr (hDN (w - j) (by omega)) rfl e5
        have hx' : lpT (u : ℝ) (v : ℝ) ε x ((w - j : ℕ) : ℝ) (j : ℝ) ∈ interior D.target.carrier := by
          rw [hξ]; exact hxi
        exact sector_dichotomy_UD C hx' u1 u2 d3 d4 d5
      · -- the end P on the side
        have hjw' : j = w := le_antisymm hj hjw
        subst hjw'
        have hη : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj0
        have uD : UTT D (u : ℝ) (v : ℝ) ε x 0 ((j : ℝ) - 1) := by
          have := HTw.1 0 (j - 1) (by omega) (by omega)
          exact UTT_congr this (by simp) (by rw [Nat.cast_sub (by omega)]; simp)
        have dN : DTT D (u : ℝ) (v : ℝ) ε x 0 ((j : ℝ) - 1) := by
          have := hDN 0 (by omega)
          exact DTT_congr this (by simp) (by rw [Nat.sub_zero, Nat.cast_pred hj0])
        have := sector_dichotomy_PD_good C hη hPG uD dN
        simpa using this
  -- the conclusion
  by_cases hall : ∀ j : ℕ, j ≤ w → UTT D (u : ℝ) (v : ℝ) ε x ((w - j : ℕ) : ℝ) (j : ℝ)
  · -- every G_j is Delta: H(w+1)
    refine ⟨fun i j hj hij => ?_, fun i j hj hij => ?_⟩
    · by_cases hlt : i + j + 1 ≤ w
      · exact HTw.1 i j (by omega) hlt
      · have hij' : i = w - j := by omega
        have := hall j (by omega)
        rw [← hij'] at this
        exact this
    · by_cases hlt : i + j + 2 ≤ w
      · exact HTw.2 i j (by omega) hlt
      · have hij' : j = w - 1 - i := by omega
        have := hDN i (by omega)
        rw [← hij'] at this
        exact this
  · exfalso
    push_neg at hall
    have hex : ∃ j : ℕ, j ≤ w ∧ ¬ UTT D (u : ℝ) (v : ℝ) ε x ((w - j : ℕ) : ℝ) (j : ℝ) := hall
    obtain ⟨js, hjsw, hjsU, hmin⟩ : ∃ js : ℕ, js ≤ w ∧ ¬ UTT D (u : ℝ) (v : ℝ) ε x ((w - js : ℕ) : ℝ) (js : ℝ) ∧
        ∀ j : ℕ, j < js → UTT D (u : ℝ) (v : ℝ) ε x ((w - j : ℕ) : ℝ) (j : ℝ) := by
      refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j hj => ?_⟩
      by_contra hn
      exact Nat.find_min hex hj ⟨by have := (Nat.find_spec hex).1; omega, hn⟩
    have hjs1 : 1 ≤ js := by
      rcases Nat.eq_zero_or_pos js with h0 | h0
      · exfalso; apply hjsU; rw [h0]; simpa using hrun
      · exact h0
    have hBE := (hG js hjsw).resolve_left hjsU
    have hTrap : TrapT D (u : ℝ) (v : ℝ) ε x (w + 1) js := by
      refine ⟨fun i j hj hij => ?_, fun i j hj hij => ?_⟩
      · by_cases hlt : i + j + 1 ≤ w
        · exact HTw.1 i j (by omega) hlt
        · have hij' : i = w - j := by omega
          have := hmin j hj
          rw [← hij'] at this
          exact this
      · by_cases hlt : i + j + 2 ≤ w
        · exact HTw.2 i j (by omega) hlt
        · have hij' : j = w - 1 - i := by omega
          have := hDN i (by omega)
          rw [← hij'] at this
          exact this
    exact L32 (w + 1) js (w - js) hjs1 (by omega) (by omega) (by omega) hTrap hBE

theorem step33 (C : CtxBaseT D u v α β γ L ax ay ε x) {n : ℕ} (L32 : L32Hyp D (u : ℝ) (v : ℝ) ε x α n)
    {w : ℕ} (hw1 : 1 ≤ w) (hwn : w < n) (hnv : n < v)
    (HTw : HT D (u : ℝ) (v : ℝ) ε x w)
    (hrun : UTT D (u : ℝ) (v : ℝ) ε x (w : ℝ) 0)
    (hPf : lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ∈ frontier D.target.carrier)
    (hPnv : lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ∉ Set.range D.target.pts)
    (hside : (ε = 1 ∧ gA ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) = 0) ∨
      (ε = -1 ∧ gB L ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) = 0))
    (hQf : lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ frontier D.target.carrier)
    (hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
      interior D.target.carrier) :
    HT D (u : ℝ) (v : ℝ) ε x (w + 1) :=
  step33_gen C L32 hw1 hwn hnv HTw hrun
    (PGood_of_frontier C (by exact_mod_cast (by omega : 0 < w)) hPf hPnv hside hint) hQf hint

#print axioms step33_gen
#print axioms step33
end Erdos634.Draft.ThmDRun
