/-
Draft/WGapGen6.lean -- written 16 November 2026 (session 15).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2).
Not imported by any aggregate.  No sorry, no native_decide.
* `col_lattice`: the column dichotomy `ColD` at `A_t = pi(t,0)` from the lattice tiles `D(t-1,.)`, `U(t,.)`, `U(t-1,.)`, `N^{t-1}`, `N^t` (`rl_gamma_fill2`).
* **`rl_gen`**: LEMMA RL (PROOF 8.2) at EVERY `i` and every left index `0 <= t <= i`, with `i + 1 <= f - 1`:
  (r1) the lattice tiles `N^{t'}`, `U(t', j+i-t')` for `t <= t' <= i`, `D(t'-1, j+i-t')` for `t < t' <= i`; (r2) = `hP4`; (r3) = `hleft` at `A_t = pi(t,0)`; conclusion `False`.
  (`rl_one`, `rl_two`, `rl_three`, ... are instances; `rl_one_sh`-type translations are not needed.)
-/
import Erdos634.Draft.WGapGen5

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

section gen6

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
theorem col_lattice (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i t0 t : ℕ) (ht1 : t0 < t) (ht2 : t ≤ i)
    (hN : ∀ t' : ℕ, t0 ≤ t' → t' ≤ i → ∃ T : Fin N,
      HasV D T (lpG (e : ℝ) f 1 x ((t' : ℝ) + 1) ((j : ℝ) + i - t')) (lpG (e : ℝ) f 1 x (t' : ℝ) ((j : ℝ) + i - t' + 1))
        (lpG (e : ℝ) f 1 x ((t' : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + i - t' + 2 + nuG (e : ℝ) f)))
    (hU : ∀ t' : ℕ, t0 ≤ t' → t' ≤ i → ∃ T : Fin N,
      HasV D T (lpG (e : ℝ) f 1 x (t' : ℝ) ((j : ℝ) + i - t')) (lpG (e : ℝ) f 1 x ((t' : ℝ) + 1) ((j : ℝ) + i - t'))
        (lpG (e : ℝ) f 1 x (t' : ℝ) ((j : ℝ) + i - t' + 1)))
    (hD : ∀ t' : ℕ, t0 < t' → t' ≤ i → ∃ T : Fin N,
      HasV D T (lpG (e : ℝ) f 1 x (t' : ℝ) ((j : ℝ) + i - t')) (lpG (e : ℝ) f 1 x ((t' : ℝ) - 1) ((j : ℝ) + i - t' + 1))
        (lpG (e : ℝ) f 1 x (t' : ℝ) ((j : ℝ) + i - t' + 1))) :
    ColD D e f x j i (t : ℝ) ((0 : ℕ) : ℝ) := by
  have he0 := S.e0
  have hef := S.hef'
  have hν0 := nuG_pos he0 hef
  obtain ⟨tDL, hD0⟩ := hD t ht1 ht2
  obtain ⟨tUl, hUl0⟩ := hU t (by omega) ht2
  obtain ⟨tUi, hUi0⟩ := hU (t - 1) (by omega) (by omega)
  obtain ⟨tN, hN0⟩ := hN (t - 1) (by omega) (by omega)
  obtain ⟨tN2, hN20⟩ := hN t (by omega) ht2
  have htc : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [htc] at hUi0 hN0
  have hfill := rl_gamma_fill2 S x ((t : ℝ) - 1) ((j : ℝ) + i - t)
    (tUi := tUi) (tDL := tDL) (tUl := tUl) (tN := tN) (tN2 := tN2)
    (hasV_congr hD0 (lpG_congr (by ring) (by ring)) (lpG_congr (by ring) (by ring)) (lpG_congr (by ring) (by ring)))
    (hasV_congr hUl0 (lpG_congr (by ring) (by ring)) (lpG_congr (by ring) (by ring)) (lpG_congr (by ring) (by ring)))
    (hasV_congr hUi0 (lpG_congr (by ring) (by ring)) (lpG_congr (by ring) (by ring)) (lpG_congr (by ring) (by ring)))
    (hasV_congr hN0 (lpG_congr (by ring) (by ring)) (lpG_congr (by ring) (by ring)) (lpG_congr (by ring) (by ring)))
    (hasV_congr hN20 (lpG_congr (by ring) (by ring)) (lpG_congr (by ring) (by ring)) (lpG_congr (by ring) (by ring)))
  have hO : ptO (e : ℝ) f x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1) = PIR (e : ℝ) f x j i (t : ℝ) 0 := by
    rw [PIR_lp he0 hef]; unfold ptO; exact lpG_congr (by ring) (by ring)
  have hY : ptY (e : ℝ) f x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1) = PIR (e : ℝ) f x j i ((t : ℝ) - 1) 1 := by
    rw [PIR_lp he0 hef]; unfold ptY; exact lpG_congr (by ring) (by ring)
  have hB : PIR (e : ℝ) f x j i (t : ℝ) 1 = ptO (e : ℝ) f x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1) + nuG (e : ℝ) f •
      (ptV (e : ℝ) f x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1) - ptO (e : ℝ) f x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1)) := by
    rw [PIR_aff (e : ℝ) f x j i (t : ℝ) 1, one_smul, wvec_eq, ptVO_dc, hO]
  have hm0 : PIR (e : ℝ) f x j i (t : ℝ) ((0 : ℕ) : ℝ) = ptO (e : ℝ) f x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1) := by
    rw [hO]; exact PIR_congr rfl (by simp)
  rcases hfill with ⟨τ1, R, hV, hcr, hRY⟩ | ⟨τ1, R, hV, hcr, hRV⟩
  · left
    exact ⟨τ1, hasV_congr hV hm0.symm (hB.symm.trans (PIR_congr rfl (by simp)))
      ((hRY.trans hY).trans (PIR_congr rfl (by simp)))⟩
  · right
    refine ⟨τ1, ptO (e : ℝ) f x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1) + nuG (e : ℝ) f •
      (ptY (e : ℝ) f x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1) - ptO (e : ℝ) f x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1)), ?_, ?_⟩
    · refine hasV_congr hV.rot.rot.swap hm0.symm ?_ rfl
      rw [hm0, one_smul, hRV, ← ptVO_dc (e : ℝ) f x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1)]
      abel
    · rw [hm0, add_sub_cancel_left, cross_smul_right', ← ptVO_dc (e : ℝ) f x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1)]
      exact mul_pos hν0 (cross_V_Y_pos he0 hef x ((t : ℝ) - 1) (((j : ℝ) + i - t) + 1))

set_option maxHeartbeats 16000000 in
/-- **Lemma RL at every `i`**, left tile at `A_t` (`0 <= t <= i`) -/
theorem rl_gen (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i t : ℕ) (hi : i + 1 ≤ f - 1) (hti : t ≤ i)
    (hN : ∀ t' : ℕ, t ≤ t' → t' ≤ i → ∃ T : Fin N,
      HasV D T (lpG (e : ℝ) f 1 x ((t' : ℝ) + 1) ((j : ℝ) + i - t')) (lpG (e : ℝ) f 1 x (t' : ℝ) ((j : ℝ) + i - t' + 1))
        (lpG (e : ℝ) f 1 x ((t' : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + i - t' + 2 + nuG (e : ℝ) f)))
    (hU : ∀ t' : ℕ, t ≤ t' → t' ≤ i → ∃ T : Fin N,
      HasV D T (lpG (e : ℝ) f 1 x (t' : ℝ) ((j : ℝ) + i - t')) (lpG (e : ℝ) f 1 x ((t' : ℝ) + 1) ((j : ℝ) + i - t'))
        (lpG (e : ℝ) f 1 x (t' : ℝ) ((j : ℝ) + i - t' + 1)))
    (hD : ∀ t' : ℕ, t < t' → t' ≤ i → ∃ T : Fin N,
      HasV D T (lpG (e : ℝ) f 1 x (t' : ℝ) ((j : ℝ) + i - t')) (lpG (e : ℝ) f 1 x ((t' : ℝ) - 1) ((j : ℝ) + i - t' + 1))
        (lpG (e : ℝ) f 1 x (t' : ℝ) ((j : ℝ) + i - t' + 1)))
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j) < 0)
    (hleft : ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f x j i (t : ℝ) ((0 : ℕ) : ℝ)) (PIR (e : ℝ) f x j i (t : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f x) R ∧
      0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j i (t : ℝ) ((0 : ℕ) : ℝ))) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have st0 : RLSt D e f x j i 0 t := by
    refine ⟨?_, ?_, ⟨0, le_rfl, hleft⟩⟩
    · intro m' hm' t' ht1 ht2
      obtain rfl : m' = 0 := by omega
      obtain ⟨T, hT⟩ := hN t' ht1 (by omega)
      exact ⟨T, hasV_PIR he0 hef hT (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
        (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩
    · intro m1 h
      omega
  by_cases ht : t = i
  · exact rl_end S x j i 0 t hi hP4 (by omega) st0
  · obtain ⟨τ', hτ', hτ'i, st1⟩ := rl_step_core S x j i 0 t hi hP4 (by omega) st0
      (fun t1 h1 h2 => col_lattice S x j i t t1 h1 (by omega) hN hU hD)
    exact rl_run S x j i hi hP4 (i - (0 + 1) - τ') (0 + 1) τ' (by omega) (by omega) st1

end gen6

#print axioms col_lattice
#print axioms rl_gen

end Erdos634.Draft.WGapStmt
