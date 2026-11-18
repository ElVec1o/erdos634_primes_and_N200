/-
Draft/WGapGen5.lean -- written 16 November 2026 (session 15).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2).
Not imported by any aggregate.  No sorry, no native_decide.
* `col_layer`: the column dichotomy `ColD` at every point `pi(t,m1+1)`, `τ < t <= i-m`, from State(m1+1,τ) (`rl_fill_layer2`).
* `rl_end`: State(m,τ) with `τ + m = i` gives `False` (`rl_close`).
* `rl_run`: State(m,τ) with `1 <= m` gives `False`, by induction on `i - m - τ` (`rl_step_core` + `col_layer` + `rl_end`).
-/
import Erdos634.Draft.WGapGen4

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

section gen5

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ}

/-- `cross dcvec (Y - O) = kappa (s - 1) > 0` for `O = pi(t,m)`, `Y = pi(t-1,m+1)` -/
theorem cross_dc_Y_pos {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j i : ℕ) (t m : ℝ) :
    0 < cross (dcvec e f x) (PIR e f x j i (t - 1) (m + 1) - PIR e f x j i t m) := by
  have hκ := kapG_pos he hef
  have hns := nu_s' he hef
  have hs2 := sMir_gt_two he hef
  have : cross (dcvec e f x) (PIR e f x j i (t - 1) (m + 1) - PIR e f x j i t m) = kapG e f * (sMir e f - 1) := by
    rw [PIR_lp he hef, PIR_lp he hef]
    unfold dcvec
    rw [cross_lpG]
    linear_combination (kapG e f) * hns
  rw [this]; exact mul_pos hκ (by linarith)

set_option maxHeartbeats 8000000 in
theorem col_layer (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i m1 τ : ℕ) (st : RLSt D e f x j i (m1 + 1) τ)
    (t : ℕ) (ht1 : τ < t) (ht2 : t + (m1 + 1) ≤ i) :
    ColD D e f x j i (t : ℝ) (((m1 + 1 : ℕ)) : ℝ) := by
  have he0 := S.e0
  have hef := S.hef'
  have hν0 := nuG_pos he0 hef
  have hO : (((m1 + 1 : ℕ)) : ℝ) = (m1 : ℝ) + 1 := by push_cast; ring
  rw [hO]
  obtain ⟨T1, h1⟩ := st.nu m1 (by omega) t (by omega) (by omega)
  obtain ⟨T2, h2⟩ := st.ga m1 rfl t ht1 (by omega)
  obtain ⟨T3, h3⟩ := st.ga m1 rfl (t + 1) (by omega) (by omega)
  obtain ⟨T4, h4⟩ := st.nu (m1 + 1) le_rfl t (by omega) ht2
  obtain ⟨T5, h5⟩ := st.nu (m1 + 1) le_rfl (t - 1) (by omega) (by omega)
  have htc : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h3' : HasV D T3 (PIR (e : ℝ) f x j i ((t : ℝ) + 1) (m1 : ℝ)) (PIR (e : ℝ) f x j i ((t : ℝ) + 1) ((m1 : ℝ) + 1))
      (PIR (e : ℝ) f x j i (t : ℝ) ((m1 : ℝ) + 1)) :=
    hasV_congr h3 (PIR_congr (by push_cast; ring) rfl) (PIR_congr (by push_cast; ring) rfl)
      (PIR_congr (by push_cast; ring) rfl)
  have h4' : HasV D T4 (PIR (e : ℝ) f x j i ((t : ℝ) + 1) ((m1 : ℝ) + 1)) (PIR (e : ℝ) f x j i (t : ℝ) ((m1 : ℝ) + 1))
      (PIR (e : ℝ) f x j i (t : ℝ) ((m1 : ℝ) + 1 + 1)) :=
    hasV_congr h4 (PIR_congr rfl (by push_cast; ring)) (PIR_congr rfl (by push_cast; ring))
      (PIR_congr rfl (by push_cast; ring))
  have h5' : HasV D T5 (PIR (e : ℝ) f x j i (t : ℝ) ((m1 : ℝ) + 1)) (PIR (e : ℝ) f x j i ((t : ℝ) - 1) ((m1 : ℝ) + 1))
      (PIR (e : ℝ) f x j i ((t : ℝ) - 1) ((m1 : ℝ) + 1 + 1)) :=
    hasV_congr h5 (PIR_congr (by rw [htc]; ring) (by push_cast; ring)) (PIR_congr (by rw [htc]) (by push_cast; ring))
      (PIR_congr (by rw [htc]) (by push_cast; ring))
  rcases rl_fill_layer2 S x j i (t : ℝ) (m1 : ℝ) h1 h2 h3' h4' h5' with ⟨τ1, R, hV, hcr, hR⟩ | ⟨τ1, R, hV, hcr, hR⟩
  · left
    refine ⟨τ1, hasV_congr hV rfl ?_ hR⟩
    rw [PIR_shift (e : ℝ) f x j i (t : ℝ) ((m1 : ℝ) + 1) 1, one_smul]
  · right
    refine ⟨τ1, PIR (e : ℝ) f x j i (t : ℝ) ((m1 : ℝ) + 1) + nuG (e : ℝ) f •
      (PIR (e : ℝ) f x j i ((t : ℝ) - 1) ((m1 : ℝ) + 1 + 1) - PIR (e : ℝ) f x j i (t : ℝ) ((m1 : ℝ) + 1)), ?_, ?_⟩
    · refine hasV_congr hV.rot.rot.swap rfl ?_ rfl
      rw [one_smul]; exact hR
    · rw [add_sub_cancel_left, cross_smul_right']
      exact mul_pos hν0 (cross_dc_Y_pos he0 hef x j i (t : ℝ) ((m1 : ℝ) + 1))

set_option maxHeartbeats 8000000 in
theorem rl_end (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i m τ : ℕ) (hi : i + 1 ≤ f - 1)
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j) < 0)
    (hτ : τ + m = i) (st : RLSt D e f x j i m τ) : False := by
  have hcs : ∀ p q : ℕ, q ≤ p → ((p - q : ℕ) : ℝ) = (p : ℝ) - q := fun p q h => Nat.cast_sub h
  obtain ⟨μ0, hμ0, hleft⟩ := st.left
  refine rl_close S x j i τ μ0 m hμ0 (by omega) hi hτ ?_ hP4 ?_ hleft
  · intro m' hm'
    obtain ⟨T, hT⟩ := st.nu m' hm' (i - m') (by omega) (by omega)
    refine ⟨T, hasV_congr hT ?_ ?_ ?_⟩
    · exact PIR_congr (by rw [hcs i m' (by omega)]) rfl
    · exact PIR_congr (by rw [hcs i m' (by omega)]) rfl
    · exact PIR_congr (by rw [hcs i m' (by omega)]) rfl
  · intro m' _ hm'
    exact st.nu m' hm' τ le_rfl (by omega)

set_option maxHeartbeats 16000000 in
theorem rl_run (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i : ℕ) (hi : i + 1 ≤ f - 1)
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j) < 0) :
    ∀ n : ℕ, ∀ m τ : ℕ, 1 ≤ m → τ + m + n = i → RLSt D e f x j i m τ → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m τ hm1 hsum st
    by_cases hn : n = 0
    · subst hn
      exact rl_end S x j i m τ hi hP4 (by omega) st
    · obtain ⟨m1, rfl⟩ : ∃ m1 : ℕ, m = m1 + 1 := ⟨m - 1, by omega⟩
      obtain ⟨τ', hττ', hτ'i, st'⟩ := rl_step_core S x j i (m1 + 1) τ hi hP4 (by omega) st
        (fun t h1 h2 => col_layer S x j i m1 τ st t h1 h2)
      exact ih (i - (m1 + 1 + 1) - τ') (by omega) (m1 + 1 + 1) τ' (by omega) (by omega) st'

end gen5

#print axioms col_layer
#print axioms rl_end
#print axioms rl_run

end Erdos634.Draft.WGapStmt
