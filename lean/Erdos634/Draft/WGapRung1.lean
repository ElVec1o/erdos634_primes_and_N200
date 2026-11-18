/-
Draft/WGapRung1.lean -- written 16 November 2026 (work item LEAN_WRUNG2_2026-11-16).  UNAUDITED beyond internal checks.
Not imported by any aggregate.  New leaf: no existing file edited.
The reduction `WGapFinal.no_tiling_W_gap_of_main` + `WGapMainRed.sigma_corner_of_all` only ever uses `SigmaAll D e f k`
for the corner run length `k` (`SigmaCfg D e f 0 0 k 0`), and `k ≤ z ≤ M (f - e)` (a run of `k` C1 in the chain, then `C_AQ'`).
So `SigmaAll D e f m` is needed only for `m ≤ M (f - e)`.  Hence:
* `no_tiling_W_gap_of_sigma_le B`: from `SigmaAllLeStmt B` (Sigma[m] for `m ≤ B e`) and `M (f-e) ≤ B e`.
* `no_tiling_W_rung2`: UNCONDITIONAL (no Proposition B) for `M (f - e) ≤ e + 2`, by `WGapSig22.st_d`.
Credit: Beeson-Rosu (framework), the W-gap formalization work item LEAN_WGAP_2026-11-15 (all of WGap*), E2R6 work item, S+ audit.
-/
import Erdos634.Draft.WGapSig22
import Erdos634.Draft.WGapMainRed

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapRung

open Erdos634.Draft.WGapStmt
open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Erdos634.Draft.FDBBaseBetaE1 Set

/-- Sigma[m] for all `m ≤ B e` (bounded version of `SigmaAllStmt`) -/
def SigmaAllLeStmt (B : ℕ → ℕ) : Prop :=
  ∀ {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay)
    (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) (he2 : 2 ≤ e) (m : ℕ), m ≤ B e → SigmaAll D e f m

/-- `st_d` is exactly `SigmaAllLeStmt (· + 2)` -/
theorem sigmaAllLe_rung2 : SigmaAllLeStmt (fun e => e + 2) :=
  fun S h2 hH4 he2 m hm => st_d S h2 hH4 m hm

set_option maxHeartbeats 1600000 in
/-- **bounded reduction**: `no_tiling_W_gap` from Sigma[m] for `m ≤ B e`, when `M (f - e) ≤ B e` -/
theorem no_tiling_W_gap_of_sigma_le {B : ℕ → ℕ} (hall : SigmaAllLeStmt B) {e f M : ℕ} (hco : Nat.Coprime e f)
    (he : 2 ≤ e) (hef : e < f) (hfM : f ≤ M * e) (hMfe : M * (f - e) < f) (hB : M * (f - e) ≤ B e) :
    ¬ Erdos634.Draft.CollarG.WTilable e f M := by
  rintro ⟨D₀, hT, hMod⟩
  have hM : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; omega
    · exact h
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
  obtain ⟨τ, h1, h2, h3⟩ := hasSides_rotG (hasSides_rotG hT)
  obtain ⟨hA, hQ, hB'⟩ := W_corners_of_sides e f (by omega) hef hMr D₀ τ h1 h2 h3
  obtain ⟨D, g, L, ax, ay, hL, hLd, hD, hP, hB'', S, Co, h2c, hdist⟩ :=
    setup_of_corners_F2 e f (by omega) hef hco D₀ hMod (rotA.trans τ) (Or.inl hA) (Or.inr hQ)
  obtain ⟨m, X, tile, τc, Ch⟩ := S.exists_chainG
  obtain ⟨x, y, z, hsum, hz⟩ := sideG_counts_gen S Ch
  have hLeq : L = (M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    rw [← hLd]; exact h2
  have hsub : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2)]; push_cast; ring
  have hnat : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2) := by
    have h' : ((x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 : ℕ) : ℝ) =
        ((M * f * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]
      linear_combination hsum.trans hLeq
    exact_mod_cast h'
  have hzle : z ≤ M * (f - e) := (SplusThick.C_AQ' (by omega) hef hco hnat).2 hMfe
  have hzlt : z < f := by omega
  have hH4 : H4 f ax ay := by
    have e1 := dist_sq_pts (mkPt ax ay) (mkPt 0 0)
    have e2 : dist (mkPt ax ay) (mkPt 0 0) = (M : ℝ) * (f : ℝ) ^ 3 := by
      rw [hdist]; exact h1
    simp only [mkPt_zero, mkPt_one] at e1
    rw [e2] at e1
    unfold H4
    have hf2 : (2 : ℝ) ≤ f := by exact_mod_cast (by omega : 2 ≤ f)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hf3 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
    have hlt : ((f : ℝ) - 1) * (f : ℝ) ^ 2 < (M : ℝ) * (f : ℝ) ^ 3 := by nlinarith [pow_pos (by linarith : (0 : ℝ) < f) 3]
    have hpos : (0 : ℝ) ≤ ((f : ℝ) - 1) * (f : ℝ) ^ 2 := by nlinarith
    nlinarith [e1]
  have hCorner2 : Corner2 e f ax ay := cornersA_two_of_angle S Co (h2c hA)
  rcases corner_side_theorem S Co Ch with ⟨i, him, hrun⟩ | ⟨k, hk1, hkf, hkm, hrun, hsucc⟩
  · have hfz := hz i f him hrun
    omega
  · have hsucc' : k = m ∨ (k < m ∧ τc k ≠ Ty.B1 ∧ τc k ≠ Ty.C1) := by
      rcases hsucc with h | ⟨h, h'⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
    have hek : e + 1 ≤ k := by
      by_contra hlt
      exact corner_run_short S Co Ch hk1 (by omega) hrun hsucc'
    have hMirror := corner_run_mirror S Co Ch hk1 hkf hrun hsucc'
    -- the run of k C1's is counted by z
    have hkz : k ≤ z := hz 0 k (by omega) (Or.inl (fun j hj => by simpa using hrun j hj))
    have hkB : k ≤ B e := by omega
    obtain ⟨-, hMir, hK2, hK3⟩ := corner_run_data S Co Ch (by omega : 1 ≤ k) (by omega : k < f) hrun hsucc'
    have hUT : UTM D (e : ℝ) (f : ℝ) 1 0 0 ((0 : ℕ) : ℝ) := by
      rw [Nat.cast_zero]
      exact (mirrorAt_iff_UTM00 S).1 (by rw [Nat.cast_zero] at hMir; exact hMir)
    have hx : xo f 0 = 0 := by simp [xo]
    have hcfg : SigmaCfg D e f 0 0 k 0 := by
      refine ⟨fun y h1 h2' => ?_, ?_, ?_⟩
      · have hy : y = 0 := by omega
        subst hy
        rw [hx]; simpa using hUT
      · rw [hx]; exact hK2
      · rw [hx]; simpa using hK3
    exact hall S hCorner2 hH4 he k hkB 0 0 (Or.inl ⟨rfl, rfl⟩) k 0 le_rfl (by omega) (by omega) (by omega) hcfg

/-- **Theorem R2 (rung `e+2`), UNCONDITIONAL**: no tiling of `W_M(e,f)` when `M (f - e) ≤ e + 2` (and `M (f-e) < f`).
No Proposition B. -/
theorem no_tiling_W_rung2 (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f) (hfM : f ≤ M * e)
    (hMf : M * (f - e) < f) (hk : M * (f - e) ≤ e + 2) : ¬ Erdos634.Draft.CollarG.WTilable e f M :=
  no_tiling_W_gap_of_sigma_le (B := fun e => e + 2) sigmaAllLe_rung2 hco he hef hfM hMf hk

#print axioms sigmaAllLe_rung2
#print axioms no_tiling_W_gap_of_sigma_le
#print axioms no_tiling_W_rung2

end Erdos634.Draft.WGapRung
