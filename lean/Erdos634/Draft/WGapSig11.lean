/-
Draft/WGapSig11.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.5 (b2)).
Not imported by any aggregate.  No sorry, no native_decide.
`sigma_row0`: `U(0,y₀+1)` is a tile, for `Σ_𝔞(s,y₀)` with `n = s−y₀ ≥ 2` and `D(i,y₀)` tiles for `i ≤ n−2` (step (a)).
-/
import Erdos634.Draft.WGapSig10

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

section sig11

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem sigma_row0 (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J s y₀ : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ y₀) (hy : y₀ < s) (hsf : s ≤ f - 1) (hn2 : 2 ≤ s - y₀)
    (hσ : SigmaCfg D e f c₀ J s y₀)
    (hDrow : ∀ i : ℕ, i + 2 ≤ s - y₀ → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (i : ℝ) (y₀ : ℝ)) :
    UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1) := by
  obtain ⟨hS1, hK2, hK3⟩ := hσ
  have C : CtxBase D e f α β γ L ax ay 1 (xo f c₀) := ⟨S, Or.inl rfl⟩
  have hq : 1 ≤ s - y₀ - 1 := by omega
  have hqj : (s - y₀ - 1) + y₀ + 1 ≤ f := by omega
  obtain ⟨tE, hE0⟩ := hS1 y₀ hJ le_rfl
  rw [zero_add] at hE0
  obtain ⟨tU, hU⟩ := hK2.1 0 y₀ le_rfl (by omega)
  rw [Nat.cast_zero] at hU
  obtain ⟨tD, hDt⟩ := hDrow 0 (by omega)
  rw [Nat.cast_zero] at hDt
  have hqpos : (0 : ℝ) < ((s - y₀ - 1 : ℕ) : ℝ) := by exact_mod_cast hq
  have hclL := row_left_clamp_E S hqpos hE0
  have hcl0 : ∃ P' : Plane, GHG (f : ℝ) P' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((y₀ : ℝ) + 1)) ∧
      lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1) ∈ openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) (0 + 1) ((y₀ : ℝ) + 1)) ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((y₀ : ℝ) + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1))
          (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) (0 + 1) ((y₀ : ℝ) + 1)) := by
    have h := row_left_clamp_E S (x := xo f c₀) (y := (y₀ : ℝ)) (q := 1) (by norm_num) hE0
    rw [show ((1 : ℕ) : ℝ) = 0 + 1 by norm_num] at h
    exact h
  have hcr := sigma_clamp_right S hy hsf hK2 hK3 hq
  have hnob := sigma_row_nob C hq hqj (fun i' hi' => hDrow i' (by omega)) hcr hclL
  have hnob0 : ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((y₀ : ℝ) + 1))),
      (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) (0 + 1) ((y₀ : ℝ) + 1)) →
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    intro ed he hsub
    refine hnob 0 le_rfl ?_ ed he hsub
    have : (1 : ℝ) ≤ ((s - y₀ - 1 : ℕ) : ℝ) := by exact_mod_cast hq
    linarith
  rcases row_stepS C hDt (Nat.cast_nonneg y₀) hcl0 hnob0 with hU1 | ⟨ix, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle, hθ, hno, hlen⟩
  · exact hU1
  · exfalso
    obtain ⟨τ, W, hZ, hZc⟩ := zstar S h2 hH4 hA hJ (by omega)
      (fun y h1 h2' => by
        have := hK2.1 0 y (by omega) (by omega)
        rwa [Nat.cast_zero] at this) hS1
    exact bad0_false S (xo f c₀) (y₀ : ℝ) (Nat.cast_nonneg _) hE0 hU hDt hZ hZc hkm hkj hmj hk ht hm hle hθ hlen

end sig11

#print axioms sigma_row0

end Erdos634.Draft.WGapStmt
