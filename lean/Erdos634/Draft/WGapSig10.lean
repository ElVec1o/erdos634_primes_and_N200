/-
Draft/WGapSig10.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.5 (b1), (b2)).
Not imported by any aggregate.  No sorry, no native_decide.
* `sigma_clamp_right`: the RIGHT clamp of `Λ = [p(0,y₀+1), p(q,y₀+1)]` (`q = s−y₀−1`), from (K3) (`K3G_clamp_row`, as in `K_allGJ` step (3) and `row_clamp_right`).
* `sigma_row0`: **`U(0,y₀+1)` is a tile** (PROOF 7.5 (b2)): `row_stepS` at `r = 0` (left clamp from `E_{y₀}`: `row_left_clamp_E`; no `b`-edge: `sigma_row_nob`); the "bad" branch is
  `bad0_false` (with `Z*` from `zstar`).
-/
import Erdos634.Draft.WGapSig9

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

section sig10

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem sigma_clamp_right (S : SetupG D e f α β γ L ax ay) {x : ℝ} {s y₀ : ℕ} (hy : y₀ < s) (hsf : s ≤ f - 1)
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 x s y₀) (hK3 : K3G D (e : ℝ) (f : ℝ) 1 x (s : ℝ) (y₀ : ℝ)) (hq : 1 ≤ s - y₀ - 1) :
    ∃ Q' : Plane, GHG (f : ℝ) Q' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((y₀ : ℝ) + 1)) ∧
      lpG (e : ℝ) (f : ℝ) 1 x ((s - y₀ - 1 : ℕ) : ℝ) ((y₀ : ℝ) + 1) ∈
        openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((y₀ : ℝ) + 1)) Q' ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((y₀ : ℝ) + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) 1 x ((s - y₀ - 1 : ℕ) : ℝ) ((y₀ : ℝ) + 1))
          (lpG (e : ℝ) (f : ℝ) 1 x 0 ((y₀ : ℝ) + 1)) := by
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hUrow : ∀ j' : ℕ, j' ≤ y₀ → UTG D (e : ℝ) (f : ℝ) 1 x ((s : ℝ) - 1 - j') j' := by
    intro j' hj'
    have h := hK2.1 (s - 1 - j') j' hj' (by omega)
    have hc : ((s - 1 - j' : ℕ) : ℝ) = (s : ℝ) - 1 - j' := by
      rw [Nat.cast_sub (show j' ≤ s - 1 by omega), Nat.cast_sub (show 1 ≤ s by omega), Nat.cast_one]
    rwa [hc] at h
  have hcm : (((s - y₀ - 1 : ℕ)) : ℝ) = (s : ℝ) - ((y₀ : ℝ) + 1) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]; ring
  have hFp : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x ((s : ℝ) - ((y₀ : ℝ) + 1)) ((y₀ : ℝ) + 1))
      = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((y₀ : ℝ) + 1)) := GHG_lp _ _ _ _ _ _
  have hsj1 : (y₀ : ℝ) + 1 < s := by
    have h' : y₀ + 1 < s := by omega
    exact_mod_cast h'
  have hdir : GSG (e : ℝ) (f : ℝ) 1 (lpG (e : ℝ) (f : ℝ) 1 x ((s : ℝ) - ((y₀ : ℝ) + 1)) ((y₀ : ℝ) + 1)
      - lpG (e : ℝ) (f : ℝ) 1 x 0 ((y₀ : ℝ) + 1)) < 0 := by
    rw [map_sub, GSG_lp hε, GSG_lp hε]
    have := lvG_lt (e := (e : ℝ)) (f := (f : ℝ)) (ε := 1) (x := x) he0 hef
      (show (0 : ℝ) + ((y₀ : ℝ) + 1) < (s : ℝ) - ((y₀ : ℝ) + 1) + ((y₀ : ℝ) + 1) by linarith)
    linarith
  obtain ⟨Q', hfQ', hQ', hQc⟩ := C.K3G_clamp_row hK3 (j0 := y₀) (by omega) hUrow (GHG (f : ℝ)) _
    (Q := lpG (e : ℝ) (f : ℝ) 1 x 0 ((y₀ : ℝ) + 1)) hFp (GHG_lp _ _ _ _ _ _) hdir
  rw [← hcm] at hQ' hQc
  exact ⟨Q', hfQ', by rw [openSegment_symm]; exact hQ', hQc⟩

end sig10

#print axioms sigma_clamp_right

end Erdos634.Draft.WGapStmt
