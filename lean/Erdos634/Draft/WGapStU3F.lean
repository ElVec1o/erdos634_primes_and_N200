/-
Draft/WGapStU3F.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.3).
Not imported by any aggregate.  STATION port of `WGapU3` (lattice origin `x`, absolute levels, floor `J0`); see WGapStInv1.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapStU3
import Erdos634.Draft.WGapDefs3
import Erdos634.Draft.WGapWL2

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapSt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set Erdos634.Draft.WGapStmt

variable {N : ℕ} {D : CongruentDissection N}


open Erdos634.Draft.WGapStmt hiding sj BotClamp Inv Unfl Flip utm_cast nearOK_inv level_known inv_hint_wall level_data ha_succ hDp_succ unfl_utm inv_step top_pt top_clamp hthird_of_inv ub ClampB FlipAt Bst bst_self ub_norm ub_ne clampB_outside clampB_tile

/-- **S3' = Lemma U3-ST at a station, F11-corrected** (statement textually that of `u3_station_stmt'` in `WGapStmt_Scratch3_20261115.lean`; PROOF 6.3):
`O = p(c₀,J₀)` with (St2), `U(c₀, J₀+j)` and `E_j = U'(0,J₀+j)` tiles for `j < H`: for every `1 ≤ j ≤ H` there is `1 ≤ c ≤ j` with (U3-a), (D) for `j < H`, and (U3-c).
No `Corner2`/`H4`: the wall is (St2) through `wl_mirror`. -/
theorem u3_station {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay) (c₀ J₀ H : ℕ)
    (hH1 : 1 ≤ H) (hHf : H ≤ f - 1)
    (hSt2 : St2 D (e : ℝ) (f : ℝ) (xo f c₀) (J₀ : ℝ))
    (hU : ∀ j : ℕ, j < H → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((J₀ + j : ℕ) : ℝ))
    (hE : ∀ j : ℕ, j < H → UTM D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((J₀ + j : ℕ) : ℝ)) :
    ∀ j : ℕ, 1 ≤ j → j ≤ H → ∃ c : ℕ, 1 ≤ c ∧ c ≤ j ∧
      (∀ i : ℕ, i < c → UTM D (e : ℝ) (f : ℝ) 1 (xo f c₀) (i : ℝ) ((J₀ + (j - 1 - i) : ℕ) : ℝ)) ∧
      (j < H → ∀ i : ℕ, i < c → DTM D (e : ℝ) (f : ℝ) 1 (xo f c₀) (i : ℝ) ((J₀ + (j - 1 - i) : ℕ) : ℝ)) ∧
      (∀ i : ℕ, i < c → ∃ (τ : Fin N) (W : Plane),
        HasV D τ (mpG (e : ℝ) f 1 (xo f c₀) (i : ℝ) ((J₀ : ℝ) + j - i))
          (mpG (e : ℝ) f 1 (xo f c₀) ((i : ℝ) + 1) ((J₀ : ℝ) + j - i - 1)) W ∧
        cross (mpG (e : ℝ) f 1 (xo f c₀) 1 ((J₀ : ℝ) + j - 1) - mpG (e : ℝ) f 1 (xo f c₀) 0 ((J₀ : ℝ) + j))
          (W - mpG (e : ℝ) f 1 (xo f c₀) (i : ℝ) ((J₀ : ℝ) + j - i)) < 0) := by
  intro j hj1 hjH
  have hWall : WallOK D e f (xo f c₀) J₀ := by
    intro q hq1 hqf hUq
    have h0 := hE 0 (by omega)
    rw [Nat.add_zero] at h0
    exact wl_mirror S c₀ J₀ q hq1 hqf h0 hSt2 (fun t ht => hUq t ht)
  have hU' : ∀ j' : ℕ, J₀ ≤ j' → j' < J₀ + H → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 (j' : ℝ) := by
    intro j' h1 h2
    have := hU (j' - J₀) (by omega)
    rwa [show J₀ + (j' - J₀) = j' by omega] at this
  have hT' : ∀ j' : ℕ, J₀ ≤ j' → j' < J₀ + H → UTM D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 (j' : ℝ) := by
    intro j' h1 h2
    have := hE (j' - J₀) (by omega)
    rwa [show J₀ + (j' - J₀) = j' by omega] at this
  obtain ⟨c, hc1, hcj, hUM, hDM, hth⟩ := u3_st_abs S (J := J₀ + H) (by omega) hWall (by omega) hU' hT' (J₀ + j) (by omega) (by omega)
  refine ⟨c, hc1, by omega, ?_, ?_, ?_⟩
  · intro i hi
    have := hUM i hi
    rwa [show J₀ + j - 1 - i = J₀ + (j - 1 - i) by omega] at this
  · intro hjH' i hi
    have := hDM (by omega) i hi
    rwa [show J₀ + j - 1 - i = J₀ + (j - 1 - i) by omega] at this
  · intro i hi
    have := hth i hi
    simpa only [Nat.cast_add] using this

#print axioms u3_station

end Erdos634.Draft.WGapSt
