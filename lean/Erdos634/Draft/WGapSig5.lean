/-
Draft/WGapSig5.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.5 (b2), P7.3: the tile `Z*`).
Not imported by any aggregate.  No sorry, no native_decide.
`zstar`: for an apex (corner or station), the tile `Z*` beside the `a`-edge `[p(0,y₀+1), p'(1,y₀)]` of `E_{y₀}` has exactly this `a`-edge (clause (U3-c) at `j = H = y₀−J+1`,
`i = 0`): `u3_mirror_clamp` (corner) / `u3_station` (station).
-/
import Erdos634.Draft.WGapSig4
import Erdos634.Draft.WGapU3
import Erdos634.Draft.WGapStU3F

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

section sig5

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem xo_zero (f : ℕ) : xo f 0 = 0 := by unfold xo; simp

theorem zstar (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J y₀ : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ y₀) (hyf : y₀ + 1 ≤ f - 1)
    (hU : ∀ y : ℕ, J ≤ y → y ≤ y₀ → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 (y : ℝ))
    (hE : StripTiles D e f c₀ J y₀) :
    ∃ (τ : Fin N) (W : Plane),
      HasV D τ (mpG (e : ℝ) f 1 (xo f c₀) 0 ((y₀ : ℝ) + 1)) (mpG (e : ℝ) f 1 (xo f c₀) 1 (y₀ : ℝ)) W ∧
      cross (mpG (e : ℝ) f 1 (xo f c₀) 1 (y₀ : ℝ) - mpG (e : ℝ) f 1 (xo f c₀) 0 ((y₀ : ℝ) + 1))
        (W - mpG (e : ℝ) f 1 (xo f c₀) 0 ((y₀ : ℝ) + 1)) < 0 := by
  rcases hA with ⟨hc, hJ0⟩ | ⟨hc1, hSt2⟩
  · subst hc; subst hJ0
    rw [xo_zero] at hU ⊢
    have hE' : ∀ y : ℕ, 0 ≤ y → y ≤ y₀ → UTM D (e : ℝ) (f : ℝ) 1 0 0 (y : ℝ) := by
      intro y h1 h2; have := hE y h1 h2; rwa [xo_zero] at this
    have key := u3_mirror_clamp S h2 hH4 (y₀ + 1) (by omega) hyf
      (fun j hj => by have := hU j (Nat.zero_le _) (by omega); exact this)
      (fun j hj => hE' j (Nat.zero_le _) (by omega)) (y₀ + 1) (by omega) le_rfl
    obtain ⟨c, hc1, hcj, -, -, h3⟩ := key
    obtain ⟨τ, W, hV, hcr⟩ := h3 0 (by omega)
    refine ⟨τ, W, ?_, ?_⟩
    · simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, sub_zero, zero_add, add_sub_cancel_right] using hV
    · simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, sub_zero, zero_add, add_sub_cancel_right] using hcr
  · have key := Erdos634.Draft.WGapSt.u3_station S c₀ J (y₀ - J + 1) (by omega) (by omega) hSt2
      (fun j hj => hU (J + j) (by omega) (by omega)) (fun j hj => hE (J + j) (by omega) (by omega))
      (y₀ - J + 1) (by omega) le_rfl
    obtain ⟨c, hc1, hcj, -, -, h3⟩ := key
    obtain ⟨τ, W, hV, hcr⟩ := h3 0 (by omega)
    have hJy : (J : ℝ) + ((y₀ - J + 1 : ℕ) : ℝ) = (y₀ : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hJ]; push_cast; ring
    refine ⟨τ, W, ?_, ?_⟩
    · simpa only [Nat.cast_zero, sub_zero, hJy, add_sub_cancel_right, zero_add,
        show (J : ℝ) + ((y₀ - J + 1 : ℕ) : ℝ) - 1 = (y₀ : ℝ) by rw [hJy]; ring] using hV
    · simpa only [Nat.cast_zero, sub_zero, hJy, add_sub_cancel_right, zero_add,
        show (J : ℝ) + ((y₀ - J + 1 : ℕ) : ℝ) - 1 = (y₀ : ℝ) by rw [hJy]; ring] using hcr

end sig5

#print axioms zstar

end Erdos634.Draft.WGapStmt
