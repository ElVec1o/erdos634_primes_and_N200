/-
Draft/WGapM2.lean -- written 15 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P2.7).
Not imported by any aggregate.  **Lemma M at an arbitrary origin p(c0,0), ALL sizes** (`lemma_M`): it is the project's `SideRunGA.MG_all` (the induction of
`SideRunGMStep`/`StepB`/`StepC`, `ChordsAt` at every origin) once (a) `MirrorAt` is identified with `UTM D e f 1 x 0 y` at any origin and level
(`mirrorAt_iff_UTM_gen`, S0 generalised) and (b) `ChordsAt` at the origin `xo f c0` is supplied (`chordsAt_xo` = `hch_origin`).  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapKN
import Erdos634.Draft.WGapMainRed
import Erdos634.Draft.SideRunGMStepC

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

section m2

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **S0 generalised**: the project's `MirrorAt` at origin `x`, level `y` is the tile `UTM D e f 1 x 0 y` -/
theorem mirrorAt_iff_UTM_gen (S : SetupG D e f α β γ L ax ay) (x y : ℝ) :
    MirrorAt D (e : ℝ) (f : ℝ) 1 x y ↔ UTM D (e : ℝ) (f : ℝ) 1 x 0 y := by
  have he0 := S.e0
  have hef := S.hef'
  have hA : mpG (e : ℝ) f 1 x 0 y = lpG (e : ℝ) f 1 x 0 y := mpG_eq_zero he0 hef x y
  have hB : mpG (e : ℝ) f 1 x 0 (y + 1) = lpG (e : ℝ) f 1 x 0 (y + 1) := mpG_eq_zero he0 hef x (y + 1)
  have hC : mpG (e : ℝ) f 1 x (0 + 1) y = lpG (e : ℝ) f 1 x (-1) (y + (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    rw [mpG_eq he0 hef]
    unfold sMir
    exact lpG_congr (by ring) (by ring)
  unfold MirrorAt UTM
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, hasV_congr ht.swap.rot hA.symm hC.symm hB.symm⟩
  · rintro ⟨t, ht⟩
    have h2 := hasV_congr ht hA hC hB
    exact ⟨t, h2.swap.rot⟩

/-- `ChordsAt` at the origin `p(c0,0)`: the open chords along `l_{c0}` are interior (from `U(c0,0)`; at the corner from `Corner2`) -/
theorem chordsAt_xo (S : SetupG D e f α β γ L ax ay) (c₀ : ℕ) (hc0 : c₀ = 0 → Corner2 e f ax ay)
    (hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0) : ChordsAt D (e : ℝ) (f : ℝ) 1 (xo f c₀) :=
  fun j hj hm => hch_origin S c₀ hc0 hU0 j hj hm

/-- **Lemma M(s, y₀; c₀), all sizes `n = s − y₀ ≤ e`** (PROOF 2.7; statement of `lemma_M` of `WGapStmt_Scratch3_20261115.lean` with the extra hypothesis
`hc0 : c₀ = 0 → Corner2` of F19, and WITHOUT `he2 : 2 ≤ e`, which is not needed) -/
theorem lemma_M (S : SetupG D e f α β γ L ax ay) (c₀ s y₀ : ℕ) (hc0 : c₀ = 0 → Corner2 e f ax ay)
    (hy : y₀ < s) (hsf : s ≤ f - 1) (hn : s ≤ y₀ + e)
    (hM1 : UTM D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 (y₀ : ℝ)) (hK2 : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) s y₀)
    (hK3 : K3G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (s : ℝ) (y₀ : ℝ)) : False := by
  have hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0 := by
    have h := hK2.1 0 0 (Nat.zero_le _) (by omega)
    rwa [Nat.cast_zero] at h
  have hch := chordsAt_xo S c₀ hc0 hU0
  have hsf' : s < f := by omega
  exact MG_all S (s - y₀) (by omega) (xo f c₀) s y₀ hch rfl hy hsf' (by omega)
    ((mirrorAt_iff_UTM_gen S _ _).2 hM1) hK2 hK3

end m2

#print axioms mirrorAt_iff_UTM_gen
#print axioms chordsAt_xo
#print axioms lemma_M

end Erdos634.Draft.WGapStmt
