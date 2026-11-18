/-
Draft/WGapCase1a.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 Case 1).
Not imported by any aggregate.  Module P-C1: `mpG_affine` (the mirror lattice is an affine image of Z^2) and `flip_botclamp`: if the alpha-wedge at `p'(i, j-i)` is the FLIPPED tile
(`Flip D e f j i`, its `c`-edge on `l'_i`), then the bottom clamp of the level-`j+1` chord of length `i` holds (`BotClamp D e f (j+1) i`): the end `p'(i, j+1-i)` is in the relative interior of the
`c`-edge (since `b < c`) and the direction of `m'_{j+1}` beyond it enters the flipped tile (short piece, `not_straddles_short`, barycentric coordinates `(1 - eps/nu - nu(1-eps), eps/nu, nu(1-eps))`,
valid for `eps < nu/(1+nu)`).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapTop

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

/-- the mirror lattice is an affine image of `Z^2` -/
theorem mpG_affine {e f : ℝ} (he : 0 < e) (hef : e < f) :
    ∃ O E1 E2 : Plane, ∀ ξ η : ℝ, mpG e f 1 0 ξ η = O + ξ • E1 + η • E2 := by
  refine ⟨mpG e f 1 0 0 0, mpG e f 1 0 1 0 - mpG e f 1 0 0 0, mpG e f 1 0 0 1 - mpG e f 1 0 0 0, ?_⟩
  intro ξ η
  simp only [mpG_eq he hef]
  unfold lpG
  ext x
  fin_cases x <;> simp <;> ring

section case1a

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem flip_botclamp (S : SetupG D e f α β γ L ax ay) {j i : ℕ} (hi : 1 ≤ i) (hF : Flip D e f j i) :
    BotClamp D e f (j + 1) i := by
  obtain ⟨τ, hτ⟩ := hF
  intro ed _
  have he0 := S.e0
  have hef := S.hef'
  have hν0 := nuG_pos he0 hef
  have hν1 := nuG_lt_one he0 hef
  obtain ⟨O, E1, E2, hm⟩ := mpG_affine he0 hef
  set ν := nuG (e : ℝ) f with hν
  have hδ : 0 < ν / (1 + ν) := by positivity
  refine not_straddles_short D.toDissection (j := τ) (δ := ν / (1 + ν)) (ρ := (i : ℝ)) hδ (by exact_mod_cast hi) ?_ ?_ ed.1 ed.2
  · unfold sj
    simp only [hm]
    ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  · intro ε h0 h1
    have hεν : ε * (1 + ν) < ν := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < 1 + ν)).mp h1
      linarith
    have hε1 : ε < 1 := by nlinarith
    have hb : 0 < ε / ν := div_pos h0 hν0
    have hc : 0 < ν * (1 - ε) := mul_pos hν0 (by linarith)
    have ha : 0 < 1 - ε / ν - ν * (1 - ε) := by
      have : ε / ν + ν * (1 - ε) < 1 := by
        rw [div_add' _ _ _ hν0.ne', div_lt_one hν0]
        nlinarith
      linarith
    have key := hasV_bary hτ ha hb hc (by ring)
    convert key using 1
    unfold sj
    simp only [hm]
    ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    push_cast
    field_simp
    ring

end case1a

end Erdos634.Draft.WGapStmt
