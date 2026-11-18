/-
Draft/WGapSide.lean -- written 15 November 2026 (session 4).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 [SIDE-1]: beyond p'(j,0) the line m'_j leaves Δ).
Not imported by any aggregate.  Module W9a: the side `s'` in mirror coordinates.  KEY FORMULA `gA_mp`: with the apex of `Corner2`, the functional of the side `QA` is
`g_A (p'(ξ,η)) = t e √(4f²-e²) f² (f²-e²) η` (the `K ξ` terms cancel: `mpG_eq` + `gA_lpG`), i.e. `s'` is the line `η = 0` of the mirror lattice and `Δ ⊆ {η ≥ 0}`.
`mp_out`: `η < 0` is outside the target.  `side1_clamp`: the bottom clamp of the chord `[p'(0,n), p'(n,0)]` at `p'(n,0) ∈ s'` (the case `c_j = j`, [SIDE-1]).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLevel
import Erdos634.Draft.SplusThickGeom

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

/-- **`g_A` on the mirror lattice**: proportional to `η` -/
theorem gA_mp {e f : ℝ} (he : 0 < e) (hef : e < f) (t ξ η : ℝ) :
    gA (t * ((2 * f ^ 2 - e ^ 2) ^ 2 - 2 * f ^ 4)) (t * (e * (2 * f ^ 2 - e ^ 2) * rtG e f)) (mpG e f 1 0 ξ η)
      = t * e * rtG e f * f ^ 2 * ((f ^ 2 - e ^ 2) * η) := by
  rw [mpG_eq he hef, SplusThick.gA_lpG e f t _ _ he hef]
  have hb : f ^ 2 - e ^ 2 ≠ 0 := by
    have := b_posG he hef; exact this.ne'
  have hs := sMir_mul he hef
  have : (2 * f ^ 2 - e ^ 2) * (-ξ) + (f ^ 2 - e ^ 2) * (η + sMir e f * ξ) = (f ^ 2 - e ^ 2) * η := by
    linear_combination ξ * hs
  rw [this]

section side

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- `η < 0` is outside the target (`Corner2`) -/
theorem mp_out (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) {ξ η : ℝ} (hη : η < 0) :
    mpG (e : ℝ) f 1 0 ξ η ∉ D.target.carrier := by
  intro hmem
  obtain ⟨t, ht, hax, hay⟩ := h2
  have hg := (S.mem hmem).2.1
  rw [hax, hay, gA_mp S.e0 S.hef' t ξ η] at hg
  have hr := rtG_pos S.e0 S.hef'
  have hb := S.b_pos
  have hf2 := S.c_pos
  have hpos : 0 < t * (e : ℝ) * rtG (e : ℝ) f * (f : ℝ) ^ 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    have := S.e0
    positivity
  nlinarith [mul_pos hpos (neg_pos.mpr hη)]

set_option maxHeartbeats 1000000 in
/-- **[SIDE-1] bottom clamp of the chord that ends on `s'`** (`c = n`): the line `m'_n` leaves Δ beyond `p'(n,0)` -/
theorem side1_clamp (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (n : ℕ) :
    ∀ ed ∈ D.lineChain (crossL (mpG (e : ℝ) f 1 0 1 ((n : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (n : ℝ)))
        (cross (mpG (e : ℝ) f 1 0 1 ((n : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (n : ℝ)) (mpG (e : ℝ) f 1 0 0 (n : ℝ))),
      ¬ Straddles ((D.tile ed.1).edge ed.2)
        (mpG (e : ℝ) f 1 0 0 (n : ℝ) + ((n : ℝ) + 1) • (mpG (e : ℝ) f 1 0 1 ((n : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (n : ℝ)))
        (mpG (e : ℝ) f 1 0 0 (n : ℝ) + (n : ℝ) • (mpG (e : ℝ) f 1 0 1 ((n : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (n : ℝ)))
        (mpG (e : ℝ) f 1 0 0 (n : ℝ)) := by
  intro ed _
  refine not_straddles_of_outside D.toDissection ?_ ed.1 ed.2
  intro y hy
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have hsp := step_pt S.e0 S.hef' 0 (n : ℝ)
  have hy : a • (mpG (e : ℝ) f 1 0 0 (n : ℝ) + ((n : ℝ) + 1) • (mpG (e : ℝ) f 1 0 1 ((n : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (n : ℝ))) +
      b • (mpG (e : ℝ) f 1 0 0 (n : ℝ) + (n : ℝ) • (mpG (e : ℝ) f 1 0 1 ((n : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (n : ℝ))) =
      mpG (e : ℝ) f 1 0 0 (n : ℝ) + ((n : ℝ) + a) • (mpG (e : ℝ) f 1 0 1 ((n : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (n : ℝ)) := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hy, hsp]
  exact mp_out S h2 (by linarith)

end side

#print axioms gA_mp
#print axioms mp_out
#print axioms side1_clamp

end Erdos634.Draft.WGapStmt
