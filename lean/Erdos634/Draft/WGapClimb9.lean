/-
Draft/WGapClimb9.lean -- written 16 November 2026 (session 16).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.2-P9.4; apex switching = re-basing the lattice at the station column).
Not imported by any aggregate.  No sorry, no native_decide.
* `xo_add`, `lpG_xo_add`: `xo f (c₀+m) = xshk f m (xo f c₀)`, `lpG (xo f (c₀+m)) ξ η = lpG (xo f c₀) (ξ+m) η`;
* `UTG_rebase`, `DTG_rebase`, `NTile_rebase`: the tiles of the lattice with origin `p(c₀,0)` at columns `>= m` are the tiles of the lattice with origin `p(c₀+m,0)`;
* `climbSt_rebase`: the climb invariant at the apex `(c₀,J)` with `lam` and parameters `(j,i)` gives the invariant at the station apex `(c₀+m, J')`, parameters `(j, i-m)`, SAME `lam`, provided the strip of the station is a tile up to level `j+lam` (PROOF 9.4 (3c), (4): `h_{lambda+1} = x_r + 1 = m`; the measure `i - lam` strictly decreases);
* controls `prop_B_one_of_climb`, `prop_B_two_of_climb`: the statements of `prop_B_one`, `prop_B_two` proved from `prop_B_le_two` (the general climb).
-/
import Erdos634.Draft.WGapClimb8

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

theorem xo_add (f c₀ m : ℕ) : xo f (c₀ + m) = xshk (f : ℝ) m (xo f c₀) := by
  unfold xo xshk
  push_cast
  ring

theorem lpG_xo_add (e f : ℝ) (fn c₀ m : ℕ) (hf : f = (fn : ℝ)) (ξ η : ℝ) :
    lpG e f 1 (xo fn (c₀ + m)) ξ η = lpG e f 1 (xo fn c₀) (ξ + m) η := by
  rw [xo_add, hf, lpG_shk]

section climb9

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem UTG_rebase {c₀ m a : ℕ} {b : ℝ} (h : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((a + m : ℕ) : ℝ) b) :
    UTG D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + m)) (a : ℝ) b := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, hasV_congr ht ?_ ?_ ?_⟩ <;>
    (rw [lpG_xo_add _ _ f c₀ m rfl]; exact lpG_congr (by push_cast; ring) rfl)

theorem DTG_rebase {c₀ m a : ℕ} {b : ℝ} (h : DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((a + m : ℕ) : ℝ) b) :
    DTG D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + m)) (a : ℝ) b := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, hasV_congr ht ?_ ?_ ?_⟩ <;>
    (rw [lpG_xo_add _ _ f c₀ m rfl]; exact lpG_congr (by push_cast; ring) rfl)

theorem NTile_rebase {c₀ m a y : ℕ} (h : NTile D e f c₀ (a + m) y) : NTile D e f (c₀ + m) a y := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, hasV_congr ht ?_ ?_ ?_⟩ <;>
    (rw [lpG_xo_add _ _ f c₀ m rfl]; exact lpG_congr (by push_cast; ring) rfl)

/-- apex switching at the column `m`: the invariant is re-based at the station, with the SAME `lam` and `i - m` (measure `i - lam` drops by `m`) -/
theorem climbSt_rebase {c₀ J J' j i lam m : ℕ} (hm : m + lam ≤ i) (hSt : ClimbSt D e f c₀ J j i lam)
    (hstrip : StripTiles D e f (c₀ + m) J' (j + lam)) : ClimbSt D e f (c₀ + m) J' j (i - m) lam := by
  obtain ⟨hC1, -, hUa, hDa⟩ := hSt
  refine ⟨?_, hstrip, ?_, ?_⟩
  · intro t h1 h2'
    have := hC1 (t + m) (by omega) (by omega)
    have e1 : j + i - (t + m) = j + (i - m) - t := by omega
    rw [e1] at this
    exact NTile_rebase this
  · intro a b hb hab
    exact UTG_rebase (hUa (a + m) b hb (by omega))
  · intro a b hb hab
    exact DTG_rebase (hDa (a + m) b hb (by omega))

section controls

variable {c₀ J : ℕ}

theorem prop_B_one_of_climb (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    (hA : IsApex D e f c₀ J) {j : ℕ} (hJ : J ≤ j) (hij : 1 + j + 1 ≤ f - 1)
    (hSig : SigmaAll D e f 1) : ¬ PiBCfg D e f c₀ J j 1 :=
  prop_B_le_two S h2 hH4 hA hJ (by omega) hij (by omega) hSig

theorem prop_B_two_of_climb (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    (hA : IsApex D e f c₀ J) {j : ℕ} (hJ : J ≤ j) (hij : 2 + j + 1 ≤ f - 1)
    (hSig : SigmaAll D e f 2) : ¬ PiBCfg D e f c₀ J j 2 :=
  prop_B_le_two S h2 hH4 hA hJ (by omega) hij (by omega) hSig

end controls

end climb9

#print axioms lpG_xo_add
#print axioms climbSt_rebase
#print axioms prop_B_one_of_climb
#print axioms prop_B_two_of_climb

end Erdos634.Draft.WGapStmt
