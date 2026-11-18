/-
Draft/WGapDefs3.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7, P9, P10).
Not imported by any aggregate.  The DEFINITIONS of the Sigma / Omega / Pi_b layer (copied from `WGapStmt_Scratch3_20261115.lean`, where they type-check as statements):
`xo`, `IsApex`, `StripTiles`, `SigmaCfg`, `NTile`, `Pi4`, `OmegaCfg`, `PiBCfg`, `SigmaAll`, `BUpTo`.  No theorems, no sorry.
-/
import Erdos634.Draft.WGapStmt
import Erdos634.Draft.SideRunGJK

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


/-- the lattice origin `p(c₀,0)` on the side line -/
noncomputable def xo (f c₀ : ℕ) : ℝ := (c₀ : ℝ) * (f : ℝ) ^ 2

/-- apex of the tiling: the corner `(0,0)` or a station `(c₀ ≥ 1, J)` with (St2) -/
def IsApex (D : CongruentDissection N) (e f c₀ J : ℕ) : Prop :=
  (c₀ = 0 ∧ J = 0) ∨ (1 ≤ c₀ ∧ St2 D (e : ℝ) (f : ℝ) (xo f c₀) (J : ℝ))

/-- (S1): the strip tiles `E_y = μ U(0,y)`, `J ≤ y ≤ y₀` -/
def StripTiles (D : CongruentDissection N) (e f c₀ J y₀ : ℕ) : Prop :=
  ∀ y : ℕ, J ≤ y → y ≤ y₀ → UTM D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 (y : ℝ)

/-- the configuration whose non-existence is `Σ_𝔞(s,y₀)`: (S1), (K2), (K3) -/
def SigmaCfg (D : CongruentDissection N) (e f c₀ J s y₀ : ℕ) : Prop :=
  StripTiles D e f c₀ J y₀ ∧ K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) s y₀ ∧ K3G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (s : ℝ) (y₀ : ℝ)

/-- `N_i(y)` is a tile: the mirror image of `U(i,y)` in its `a`-edge (third vertex as in `CtxJ.noNJ`) -/
def NTile (D : CongruentDissection N) (e f c₀ i y : ℕ) : Prop :=
  ∃ t, HasV D t (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) + 1) y) (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) i ((y : ℝ) + 1))
    (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) - nuG (e : ℝ) (f : ℝ)) ((y : ℝ) + 2 + nuG (e : ℝ) (f : ℝ)))

/-- (Π4) = `F_b`: a tile on the right of `Λ₃` (direction `Y − O`) with its `b`-edge `[O, O + ν (Y − O)]` on `Λ₃` -/
def Pi4 (D : CongruentDissection N) (e f c₀ i y : ℕ) : Prop :=
  ∃ (F : Fin N) (R : Plane),
    HasV D F (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) + 1) y)
      (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) + 1) y + nuG (e : ℝ) (f : ℝ) •
        (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) - nuG (e : ℝ) (f : ℝ)) ((y : ℝ) + 2 + nuG (e : ℝ) (f : ℝ)) -
          lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) + 1) y)) R ∧
    cross (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) - nuG (e : ℝ) (f : ℝ)) ((y : ℝ) + 2 + nuG (e : ℝ) (f : ℝ)) -
        lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) + 1) y) (R - lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) + 1) y) < 0

/-- `Ω_𝔞(s,y₀,i)` of PROOF 7.1 (the tile `F` is not part of it) -/
def OmegaCfg (D : CongruentDissection N) (e f c₀ J s y₀ i : ℕ) : Prop :=
  SigmaCfg D e f c₀ J s y₀ ∧ (∀ k : ℕ, k < i → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (k : ℝ) (y₀ : ℝ)) ∧
    NTile D e f c₀ i y₀ ∧ UTM D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + i + 1)) 0 (y₀ : ℝ)

/-- `Π_b^𝔞(j,i)` of PROOF 9.1 -/
def PiBCfg (D : CongruentDissection N) (e f c₀ J j i : ℕ) : Prop :=
  StripTiles D e f c₀ J j ∧
    (∀ a b : ℕ, b ≤ j → a + b ≤ i + j → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ)) ∧
    (∀ a b : ℕ, b < j → a + b + 1 ≤ i + j → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ)) ∧
    (∀ a : ℕ, a < i → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (j : ℝ)) ∧
    NTile D e f c₀ i j ∧ Pi4 D e f c₀ i j

/-- `Σ[m]`: `Σ_𝔞(s,y₀)` for every apex and every `(s,y₀)` with `J ≤ y₀ < s ≤ f − 1`, `s − y₀ ≤ m` -/
def SigmaAll (D : CongruentDissection N) (e f m : ℕ) : Prop :=
  ∀ c₀ J : ℕ, IsApex D e f c₀ J → ∀ s y₀ : ℕ, J ≤ y₀ → y₀ < s → s ≤ f - 1 → s ≤ y₀ + m → ¬ SigmaCfg D e f c₀ J s y₀

/-- `B` up to the index `n` (exclusive): `Π_b^𝔞(j,i)` does not occur, for every apex, level `j ≥ J` and `i < n` with `i + j + 1 ≤ f − 1` -/
def BUpTo (D : CongruentDissection N) (e f n : ℕ) : Prop :=
  ∀ c₀ J : ℕ, IsApex D e f c₀ J → ∀ j i : ℕ, J ≤ j → i < n → i + j + 1 ≤ f - 1 → ¬ PiBCfg D e f c₀ J j i

end Erdos634.Draft.WGapStmt
