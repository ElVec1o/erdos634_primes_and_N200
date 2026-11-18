/-
Draft/WGapClimb10.lean -- written 16 November 2026 (session 16).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 with apex switching).
Not imported by any aggregate.  No sorry, no native_decide.
**CONDITIONAL REDUCTION, not a result**: `StationStmt` is the statement of PROOF 9.4 (3a)-(3c) at the first column `x` carrying `N_x` in the row `y = j + lam` (`lam >= 1`): the station apex data
`IsApex (c₀+x+1) (j+lam)` (= `St2` at `O = p(x+1, j+lam)`, from the tile `F` in the wedge `(2α,3α)`: `F` lays `c` on the chord of `N_x` and `b` on `L_O`; the case `F` lays `b` is `Pi_b` at the index `x < i` and is excluded by `BUpTo`)
and the strip tile `E` at level `j+lam` (the mirror image of `U(x+1, j+lam)`; the case `E` lays `c` is `K1J` at the origin `p(x+1,0)` plus Lemma N, contradicting `N^{i-lam}`).  `StationStmt` is NOT proved here.
* `Pi4_rebase`, `SigmaAll.mono`, `BUpTo.mono`;
* `climb_gen_aux`: GIVEN `StationStmt`, the climb closes for every `(c₀, J, j, i, lam)` by strong induction on `i - lam` (all-`D` row: `climb_step0`; first `N` at `x`: station, `climbSt_rebase`, `Pi4_rebase`; `lam = i`: `climb_end0`);
* `prop_B_of_station`: `StationStmt` implies Proposition B at every `(i, j)` with `j + i >= 1` (the case `i = j = 0` needs `rl_A0_fill` at level 0, not built).
-/
import Erdos634.Draft.WGapClimb9

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

theorem SigmaAll.mono' {e f m m' : ℕ} (h : SigmaAll D e f m) (hm : m' ≤ m) : SigmaAll D e f m' :=
  fun c J hA s y hJ hy hsf hs hσ => h c J hA s y hJ hy hsf (by omega) hσ

theorem BUpTo.mono' {e f n n' : ℕ} (h : BUpTo D e f n) (hn : n' ≤ n) : BUpTo D e f n' :=
  fun c J hA j i hJ hi hij => h c J hA j i hJ (by omega) hij

section climb10

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem Pi4_rebase {c₀ i j m : ℕ} (hm : m ≤ i) (h : Pi4 D e f c₀ i j) : Pi4 D e f (c₀ + m) (i - m) j := by
  obtain ⟨F, R, hF, hc⟩ := h
  have hcm : (((i - m : ℕ)) : ℝ) + (m : ℝ) = (i : ℝ) := by rw [Nat.cast_sub hm]; ring
  have q1 : lpG (e : ℝ) f 1 (xo f (c₀ + m)) (((i - m : ℕ) : ℝ) + 1) j = lpG (e : ℝ) f 1 (xo f c₀) ((i : ℝ) + 1) j := by
    rw [lpG_xo_add _ _ f c₀ m rfl]; exact lpG_congr (by linarith) rfl
  have q2 : lpG (e : ℝ) f 1 (xo f (c₀ + m)) (((i - m : ℕ) : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) =
      lpG (e : ℝ) f 1 (xo f c₀) ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) := by
    rw [lpG_xo_add _ _ f c₀ m rfl]; exact lpG_congr (by linarith) rfl
  refine ⟨F, R, ?_, ?_⟩
  · rw [q1, q2]; exact hF
  · rw [q1, q2]; exact hc

/-- PROOF 9.4 (3a)-(3c): at the first column `x <= i - lam - 2` of the row `y = j+lam` carrying `N_x` (columns before it are `D`), the point `O = p(x+1, j+lam)` is a station: `St2` and the strip tile.  NOT PROVED. -/
def StationStmt : Prop :=
  ∀ {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay)
    (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) {c₀ J j i lam : ℕ}, IsApex D e f c₀ J → J ≤ j + lam →
    i + j + 1 ≤ f - 1 → 1 ≤ lam → lam < i → ClimbSt D e f c₀ J j i lam → SigmaAll D e f i → BUpTo D e f (i - 1) →
    Pi4 D e f c₀ i j → ∀ x : ℕ, x + 2 + lam ≤ i →
    (∀ x' : ℕ, x' < x → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x' : ℝ) ((j + lam : ℕ) : ℝ)) → NTile D e f c₀ x (j + lam) →
    IsApex D e f (c₀ + (x + 1)) (j + lam) ∧ StripTiles D e f (c₀ + (x + 1)) (j + lam) (j + lam)

set_option maxHeartbeats 32000000 in
theorem climb_gen_aux (hst : StationStmt) (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) :
    ∀ n : ℕ, ∀ {c₀ J j i lam : ℕ}, i - lam = n → lam ≤ i → IsApex D e f c₀ J → J ≤ j + lam → i + j + 1 ≤ f - 1 →
    1 ≤ j + i → (lam = 0 → ∀ x : ℕ, x < i → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x : ℝ) (j : ℝ)) →
    ClimbSt D e f c₀ J j i lam → SigmaAll D e f i → BUpTo D e f (i - 1) → Pi4 D e f c₀ i j → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c₀ J j i lam hn hli hA hJ hij hj1 hrow0 hCl hSig hB hP4
    by_cases hlam : lam = i
    · subst hlam
      exact climb_end0 S (by omega) hij hj1 hCl hP4
    · have hlt : lam < i := by omega
      by_cases hall : ∀ x : ℕ, x < i - lam → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x : ℝ) ((j + lam : ℕ) : ℝ)
      · have hCl' := climb_step0 S h2 hH4 hA hJ hij hlt hCl hall hP4 hSig
        exact ih (i - (lam + 1)) (by omega) rfl (by omega) hA (by omega) hij hj1
          (fun h => by omega) hCl' hSig hB hP4
      · have hex : ∃ x : ℕ, x < i - lam ∧ ¬ DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x : ℝ) ((j + lam : ℕ) : ℝ) := by
          by_contra hne
          push_neg at hne
          exact hall (fun x hx => hne x hx)
        have hlam1 : 1 ≤ lam := by
          by_contra h0
          obtain ⟨x0, hx0, hnd⟩ := hex
          have : lam = 0 := by omega
          subst this
          exact hnd (by simpa using hrow0 rfl x0 (by omega))
        obtain ⟨hxlt, hxnd⟩ := Nat.find_spec hex
        set x := Nat.find hex with hxdef
        have hbefore : ∀ x' : ℕ, x' < x → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x' : ℝ) ((j + lam : ℕ) : ℝ) := by
          intro x' hx'
          by_contra hnd
          exact Nat.find_min hex hx' ⟨by omega, hnd⟩
        have hN : NTile D e f c₀ x (j + lam) := by
          rcases row_cases S hA hJ hij hlam1 hlt hCl hSig hxlt with hD' | hN'
          · exact absurd hD' hxnd
          · exact hN'
        have hx2 : x + 2 + lam ≤ i := by
          by_contra hx2
          have hxe : x = i - lam - 1 := by omega
          rw [hxe] at hN
          exact rowN_false S hij hlam1 hlt hCl hP4 hN
        obtain ⟨hAp, hStrip⟩ := hst S h2 hH4 hA hJ hij hlam1 hlt hCl hSig hB hP4 x hx2 hbefore hN
        have hCl'' := climbSt_rebase (J' := j + lam) (m := x + 1) (by omega) hCl hStrip
        exact ih ((i - (x + 1)) - lam) (by omega) rfl (by omega) hAp le_rfl (by omega) (by omega)
          (fun h => by omega) hCl'' (hSig.mono' (by omega)) (hB.mono' (by omega)) (Pi4_rebase (by omega) hP4)

/-- Proposition B at every `(i, j)` with `j + i >= 1` from `StationStmt` (conditional reduction) -/
theorem prop_B_of_station (hst : StationStmt) (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J j i : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j) (hij : i + j + 1 ≤ f - 1) (hj1 : 1 ≤ j + i)
    (hSig : SigmaAll D e f i) (hB : BUpTo D e f (i - 1)) : ¬ PiBCfg D e f c₀ J j i := by
  rintro ⟨hS1, hUall, hDall, hD0, hN, hP4⟩
  refine climb_gen_aux hst S h2 hH4 (i - 0) rfl (Nat.zero_le _) hA (by omega) hij hj1
    (fun _ x hx => hD0 x hx) ?_ hSig hB hP4
  refine ⟨?_, hS1, hUall, hDall⟩
  intro t h1 h2'
  have : t = i := by omega
  subst this
  have e1 : j + t - t = j := by omega
  rw [e1]
  exact hN

end climb10

#print axioms Pi4_rebase
#print axioms climb_gen_aux
#print axioms prop_B_of_station

end Erdos634.Draft.WGapStmt
