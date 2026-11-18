/-
Draft/WGapDich4.lean -- written 15 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.1, ST dichotomy).
Not imported by any aggregate.  No sorry, no native_decide.
`st_dichotomy_core`: from `Ω` (the parts K2, `N_i(y₀)` a tile, `E′ = μU(0,y₀)` at the origin `p(c₀+i+1,0)`) the filler `F` is `F_c` (`St2` at the station `O = p(c₀+i+1,y₀)`)
or `F_b` (`Pi4`).  Interior case `y₀ ≥ 1` by `dich_fill_int`, side case `y₀ = 0` by `dich_fill_bdry`.
-/
import Erdos634.Draft.WGapDich3

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

theorem xo_shift (f c₀ i : ℕ) : xo f (c₀ + i + 1) = xo f c₀ + 1 * ((i : ℝ) + 1) * (f : ℝ) ^ 2 := by
  unfold xo; push_cast; ring

section dich4

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- `E′` in the coordinates of the lattice with origin `p(c₀,0)` -/
theorem hE_conv (S : SetupG D e f α β γ L ax ay) (c₀ i : ℕ) (y : ℝ)
    (hE : UTM D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + i + 1)) 0 y) :
    ∃ tE, HasV D tE (lpG (e : ℝ) f 1 (xo f c₀) ((i : ℝ) + 1) y) (lpG (e : ℝ) f 1 (xo f c₀) ((i : ℝ) + 1) (y + 1))
      (lpG (e : ℝ) f 1 (xo f c₀) (i : ℝ) (y + sMir (e : ℝ) f)) := by
  obtain ⟨t, ht⟩ := (mirrorAt_iff_UTM_gen S _ _).2 hE
  refine ⟨t, hasV_congr ht ?_ ?_ ?_⟩
  · rw [xo_shift, Erdos634.Draft.WGapStmt.lpG_shift]; exact lpG_congr (by ring) rfl
  · rw [xo_shift, Erdos634.Draft.WGapStmt.lpG_shift]; exact lpG_congr (by ring) rfl
  · rw [xo_shift, Erdos634.Draft.WGapStmt.lpG_shift]
    exact lpG_congr (by ring) (by unfold sMir; ring)

theorem mp_xo_zero (S : SetupG D e f α β γ L ax ay) (c₀ i : ℕ) (y : ℝ) :
    mpG (e : ℝ) f 1 (xo f (c₀ + i + 1)) 0 y = ptO e f (xo f c₀) i y := by
  rw [mpG_eq_zero S.e0 S.hef', xo_shift, Erdos634.Draft.WGapStmt.lpG_shift]
  unfold ptO; exact lpG_congr (by ring) rfl

theorem mp_xo_one (S : SetupG D e f α β γ L ax ay) (c₀ i : ℕ) (y : ℝ) :
    mpG (e : ℝ) f 1 (xo f (c₀ + i + 1)) 1 y = ptV e f (xo f c₀) i y := by
  rw [mpG_eq S.e0 S.hef', xo_shift, Erdos634.Draft.WGapStmt.lpG_shift]
  unfold ptV; exact lpG_congr (by ring) (by ring)

/-- translating the output of the fillers into `St2` / `Pi4` -/
theorem dich_translate (S : SetupG D e f α β γ L ax ay) (c₀ i y : ℕ)
    (h : (∃ τ : Fin N, ∃ R, HasV D τ (ptO e f (xo f c₀) i (y : ℝ))
        (ptO e f (xo f c₀) i (y : ℝ) + nuG (e : ℝ) f • (ptV e f (xo f c₀) i (y : ℝ) - ptO e f (xo f c₀) i (y : ℝ))) R ∧
        0 < cross (ptV e f (xo f c₀) i (y : ℝ) - ptO e f (xo f c₀) i (y : ℝ)) (R - ptO e f (xo f c₀) i (y : ℝ))) ∨
      (∃ τ : Fin N, ∃ R, HasV D τ (ptO e f (xo f c₀) i (y : ℝ))
        (ptO e f (xo f c₀) i (y : ℝ) + nuG (e : ℝ) f • (ptY e f (xo f c₀) i (y : ℝ) - ptO e f (xo f c₀) i (y : ℝ))) R ∧
        cross (ptY e f (xo f c₀) i (y : ℝ) - ptO e f (xo f c₀) i (y : ℝ)) (R - ptO e f (xo f c₀) i (y : ℝ)) < 0)) :
    St2 D (e : ℝ) f (xo f (c₀ + i + 1)) (y : ℝ) ∨ Pi4 D e f c₀ i y := by
  rcases h with ⟨τ, R, h1, h2⟩ | ⟨τ, R, h1, h2⟩
  · left
    refine ⟨τ, ptO e f (xo f c₀) i (y : ℝ) + nuG (e : ℝ) f • (ptV e f (xo f c₀) i (y : ℝ) - ptO e f (xo f c₀) i (y : ℝ)), R, ?_, ?_, ?_⟩
    · rw [mp_xo_zero S]; exact h1
    · rw [mp_xo_zero S, mp_xo_one S]
    · rw [mp_xo_zero S, mp_xo_one S]; exact h2
  · right
    exact ⟨τ, R, h1, h2⟩

/-- **ST dichotomy, core**: the filler `F` of `Ω` is `F_c` (`St2` at the station `p(c₀+i+1,y₀)`) or `F_b` (`Pi4`) -/
theorem st_dichotomy_core (S : SetupG D e f α β γ L ax ay) {c₀ s y₀ i : ℕ} (hy : y₀ < s) (hsf : s ≤ f - 1)
    (hi : i + 2 ≤ s - y₀) (hK2 : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) s y₀) (hNt : NTile D e f c₀ i y₀)
    (hEt : UTM D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + i + 1)) 0 (y₀ : ℝ)) :
    St2 D (e : ℝ) f (xo f (c₀ + i + 1)) (y₀ : ℝ) ∨ Pi4 D e f c₀ i y₀ := by
  obtain ⟨tN, hN⟩ := hNt
  obtain ⟨tE, hE⟩ := hE_conv S c₀ i (y₀ : ℝ) hEt
  rcases Nat.eq_zero_or_pos y₀ with h0 | hpos
  · -- the point `O` is on the side
    subst h0
    obtain ⟨tUa, hUa⟩ := hK2.1 (i + 1) 0 le_rfl (by omega)
    obtain ⟨tUi, hUi⟩ := hK2.1 i 0 le_rfl (by omega)
    rw [Nat.cast_add, Nat.cast_one] at hUa
    obtain ⟨hx0, hxL, -⟩ := open_shift_K2 S hK2 (n := i + 1) (by omega) (by omega)
    have hfr := S.base_frontier hx0 hxL
    have hpt : mkPt (shiftX (f : ℝ) 1 (xo f c₀) (i + 1)) 0 = lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) + 1) ((0 : ℕ) : ℝ) := by
      unfold lpG shiftX; exact mkPt_congr (by push_cast; ring) (by simp)
    rw [hpt] at hfr
    exact dich_translate S c₀ i 0 (dich_fill_bdry S (xo f c₀) (i : ℝ) ((0 : ℕ) : ℝ) hUa hUi hN hE (Nat.cast_nonneg 0) hfr)
  · obtain ⟨j, rfl⟩ : ∃ j, y₀ = j + 1 := ⟨y₀ - 1, by omega⟩
    obtain ⟨tDL, hDL⟩ := hK2.2 i j (by omega) (by omega)
    obtain ⟨tUl, hUl⟩ := hK2.1 (i + 1) j (by omega) (by omega)
    obtain ⟨tDl, hDl⟩ := hK2.2 (i + 1) j (by omega) (by omega)
    obtain ⟨tUr, hUr⟩ := hK2.1 (i + 1) (j + 1) le_rfl (by omega)
    obtain ⟨tUi, hUi⟩ := hK2.1 i (j + 1) le_rfl (by omega)
    simp only [Nat.cast_add, Nat.cast_one] at hUl hDl hUr hUi hN hE
    have key := dich_fill_int S (xo f c₀) (i : ℝ) (j : ℝ) hDL hUl hDl hUr hUi hN hE
    have hy1 : (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    refine dich_translate S c₀ i (j + 1) ?_
    rw [hy1]
    exact key

end dich4

#print axioms dich_translate
#print axioms st_dichotomy_core

end Erdos634.Draft.WGapStmt
