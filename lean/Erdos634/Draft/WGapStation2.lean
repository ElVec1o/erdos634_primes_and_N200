/-
Draft/WGapStation2.lean -- written 16 November 2026 (session 17).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 (3a)-(3c)).
Not imported by any aggregate.  No sorry, no native_decide.
**`station_stmt : StationStmt`** (the statement of `WGapClimb10.StationStmt`, unchanged), hence the climb `climb_gen_aux` and `prop_B_of_station` of session 16 become UNCONDITIONAL.
Proof (PROOF 9.4 (3)): at the first column `x` carrying `N_x` in the row `y = j+lam`, `O = p(x+1, j+lam)`:
(3b) the tile `E` beside the `b`-edge of `U(x+1,j+lam)` (`station_E_lat`, WGapStation1): if it lays `c` then `K1J` holds at the origin `p(c₀+x+1, 0)` with `js = j+lam`, and `N_at_origin` contradicts (C1) (`N^{i-lam}`);
so it lays `b`: `UTM` at the new origin (the strip tile);
(3a) the filler `F` of the wedge `(2α,3α)`: `st_dichotomy_core` (the Sigma-station template of session 8) gives `St2` at `O` (`F` lays `c` on the chord of `N_x`, `b` on `L_O`) or `Pi4` (`F` lays `b` on the chord),
and `Pi4` is excluded by `BUpTo` (`station_Pi4_false`).  `(3c)`: the strip tile of the station is `E`.
Credit: Beeson-Rosu / Laczkovich for the wedge-and-chord method, the project's `WGapDich*`, `WGapKN`, `WGapClimb*`.
-/
import Erdos634.Draft.WGapStation1

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

set_option maxHeartbeats 16000000 in
theorem station_stmt : StationStmt := by
  intro N D e f α β γ L ax ay S h2 hH4 c₀ J j i lam hA hJ hij hlam1 hlt hCl hSig hB hP4 x hx2 hbefore hN
  obtain ⟨y1, hy1⟩ : ∃ y1, j + lam = y1 + 1 := ⟨j + lam - 1, by omega⟩
  have hcy : (((j + lam : ℕ)) : ℝ) = (y1 : ℝ) + 1 := by rw [hy1]; push_cast; ring
  have hCl' := hCl
  obtain ⟨hC1, hS1, hUa, hDa⟩ := hCl
  have hDL := hDa x y1 (by omega) (by omega)
  have hUl := hUa (x + 1) y1 (by omega) (by omega)
  have hDl := hDa (x + 1) y1 (by omega) (by omega)
  have hUr := hUa (x + 1) (y1 + 1) (by omega) (by omega)
  have hUi := hUa x (y1 + 1) (by omega) (by omega)
  have hN' := hN
  simp only [Nat.cast_add, Nat.cast_one] at hDL hUl hDl hUr hUi
  obtain ⟨tDL, hDL⟩ := hDL
  obtain ⟨tUl, hUl⟩ := hUl
  obtain ⟨tDl, hDl⟩ := hDl
  obtain ⟨tUr, hUr⟩ := hUr
  obtain ⟨tUi, hUi⟩ := hUi
  obtain ⟨tN, hNv⟩ := hN'
  rw [hy1] at hNv
  simp only [Nat.cast_add, Nat.cast_one] at hNv
  have hE := station_E_lat S (xo f c₀) (x : ℝ) (y1 : ℝ) (x + 1) (by push_cast; ring) hDL hUl hDl hUr hUi hNv
  -- the strip tile of the station at level `j + lam`
  have hEt : UTM D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + x + 1)) 0 (((j + lam : ℕ)) : ℝ) := by
    rcases hE with ⟨iT, k, m, t, hkm, hk, hm, ht, hlen, hle⟩ | hmir
    · exfalso
      -- `E` lays `c`: `K1J` at the origin `p(c₀+x+1, 0)`
      have hK1 : K1J D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + (x + 1))) (j + lam) := by
        refine ⟨iT, k, m, t, hkm, ?_, ?_, ht, hlen, ?_⟩
        · rw [hk, lpG_xo_add _ _ f c₀ (x + 1) rfl, hcy]
          exact lpG_congr (by push_cast; ring) rfl
        · rw [hm, lpG_xo_add _ _ f c₀ (x + 1) rfl, hcy]
          exact lpG_congr (by push_cast; ring) (by ring)
        · intro i'
          have h0 : lvG (e : ℝ) (f : ℝ) 1 (xo f (c₀ + (x + 1))) 0 = lvG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((x : ℝ) + 1) := by
            rw [xo_add, lvG_shk]
            congr 1
            push_cast; ring
          rw [h0]
          exact hle i'
      have hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + (x + 1))) 0 0 := by
        have := UTG_rebase (c₀ := c₀) (m := x + 1) (a := 0) (b := ((0 : ℕ) : ℝ))
          (hUa (0 + (x + 1)) 0 (by omega) (by omega))
        rw [Nat.cast_zero] at this
        exact this
      have hNn : NTile D e f (c₀ + (x + 1)) (i - lam - (x + 1)) (j + lam) := by
        have h1 := hC1 (i - lam) le_rfl (by omega)
        have e1 : j + i - (i - lam) = j + lam := by omega
        rw [e1] at h1
        have e2 : i - lam = (i - lam - (x + 1)) + (x + 1) := by omega
        rw [e2] at h1
        exact NTile_rebase h1
      refine N_at_origin S (c₀ + (x + 1)) (j + lam) (fun h => absurd h (by omega)) hU0 hK1
        (i - lam - (x + 1)) (j + lam) le_rfl (by omega) ?_ ?_ ?_ hNn
      · intro i' j' hj' hij'
        exact UTG_rebase (c₀ := c₀) (m := x + 1) (a := i') (b := (j' : ℝ))
          (hUa (i' + (x + 1)) j' (by omega) (by omega))
      · intro i' j' hj' hij'
        exact DTG_rebase (c₀ := c₀) (m := x + 1) (a := i') (b := (j' : ℝ))
          (hDa (i' + (x + 1)) j' (by omega) (by omega))
      · intro m' hm1 hm2
        exact K_at_origin S (c₀ + (x + 1)) (j + lam) (fun h => absurd h (by omega)) hU0 hK1 m' hm1
    · have hxe : shiftX (f : ℝ) 1 (xo f c₀) (x + 1) = xo f (c₀ + x + 1) := by
        unfold shiftX xo; push_cast; ring
      have := (mirrorAt_iff_UTM_gen S _ _).1 hmir
      rw [hxe, ← hcy] at this
      exact this
  have hK2 : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (j + lam + x + 2) (j + lam) :=
    ⟨fun a b hb hab => hUa a b hb (by omega), fun a b hb hab => hDa a b hb (by omega)⟩
  have hdich := st_dichotomy_core S (c₀ := c₀) (s := j + lam + x + 2) (y₀ := j + lam) (i := x)
    (by omega) (by omega) (by omega) hK2 hN hEt
  rcases hdich with hSt2 | hPi4
  · refine ⟨Or.inr ⟨by omega, hSt2⟩, ?_⟩
    intro y h1 h2
    have : y = j + lam := by omega
    subst this
    exact hEt
  · exact absurd hPi4 (fun h => station_Pi4_false hA hJ hij hlt hCl' hB hx2 hbefore hN h)

#print axioms station_stmt

end Erdos634.Draft.WGapStmt
