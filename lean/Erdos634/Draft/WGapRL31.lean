/-
Draft/WGapRL31.lean -- written 16 November 2026 (session 14).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 at `i = 2`: `lambda = 0 -> 1 -> 2`, then 9.3 = `rl_two`).
Not imported by any aggregate.  No sorry, no native_decide.
`prop_B_two`: **Proposition B at `i = 2`**: given `Sigma[2]`, `Pi_b^a(j, 2)` does not occur.  Steps: `lambda = 0`: (5) `row_two` (`U(0,j+1)`, `U(1,j+1)`), (6) `step6_two` (`N^1`), (7) `Tplus_core` + `N_at_origin` (`i_N = 1`) give `E_{j+1}`;
`lambda = 1`: (1) `m_nextG`: `S_0 = D(0,j+1)` | `N_0(j+1)` (`lam1_N_false`) | `K3G` (Sigma[1]); (5) `row_up_one` at level `j+1`; (6) `rl_step6` (`N^0` | `(r3)` at `t = 1`: `rl_one_sh` | `c`-edge: `step6_c_false`);
(7) `Tplus_core` + `N_at_origin` (`i_N = 0`); 9.3: `rl_A0_fill` + `rl_two`.
-/
import Erdos634.Draft.WGapRL30

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

/-- conversion of the lattice coordinates of a `HasV` (the six coordinate equalities are `push_cast; ring`) -/
macro "hv " h:term : term =>
  `(hasV_lp $h (by push_cast; try ring) (by push_cast; try ring) (by push_cast; try ring)
    (by push_cast; try ring) (by push_cast; try ring) (by push_cast; try ring))

theorem PIR_lvl {e f : ℝ} (x : ℝ) (j : ℕ) (t m : ℝ) : PIR e f x (j + 1) 1 t m = PIR e f x j 2 t m := by
  unfold PIR
  exact lpG_congr rfl (by push_cast; ring)

theorem PIR_lvl_sh {e f : ℝ} (x : ℝ) (j : ℕ) :
    PIR e f x (j + 1) 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) = PIR e f (xsh1 f x) j 1 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) := by
  rw [PIR_sh1, PIR_lvl]
  exact PIR_congr (by norm_num) rfl

section rl31

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 32000000 in
theorem prop_B_two (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J : ℕ} (hA : IsApex D e f c₀ J) {j : ℕ} (hJ : J ≤ j) (hij : 2 + j + 1 ≤ f - 1)
    (hSig : SigmaAll D e f 2) : ¬ PiBCfg D e f c₀ J j 2 := by
  rintro ⟨hS1, hUall, hDall, hD0, hN2, hP4⟩
  have he0 := S.e0
  have hef := S.hef'
  have hSig1 : SigmaAll D e f 1 := fun c J' hA' s y hJ' hy hsf hs hσ => hSig c J' hA' s y hJ' hy hsf (by omega) hσ
  set x := xo f c₀ with hxdef
  -- `lambda = 0`: steps (5), (6)
  obtain ⟨hU01, hU11⟩ := row_two S h2 hH4 hA hJ (by omega) hS1 hUall hDall hD0 hN2 hSig1
  have hN1 := step6_two S h2 hA hJ (by omega) hS1 hUall hDall hD0 hU01 hU11 hN2 hP4 hSig
  have hUc : ∀ y : ℕ, J ≤ y → y ≤ j → UTG D (e : ℝ) (f : ℝ) 1 x ((0 : ℕ) : ℝ) (y : ℝ) :=
    fun y h1 h2' => hUall 0 y h2' (by omega)
  have hU0 : UTG D (e : ℝ) (f : ℝ) 1 x 0 0 := by
    have := hUall 0 0 (Nat.zero_le _) (by omega)
    rwa [Nat.cast_zero] at this
  have hU01z : UTG D (e : ℝ) (f : ℝ) 1 x 0 ((j : ℝ) + 1) := by rwa [Nat.cast_zero] at hU01
  -- step (7): `T+` is the strip tile
  have hE1 : UTM D (e : ℝ) (f : ℝ) 1 x 0 ((j : ℝ) + 1) := by
    rcases Tplus_core S hJ hS1 (hUc j hJ le_rfl) hU01z with hK1 | hE
    · exfalso
      refine N_at_origin S c₀ (j + 1) (fun _ => h2) hU0 hK1 1 (j + 1) le_rfl (by omega) ?_ ?_ ?_ hN1
      · intro i' j'' hj'' hij''
        rcases Nat.lt_or_ge j'' (j + 1) with hlt | hge
        · exact hUall i' j'' (by omega) (by omega)
        · have hje : j'' = j + 1 := by omega
          subst hje
          rw [Nat.cast_add, Nat.cast_one]
          rcases (by omega : i' = 0 ∨ i' = 1) with rfl | rfl
          · exact hU01
          · exact hU11
      · intro i' j'' hj'' hij''
        rcases Nat.lt_or_ge j'' j with hlt | hge
        · exact hDall i' j'' hlt (by omega)
        · have hje : j'' = j := by omega
          rw [hje]
          exact hD0 i' (by omega)
      · intro m' hm1 hm2
        exact K_at_origin S c₀ (j + 1) (fun _ => h2) hU0 hK1 m' hm1
    · exact hE
  -- the state after `lambda = 0`
  have hS1' : StripTiles D e f c₀ J (j + 1) := by
    intro y hy1 hy2
    rcases Nat.lt_or_ge y (j + 1) with hlt | hge
    · exact hS1 y hy1 (by omega)
    · have hye : y = j + 1 := by omega
      rw [hye, Nat.cast_add, Nat.cast_one]
      exact hE1
  have hUall' : ∀ a b : ℕ, b ≤ j + 1 → a + b ≤ 1 + (j + 1) → UTG D (e : ℝ) (f : ℝ) 1 x (a : ℝ) (b : ℝ) := by
    intro a b hb hab
    rcases Nat.lt_or_ge b (j + 1) with hlt | hge
    · exact hUall a b (by omega) (by omega)
    · have hbe : b = j + 1 := by omega
      rw [hbe, Nat.cast_add, Nat.cast_one]
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · exact hU01
      · exact hU11
  have hDall' : ∀ a b : ℕ, b < j + 1 → a + b + 1 ≤ 1 + (j + 1) → DTG D (e : ℝ) (f : ℝ) 1 x (a : ℝ) (b : ℝ) := by
    intro a b hb hab
    rcases Nat.lt_or_ge b j with hlt | hge
    · exact hDall a b hlt (by omega)
    · have hbe : b = j := by omega
      rw [hbe]
      exact hD0 a (by omega)
  -- `lambda = 1`: step (1), the tile `S_0` beside the `a`-edge ray of `U(0,j+1)`
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hU01n : UTG D (e : ℝ) (f : ℝ) 1 x ((0 : ℕ) : ℝ) ((j + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]; exact hU01
  have hU11n : UTG D (e : ℝ) (f : ℝ) 1 x (((0 : ℕ) : ℝ) + 1) ((j + 1 : ℕ) : ℝ) := by
    have := hU11
    simp only [Nat.cast_one, Nat.cast_zero, zero_add, Nat.cast_add] at this ⊢
    exact this
  obtain ⟨t0, hUt⟩ := hU01n
  obtain ⟨t1, hU1t⟩ := hU11n
  have hD1n : DTG D (e : ℝ) (f : ℝ) 1 x (((0 + 1 : ℕ)) : ℝ) (((j + 1 - 1 : ℕ)) : ℝ) := by
    have := hD0 1 (by norm_num)
    simp only [Nat.cast_one, Nat.cast_zero, zero_add, Nat.cast_add, Nat.add_sub_cancel] at this ⊢
    exact this
  have hcl := C.m_clamp_natG 0 (j + 1) (Or.inr ⟨by omega, hD1n⟩)
  rcases C.m_nextG (ξ := ((0 : ℕ) : ℝ)) (η := j + 1) hUt ⟨1, one_pos, hU1t.mem₂⟩ hcl with
    ⟨tD0, hD0t⟩ | ⟨tN0, hN0t⟩ | ⟨w, hw⟩
  · -- `S_0 = D(0,j+1)`
    have hD0'' : DTG D (e : ℝ) (f : ℝ) 1 x ((0 : ℕ) : ℝ) ((j + 1 : ℕ) : ℝ) := ⟨tD0, hD0t⟩
    have hUc' : ∀ y : ℕ, J ≤ y → y ≤ j + 1 → UTG D (e : ℝ) (f : ℝ) 1 x ((0 : ℕ) : ℝ) (y : ℝ) :=
      fun y h1 h2' => hUall' 0 y h2' (by omega)
    have hU0' : UTG D (e : ℝ) (f : ℝ) 1 x 0 0 := hU0
    -- step (5): `U(0,j+2)`
    have hU02 : UTG D (e : ℝ) (f : ℝ) 1 x 0 (((j + 1 : ℕ) : ℝ) + 1) :=
      row_up_one S h2 hH4 hA (by omega) (by omega) hS1' hUc' hD0'' hN1
    obtain ⟨tU02, hU02t⟩ := hU02
    obtain ⟨tD0', hD0t'⟩ := hD0''
    obtain ⟨tUl, hUlt⟩ := hUall' 1 (j + 1) (by omega) (by omega)
    obtain ⟨tN1, hN1t⟩ := hN1
    -- the tiles in the form of `rl_step6` at level `j+1`
    have hDL : HasV D tD0 (p1j (e : ℝ) f x (j + 1)) (p0j1 (e : ℝ) f x (j + 1)) (pA1 (e : ℝ) f x (j + 1)) := hv hD0t
    have hUl : HasV D tUl (p1j (e : ℝ) f x (j + 1)) (p2j (e : ℝ) f x (j + 1)) (pA1 (e : ℝ) f x (j + 1)) := hv hUlt
    have hUi : HasV D tU02 (p0j1 (e : ℝ) f x (j + 1)) (pA1 (e : ℝ) f x (j + 1)) (pA0 (e : ℝ) f x (j + 1)) := hv hU02t
    have hN2' : HasV D tN1 (p2j (e : ℝ) f x (j + 1)) (pA1 (e : ℝ) f x (j + 1)) (pB0 (e : ℝ) f x (j + 1)) := hv hN1t
    -- the tiles `D(1,j)`, `U(2,j)`, `U(1,j+1)`, `N^1`, `N^2` in the form of `rl_two`
    obtain ⟨tDa, hDat⟩ := hD0 1 (by norm_num)
    obtain ⟨tUa, hUat⟩ := hUall 2 j (by omega) (by omega)
    obtain ⟨tNa, hNat⟩ := hN2
    have hDa : HasV D tDa (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1))
        (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1)) := hv hDat
    have hUa : HasV D tUa (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 + 1) (j : ℝ))
        (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1)) := hv hUat
    have hUb : HasV D t1 (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1))
        (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1 + 1)) := hv hU1t
    have hNb : HasV D tN1 (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) f 1 x 1 ((j : ℝ) + 1 + 1))
        (lpG (e : ℝ) f 1 x (1 - nuG (e : ℝ) f) ((j : ℝ) + 1 + 2 + nuG (e : ℝ) f)) := hv hN1t
    have hNa' : HasV D tNa (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 + 1) (j : ℝ)) (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1) ((j : ℝ) + 1))
        (lpG (e : ℝ) f 1 x ((1 : ℝ) + 1 - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f)) := hv hNat
    -- step (6) at `A_1 = p(1,j+2)`
    rcases rl_step6 S x (j + 1) hDL hUl hUi hN2' with ⟨tN0', hN0'⟩ | ⟨F, R, lamc, hl, hF, hR⟩ |
        ⟨τ, P, W, hV, hP, hW, hang, hPW, hc, hWd⟩
    · -- `N^0 = N_0(j+2)` is a tile: step (7)
      have hU02z : UTG D (e : ℝ) (f : ℝ) 1 x 0 (((j + 1 : ℕ) : ℝ) + 1) := ⟨tU02, hU02t⟩
      rcases Tplus_core S (by omega : J ≤ j + 1) hS1' (by have := hUc' (j + 1) (by omega) le_rfl; exact this) hU02z with hK1 | hE2
      · exfalso
        refine N_at_origin S c₀ (j + 2) (fun _ => h2) hU0 hK1 0 (j + 2) le_rfl (by omega) ?_ ?_ ?_ ?_
        · intro i' j'' hj'' hij''
          rcases Nat.lt_or_ge j'' (j + 2) with hlt | hge
          · exact hUall' i' j'' (by omega) (by omega)
          · have hje : j'' = j + 2 := by omega
            have hi0 : i' = 0 := by omega
            rw [hje, hi0, Nat.cast_zero]
            have : (((j + 2 : ℕ)) : ℝ) = ((j + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
            rw [this]
            exact ⟨tU02, hU02t⟩
        · intro i' j'' hj'' hij''
          rcases Nat.lt_or_ge j'' (j + 1) with hlt | hge
          · exact hDall' i' j'' hlt (by omega)
          · have hje : j'' = j + 1 := by omega
            have hi0 : i' = 0 := by omega
            rw [hje, hi0]
            exact ⟨tD0', hD0t'⟩
        · intro m' hm1 hm2
          omega
        · exact ⟨tN0', hv hN0'⟩
      · -- `T+ = E_{j+2}`: `rl_A0_fill` and `rl_two`
        obtain ⟨tE2, hE2t⟩ := hE2
        obtain ⟨F, R, lamc, hl, hF, hR⟩ := rl_A0_fill S x (j + 1) hE2t hUi hN0'
        rw [PIR_lvl] at hF hR
        have hP4' := hP4
        refine rl_two S x j (by omega) hDa hUa hUb hNb hNa' (tDc := tD0) (tUc := tU02) (tNc := tN0')
          (hv hD0t) (hv hU02t) (hv hN0') hP4' ⟨F, R, lamc, hl, hF, hR⟩
    · -- `(r3)` at `t = 1`: `RL(2,1)` = `rl_one_sh`
      exfalso
      rw [PIR_lvl_sh, ← dcvec_sh1] at hF hR
      exact rl_one_sh S x j (by omega) hDa hUa hUb hNb hNa' hP4 ⟨F, R, lamc, hl, hF, hR⟩
    · -- the `c`-edge: `K` or `Sigma` of size 1
      exact step6_c_false S h2 hA (by omega : J ≤ j + 1) (by omega) hS1' hUall' hDall' ⟨tD0, hD0t⟩ hN2' ⟨tU02, hU02t⟩
        hSig1 hV hP hW hc
  · -- `S_0 = N_0(j+1)`: impossible
    exfalso
    obtain ⟨tUl, hUlt⟩ := hUall 1 j (by omega) (by omega)
    obtain ⟨tDl, hDlt⟩ := hD0 1 (by norm_num)
    obtain ⟨tDL, hDLt⟩ := hD0 0 (by norm_num)
    obtain ⟨tUi, hUit⟩ := hU01
    obtain ⟨tUr, hUrt⟩ := hU11
    obtain ⟨tUa, hUat⟩ := hUall 2 j (by omega) (by omega)
    obtain ⟨tN1, hN1t⟩ := hN1
    obtain ⟨tNa, hNat⟩ := hN2
    refine lam1_N_false S x j (by omega) (tDL := tDL) (tUl := tUl) (tDl := tDl) (tUr := tUr) (tUi := tUi)
      (tN := tN0) (tN1 := tN1) (tUa := tUa) (tNa := tNa) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hP4
    · exact hv hDLt
    · exact hv hUlt
    · exact hv hDlt
    · exact hv hUrt
    · exact hv hUit
    · exact hv hN0t
    · exact hv hN1t
    · exact hv hUat
    · exact hv hNat
  · -- `S_0` lays `b` or `c`: `Sigma[1]` is violated
    exfalso
    have hs : (((0 : ℕ) : ℝ) + ((j + 1 : ℕ) : ℝ) + 1) = ((j + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hs] at hw
    have hK3 : K3G D (e : ℝ) (f : ℝ) 1 x ((j + 2 : ℕ) : ℝ) ((j + 1 : ℕ) : ℝ) := Or.inr ⟨w, hw⟩
    have hK2 : K2G D (e : ℝ) (f : ℝ) 1 x (j + 2) (j + 1) := by
      refine ⟨fun i' j'' hj'' hij'' => hUall' i' j'' hj'' (by omega), fun i' j'' hj'' hij'' => hDall' i' j'' hj'' (by omega)⟩
    exact hSig1 c₀ J hA (j + 2) (j + 1) (by omega) (by omega) (by omega) (by omega) ⟨hS1', hK2, hK3⟩

end rl31

#print axioms prop_B_two

end Erdos634.Draft.WGapStmt
