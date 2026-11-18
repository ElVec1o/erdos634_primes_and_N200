/-
Draft/WGapRL28.lean -- written 16 November 2026 (session 14).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 steps (5), (6) at `i = 2`, `lambda = 0`).
Not imported by any aggregate.  No sorry, no native_decide.
* `row_two`: `U(0,j+1)` and `U(1,j+1)` are tiles (step (5) at `i = 2`: `row_up_q`, `sigma_rowB2` at `q = 2`, "K or Sigma" `kor_one`).
* `step6_two`: step (6) at `A_2 = p(2,j+1)`: `N^1 = N_1(j+1)` is a tile (`rl_step6` at the shifted origin; `(r3)` at `t = 2` is `rl_close`; the `c`-edge is `K3G` of size 2 against `kor_two`).
-/
import Erdos634.Draft.WGapRL27

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

theorem toSh {e f x a b a' b' : ℝ} (ha : a = a' + 1) (hb : b = b') :
    lpG e f 1 x a b = lpG e f 1 (xsh1 f x) a' b' := by
  rw [lpG_sh1]; exact lpG_congr ha hb

section rl28

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 8000000 in
theorem row_two (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J j : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j) (hjf : j + 3 ≤ f - 1)
    (hS1 : StripTiles D e f c₀ J j)
    (hUall : ∀ a b : ℕ, b ≤ j → a + b ≤ 2 + j → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hDall : ∀ a b : ℕ, b < j → a + b + 1 ≤ 2 + j → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hD0 : ∀ a : ℕ, a < 2 → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (j : ℝ))
    (hN2 : NTile D e f c₀ 2 j) (hIH : SigmaAll D e f 1) :
    UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) ((j : ℝ) + 1) ∧
    UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((1 : ℕ) : ℝ) ((j : ℝ) + 1) := by
  have C : CtxBase D e f α β γ L ax ay 1 (xo f c₀) := ⟨S, Or.inl rfl⟩
  have hUc : ∀ y : ℕ, J ≤ y → y ≤ j → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (y : ℝ) :=
    fun y h1 h2' => hUall 0 y h2' (by omega)
  have hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0 := by
    have := hUall 0 0 (Nat.zero_le _) (by omega)
    rwa [Nat.cast_zero] at this
  have hU01 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((j : ℝ) + 1) :=
    row_up_q S h2 hH4 hA hJ (by omega) (by norm_num) (by omega) hS1 hUc hD0 hN2
  have hU01' : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) ((j : ℝ) + 1) := by
    rwa [Nat.cast_zero]
  refine ⟨hU01', ?_⟩
  have hq : (0 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
  obtain ⟨tE, hE0⟩ := hS1 j hJ le_rfl
  rw [zero_add] at hE0
  have hclL := row_left_clamp_E S (q := 2) hq hE0
  obtain ⟨tN, hNt⟩ := hN2
  have hcr := row_right_clamp_Nq S (x := xo f c₀) (y := (j : ℝ)) (a := ((2 : ℕ) : ℝ)) hq hNt
  have hrow := sigma_rowB2 C (j := j) (q := 2) (by norm_num) (by omega)
    (fun i' j' hj' hij => hUall i' j' hj' (by omega))
    (fun i' j' hj' hij => hDall i' j' hj' (by omega))
    hD0 hcr hclL (by rwa [Nat.cast_zero] at hU01')
    (fun m' hm1 hm2 s' hs1 hs2 hs3 hK2 hK3 => by
      obtain rfl : s' = j + 2 := by omega
      exact kor_one S h2 hA hJ (by omega) hS1 hUc hU0 hU01 hIH hK2 hK3)
  exact hrow 1 (by norm_num)

set_option maxHeartbeats 16000000 in
theorem step6_two (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay)
    {c₀ J j : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j) (hjf : j + 3 ≤ f - 1)
    (hS1 : StripTiles D e f c₀ J j)
    (hUall : ∀ a b : ℕ, b ≤ j → a + b ≤ 2 + j → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hDall : ∀ a b : ℕ, b < j → a + b + 1 ≤ 2 + j → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hD0 : ∀ a : ℕ, a < 2 → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (j : ℝ))
    (hU01 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) ((j : ℝ) + 1))
    (hU11 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((1 : ℕ) : ℝ) ((j : ℝ) + 1))
    (hN2 : NTile D e f c₀ 2 j) (hP4 : Pi4 D e f c₀ 2 j) (hSig : SigmaAll D e f 2) :
    NTile D e f c₀ 1 (j + 1) := by
  have he0 := S.e0
  have hef := S.hef'
  have hν0 := nuG_pos he0 hef
  set x := xo f c₀ with hxdef
  obtain ⟨tDL, hDLt⟩ := hD0 1 (by norm_num)
  obtain ⟨tUl, hUlt⟩ := hUall 2 j le_rfl (by omega)
  have hU11c := hU11
  obtain ⟨tUi, hUit⟩ := hU11
  obtain ⟨tN2, hN2t⟩ := hN2
  have hDL : HasV D tDL (p1j (e : ℝ) f (xsh1 (f : ℝ) x) j) (p0j1 (e : ℝ) f (xsh1 (f : ℝ) x) j) (pA1 (e : ℝ) f (xsh1 (f : ℝ) x) j) :=
    hasV_congr hDLt (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl)
  have hUl : HasV D tUl (p1j (e : ℝ) f (xsh1 (f : ℝ) x) j) (p2j (e : ℝ) f (xsh1 (f : ℝ) x) j) (pA1 (e : ℝ) f (xsh1 (f : ℝ) x) j) :=
    hasV_congr hUlt (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl)
  have hUi : HasV D tUi (p0j1 (e : ℝ) f (xsh1 (f : ℝ) x) j) (pA1 (e : ℝ) f (xsh1 (f : ℝ) x) j) (pA0 (e : ℝ) f (xsh1 (f : ℝ) x) j) :=
    hasV_congr hUit (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl)
  have hN2' : HasV D tN2 (p2j (e : ℝ) f (xsh1 (f : ℝ) x) j) (pA1 (e : ℝ) f (xsh1 (f : ℝ) x) j) (pB0 (e : ℝ) f (xsh1 (f : ℝ) x) j) :=
    hasV_congr hN2t (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl) (toSh (by push_cast; ring) rfl)
  rcases rl_step6 S (xsh1 (f : ℝ) x) j hDL hUl hUi hN2' with ⟨tN, hN⟩ | ⟨F, R, lamc, hl, hF, hR⟩ | ⟨τ, P, W, hV, hP, hW, hang, hPW, hc, hWd⟩
  · -- `N^1` is a tile
    refine ⟨tN, hasV_congr hN (toSh (by push_cast; ring) (by push_cast; ring)).symm
      (toSh (by push_cast; ring) (by push_cast; ring)).symm (toSh (by push_cast; ring) (by push_cast; ring)).symm⟩
  · -- (r3) at `t = 2`: `rl_close`
    exfalso
    have e1 : PIR (e : ℝ) f (xsh1 (f : ℝ) x) j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) = PIR (e : ℝ) f x j 2 ((2 : ℕ) : ℝ) ((0 : ℕ) : ℝ) := by
      rw [PIR_sh1]
      exact PIR_congr (by norm_num) rfl
    rw [e1, dcvec_sh1] at hF hR
    have hN2P : ∃ T : Fin N, HasV D T (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) + 1) 0) (PIR (e : ℝ) f x j 2 ((2 : ℕ) : ℝ) 0)
        (PIR (e : ℝ) f x j 2 ((2 : ℕ) : ℝ) 1) :=
      ⟨tN2, hasV_PIR he0 hef hN2t (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
        (by push_cast; ring) (by push_cast; ring)⟩
    obtain ⟨T1, hT1⟩ := hN2P
    have hnuA : ∀ m' : ℕ, m' ≤ 0 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') m')
          (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) - m') ((m' : ℝ) + 1)) := by
      intro m' hm'
      obtain rfl : m' = 0 := by omega
      exact ⟨T1, hasV_congr hT1 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
        (PIR_congr (by norm_num) (by norm_num))⟩
    have hnuB : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 0 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j 2 (((2 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j 2 ((2 : ℕ) : ℝ) m')
          (PIR (e : ℝ) f x j 2 ((2 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
      intro m' _ hm'
      obtain rfl : m' = 0 := by omega
      exact ⟨T1, hasV_congr hT1 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
        (PIR_congr (by norm_num) (by norm_num))⟩
    exact rl_close S x j 2 2 0 0 (by omega) (by omega) (by omega) (by omega) hnuA hP4 hnuB ⟨F, R, lamc, hl, hF, hR⟩
  · -- the `c`-edge: `K3G` of size 2
    exfalso
    have hK3' := K3G_of_cedge S (xsh1 (f : ℝ) x) j hN2' hV hP hW hc
    have hK3s := K3G_shift1 x hK3'
    have hcast : (((j + 2 : ℕ) : ℝ) + 1) = ((j + 3 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at hK3s
    have hK2 : K2G D (e : ℝ) (f : ℝ) 1 x (j + 3) (j + 1) := by
      refine ⟨fun i j' hj' hij => ?_, fun i j' hj' hij => ?_⟩
      · rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
        · exact hUall i j' (by omega) (by omega)
        · have hje : j' = j + 1 := by omega
          subst hje
          rw [Nat.cast_add, Nat.cast_one]
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
          · exact hU01
          · exact hU11c
      · rcases Nat.lt_or_ge j' j with hlt | hge
        · exact hDall i j' hlt (by omega)
        · have hje : j' = j := by omega
          subst hje
          exact hD0 i (by omega)
    have hUc : ∀ y : ℕ, J ≤ y → y ≤ j → UTG D (e : ℝ) (f : ℝ) 1 x ((0 : ℕ) : ℝ) (y : ℝ) :=
      fun y h1 h2' => hUall 0 y h2' (by omega)
    have hU0 : UTG D (e : ℝ) (f : ℝ) 1 x 0 0 := by
      have := hUall 0 0 (Nat.zero_le _) (by omega)
      rwa [Nat.cast_zero] at this
    have hU01z : UTG D (e : ℝ) (f : ℝ) 1 x 0 ((j : ℝ) + 1) := by rwa [Nat.cast_zero] at hU01
    exact kor_two S h2 hA hJ hjf hS1 hUc hU0 hU01z hSig hK2 hK3s

end rl28

#print axioms row_two
#print axioms step6_two

end Erdos634.Draft.WGapStmt
