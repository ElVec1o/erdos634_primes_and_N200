/-
Draft/WGapClimb2.lean -- written 16 November 2026 (session 16).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 steps (5), (6) at `lambda = 0`, GENERAL `q = k+1`).
Not imported by any aggregate.  No sorry, no native_decide.
* `row_gen`: `U(r, j+1)` for every `r < k+1` (step (5); `row_up_q` + `sigma_rowB2` + `kor_gen`); generalizes `row_two`;
* `step6_gen`: `N_k(j+1)` is a tile (step (6): `rl_step6` at the `k`-fold shifted origin; `(r3)` at `t = k+1` is `rl_close`; the `c`-edge is `K3G_of_cedge` against `kor_gen`); generalizes `step6_two`.
-/
import Erdos634.Draft.WGapClimb1

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

section climb2

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
theorem row_gen (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J j k : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j) (hjf : j + k + 2 ≤ f - 1)
    (hS1 : StripTiles D e f c₀ J j)
    (hUall : ∀ a b : ℕ, b ≤ j → a + b ≤ (k + 1) + j → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hDall : ∀ a b : ℕ, b < j → a + b + 1 ≤ (k + 1) + j → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hD0 : ∀ a : ℕ, a < k + 1 → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (j : ℝ))
    (hN : NTile D e f c₀ (k + 1) j) (hIH : SigmaAll D e f k) :
    ∀ r : ℕ, r < k + 1 → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (r : ℝ) ((j : ℝ) + 1) := by
  have C : CtxBase D e f α β γ L ax ay 1 (xo f c₀) := ⟨S, Or.inl rfl⟩
  have hUc : ∀ y : ℕ, J ≤ y → y ≤ j → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (y : ℝ) :=
    fun y h1 h2' => hUall 0 y h2' (by omega)
  have hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0 := by
    have := hUall 0 0 (Nat.zero_le _) (by omega)
    rwa [Nat.cast_zero] at this
  have hU01 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((j : ℝ) + 1) :=
    row_up_q S h2 hH4 hA hJ (by omega) (by omega) (by omega) hS1 hUc hD0 hN
  have hU01' : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) ((j : ℝ) + 1) := by
    rwa [Nat.cast_zero]
  have hq : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨tE, hE0⟩ := hS1 j hJ le_rfl
  rw [zero_add] at hE0
  have hclL := row_left_clamp_E S (q := k + 1) hq hE0
  obtain ⟨tN, hNt⟩ := hN
  have hcr := row_right_clamp_Nq S (x := xo f c₀) (y := (j : ℝ)) (a := ((k + 1 : ℕ) : ℝ)) hq hNt
  exact sigma_rowB2 C (j := j) (q := k + 1) (by omega) (by omega)
    (fun i' j' hj' hij => hUall i' j' hj' (by omega))
    (fun i' j' hj' hij => hDall i' j' hj' (by omega))
    hD0 hcr hclL (by rwa [Nat.cast_zero] at hU01')
    (fun m' hm1 hm2 s' hs1 hs2 hs3 hK2 hK3 => by
      obtain rfl : s' = j + 1 + m' := by omega
      exact kor_gen S h2 hA hJ hm1 (by omega) hS1 hUc hU0 hU01
        (fun c J' hA' s y hJ' hy hsf hs hσ => hIH c J' hA' s y hJ' hy hsf (by omega) hσ) hK2 hK3)

set_option maxHeartbeats 32000000 in
theorem step6_gen (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay)
    {c₀ J j k : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j) (hjf : j + k + 2 ≤ f - 1)
    (hS1 : StripTiles D e f c₀ J j)
    (hUall : ∀ a b : ℕ, b ≤ j → a + b ≤ (k + 1) + j → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hDall : ∀ a b : ℕ, b < j → a + b + 1 ≤ (k + 1) + j → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (b : ℝ))
    (hD0 : ∀ a : ℕ, a < k + 1 → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (a : ℝ) (j : ℝ))
    (hrow : ∀ r : ℕ, r < k + 1 → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (r : ℝ) ((j : ℝ) + 1))
    (hN : NTile D e f c₀ (k + 1) j) (hP4 : Pi4 D e f c₀ (k + 1) j) (hSig : SigmaAll D e f (k + 1)) :
    NTile D e f c₀ k (j + 1) := by
  have he0 := S.e0
  have hef := S.hef'
  have hν0 := nuG_pos he0 hef
  set x := xo f c₀ with hxdef
  obtain ⟨tDL, hDLt⟩ := hD0 k (by omega)
  obtain ⟨tUl, hUlt⟩ := hUall (k + 1) j le_rfl (by omega)
  have hUic := hrow k (by omega)
  obtain ⟨tUi, hUit⟩ := hUic
  obtain ⟨tN2, hN2t⟩ := hN
  have hDL : HasV D tDL (p1j (e : ℝ) f (xshk (f : ℝ) k x) j) (p0j1 (e : ℝ) f (xshk (f : ℝ) k x) j) (pA1 (e : ℝ) f (xshk (f : ℝ) k x) j) :=
    hasV_congr hDLt (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl)
  have hUl : HasV D tUl (p1j (e : ℝ) f (xshk (f : ℝ) k x) j) (p2j (e : ℝ) f (xshk (f : ℝ) k x) j) (pA1 (e : ℝ) f (xshk (f : ℝ) k x) j) :=
    hasV_congr hUlt (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl)
  have hUi : HasV D tUi (p0j1 (e : ℝ) f (xshk (f : ℝ) k x) j) (pA1 (e : ℝ) f (xshk (f : ℝ) k x) j) (pA0 (e : ℝ) f (xshk (f : ℝ) k x) j) :=
    hasV_congr hUit (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl)
  have hN2' : HasV D tN2 (p2j (e : ℝ) f (xshk (f : ℝ) k x) j) (pA1 (e : ℝ) f (xshk (f : ℝ) k x) j) (pB0 (e : ℝ) f (xshk (f : ℝ) k x) j) :=
    hasV_congr hN2t (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl) (toShk (by push_cast; ring) rfl)
  rcases rl_step6 S (xshk (f : ℝ) k x) j hDL hUl hUi hN2' with ⟨tN, hN⟩ | ⟨F, R, lamc, hl, hF, hR⟩ | ⟨τ, P, W, hV, hP, hW, hang, hPW, hc, hWd⟩
  · -- `N_k(j+1)` is a tile
    refine ⟨tN, hasV_congr hN (toShk (by push_cast; ring) (by push_cast; ring)).symm
      (toShk (by push_cast; ring) (by push_cast; ring)).symm (toShk (by push_cast; ring) (by push_cast; ring)).symm⟩
  · -- (r3) at `t = k+1`: `rl_close`
    exfalso
    have e1 : PIR (e : ℝ) f (xshk (f : ℝ) k x) j 1 ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) =
        PIR (e : ℝ) f x j (k + 1) (((k + 1 : ℕ)) : ℝ) ((0 : ℕ) : ℝ) := by
      rw [PIR_shk, Nat.add_comm 1 k]
      exact PIR_congr (by push_cast; ring) rfl
    rw [e1, dcvec_shk] at hF hR
    have hN2P : ∃ T : Fin N, HasV D T (PIR (e : ℝ) f x j (k + 1) (((k + 1 : ℕ) : ℝ) + 1) 0)
        (PIR (e : ℝ) f x j (k + 1) ((k + 1 : ℕ) : ℝ) 0) (PIR (e : ℝ) f x j (k + 1) ((k + 1 : ℕ) : ℝ) 1) :=
      ⟨tN2, hasV_PIR he0 hef hN2t (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
        (by push_cast; ring) (by push_cast; ring)⟩
    obtain ⟨T1, hT1⟩ := hN2P
    have hnuA : ∀ m' : ℕ, m' ≤ 0 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j (k + 1) (((k + 1 : ℕ) : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j (k + 1) (((k + 1 : ℕ) : ℝ) - m') m')
          (PIR (e : ℝ) f x j (k + 1) (((k + 1 : ℕ) : ℝ) - m') ((m' : ℝ) + 1)) := by
      intro m' hm'
      obtain rfl : m' = 0 := by omega
      exact ⟨T1, hasV_congr hT1 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
        (PIR_congr (by norm_num) (by norm_num))⟩
    have hnuB : ∀ m' : ℕ, 0 ≤ m' → m' ≤ 0 → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j (k + 1) (((k + 1 : ℕ) : ℝ) + 1) m') (PIR (e : ℝ) f x j (k + 1) ((k + 1 : ℕ) : ℝ) m')
          (PIR (e : ℝ) f x j (k + 1) ((k + 1 : ℕ) : ℝ) ((m' : ℝ) + 1)) := by
      intro m' _ hm'
      obtain rfl : m' = 0 := by omega
      exact ⟨T1, hasV_congr hT1 (PIR_congr (by norm_num) (by norm_num)) (PIR_congr (by norm_num) (by norm_num))
        (PIR_congr (by norm_num) (by norm_num))⟩
    exact rl_close S x j (k + 1) (k + 1) 0 0 (by omega) (by omega) (by omega) (by omega) hnuA hP4 hnuB ⟨F, R, lamc, hl, hF, hR⟩
  · -- the `c`-edge: `K3G` of size `k+1`
    exfalso
    have hK3' := K3G_of_cedge S (xshk (f : ℝ) k x) j hN2' hV hP hW hc
    have hK3s := K3G_shiftk x k hK3'
    have hcast : (((j + 2 : ℕ) : ℝ) + (k : ℝ)) = ((j + 1 + (k + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at hK3s
    have hK2 : K2G D (e : ℝ) (f : ℝ) 1 x (j + 1 + (k + 1)) (j + 1) := by
      refine ⟨fun i j' hj' hij => ?_, fun i j' hj' hij => ?_⟩
      · rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
        · exact hUall i j' (by omega) (by omega)
        · have hje : j' = j + 1 := by omega
          subst hje
          rw [Nat.cast_add, Nat.cast_one]
          exact hrow i (by omega)
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
    have hU01z : UTG D (e : ℝ) (f : ℝ) 1 x 0 ((j : ℝ) + 1) := by
      have := hrow 0 (by omega)
      rwa [Nat.cast_zero] at this
    exact kor_gen S h2 hA hJ (by omega) (by omega) hS1 hUc hU0 hU01z hSig hK2 hK3s

end climb2

#print axioms row_gen
#print axioms step6_gen

end Erdos634.Draft.WGapStmt
