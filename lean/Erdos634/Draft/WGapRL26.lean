/-
Draft/WGapRL26.lean -- written 16 November 2026 (session 14).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 step (5) at `i = 2`, `lambda = 0`).
Not imported by any aggregate.  No sorry, no native_decide.
* `row_right_clamp_Nq`: the right clamp of the chord `[p(0,y+1), p(q,y+1)]` from `N_q(y)` (vertex `p(q,y+1)`, `q ≥ 1` a natural number).
* `row_up_q`: `U(0,y0+1)` is a tile, from the strip `E_{y0}`, `U(0,y)`, `D(i',y0)` (`i' < q`), `N_q(y0)` (generalizes `row_up_one`).
* `kor_one`: "K or Sigma" of size 1 at the row `y0+1`: no `(K2),(K3)` pair `(y0+2, y0+1)` (from `Tplus_core`, `K_at_origin`, `Sigma[1]`).
-/
import Erdos634.Draft.WGapRL25
import Erdos634.Draft.WGapRL18

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

section rl26

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem row_right_clamp_Nq (S : SetupG D e f α β γ L ax ay) {x y a : ℝ} (ha : 0 < a) {tN : Fin N}
    (hN : HasV D tN (lpG (e : ℝ) f 1 x (a + 1) y) (lpG (e : ℝ) f 1 x a (y + 1))
      (lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (y + 2 + nuG (e : ℝ) f))) :
    ∃ Q' : Plane, GHG (f : ℝ) Q' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (y + 1)) ∧
      lpG (e : ℝ) (f : ℝ) 1 x a (y + 1) ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 (y + 1)) Q' ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (y + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) 1 x a (y + 1)) (lpG (e : ℝ) (f : ℝ) 1 x 0 (y + 1)) := by
  have he0 := S.e0
  have hef := S.hef'
  have hν0 := nuG_pos he0 hef
  have hA : HasV D tN (lpG (e : ℝ) f 1 x a (y + 1)) (lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (y + 2 + nuG (e : ℝ) f))
      (lpG (e : ℝ) f 1 x (a + 1) y) := hN.rot
  obtain ⟨ε₀, hε₀, hpush⟩ := hasV_push hA (θ1 := a) (θ2 := a * (1 + nuG (e : ℝ) f)) ha (by positivity)
  have hvec : lpG (e : ℝ) f 1 x a (y + 1) - lpG (e : ℝ) f 1 x 0 (y + 1) =
      a • (lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (y + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x a (y + 1)) +
        (a * (1 + nuG (e : ℝ) f)) • (lpG (e : ℝ) f 1 x (a + 1) y - lpG (e : ℝ) f 1 x a (y + 1)) := by
    unfold lpG
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
  have hfA0 : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x a (y + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (y + 1)) :=
    GHG_lp _ _ _ _ _ _
  have hfAq : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x 0 (y + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (y + 1)) :=
    GHG_lp _ _ _ _ _ _
  obtain ⟨P', hfP', hP', hsub⟩ := ext_point_of_push (T := D.tile tN) (GHG (f : ℝ)) hfA0 hfAq
    (by obtain ⟨k0, -, -, -, -, -, hk0, -, -⟩ := hA; have := Erdos634.RouteOneCrossing.pts_mem_carrier (D.tile tN) k0; rw [hk0] at this; exact this)
    ⟨ε₀, hε₀, fun ε hε hε1 => by rw [hvec]; exact hpush ε hε hε1⟩
  refine ⟨P', hfP', ?_, fun ed _ => not_straddles_of_interior D.toDissection hsub ed.1 ed.2⟩
  rw [openSegment_symm]; exact hP'

set_option maxHeartbeats 4000000 in
theorem row_up_q (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J y₀ q : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ y₀) (hyf : y₀ + 1 ≤ f - 1) (hq : 1 ≤ q)
    (hqf : q + y₀ + 1 ≤ f)
    (hS1 : StripTiles D e f c₀ J y₀)
    (hUc : ∀ y : ℕ, J ≤ y → y ≤ y₀ → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (y : ℝ))
    (hD : ∀ i' : ℕ, i' < q → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (i' : ℝ) (y₀ : ℝ))
    (hNq : NTile D e f c₀ q y₀) :
    UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1) := by
  have C : CtxBase D e f α β γ L ax ay 1 (xo f c₀) := ⟨S, Or.inl rfl⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨tE, hE0⟩ := hS1 y₀ hJ le_rfl
  rw [zero_add] at hE0
  obtain ⟨tU, hU⟩ := hUc y₀ hJ le_rfl
  rw [Nat.cast_zero] at hU
  obtain ⟨tD, hDt⟩ := hD 0 (by omega)
  rw [Nat.cast_zero] at hDt
  have hclL := row_left_clamp_E S (q := q) hqpos hE0
  have hcl0 : ∃ P' : Plane, GHG (f : ℝ) P' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((y₀ : ℝ) + 1)) ∧
      lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1) ∈ openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) (0 + 1) ((y₀ : ℝ) + 1)) ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((y₀ : ℝ) + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1))
          (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) (0 + 1) ((y₀ : ℝ) + 1)) := by
    have h := row_left_clamp_E S (x := xo f c₀) (y := (y₀ : ℝ)) (q := 1) (by norm_num) hE0
    rw [show ((1 : ℕ) : ℝ) = 0 + 1 by norm_num] at h
    exact h
  obtain ⟨tN, hNt⟩ := hNq
  have hcr := row_right_clamp_Nq S (x := xo f c₀) (y := (y₀ : ℝ)) (a := (q : ℝ)) hqpos hNt
  have hnob := sigma_row_nob C (j := y₀) (q := q) hq hqf hD hcr hclL
  have hnob0 : ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((y₀ : ℝ) + 1))),
      (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) (0 + 1) ((y₀ : ℝ) + 1)) →
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    intro ed he hsub
    refine hnob 0 le_rfl ?_ ed he hsub
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  rcases row_stepS C hDt (Nat.cast_nonneg y₀) hcl0 hnob0 with hU1 | ⟨ix, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle, hθ, hno, hlen⟩
  · exact hU1
  · exfalso
    obtain ⟨τ, W, hZ, hZc⟩ := zstar S h2 hH4 hA hJ hyf
      (fun y h1 h2' => by
        have := hUc y h1 h2'
        rwa [Nat.cast_zero] at this) hS1
    exact bad0_false S (xo f c₀) (y₀ : ℝ) (Nat.cast_nonneg _) hE0 hU hDt hZ hZc hkm hkj hmj hk ht hm hle hθ hlen

/-- "K or Sigma" of size 1 at the row `y₀+1`: the pair `(y₀+2, y₀+1)` with `(K2)`, `(K3)` cannot occur, given `U(0,y₀+1)` (so that `T⁺` is
`K1J` or the strip tile), `Sigma[1]` and Theorem K. -/
theorem kor_one (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) {c₀ J y₀ : ℕ}
    (hA : IsApex D e f c₀ J) (hJ : J ≤ y₀) (hjf : y₀ + 2 ≤ f - 1)
    (hS1 : StripTiles D e f c₀ J y₀)
    (hUc : ∀ y : ℕ, J ≤ y → y ≤ y₀ → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (y : ℝ))
    (hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0)
    (hU01 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1))
    (hIH : SigmaAll D e f 1)
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (y₀ + 2) (y₀ + 1))
    (hK3 : K3G D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((y₀ + 2 : ℕ) : ℝ) ((y₀ + 1 : ℕ) : ℝ)) : False := by
  have hUy := hUc y₀ hJ le_rfl
  rcases Tplus_core S hJ hS1 hUy hU01 with hK1 | hE1
  · exact K_at_origin S c₀ (y₀ + 1) (fun _ => h2) hU0 hK1 1 le_rfl (y₀ + 2) (y₀ + 1) le_rfl (by omega) (by omega)
      (by omega) hK2 hK3
  · refine hIH c₀ J hA (y₀ + 2) (y₀ + 1) (by omega) (by omega) (by omega) (by omega) ⟨?_, hK2, hK3⟩
    intro y hy1 hy2
    rcases Nat.lt_or_ge y (y₀ + 1) with hlt | hge
    · exact hS1 y hy1 (by omega)
    · have hye : y = y₀ + 1 := by omega
      subst hye
      rw [Nat.cast_add, Nat.cast_one]
      exact hE1

end rl26

#print axioms row_right_clamp_Nq
#print axioms row_up_q
#print axioms kor_one

end Erdos634.Draft.WGapStmt
