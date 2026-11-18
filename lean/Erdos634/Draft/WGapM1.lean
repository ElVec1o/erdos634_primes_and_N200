/-
Draft/WGapM1.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P2.7, size 1).
Not imported by any aggregate.  Lemma M, SIZE 1 (`M_size1`): the mirror tile `T = μ U(0,y₀)`, the row tiles and (K3) are contradictory.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapKN
import Erdos634.Draft.WGapTop
import Erdos634.Draft.SideRunGChordB

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


section m1

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- `GS` on the mirror lattice -/
theorem GSG_mpG {x : ℝ} (hE : 0 < (e : ℝ)) (hEF : (e : ℝ) < f) (ξ η : ℝ) :
    GSG (e : ℝ) (f : ℝ) 1 (mpG (e : ℝ) f 1 x ξ η) = -lvG (e : ℝ) (f : ℝ) 1 x (-ξ + (η + sMir (e : ℝ) f * ξ)) := by
  rw [mpG_eq hE hEF, GSG_lp (by norm_num)]

/-- **Lemma M, size 1** (PROOF 2.7, "Size 1"): `s = y₀ + 1`; (M1) the mirror tile `T = μ U(0,y₀)`, the rows `U(s−1−j', j')`, `j' ≤ y₀`, and (K3) cannot hold together.
First form of (K3): `T` has interior points beyond `m_s`; second form: the tile `ψ` of the `m`-chord principle (`psiG`) and `T` overlap. -/
theorem M_size1 (S : SetupG D e f α β γ L ax ay) {x : ℝ} {y₀ : ℕ} (hyf : y₀ + 1 < f)
    (hT : UTM D (e : ℝ) (f : ℝ) 1 x 0 (y₀ : ℝ))
    (hU : ∀ j' : ℕ, j' ≤ y₀ → UTG D (e : ℝ) (f : ℝ) 1 x (((y₀ + 1 : ℕ) : ℝ) - 1 - j') j')
    (hK3 : K3G D (e : ℝ) (f : ℝ) 1 x ((y₀ + 1 : ℕ) : ℝ) (y₀ : ℝ)) : False := by
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hs2 := sMir_gt_two he0 hef
  have hκ : 0 < (f : ℝ) ^ 2 * hhG (e : ℝ) f := mul_pos S.c_pos (hhG_pos he0 hef)
  obtain ⟨tT, hTv⟩ := hT
  rw [zero_add] at hTv
  set X := mpG (e : ℝ) f 1 x 0 ((y₀ : ℝ) + 1) with hX
  have hTx : HasV D tT X (mpG (e : ℝ) f 1 x 0 (y₀ : ℝ)) (mpG (e : ℝ) f 1 x 1 (y₀ : ℝ)) := hTv.rot.rot
  have hGX : GSG (e : ℝ) (f : ℝ) 1 X = -lvG (e : ℝ) (f : ℝ) 1 x (((y₀ + 1 : ℕ) : ℝ)) := by
    rw [hX, GSG_mpG he0 hef]; push_cast; congr 1; ring
  -- the push direction `w` into the interior of `T`, pointing into `ρ_s`
  set θ1 : ℝ := (sMir (e : ℝ) f - 2) / 2 with hθ1
  have hθ10 : 0 < θ1 := by rw [hθ1]; linarith
  obtain ⟨ε₁, hε₁, hpT⟩ := hasV_push hTx hθ10 one_pos
  set w : Plane := θ1 • (mpG (e : ℝ) f 1 x 0 (y₀ : ℝ) - X) + (1 : ℝ) • (mpG (e : ℝ) f 1 x 1 (y₀ : ℝ) - X) with hw
  have hGw : GSG (e : ℝ) (f : ℝ) 1 w < 0 := by
    have hG0 := GSG_mpG (x := x) he0 hef 0 (y₀ : ℝ)
    have hG1 := GSG_mpG (x := x) he0 hef 1 (y₀ : ℝ)
    rw [hw, map_add, map_smul, map_smul, map_sub, map_sub, hG0, hG1, hGX]
    unfold lvG
    push_cast
    simp only [smul_eq_mul]
    have : ((f : ℝ) ^ 2 * hhG (e : ℝ) f) * (sMir (e : ℝ) f - 2) > 0 := mul_pos hκ (by linarith)
    rw [hθ1]
    nlinarith
  rcases hK3 with hout | ⟨ψw, k, m, η₁, η₂, hkm, h1, h2, hk, hm, hlen, hle, hcl⟩
  · -- first form: `Δ` lies on one side of `m_s`
    have hmem := hpT (ε₁ / 2) (by positivity) (by linarith)
    have hin := Erdos634.BaseSelection.tile_subset_target D.toDissection tT (interior_subset hmem)
    have h3 := hout _ hin
    rw [map_add, map_smul, hGX] at h3
    simp only [smul_eq_mul] at h3
    have : GSG (e : ℝ) (f : ℝ) 1 (θ1 • (mpG (e : ℝ) f 1 x 0 (y₀ : ℝ) - X) + (1 : ℝ) • (mpG (e : ℝ) f 1 x 1 (y₀ : ℝ) - X)) < 0 := hGw
    nlinarith [mul_pos (by positivity : (0 : ℝ) < ε₁ / 2) (neg_pos.mpr this)]
  · -- second form: the tile `ψ` of the `m`-chord principle
    have hJ : ((y₀ + 1 : ℕ) : ℝ) - ((y₀ + 1 : ℕ) : ℝ) = 0 := by ring
    obtain ⟨ψ, hψX, hψang, hψpush⟩ := C.psiG (J := y₀ + 1) (s := ((y₀ + 1 : ℕ) : ℝ)) hkm (lt_of_le_of_lt (by exact_mod_cast h1) (Nat.lt_succ_self y₀)) h2
      hk hm hlen hle hcl hyf (fun j' hj1 hj2 => hU j' (by omega))
    rw [hJ] at hψpush hψang hψX
    have hXψ : lpG (e : ℝ) f 1 x (0 : ℝ) ((y₀ + 1 : ℕ) : ℝ) = X := by
      rw [hX, mp_zero_eta]; push_cast; rfl
    obtain ⟨ε₂, hε₂, hψp⟩ := hψpush w hGw
    rw [hXψ] at hψp hψang hψX
    have hεpos : 0 < min ε₁ ε₂ / 2 := by have := lt_min hε₁ hε₂; positivity
    have hεlt1 : min ε₁ ε₂ / 2 < ε₁ := by have := min_le_left ε₁ ε₂; linarith [lt_min hε₁ hε₂]
    have hεlt2 : min ε₁ ε₂ / 2 < ε₂ := by have := min_le_right ε₁ ε₂; linarith [lt_min hε₁ hε₂]
    have h1' : X + (min ε₁ ε₂ / 2) • w ∈ interior (D.tile tT).carrier := hpT _ hεpos hεlt1
    have h2' : X + (min ε₁ ε₂ / 2) • w ∈ interior (D.tile ψ).carrier := hψp _ hεpos hεlt2
    have hψT : ψ = tT := by
      by_contra hne
      exact (Set.disjoint_left.mp (D.interiors_disjoint hne) h2') h1'
    subst hψT
    obtain ⟨k0, -, -, -, -, -, hk0, -, -⟩ := hTx
    rw [← hk0, Tri.localAngle_vertex] at hψang
    have hlt := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi (D.tile ψ) k0
    rw [hψang] at hlt
    exact lt_irrefl _ hlt

end m1

#print axioms M_size1

end Erdos634.Draft.WGapStmt
