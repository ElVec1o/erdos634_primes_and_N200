/-
Draft/WGapStSide.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.3).
Not imported by any aggregate.  STATION port of `WGapSide` (lattice origin `x`, absolute levels, floor `J0`); see WGapStInv1.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapSide3c
import Erdos634.Draft.WGapStCase1

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapSt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set Erdos634.Draft.WGapStmt

variable {N : ℕ} {D : CongruentDissection N}


open Erdos634.Draft.WGapStmt hiding sj BotClamp Inv Unfl Flip utm_cast nearOK_inv level_known inv_hint_wall level_data ha_succ hDp_succ unfl_utm inv_step top_pt top_clamp hthird_of_inv ub ClampB FlipAt Bst bst_self ub_norm ub_ne clampB_outside clampB_tile

section stside

variable {e f : ℕ} {α β γ L ax ay : ℝ} {x : ℝ} {J0 : ℕ}

/-- **[SIDE-1] at a station**: the bottom clamp of the chord that ends on the wall row (`c + J0 = j`), from the wall tile at `q'(c+1, J0)` -/
theorem side1_supplier (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ J0 + (f - 1)) (hW : WallOK D e f x J0)
    {j c : ℕ} (hjJ : j < J) (hc : c + J0 = j)
    (hUall : ∀ t : ℕ, t ≤ c → UTM D (e : ℝ) f 1 x (t : ℝ) (J0 : ℝ)) :
    BotClamp D e f x (j + 1) (c + 1) := by
  intro ed _
  have he0 := S.e0
  have hef := S.hef'
  have hκ := kapG_pos he0 hef
  obtain ⟨φ, -, -, hpush⟩ := hW (c + 1) (by omega) (by omega) (fun t ht => by
    have := hUall t (by omega); exact this)
  have hcr : 0 < cross (mpG (e : ℝ) f 1 x 1 (J0 : ℝ) - mpG (e : ℝ) f 1 x 0 (J0 : ℝ)) (sj e f x (j + 1)) := by
    unfold sj
    rw [cross_mpG he0 hef]
    have e1 : ((1 : ℝ) - 0) * ((((j + 1 : ℕ) : ℝ) - 1) - ((j + 1 : ℕ) : ℝ)) - ((J0 : ℝ) - (J0 : ℝ)) * ((1 : ℝ) - 0) = -1 := by ring
    rw [e1]; linarith
  obtain ⟨ε₀, hε₀, hp⟩ := hpush _ hcr
  have hP : mpG (e : ℝ) f 1 x 0 ((j + 1 : ℕ) : ℝ) + ((c + 1 : ℕ) : ℝ) • sj e f x (j + 1) =
      mpG (e : ℝ) f 1 x ((c + 1 : ℕ) : ℝ) (J0 : ℝ) := by
    unfold sj
    refine (step_pt he0 hef x ((j + 1 : ℕ) : ℝ) ((c + 1 : ℕ) : ℝ)).trans (mpG_congr' rfl ?_)
    have : ((c : ℝ) + J0 = j) := by exact_mod_cast hc
    push_cast; linarith
  refine not_straddles_short D.toDissection (j := φ) hε₀ (ρ := ((c + 1 : ℕ) : ℝ)) (by positivity) ?_ ?_ ed.1 ed.2
  · ext i; simp; ring
  · intro ε h0 h1
    have h := hp ε h0 h1
    have e2 : mpG (e : ℝ) f 1 x 0 ((j + 1 : ℕ) : ℝ) + ((c + 1 : ℕ) : ℝ) • sj e f x (j + 1) +
        ε • (mpG (e : ℝ) f 1 x 0 ((j + 1 : ℕ) : ℝ) + (((c + 1 : ℕ) : ℝ) + 1) • sj e f x (j + 1) -
          (mpG (e : ℝ) f 1 x 0 ((j + 1 : ℕ) : ℝ) + ((c + 1 : ℕ) : ℝ) • sj e f x (j + 1))) =
        mpG (e : ℝ) f 1 x ((c + 1 : ℕ) : ℝ) (J0 : ℝ) + ε • sj e f x (j + 1) := by
      have e3 : mpG (e : ℝ) f 1 x 0 ((j + 1 : ℕ) : ℝ) + (((c + 1 : ℕ) : ℝ) + 1) • sj e f x (j + 1) -
          (mpG (e : ℝ) f 1 x 0 ((j + 1 : ℕ) : ℝ) + ((c + 1 : ℕ) : ℝ) • sj e f x (j + 1)) = sj e f x (j + 1) := by
        ext i; simp; ring
      rw [e3, hP]
    rw [e2]; exact h

/-- the wall tile lies in the closed half-plane `0 ≤ cross d (y - X)` -/
theorem edgeCover_halfplane {X d : Plane} (φ : Fin N) (hang : (D.tile φ).localAngle X = Real.pi)
    (hpush : ∀ w : Plane, 0 < cross d w → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
      X + ε' • w ∈ interior (D.tile φ).carrier) :
    ∀ y ∈ (D.tile φ).carrier, 0 ≤ cross d (y - X) := by
  intro y hy
  by_contra hneg
  push_neg at hneg
  have hw : 0 < cross d (X - y) := by
    have : cross d (X - y) = -cross d (y - X) := by simp [cross]; ring
    linarith
  obtain ⟨ε₀, hε₀, hp⟩ := hpush _ hw
  have hε : 0 < ε₀ / 2 := by positivity
  have hz := hp (ε₀ / 2) hε (by linarith)
  have hXint : X ∈ interior (D.tile φ).carrier := by
    have h := (D.tile φ).convex.combo_interior_self_mem_interior hz hy
      (a := 1 / (1 + ε₀ / 2)) (b := (ε₀ / 2) / (1 + ε₀ / 2)) (by positivity) (by positivity) (by field_simp)
    convert h using 1
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp; ring
  have h2 := Tri.localAngle_interior _ hXint
  rw [hang] at h2
  linarith [Real.pi_pos]

/-- **the clamp from the angle count at a point with a wall tile**: like `no_straddle_left`, with the wall tile `Wt` (angle `π`, lying in the closed
half-plane `0 ≤ cross d (· - X)`) counted separately; `K` (angles `< π`) and `Wt` carry `Ω - θ` -/
theorem no_straddle_wall (D : Dissection N) {X Y P' d : Plane} (hXY : X ≠ Y)
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    {Ω θ : ℝ} (hΩ : ∑ i, (D.tile i).localAngle X = Ω) (K : Finset (Fin N)) (Wt : Fin N) (hWK : Wt ∉ K)
    (hWang : (D.tile Wt).localAngle X = Real.pi)
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - Real.pi - θ) (hθ : θ < Real.pi)
    (hKlt : ∀ k ∈ K, (D.tile k).localAngle X < Real.pi)
    (hWh : ∀ y ∈ (D.tile Wt).carrier, 0 ≤ cross d (y - X)) (hdu : cross d (Y - X) < 0) :
    ∀ ed ∈ D.lineChain (crossL (X - Y)) (cross (X - Y) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y := by
  intro ed hed hs
  have hu : X - Y ≠ 0 := sub_ne_zero.mpr hXY
  have hF := Erdos634.Geometry.crossL_ne_zero hu
  have hcr : ∀ v : Plane, cross (X - Y) v = -cross (Y - X) v := by
    intro v; simp [cross]; ring
  have hcl : ∀ v : Plane, crossL (X - Y) v = -cross (Y - X) v := by
    intro v; rw [crossL_apply, hcr]
  have hfX : crossL (X - Y) X = cross (X - Y) X := crossL_apply _ _
  have hfY : crossL (X - Y) Y = cross (X - Y) X := by
    rw [hcl, hcr]
    have : cross (Y - X) Y = cross (Y - X) (Y - X) + cross (Y - X) X := by
      rw [← cross_add_right]; congr 1; abel
    rw [this]; simp [cross]; ring
  have hfP' : crossL (X - Y) P' = cross (X - Y) X := by
    rw [hcl, hcr]
    have : cross (Y - X) P' = cross (Y - X) (P' - X) + cross (Y - X) X := by
      rw [← cross_add_right]; congr 1; abel
    rw [this, hP']; ring
  obtain ⟨-, hang, hpush⟩ := straddle_data D (crossL (X - Y)) hF (cross (X - Y) X) hXY hfX hfY hfP' hXP hed hs
  have hnotK : ed.1 ∉ K := fun hm => absurd (hKlt _ hm) (by rw [hang]; exact lt_irrefl _)
  have hnotW : ed.1 ≠ Wt := by
    intro hW
    have hv : crossL (X - Y) ((Y - X) + d) < 0 := by
      rw [hcl]
      have h2 : cross (Y - X) d = -cross d (Y - X) := by simp [cross]; ring
      have h3 : cross (Y - X) ((Y - X) + d) = cross (Y - X) d := by simp [cross]; ring
      rw [h3, h2]; linarith
    obtain ⟨ε₀, hε₀, hp⟩ := hpush _ hv
    have hmem := hp (ε₀ / 2) (by positivity) (by linarith)
    have hmem' : X + (ε₀ / 2) • ((Y - X) + d) ∈ (D.tile Wt).carrier := by
      rw [← hW]; exact interior_subset hmem
    have h0 := hWh _ hmem'
    have h4 : cross d (X + (ε₀ / 2) • ((Y - X) + d) - X) = (ε₀ / 2) * cross d (Y - X) := by
      simp [cross]; ring
    rw [h4] at h0
    nlinarith
  have hnot : ed.1 ∉ insert Wt K := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hnotW, hnotK⟩
  have hsd := Finset.sum_sdiff (Finset.subset_univ (insert Wt K)) (f := fun i => (D.tile i).localAngle X)
  have hle : (D.tile ed.1).localAngle X ≤ ∑ i ∈ Finset.univ \ insert Wt K, (D.tile i).localAngle X :=
    Finset.single_le_sum (f := fun i => (D.tile i).localAngle X) (fun j _ => Tri.localAngle_nonneg _ _)
      (by simp [hnot])
  rw [hang] at hle
  have h1 : ∑ i, (D.tile i).localAngle X = Ω := hΩ
  have h2 : ∑ i ∈ insert Wt K, (D.tile i).localAngle X = Ω - θ := by
    rw [Finset.sum_insert hWK, hWang, hK]; ring
  simp only at hsd
  linarith

end stside

end Erdos634.Draft.WGapSt
