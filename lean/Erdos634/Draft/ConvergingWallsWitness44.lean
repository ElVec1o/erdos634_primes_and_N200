-- Draft/ConvergingWallsWitness44.lean — non-vacuity witnesses for the frame-free helpers introduced with
-- CW, P2, S4 (Draft/ConvergingWallsLocal.lean, ConvergingWallsReal.lean, PatchCompleteReal.lean):
-- `wall_lattice` and `start_gen` have all hypotheses discharged on the first tile of the real
-- kernel-checked N = 44 tiling (`ApexWitness44.D44`, m = 2); `mirror_ident` (a plane lemma, no
-- dissection in it) on the four points (0,1), (−1,0), (1,0), (0,−1).
-- Not witnessable: every frame-bound statement — `CWH`, `P2H`, `CWInv`, `P2Inv`,
-- `PiK`, and every lemma taking an `HFrame` (`band_str`, `r_str`, `slot2`, `far_word`, `junction`,
-- `ad_march`, `chain_alpha`, `no_two_straight(_b)`, `cw_frame`, `p2_frame`, `s4_frame`, `r9_frame`,
-- `s5_frame`, `lc_phase`) — needs an `m = 1` member with `2 ≤ e ≤ f − 2`; `D44` is `e = 1, f = 2,
-- m = 2`, so no `HFrame` exists on it, and the `m = 1` frame hypotheses cannot be jointly witnessed
-- (their non-existence is Theorem H's goal).  At N = 44 the CW/P2 hypotheses never arise (no b-seed on
-- any ℓ_j, no L_b), and S4 fails first at level 2, row 2 (far side one `c`,
-- `2a = c`).  `card_three` (a finset count) is not witnessed on D44 (it would need a D44 point with
-- three equal local angles).  Imported directly by `All`.
import Erdos634.Draft.PatchCompleteReal
import Erdos634.Draft.ApexWitness44

namespace Erdos634.Draft.ConvergingWallsWitness44

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.RowWallReal Erdos634.Draft.ApexWitness44
open Erdos634.Draft.HalfTurnR3R4Glue (IsMirror)

/-- The first tile of the real 44-tiling. -/
noncomputable def T0 : Tri := D44.tile ⟨0, by decide⟩

theorem T0_ne01 : T0.pts 0 ≠ T0.pts 1 := pts_ne T0 (by decide)

/-- `wall_lattice` on the real tile: the open edge `(p₀, p₁)` of `T0` (one lattice step, `q = 1`,
`L = |p₀p₁|`) meets no tile interior. -/
theorem w_wall_lattice :
    ∀ x ∈ Set.Ioo 0 (((1 : ℕ) : ℝ) * dist (T0.pts 0) (T0.pts 1)), ∀ i,
      T0.pts 0 + x • ((1 / dist (T0.pts 0) (T0.pts 1)) • (T0.pts 1 - T0.pts 0))
        ∉ interior (D44.tile i).carrier := by
  have hL : 0 < dist (T0.pts 0) (T0.pts 1) := dist_pos.mpr T0_ne01
  have hu0 : (1 / dist (T0.pts 0) (T0.pts 1)) • (T0.pts 1 - T0.pts 0) ≠ 0 :=
    smul_ne_zero (one_div_ne_zero hL.ne') (sub_ne_zero.mpr T0_ne01.symm)
  refine wall_lattice (D := D44) hu0 hL 1 (fun k hk => ⟨⟨0, by decide⟩, ?_, ?_⟩)
  · obtain rfl : k = 0 := by omega
    simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero]
    exact ⟨0, rfl⟩
  · obtain rfl : k = 0 := by omega
    have : T0.pts 0 + ((((0 : ℕ) : ℝ) + 1) * dist (T0.pts 0) (T0.pts 1)) •
        ((1 / dist (T0.pts 0) (T0.pts 1)) • (T0.pts 1 - T0.pts 0)) = T0.pts 1 := by
      rw [Nat.cast_zero, zero_add, one_mul, smul_smul, mul_one_div_cancel hL.ne', one_smul]
      abel
    rw [this]; exact ⟨1, rfl⟩

/-- `start_gen` on the real tile: with `g = −κ·cross(p₁ − p₀, ·)` (`κ = cross(p₁ − p₀, p₂ − p₀)`), the
edge `(T0, 0) = [p₀, p₁]` lies in `lineChain g (g p₀)` (the tile is in `{g ≤ g p₀}`), and no edge of that
side has `p₀` in its relative interior. -/
theorem w_start_gen :
    ¬ TraceCovering.Straddled D44.toDissection
      ((-(cross (T0.pts 1 - T0.pts 0) (T0.pts 2 - T0.pts 0))) • crossL (T0.pts 1 - T0.pts 0))
      (((-(cross (T0.pts 1 - T0.pts 0) (T0.pts 2 - T0.pts 0))) • crossL (T0.pts 1 - T0.pts 0))
        (T0.pts 0))
      (T0.pts 0 + (0 : ℝ) • (T0.pts 1 - T0.pts 0)) := by
  set u := T0.pts 1 - T0.pts 0 with hu
  set κ := cross u (T0.pts 2 - T0.pts 0) with hκ
  set g : Plane →ₗ[ℝ] ℝ := (-κ) • crossL u with hg
  have hr : Set.range (D44.tile ⟨0, by decide⟩).pts = {T0.pts 0, T0.pts 1, T0.pts 2} :=
    MarchInduction.range_pts_eq _
  obtain ⟨m, hm, hfl⟩ := flank_of_range hr
  have hκ0 : κ ≠ 0 := by
    have hc := ApexPlacement.flank_cross_ne hm hfl
    simpa [hκ, hu] using hc
  have happ : ∀ y, g y = -κ * cross u y := fun y => by
    simp [hg, crossL_apply]
  have hgu : g u = 0 := by rw [happ, cross_self', mul_zero]
  have hg0 : g ≠ 0 := by
    intro h
    have := happ (T0.pts 2 - T0.pts 0)
    rw [h, LinearMap.zero_apply, ← hκ] at this
    have : κ * κ = 0 := by linarith
    exact hκ0 (mul_self_eq_zero.mp this)
  have hu0 : u ≠ 0 := sub_ne_zero.mpr T0_ne01.symm
  have hp1 : g (T0.pts 1) = g (T0.pts 0) := by
    have : g (T0.pts 1) - g (T0.pts 0) = 0 := by rw [← map_sub, ← hu, hgu]
    linarith
  have hp2 : g (T0.pts 2) ≤ g (T0.pts 0) := by
    have : g (T0.pts 2) - g (T0.pts 0) = -(κ * κ) := by
      rw [← map_sub, happ, ← hκ]; ring
    nlinarith [mul_self_nonneg κ]
  have hε : ((⟨0, by decide⟩ : Fin Tiling44.tiles.length), (0 : Fin 3)) ∈
      D44.toDissection.lineChain g (g (T0.pts 0)) := by
    rw [Dissection.mem_lineChain]
    refine ⟨rfl, hp1, fun k => ?_⟩
    fin_cases k
    · exact le_rfl
    · exact hp1.le
    · exact hp2
  have hedge : (D44.tile ⟨0, by decide⟩).edge 0 =
      segment ℝ (T0.pts 0 + (0 : ℝ) • u) (T0.pts 0 + (1 : ℝ) • u) := by
    rw [zero_smul, add_zero, one_smul, hu, add_sub_cancel, Tri.edge]; rfl
  exact start_gen (D := D44) hg0 (fun y => Iff.rfl) hg0 rfl hgu hu0 hε one_pos hedge

/-- `mirror_ident` on four plane points: `M = (0,−1)` is the mirror of `X = (0,1)` across the line
through `Y = (−1,0)`, `Z = (1,0)`, and the candidate `C = M` is identified. -/
theorem w_mirror_ident :
    (!₂[(0 : ℝ), -1] : Plane) = !₂[(0 : ℝ), -1] := by
  have hYZ : (!₂[(-1 : ℝ), 0] : Plane) ≠ !₂[(1 : ℝ), 0] := by
    intro h; have := congrArg (fun p : Plane => p 0) h; norm_num at this
  have hXC : (!₂[(0 : ℝ), 1] : Plane) ≠ !₂[(0 : ℝ), -1] := by
    intro h; have := congrArg (fun p : Plane => p 1) h; norm_num at this
  have d1 : dist (!₂[(0 : ℝ), -1] : Plane) !₂[(-1 : ℝ), 0] = dist (!₂[(0 : ℝ), 1] : Plane)
      !₂[(-1 : ℝ), 0] := by
    simp [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  have d2 : dist (!₂[(0 : ℝ), -1] : Plane) !₂[(1 : ℝ), 0] = dist (!₂[(0 : ℝ), 1] : Plane)
      !₂[(1 : ℝ), 0] := by
    simp [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  have hM : IsMirror (!₂[(0 : ℝ), 1] : Plane) !₂[(-1 : ℝ), 0] !₂[(1 : ℝ), 0] !₂[(0 : ℝ), -1] :=
    ⟨hXC.symm, d1, d2⟩
  exact mirror_ident hYZ hXC hM d1 d2

end Erdos634.Draft.ConvergingWallsWitness44

#print axioms Erdos634.Draft.ConvergingWallsWitness44.w_wall_lattice
#print axioms Erdos634.Draft.ConvergingWallsWitness44.w_start_gen
#print axioms Erdos634.Draft.ConvergingWallsWitness44.w_mirror_ident
