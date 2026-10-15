import Erdos634.Draft.GammaTrapWitness44
import Erdos634.TileAt
import Erdos634.BaseDecomposition

/-!
# The base-β wrappers instantiated on the 44-tiling

The target of `Tiling44Bridge` is the base-β member `(e,f) = (1,2)` at `m = 2` (tile `(2,3,4)`
scaled by 8, target sides `176,128,128`).  Here the hypothesis bundle of each base-β wrapper is
discharged on `D44 := Tiling44Bridge.dissection.relabelModel τ` and conclusions are extracted:

* `TilePlacement.corner_multiplicities` / `base_corner_counts` / `apex_counts` (through the
  `TileAt.congruentDissection_*` wrappers, which build `hvals` themselves);
* `TileAt.congruentDissection_{localAngle_mem, hcorners, base_corner_tile_unique,
  base_corner_tile_vertex, endpoints}`;
* `BaseWalkGeneral.base_walk_pos_general` (leg `k = 1`), hence `side_walk_pos2_of_dissection`.

The vertex labelling `hα' hβ' hγ'` is `D44_hα D44_hβ D44_hγ` (`relabelModel τ`); `hcorner` of a
base corner is `tgt_hb0`/`tgt_hb1`, the apex one is `D44_hcorner`.

**The `ℤ`/`ℕ`-typed wrappers cannot be satisfied** (`base_walk_pos_int`, `base_decomposition_*`,
`SideWalk.int_walk_of_dissection`): they fix `hC : sideOpp model 2 = f0*f0` (model scale 1).
`D44`'s `sideOpp model 2 = 32` is not a perfect square (`no_nat_scale`, `no_int_scale`), and its
target sides are `16 = m·8` times the `m=1` ones.  So these are satisfiable only by a genuine
`N = 3f² - e²` dissection, whose existence this file does not decide; `D44` is the `m = 2` member.

This file is a satisfiability and scope check for the wrappers.  No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BBWWitness44

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.Z15Real Erdos634.Tiling44Bridge
  Erdos634.BaseBetaTargetCoord Erdos634.SideWall Erdos634.TilePlacement
open Erdos634.Draft.ApexWitness44 Erdos634.Draft.GammaTrapWitness44

/-- The ten `≠` facts the wrappers take, for `(α, β, γ = 2α+β)` of the `(1,2)` member. -/
theorem ne_facts :
    modelAlpha 1 ((2 : ℕ) : ℝ) ≠ modelBeta 1 ((2 : ℕ) : ℝ) ∧
    modelAlpha 1 ((2 : ℕ) : ℝ) ≠ 2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ) ∧
    modelAlpha 1 ((2 : ℕ) : ℝ) ≠ Real.pi ∧ modelAlpha 1 ((2 : ℕ) : ℝ) ≠ 0 ∧
    modelBeta 1 ((2 : ℕ) : ℝ) ≠ 2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ) ∧
    modelBeta 1 ((2 : ℕ) : ℝ) ≠ Real.pi ∧ modelBeta 1 ((2 : ℕ) : ℝ) ≠ 0 ∧
    2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ) ≠ Real.pi ∧
    2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ) ≠ 0 := by
  have hA := angle_bundle
  have h1 := hA.hα
  have h2 := hA.hβ
  have h4 := hA.hrel
  have h5 := Real.pi_pos
  refine ⟨hA.hαβ, ?_, ?_, h1.ne', ?_, ?_, h2.ne', ?_, ?_⟩ <;> intro h <;> linarith

/-- `hvals` at every target vertex: derived, not assumed. -/
theorem D44_localAngle_mem (k : Fin 3) (i : Fin Tiling44.tiles.length) :
    (D44.tile i).localAngle (D44.target.pts k) ∈
      ({modelAlpha 1 ((2 : ℕ) : ℝ), modelBeta 1 ((2 : ℕ) : ℝ),
        2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ), Real.pi, 0} : Finset ℝ) :=
  congruentDissection_localAngle_mem D44 _ _ _ D44_hα D44_hβ D44_hγ k i

theorem D44_hcorners : ∀ (i : Fin Tiling44.tiles.length) (j : Fin 3),
    cornerAngle ((D44.tile i).pts (j + 1)) ((D44.tile i).pts j) ((D44.tile i).pts (j + 2))
      ∈ ({modelAlpha 1 ((2 : ℕ) : ℝ), modelBeta 1 ((2 : ℕ) : ℝ),
        2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)} : Finset ℝ) :=
  congruentDissection_hcorners D44 _ _ _ D44_hα D44_hβ D44_hγ

/-- `corner_multiplicities` (via its TileAt wrapper) at the base corner `k`, conclusion extracted:
exactly one tile presents `β`, none `α`, `γ`, `π`. -/
theorem D44_base_counts (k : Fin 3)
    (hc : cornerAngle (D44.target.pts (k + 1)) (D44.target.pts k) (D44.target.pts (k + 2))
      = modelBeta 1 ((2 : ℕ) : ℝ)) :
    ({i | (D44.tile i).localAngle (D44.target.pts k) = modelBeta 1 ((2 : ℕ) : ℝ)} :
        Finset (Fin Tiling44.tiles.length)).card = 1 ∧
    ({i | (D44.tile i).localAngle (D44.target.pts k) = modelAlpha 1 ((2 : ℕ) : ℝ)} :
        Finset (Fin Tiling44.tiles.length)).card = 0 := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := ne_facts
  have hA := angle_bundle
  obtain ⟨a, b, -, -⟩ := congruentDissection_base_corner_counts D44 _ _ _ n1 n2 n3 n4 n5 n6 n7 n8
    n9 Real.pi_ne_zero hA.hγdef hA.hrel hA.hirr D44_hα D44_hβ D44_hγ k hc
  exact ⟨b, a⟩

theorem D44_base0_counts :
    ({i | (D44.tile i).localAngle (D44.target.pts 0) = modelBeta 1 ((2 : ℕ) : ℝ)} :
        Finset (Fin Tiling44.tiles.length)).card = 1 ∧
    ({i | (D44.tile i).localAngle (D44.target.pts 0) = modelAlpha 1 ((2 : ℕ) : ℝ)} :
        Finset (Fin Tiling44.tiles.length)).card = 0 := D44_base_counts 0 tgt_hb0
theorem D44_base1_counts :
    ({i | (D44.tile i).localAngle (D44.target.pts 1) = modelBeta 1 ((2 : ℕ) : ℝ)} :
        Finset (Fin Tiling44.tiles.length)).card = 1 ∧
    ({i | (D44.tile i).localAngle (D44.target.pts 1) = modelAlpha 1 ((2 : ℕ) : ℝ)} :
        Finset (Fin Tiling44.tiles.length)).card = 0 := D44_base_counts 1 tgt_hb1

/-- The apex (vertex `2`) fills as exactly three `α`-tiles (`apex_counts`). -/
theorem D44_apex_counts :
    ({i | (D44.tile i).localAngle (D44.target.pts 2) = modelAlpha 1 ((2 : ℕ) : ℝ)} :
        Finset (Fin Tiling44.tiles.length)).card = 3 := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := ne_facts
  have hA := angle_bundle
  exact (congruentDissection_apex_counts D44 _ _ _ n1 n2 n3 n4 n5 n6 n7 n8 n9 Real.pi_ne_zero
    hA.hγdef hA.hrel hA.hirr D44_hα D44_hβ D44_hγ 2 D44_hcorner).1

/-- `corner_multiplicities` itself (raw weighted equation), at vertex `1`. -/
theorem D44_corner_multiplicities_1 :
    (({i | (D44.tile i).localAngle (D44.target.pts 1) = modelAlpha 1 ((2 : ℕ) : ℝ)} :
        Finset (Fin Tiling44.tiles.length)).card : ℝ) * modelAlpha 1 ((2 : ℕ) : ℝ)
    + (({i | (D44.tile i).localAngle (D44.target.pts 1) = modelBeta 1 ((2 : ℕ) : ℝ)} :
        Finset (Fin Tiling44.tiles.length)).card : ℝ) * modelBeta 1 ((2 : ℕ) : ℝ)
    + (({i | (D44.tile i).localAngle (D44.target.pts 1)
          = 2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)} :
        Finset (Fin Tiling44.tiles.length)).card : ℝ)
        * (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ))
    + (({i | (D44.tile i).localAngle (D44.target.pts 1) = Real.pi} :
        Finset (Fin Tiling44.tiles.length)).card : ℝ) * Real.pi
    = cornerAngle (D44.target.pts (1 + 1)) (D44.target.pts 1) (D44.target.pts (1 + 2)) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := ne_facts
  exact corner_multiplicities D44.toDissection _ _ _ n1 n2 n3 n4 n5 n6 n7 n8 n9
    Real.pi_ne_zero 1 (fun i => D44_localAngle_mem 1 i)

/-- The unique tile at the base corner `pts 1`, as a vertex of that tile with angle `β`. -/
theorem D44_corner1_tile :
    ∃ i : Fin Tiling44.tiles.length, ∃ j : Fin 3, D44.target.pts 1 = (D44.tile i).pts j
      ∧ (D44.tile i).localAngle (D44.target.pts 1) = modelBeta 1 ((2 : ℕ) : ℝ)
      ∧ ∀ i', D44.target.pts 1 ∈ (D44.tile i').carrier → i' = i := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := ne_facts
  have hA := angle_bundle
  have hβ2 : modelBeta 1 ((2 : ℕ) : ℝ) ≠ 2 * Real.pi := by
    have := hA.hrel; have := hA.hα; have := hA.hβ; have := Real.pi_pos
    intro h; linarith
  exact congruentDissection_base_corner_tile_vertex D44 _ _ _ n1 n2 n3 n4 n5 n6 n7 hβ2 n8 n9
    Real.pi_ne_zero hA.hγdef hA.hrel hA.hirr D44_hα D44_hβ D44_hγ 1 tgt_hb1

/-- `congruentDissection_endpoints` on the leg `[pts 1, pts 2]`: the wall chain's first tile
presents `β` at `pts 1`, its last presents `α` at the apex. -/
theorem D44_endpoints :
    ∃ E : ℕ → Fin Tiling44.tiles.length × Fin 3, ∃ n : ℕ, 0 < n ∧
      (D44.tile (E 0).1).localAngle (D44.target.pts 1) = modelBeta 1 ((2 : ℕ) : ℝ) ∧
      (D44.tile (E (n - 1)).1).localAngle (D44.target.pts 2) = modelAlpha 1 ((2 : ℕ) : ℝ) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := ne_facts
  have hA := angle_bundle
  have hne : (1 : Fin 3) ≠ 2 := by decide
  obtain ⟨E, n, -, hn, -, -, -, -, -, h1, h2⟩ :=
    congruentDissection_endpoints hN44 D44 _ _ _ n1 n2 n3 n4 n5 n6 n7 n8 n9 Real.pi_ne_zero
      hA.hγdef hA.hrel hA.hirr D44_hα D44_hβ D44_hγ 1 2 (wallFun D44.target 1) 0
      (dirFun D44.target 1).linear (hker_wallFun D44.target 1)
      (fun y hy => wallFun_le D44.target 1 hy)
      (Erdos634.TilePlacement.pts_ne D44.target hne) (dirFun_mono D44.target 1)
      (edge_subset_frontier D44.target 1) (fun y hy => wallFun_eq_zero D44.target 1 hy)
      (hface_wallFun D44.target 1)
      (hthird_general D44.toDissection (wallFun D44.target 1) 0
        (wallFun_linear_ne_zero D44.target 1)
        (fun y hy => by simpa using wallFun_le D44.target 1 hy))
      tgt_hb1 D44_hcorner
  exact ⟨E, n, hn, h1, h2⟩

/-- `base_walk_pos_general` on the real 44-tiling, leg `k = 1` (all hypotheses discharged), and
the conclusion read in the model's real scale: `16·Pc + 24·Qc + 32·Rc = 128`, `Rc ≥ 1`. -/
theorem D44_base_walk_pos :
    ∃ Pc Qc Rc : ℕ, 1 ≤ Rc ∧ 2 * Pc + 3 * Qc + 4 * Rc = 16 := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := ne_facts
  have hA := angle_bundle
  obtain ⟨Pc, Qc, Rc, hR, heq⟩ := base_walk_pos_general hN44 D44 _ _ _
    n1 n2 n3 n4 n5 n6 n7 n8 n9 Real.pi_ne_zero hA.hγdef hA.hrel hA.hirr D44_scalene
    D44_hα D44_hβ D44_hγ 1 (dirFun_mono D44.target 1) tgt_hb1 D44_hcorner
  refine ⟨Pc, Qc, Rc, hR, ?_⟩
  have h128 : dist (D44.target.pts 1) (D44.target.pts (1 + 1)) = 128 := tgt_d12
  rw [h128, model_s0, model_s1, model_s2] at heq
  have : ((2 * Pc + 3 * Qc + 4 * Rc : ℕ) : ℝ) = ((16 : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

/-! ## The `ℕ`/`ℤ`-typed wrappers: the failing hypothesis, proved -/

/-- `hC : sideOpp model 2 = f0*f0` (m = 1 model scale) is FALSE for `D44` for every `f0 : ℕ`:
`32` is not a perfect square. -/
theorem no_nat_scale : ¬ ∃ f0 : ℕ, sideOpp D44.model 2 = ((f0 * f0 : ℕ) : ℝ) := by
  rintro ⟨f0, h⟩
  rw [model_s2] at h
  have h' : (32 : ℕ) = f0 * f0 := by exact_mod_cast h
  have : f0 ≤ 6 := by nlinarith
  interval_cases f0 <;> omega

theorem no_int_scale : ¬ ∃ f0 : ℤ, sideOpp D44.model 2 = ((f0 ^ 2 : ℤ) : ℝ) := by
  rintro ⟨f0, h⟩
  rw [model_s2] at h
  have h' : (32 : ℤ) = f0 ^ 2 := by exact_mod_cast h
  have h1 : f0 ≤ 6 := by nlinarith
  have h2 : -6 ≤ f0 := by nlinarith
  interval_cases f0 <;> omega

/-- So `base_walk_pos_int`, `base_decomposition_general`, `base_decomposition_2e` and
`int_walk_of_dissection` have unsatisfiable `hC` at `D44` (any `e0`, `f0`, `k`). -/
theorem int_wrappers_hC_false (f0 : ℕ) :
    ¬ (sideOpp D44.model 2 = ((f0 * f0 : ℕ) : ℝ)) := fun h => no_nat_scale ⟨f0, h⟩

/-- What `D44` does satisfy: the model is the `(e,f) = (1,2)` triple `(2,3,4)` scaled by `8`,
and the base (`k = 0`) is `176 = 16·11 = 16·e(3f²-e²)`: model scale 8, target scale `16 = m·8`. -/
theorem D44_scales :
    sideOpp D44.model 0 = 8 * ((1 * 2 : ℕ) : ℝ) ∧
    sideOpp D44.model 1 = 8 * ((2 * 2 - 1 * 1 : ℕ) : ℝ) ∧
    sideOpp D44.model 2 = 8 * ((2 * 2 : ℕ) : ℝ) ∧
    dist (D44.target.pts 0) (D44.target.pts (0 + 1)) = 16 * ((1 * (3 * (2 * 2) - 1 * 1) : ℕ) : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [model_s0]; norm_num
  · rw [model_s1]; norm_num
  · rw [model_s2]; norm_num
  · have : dist (D44.target.pts 0) (D44.target.pts (0 + 1)) = 176 := tgt_d01
    rw [this]; norm_num

#print axioms D44_base_counts
#print axioms D44_base0_counts
#print axioms D44_base1_counts
#print axioms D44_apex_counts
#print axioms D44_corner_multiplicities_1
#print axioms D44_corner1_tile
#print axioms D44_endpoints
#print axioms D44_base_walk_pos
#print axioms no_nat_scale
#print axioms no_int_scale
#print axioms D44_scales

end Erdos634.Draft.BBWWitness44
