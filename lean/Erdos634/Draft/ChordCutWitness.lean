/-
Draft/ChordCutWitness.lean  In `AllThreshold`.

Non-vacuity of `Draft.ChordCut` (`straddlers_eq_empty_of_wall`, `restrict_above`): the median wall of
`EdgeWordConversion.wallCongruentDissection`, the right isosceles triangle `(0,0), (2,0), (0,2)` cut by the median to
`(1,1)` into the two congruent tiles `wallTileA = (0,0),(1,1),(2,0)` and `wallTileB = (0,0),(0,2),(1,1)`; the wall is the
segment `[wallU, wallV] = [(0,0), (1,1)]` on the line `{wallF = 0}`, `wallF v = v₀ − v₁`.

    wall_hline               -- every point of the target on the line `{wallF = 0}` lies on `[wallU, wallV]` (new here)
    wall_straddlers_empty    -- `straddlers wallCongruentDissection wallF 0 = ∅`, from `ChordCut.straddlers_eq_empty_of_wall`
                             --   with `TPErdos.wall_hwall` (existing) and `wall_hline`
    wallA_carrier            -- `wallTileA.carrier = target ∩ {0 ≤ wallF}`
    restrict_above_witness   -- `ChordCut.restrict_above` applied: a congruent dissection of `wallTileA` with the model of
                             --   `wallCongruentDissection`

So the hypotheses of the three lemmas of `ChordCut` are satisfied by a real dissection with a tile on each side.
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.ChordCut
import Erdos634.EdgeWordConversion

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.TPErdos Erdos634.ChordTraceReal Erdos634.Draft.ChordCut
  Erdos634.EdgeWordConversion

namespace Erdos634.Draft.ChordCutWitness

/-- `v ↦ v₀ + v₁` -/
noncomputable def witSum : Plane →ₗ[ℝ] ℝ where
  toFun v := v 0 + v 1
  map_add' := by intro a b; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- `v ↦ −v₀` -/
noncomputable def witNegX : Plane →ₗ[ℝ] ℝ where
  toFun v := -v 0
  map_add' := by intro a b; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem witSum_apply (v : Plane) : witSum v = v 0 + v 1 := rfl
@[simp] theorem witNegX_apply (v : Plane) : witNegX v = -v 0 := rfl

/-- every point of the target on the median line lies on the segment `[(0,0), (1,1)]` -/
theorem wall_hline : ∀ y ∈ wallTarget.carrier, wallF y = 0 → y ∈ segment ℝ wallU wallV := by
  intro y hy hF
  rw [wallF_apply] at hF
  have h1 : witNegX y ≤ 0 := wallTarget.carrier_subset_halfplane witNegX 0 (by
    intro i
    fin_cases i <;> simp [wallTarget] <;> norm_num) y hy
  have h2 : witSum y ≤ 2 := wallTarget.carrier_subset_halfplane witSum 2 (by
    intro i
    fin_cases i <;> simp [wallTarget] <;> norm_num) y hy
  rw [witNegX_apply] at h1
  rw [witSum_apply] at h2
  rw [segment_eq_image_lineMap]
  refine ⟨y 0, ⟨by linarith, by linarith⟩, ?_⟩
  refine PiLp.ext (fun i => ?_)
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> simp [wallU, wallV, AffineMap.lineMap_apply_module] <;> linarith

/-- **No tile crosses the median line** (from the wall) -/
theorem wall_straddlers_empty : straddlers wallCongruentDissection.toDissection wallF 0 = ∅ :=
  straddlers_eq_empty_of_wall _ wallF 0 (P := wallU) (Q := wallV) wall_hline wall_hwall

/-- the tile `wallTileA` is the part of the target on the side `{0 ≤ wallF}` -/
theorem wallA_carrier :
    wallTileA.carrier = wallCongruentDissection.target.carrier ∩ {y | 0 ≤ wallF y} := by
  ext y
  constructor
  · intro hy
    refine ⟨wallTiles_subset 0 hy, ?_⟩
    exact (ChordTraceReal.Tri.ge_iff_forall_vertices_ge wallTileA wallF 0).mpr (by
      intro i
      fin_cases i <;> simp [wallTileA] <;> norm_num) y hy
  · rintro ⟨hy, hF⟩
    have hy' : y ∈ ⋃ i, (wallDissection.tile i).carrier := by
      rw [wallDissection.covers]
      exact hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy'
    fin_cases i
    · exact hi
    · have hB : ∀ z ∈ wallTileB.carrier, wallF z ≤ 0 :=
        wallTileB.carrier_subset_halfplane wallF 0 (by
          intro k
          fin_cases k <;> simp [wallTileB] <;> norm_num)
      have hF0 : wallF y = 0 := le_antisymm (hB y hi) hF
      have hseg := wall_hline y hy hF0
      have hU : wallU ∈ wallTileA.carrier := subset_convexHull ℝ _ ⟨0, rfl⟩
      have hV : wallV ∈ wallTileA.carrier := subset_convexHull ℝ _ ⟨1, rfl⟩
      exact wallTileA.convex.segment_subset hU hV hseg

/-- **`ChordCut.restrict_above` applied**: the tiles of the median dissection on the side `{0 ≤ wallF}` form a congruent
dissection of `wallTileA` with the same model. -/
theorem restrict_above_witness :
    ∃ (N' : ℕ) (D' : CongruentDissection N'), D'.target = wallTileA ∧
      D'.model = wallCongruentDissection.model :=
  restrict_above wallCongruentDissection wallF wallF_ne 0 wall_straddlers_empty wallTileA wallA_carrier

end Erdos634.Draft.ChordCutWitness

#print axioms Erdos634.Draft.ChordCutWitness.wall_hline
#print axioms Erdos634.Draft.ChordCutWitness.wall_straddlers_empty
#print axioms Erdos634.Draft.ChordCutWitness.wallA_carrier
#print axioms Erdos634.Draft.ChordCutWitness.restrict_above_witness
