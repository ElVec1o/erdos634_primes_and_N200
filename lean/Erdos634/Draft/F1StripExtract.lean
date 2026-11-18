/-
Draft/F1StripExtract.lean -- cutting a dissection of a triangle along a line (Erdos #634, F1 strip lemma).

If a `CongruentDissection D` of a triangle has every tile on one side of a line `f = c` (tiles of the
family `g` in `f <= c`, all other tiles in `f >= c`), then the tiles of the family `g` tile the cut-off
region `target ∩ {f <= c}`.  The only non-formal point is the covering of the points of the line: such a
point is a limit of points of `target ∩ {f < c}` (convexity), each of which lies in a tile of the family,
and the union of the family is closed.

This is how a SINGLE certificate of `T_3` yields both bases of the strip lemma: the tiles in `{p <= b}`
tile the strip `S_3` and the tiles in `{p >= b}` tile a translate of `T_2`.

UNAUDITED beyond the internal build.  No sorry, no native_decide.
-/
import Erdos634.Draft.F1StripGeom

namespace Erdos634.Draft.F1StripExtract

open Erdos634.Geometry Erdos634.Draft.RegionTiling Erdos634.Draft.F1StripGeom Filter Topology

/-- an affine functional along a segment -/
theorem aff_seg (f : Plane →ᵃ[ℝ] ℝ) (x y : Plane) (t : ℝ) :
    f (x + t • (y - x)) = f x + t * (f y - f x) := by
  have h1 : x + t • (y - x) = t • (y -ᵥ x) +ᵥ x := by
    simp [vadd_eq_add, vsub_eq_sub, add_comm]
  rw [h1, AffineMap.map_vadd, LinearMap.map_smul, AffineMap.linearMap_vsub]
  simp only [vadd_eq_add, vsub_eq_sub, smul_eq_mul]
  ring

/-- **A subfamily of tiles on one side of a line tiles the cut-off region.** -/
theorem family_tiled {N n : ℕ} (D : CongruentDissection N) (g : Fin n → Fin N)
    (hg : Function.Injective g) (f : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (hle : ∀ i, ∀ x ∈ (D.tile (g i)).carrier, f x ≤ c)
    (hge : ∀ j, (∀ i, g i ≠ j) → ∀ x ∈ (D.tile j).carrier, c ≤ f x)
    (hy : ∃ y ∈ D.target.carrier, f y < c) :
    Tiled {x | x ∈ D.target.carrier ∧ f x ≤ c} D.model n := by
  obtain ⟨y, hyT, hyf⟩ := hy
  have hsub : ∀ i, (D.tile (g i)).carrier ⊆ D.target.carrier := by
    intro i x hx
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨g i, hx⟩
  have hclosed : IsClosed (⋃ i, (D.tile (g i)).carrier) :=
    isClosed_iUnion_of_finite (fun i => (D.tile (g i)).isCompact.isClosed)
  refine ⟨{ tile := fun i => D.tile (g i), covers := ?_,
            disj := fun i j hij => D.interiors_disjoint (fun h => hij (hg h)),
            cong := fun i => D.tiles_congruent (g i) }⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨hsub i hi, hle i x hi⟩
  · rintro ⟨hxT, hxf⟩
    -- every point of the open segment from `x` towards `y` lies in the union
    have hseg : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → x + t • (y - x) ∈ ⋃ i, (D.tile (g i)).carrier := by
      intro t ht
      have hmem : x + t • (y - x) ∈ D.target.carrier :=
        D.target.convex.add_smul_sub_mem hxT hyT ⟨ht.1.le, ht.2⟩
      have hfv : f (x + t • (y - x)) < c := by
        rw [aff_seg]
        nlinarith [ht.1, ht.2]
      rw [← D.covers] at hmem
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
      by_cases hjg : ∃ i, g i = j
      · obtain ⟨i, rfl⟩ := hjg
        exact Set.mem_iUnion.mpr ⟨i, hj⟩
      · push_neg at hjg
        exact absurd (hge j hjg _ hj) (not_le.mpr hfv)
    have hcont : Continuous (fun t : ℝ => x + t • (y - x)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have htend : Tendsto (fun t : ℝ => x + t • (y - x)) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have := hcont.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • (y - x) ∈ ⋃ i, (D.tile (g i)).carrier := by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
      exact hseg t ⟨ht.1, ht.2.le⟩
    exact hclosed.mem_of_tendsto htend hev

/-- **Cutting a dissection into two families by a line.**  `D` is a dissection into `n₁ + n₂` tiles; the first
`n₁` lie in `{f <= c}`, the last `n₂` in `{f >= c}`, and the line really cuts the target. -/
theorem split_tiled {n₁ n₂ : ℕ} (D : CongruentDissection (n₁ + n₂)) (f : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (h1 : ∀ i : Fin n₁, ∀ x ∈ (D.tile (Fin.castAdd n₂ i)).carrier, f x ≤ c)
    (h2 : ∀ j : Fin n₂, ∀ x ∈ (D.tile (Fin.natAdd n₁ j)).carrier, c ≤ f x)
    (hy1 : ∃ y ∈ D.target.carrier, f y < c) (hy2 : ∃ y ∈ D.target.carrier, c < f y) :
    Tiled {x | x ∈ D.target.carrier ∧ f x ≤ c} D.model n₁ ∧
    Tiled {x | x ∈ D.target.carrier ∧ c ≤ f x} D.model n₂ := by
  refine ⟨family_tiled D (Fin.castAdd n₂) (Fin.castAdd_injective _ _) f c h1 ?_ hy1, ?_⟩
  · intro j hj x hx
    induction j using Fin.addCases with
    | left i => exact absurd rfl (hj i)
    | right k => exact h2 k x hx
  · have hneg : ∀ p : Plane, (-f) p = -(f p) := by
      intro p
      have := congrFun (AffineMap.coe_neg f) p
      simpa using this
    have key := family_tiled D (Fin.natAdd n₁) (Fin.natAdd_injective _ _) (-f) (-c)
      (fun j x hx => by rw [hneg]; linarith [h2 j x hx])
      (by
        intro j hj x hx
        induction j using Fin.addCases with
        | left i => rw [hneg]; linarith [h1 i x hx]
        | right k => exact absurd rfl (hj k))
      (by
        obtain ⟨y, hy, hyf⟩ := hy2
        exact ⟨y, hy, by rw [hneg]; linarith⟩)
    refine key.congr_set ?_
    ext x
    simp only [Set.mem_setOf_eq, hneg, neg_le_neg_iff]

/-- **Threshold form.**  `D` is a dissection into `N = n₁ + n₂` tiles; the tiles with index `< n₁` lie in
`{f <= c}`, those with index `>= n₁` in `{f >= c}`, and the line really cuts the target.  (No cast of the
dissection is needed, which is what a certificate indexed by `tiles.length` wants.) -/
theorem split_tiled_thr {N n₁ n₂ : ℕ} (hN : n₁ + n₂ = N) (D : CongruentDissection N)
    (f : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (h1 : ∀ i : Fin N, i.val < n₁ → ∀ x ∈ (D.tile i).carrier, f x ≤ c)
    (h2 : ∀ i : Fin N, n₁ ≤ i.val → ∀ x ∈ (D.tile i).carrier, c ≤ f x)
    (hy1 : ∃ y ∈ D.target.carrier, f y < c) (hy2 : ∃ y ∈ D.target.carrier, c < f y) :
    Tiled {x | x ∈ D.target.carrier ∧ f x ≤ c} D.model n₁ ∧
    Tiled {x | x ∈ D.target.carrier ∧ c ≤ f x} D.model n₂ := by
  subst hN
  refine ⟨family_tiled D (fun i : Fin n₁ => Fin.castAdd n₂ i) (Fin.castAdd_injective _ _) f c
    (fun i x hx => h1 _ (by simp) x hx) ?_ hy1, ?_⟩
  · intro j hj x hx
    refine h2 j ?_ x hx
    by_contra hlt
    push_neg at hlt
    exact hj ⟨j.val, hlt⟩ (by ext; simp)
  · have hneg : ∀ p : Plane, (-f) p = -(f p) := by
      intro p
      have := congrFun (AffineMap.coe_neg f) p
      simpa using this
    have key := family_tiled D (fun i : Fin n₂ => Fin.natAdd n₁ i) (Fin.natAdd_injective _ _) (-f) (-c)
      (fun j x hx => by rw [hneg]; linarith [h2 _ (by simp) x hx])
      (by
        intro j hj x hx
        rw [hneg]
        have hlt : j.val < n₁ := by
          by_contra hge
          push_neg at hge
          exact hj ⟨j.val - n₁, by omega⟩ (by ext; simp; omega)
        linarith [h1 j hlt x hx])
      (by
        obtain ⟨y, hy, hyf⟩ := hy2
        exact ⟨y, hy, by rw [hneg]; linarith⟩)
    refine key.congr_set ?_
    ext x
    simp only [Set.mem_setOf_eq, hneg, neg_le_neg_iff]

end Erdos634.Draft.F1StripExtract

#print axioms Erdos634.Draft.F1StripExtract.split_tiled
