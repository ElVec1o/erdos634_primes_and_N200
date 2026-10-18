import Mathlib.Tactic
import Erdos634.Draft.ThmDSector4
import Erdos634.Draft.W2E1Last

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (2): the `β`-tile `T₀` at an interior `γ`-stop  

`stop_beta_tile`: at a frontier non-vertex `X₀` of the target (a point of a side, interior to the side), let `T₁` be a tile with
angle `α` at `X₀` and edges `[X₀, Y]` (the `b`-ray into the target) and `[X₀, W]` (along the side), and `T₂` a tile with angle
`γ` at `X₀` having a vertex `Z` on the side beyond `X₀` (`X₀ ∈ ]W, Z[`).  Then there is a third tile `T₀` with angle `β` at `X₀`
and an edge `[X₀, X₀ + t (Y - X₀)]` on the ray of `T₁`'s `b`-edge, on the other side of the ray from `T₁`.
Route: the fan at a frontier non-vertex has total `π`; `residue_beta_total` for `{T₁, T₂}` leaves `β`; the tile `T₀` is found by
`next_tile` along the ray (the clamp behind `X₀` is the outside of the target, as in `sector_dichotomy_P`); `T₀ ≠ T₂` because the
angle between the side-east direction and the ray is `π − α ≠ 2α`.
-/

open scoped Classical
open EuclideanGeometry
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

/-- at a vertex, the local angle is the angle between the other two vertices, in either order -/
theorem localAngle_vertex3 (T : Tri) {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) :
    T.localAngle (T.pts k) = ∠ (T.pts m) (T.pts k) (T.pts j) := by
  rw [Tri.localAngle_vertex]
  rcases Erdos634.MarchInduction.fin3_succ k m j hkm hkj hmj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; rfl
  · rw [h1, h2]; exact angle_comm _ _ _

theorem sbtw_of_openSegment {W Z X : Plane} (h : X ∈ openSegment ℝ W Z) (hW : W ≠ X) :
    Sbtw ℝ W X Z := by
  rw [sbtw_iff_mem_image_Ioo_and_ne]
  rw [openSegment_eq_image_lineMap] at h
  refine ⟨h, ?_⟩
  intro hWZ
  obtain ⟨s, -, hs⟩ := h
  rw [← hWZ, AffineMap.lineMap_same_apply] at hs
  exact hW hs

theorem angle_ray {X Y W : Plane} {t : ℝ} (ht : 0 < t) :
    ∠ W X (AffineMap.lineMap X Y t) = ∠ W X Y := by
  unfold EuclideanGeometry.angle
  rw [AffineMap.lineMap_vsub_left]
  exact InnerProductGeometry.angle_smul_right_of_pos _ _ ht

theorem lineMap_map_linear (F : Plane →ₗ[ℝ] ℝ) (p q : Plane) (t : ℝ) :
    F (AffineMap.lineMap p q t) = F p + t * (F q - F p) := by
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, smul_eq_mul]
  ring

theorem stop_beta_tile (S : SetupT D u v α β γ L ax ay)
    {X0 Y : Plane} (hX : X0 ∈ frontier D.target.carrier) (hXv : X0 ∉ Set.range D.target.pts)
    (φ : Plane → ℝ)
    (hφl : ∀ (p q : Plane) (t : ℝ), φ (AffineMap.lineMap p q t) = φ p + t * (φ q - φ p))
    (hφ : ∀ q ∈ D.target.carrier, 0 ≤ φ q) (hφ0 : φ X0 = 0) (hφY : 0 < φ Y)
    (hint : openSegment ℝ X0 Y ⊆ interior D.target.carrier)
    {t1 t2 : Fin N} {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j)
    (hk : (D.tile t1).pts k = X0) (hm : (D.tile t1).pts m = Y)
    (hα1 : (D.tile t1).localAngle X0 = α)
    {Z : Plane} {k2 : Fin 3} (hZ : (D.tile t2).pts k2 = Z)
    (hWZ : X0 ∈ openSegment ℝ ((D.tile t1).pts j) Z)
    (hγ2 : (D.tile t2).localAngle X0 = γ) :
    ∃ (e : Fin N) (k' m' : Fin 3) (t : ℝ), e ≠ t1 ∧ e ≠ t2 ∧ k' ≠ m' ∧ (D.tile e).pts k' = X0 ∧ 0 < t ∧
      (D.tile e).pts m' = AffineMap.lineMap X0 Y t ∧ (D.tile e).localAngle X0 = β ∧
      (∀ i, cross (Y - X0) ((D.tile e).pts i - X0) * cross (Y - X0) ((D.tile t1).pts j - X0) ≤ 0) := by
  have hu := S.u0
  have huv := S.uv'
  have hab := S.tile.hab
  have hac := S.tile.ac
  have hbc := S.tile.bc
  have hβpos : 0 < β := by
    have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
    have e' : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
    rw [e'] at h; exact h
  have hγpos : 0 < γ := by rw [S.hγ]; linarith [S.hα]
  have h3α : 3 * α < Real.pi := by have := S.hβ; linarith
  set W : Plane := (D.tile t1).pts j with hW
  have hWX : W ≠ X0 := by
    rw [← hk]; exact fun h => hkj ((D.tile t1).indep.injective h).symm
  have hXY : X0 ≠ Y := by
    rw [← hk, ← hm]; exact fun h => hkm ((D.tile t1).indep.injective h)
  have hcW : cross (Y - X0) (W - X0) ≠ 0 := by
    have := Erdos634.Draft.W2E1.cross_ne_zero_of_tri (D.tile t1) hkm hkj hmj
    rwa [hk, hm] at this
  -- the sign and the functional
  set d : Plane := Y - X0 with hd
  set σ : ℝ := if 0 < cross d (W - X0) then 1 else -1 with hσ
  have hσσ : σ * σ = 1 := by rw [hσ]; split_ifs <;> norm_num
  have hσpos : 0 < σ * cross d (W - X0) := by
    rw [hσ]; split_ifs with h
    · linarith
    · have : cross d (W - X0) < 0 := lt_of_le_of_ne (not_lt.mp h) hcW
      linarith
  set F : Plane →ₗ[ℝ] ℝ := σ • crossL d with hFdef
  set c : ℝ := F X0 with hc
  have hFapply : ∀ p, F p = σ * cross d p := fun p => by
    simp [hFdef, crossL_apply]
  have hFsub : ∀ p, F p - c = σ * cross d (p - X0) := fun p => by
    rw [hc, hFapply, hFapply, cross_sub_right]; ring
  have hFW : c < F W := by
    have := hFsub W; linarith
  have hF : F ≠ 0 := by
    intro h0
    have : F W - c = 0 := by simp [hc, h0]
    linarith
  have hFY : F Y = c := by
    have := hFsub Y
    rw [hd, cross_self] at this; linarith
  set P' : Plane := AffineMap.lineMap X0 Y (-1 : ℝ) with hP'def
  have hFP' : F P' = c := by
    rw [hP'def, lineMap_map_linear, hFY]; ring
  have hP' : X0 ∈ openSegment ℝ P' Y := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [hP'def]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hout : ∀ y ∈ openSegment ℝ P' X0, y ∉ D.target.carrier := by
    intro y hy hmem
    rw [openSegment_eq_image_lineMap] at hy
    obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
    have h1' := hφ _ hmem
    rw [hφl, hP'def, hφl, hφ0] at h1'
    nlinarith
  have hwall : ∀ y ∈ openSegment ℝ X0 Y, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    refine seg_wall D.toDissection (t := t1) hkm ?_
    rw [hk, hm]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨e, he, k', m', t0, hkm', hk', ht0, hm', hle, hedge, hdist⟩ :=
    next_tile D.toDissection F hF c hXY rfl hFY hFP' hP' hint hwall
      (fun e _ => not_straddles_of_outside D.toDissection hout e.1 e.2)
  -- e is not t1
  have n1 : e.1 ≠ t1 := ne_of_F (D := D) F hle (i := j) hFW
  -- angle facts at X0
  obtain ⟨j₃, hjk, hjm⟩ := fin3_third k' m' hkm'
  have hkj3 : k' ≠ j₃ := Ne.symm hjk
  have hmj3 : m' ≠ j₃ := Ne.symm hjm
  have hang := angle_at_vertexT D hab hac hbc S.hM e.1 hkm' hkj3 hmj3
  have hop := vertex_dist_casesT D S.hM e.1 hmj3
  have hnz : (D.tile e.1).localAngle X0 ≠ 0 := by
    rw [← hk']
    rcases hop with h | h | h
    · rw [hang.1 h]; exact S.hα.ne'
    · rw [hang.2.1 h]; exact hβpos.ne'
    · rw [hang.2.2 h]; exact hγpos.ne'
  have a12 : (D.tile t1).localAngle X0 ≠ (D.tile t2).localAngle X0 := by
    rw [hα1, hγ2]; exact alpha_ne_gamma S
  have h12 : t1 ≠ t2 := ne_of_angle a12
  have hsum : ∑ i ∈ ({t1, t2} : Finset (Fin N)), (D.tile i).localAngle X0
      = Real.pi - (Real.pi - 3 * α) := by
    rw [Finset.sum_insert (by simp [h12]), Finset.sum_singleton, hα1, hγ2, S.hγ]; ring
  have htot := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hX hXv
  -- e is not t2
  have n2 : e.1 ≠ t2 := by
    intro he2
    have hsb : Sbtw ℝ W X0 Z := sbtw_of_openSegment hWZ hWX
    have hZX : Z ≠ X0 := fun h => hsb.ne_right h.symm
    have hπ : ∠ W X0 Z = Real.pi := hsb.angle₁₂₃_eq_pi
    -- the angle of t1 at X0
    have hA1 : ∠ Y X0 W = α := by
      have := localAngle_vertex3 (D.tile t1) hkm hkj hmj
      rw [hk, hm] at this
      rw [← this, hα1]
    have hA2 : ∠ (AffineMap.lineMap X0 Y t0) X0 W = α := by
      rw [angle_comm, angle_ray ht0, angle_comm]; exact hA1
    have hY'X : AffineMap.lineMap X0 Y t0 ≠ X0 := by
      rw [← hm', ← hk']; exact fun h => hkm' ((D.tile e.1).indep.injective h).symm
    have hZY : Z ≠ AffineMap.lineMap X0 Y t0 := by
      intro h
      have h1 : ∠ W X0 (AffineMap.lineMap X0 Y t0) = α := by rw [angle_comm]; exact hA2
      rw [h] at hπ
      linarith [S.hα, Real.pi_pos]
    -- Z is the third vertex of e = t2
    have hk2 : k2 = j₃ := by
      have key : ∀ a b c d : Fin 3, a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c = d := by decide
      refine (key k' m' j₃ k2 hkm' hjk hjm ?_ ?_).symm
      · intro h
        apply hZX
        rw [← hZ, h, ← he2, hk']
      · intro h
        apply hZY
        rw [← hZ, h, ← he2, hm']
    have hang2 := localAngle_vertex3 (D.tile e.1) hkm' hkj3 hmj3
    rw [hk', hm'] at hang2
    have hjv : (D.tile e.1).pts j₃ = Z := by rw [he2, ← hk2]; exact hZ
    rw [hjv, he2, hγ2] at hang2
    have hsum2 := angle_add_angle_eq_pi_of_angle_eq_pi (AffineMap.lineMap X0 Y t0) hπ
    have hγeq := S.hγ
    linarith [S.hα, Real.pi_pos]
  have hβ' := residue_beta_total D.toDissection D.model (fun i => (D.tiles_congruent i).symm) α S.hirr
    (S.hM.hα') (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α (Θ := Real.pi) htot {t1, t2}
    (by rw [hsum]) e.1 (by simp [n1, n2]) hnz
  refine ⟨e.1, k', m', t0, n1, n2, hkm', hk', ht0, hm', ?_, ?_⟩
  · exact hβ'.trans S.hβ.symm
  · intro i
    have h1 := hFsub ((D.tile e.1).pts i)
    have h2 := hFsub W
    have h3 := hle i
    nlinarith [hσσ]

#print axioms stop_beta_tile
end Erdos634.Draft.ThmDRun
