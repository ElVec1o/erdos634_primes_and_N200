import Mathlib.Tactic
import Erdos634.Draft.ThmDStopBeta

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (2): the tile across the `b`-ray at the three kinds of start  

`ray_across_tile`: `T₁` a tile with the edge `[X₀, Y]`, `φ` a supporting functional of the target at `X₀` with `φ Y > 0`
(the segment `]X₀, Y[` is interior): `next_tile` along the ray gives a tile `E ≠ T₁` with a vertex at `X₀`, an edge
`[X₀, X₀ + t (Y - X₀)]` on the ray and lying on the other side of the ray from `T₁`'s third vertex; its angle at `X₀` is `α, β` or `γ`
with the edge length `∈ {b,c}`, `{a,c}`, `{a,b}`.
* `apex_ray_tile` : at a target vertex of corner angle `π - 2α`, `T₁` with `α`: `E` has `β`, edge `a` or `c`.
* `alphaalpha_ray_tile` : at a frontier non-vertex with `α | α` (`T₁`, `T₂`, `X₀ ∈ ]W, Z[`): the tile across the ray of `T₁` or the tile
  across the ray of `T₂` has an `a`- or `c`-edge on its ray (the other may be the `α`-tile with a `b`-edge).
* `stop_ray_tile` : the interior `γ`-stop (`stop_beta_tile`) with the edge length `a` or `c` added.
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

/-- the edge lengths at a vertex with a given angle -/
theorem edge_len_at (S : SetupT D u v α β γ L ax ay) (i : Fin N) {k m j : Fin 3} (hkm : k ≠ m)
    (hkj : k ≠ j) (hmj : m ≠ j) :
    ((D.tile i).localAngle ((D.tile i).pts k) = α →
        (dist ((D.tile i).pts k) ((D.tile i).pts m) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 ∨
          dist ((D.tile i).pts k) ((D.tile i).pts m) = (u : ℝ) * v)) ∧
    ((D.tile i).localAngle ((D.tile i).pts k) = β →
        (dist ((D.tile i).pts k) ((D.tile i).pts m) = (u : ℝ) ^ 2 ∨
          dist ((D.tile i).pts k) ((D.tile i).pts m) = (u : ℝ) * v)) := by
  have hab := S.tile.hab
  have hac := S.tile.ac
  have hbc := S.tile.bc
  have hang := angle_at_vertexT D hab hac hbc S.hM i hkm hkj hmj
  have hop := vertex_dist_casesT D S.hM i hmj
  have hαβ := alpha_ne_beta S
  have hαγ := alpha_ne_gamma S
  have hβγ := beta_ne_gamma S
  have hkm3 := vertex_dist_casesT D S.hM i hkm
  constructor
  · intro hα
    -- the opposite side is a
    have hopp : dist ((D.tile i).pts m) ((D.tile i).pts j) = (u : ℝ) ^ 2 := by
      rcases hop with h | h | h
      · exact h
      · have := hang.2.1 h; rw [hα] at this; exact absurd this hαβ
      · have := hang.2.2 h; rw [hα] at this; exact absurd this hαγ
    rcases hkm3 with h | h | h
    · exfalso
      rcases sides_of_a_edgeT D S.tile S.hM i hkm hkj hmj h with ⟨s1, s2⟩ | ⟨s1, s2⟩
      · rw [dist_comm] at s2; rw [hopp] at s2; exact hab (by linarith)
      · rw [dist_comm] at s2; rw [hopp] at s2; exact hac (by linarith)
    · exact Or.inl h
    · exact Or.inr h
  · intro hβ
    have hopp : dist ((D.tile i).pts m) ((D.tile i).pts j) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
      rcases hop with h | h | h
      · have := hang.1 h; rw [hβ] at this; exact absurd this.symm hαβ
      · exact h
      · have := hang.2.2 h; rw [hβ] at this; exact absurd this hβγ
    rcases hkm3 with h | h | h
    · exact Or.inl h
    · exfalso
      rcases sides_of_b_edgeT D S.tile S.hM i hkm hkj hmj h with ⟨s1, s2⟩ | ⟨s1, s2⟩
      · rw [dist_comm] at s2; rw [hopp] at s2; exact hbc (by linarith)
      · rw [dist_comm] at s2; rw [hopp] at s2; exact hab (by linarith)
    · exact Or.inr h

/-- a tile with a vertex at `X₀` and an edge on a ray from `X₀` through `Y` whose other end is a vertex `Z` with `X₀ ∈ ]W, Z[`
has the angle `π - θ` at `X₀`, where `θ = ∠ Y X₀ W` -/
theorem across_angle {W Z X0 Y : Plane} {θ : ℝ} (hsb : Sbtw ℝ W X0 Z) (hθ : ∠ Y X0 W = θ) (hθπ : θ ≠ Real.pi)
    {t : ℝ} (ht : 0 < t) {T : Tri} {k' m' k2 : Fin 3} (hkm' : k' ≠ m') (hk' : T.pts k' = X0)
    (hm' : T.pts m' = AffineMap.lineMap X0 Y t) (hZ : T.pts k2 = Z) :
    T.localAngle X0 = Real.pi - θ := by
  have hπ : ∠ W X0 Z = Real.pi := hsb.angle₁₂₃_eq_pi
  have hZX : Z ≠ X0 := fun h => hsb.ne_right h.symm
  have hA : ∠ (AffineMap.lineMap X0 Y t) X0 W = θ := by
    rw [angle_comm, angle_ray ht, angle_comm]; exact hθ
  have hZY : Z ≠ AffineMap.lineMap X0 Y t := by
    intro h
    have h1 : ∠ W X0 (AffineMap.lineMap X0 Y t) = θ := by rw [angle_comm]; exact hA
    rw [h] at hπ
    exact hθπ (h1.symm.trans hπ)
  obtain ⟨j₃, hjk, hjm⟩ := fin3_third k' m' hkm'
  have hk2 : k2 = j₃ := by
    have key : ∀ a b c d : Fin 3, a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c = d := by decide
    refine (key k' m' j₃ k2 hkm' hjk hjm ?_ ?_).symm
    · intro h; apply hZX; rw [← hZ, h, hk']
    · intro h; apply hZY; rw [← hZ, h, hm']
  have hang := localAngle_vertex3 T hkm' (Ne.symm hjk) (Ne.symm hjm)
  rw [hk', hm'] at hang
  have hjv : T.pts j₃ = Z := by rw [← hk2]; exact hZ
  rw [hjv] at hang
  have hsum := angle_add_angle_eq_pi_of_angle_eq_pi (AffineMap.lineMap X0 Y t) hπ
  rw [hA] at hsum
  rw [hang]; linarith

/-- **The tile across the `b`-ray.** -/
theorem ray_across_tile (S : SetupT D u v α β γ L ax ay)
    {X0 Y : Plane} (φ : Plane → ℝ)
    (hφl : ∀ (p q : Plane) (t : ℝ), φ (AffineMap.lineMap p q t) = φ p + t * (φ q - φ p))
    (hφ : ∀ q ∈ D.target.carrier, 0 ≤ φ q) (hφ0 : φ X0 = 0) (hφY : 0 < φ Y)
    (hint : openSegment ℝ X0 Y ⊆ interior D.target.carrier)
    {t1 : Fin N} {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j)
    (hk : (D.tile t1).pts k = X0) (hm : (D.tile t1).pts m = Y) :
    ∃ (e : Fin N) (k' m' : Fin 3) (t : ℝ), e ≠ t1 ∧ k' ≠ m' ∧ (D.tile e).pts k' = X0 ∧ 0 < t ∧
      (D.tile e).pts m' = AffineMap.lineMap X0 Y t ∧ (D.tile e).localAngle X0 ≠ 0 ∧
      ((D.tile e).localAngle X0 = α ∨ (D.tile e).localAngle X0 = β ∨ (D.tile e).localAngle X0 = γ) ∧
      ((D.tile e).localAngle X0 = α →
        (dist ((D.tile e).pts k') ((D.tile e).pts m') = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 ∨
          dist ((D.tile e).pts k') ((D.tile e).pts m') = (u : ℝ) * v)) ∧
      ((D.tile e).localAngle X0 = β →
        (dist ((D.tile e).pts k') ((D.tile e).pts m') = (u : ℝ) ^ 2 ∨
          dist ((D.tile e).pts k') ((D.tile e).pts m') = (u : ℝ) * v)) ∧
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
  set W : Plane := (D.tile t1).pts j with hW
  have hWX : W ≠ X0 := by
    rw [← hk]; exact fun h => hkj ((D.tile t1).indep.injective h).symm
  have hXY : X0 ≠ Y := by
    rw [← hk, ← hm]; exact fun h => hkm ((D.tile t1).indep.injective h)
  have hcW : cross (Y - X0) (W - X0) ≠ 0 := by
    have := Erdos634.Draft.W2E1.cross_ne_zero_of_tri (D.tile t1) hkm hkj hmj
    rwa [hk, hm] at this
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
  have n1 : e.1 ≠ t1 := ne_of_F (D := D) F hle (i := j) hFW
  obtain ⟨j₃, hjk, hjm⟩ := fin3_third k' m' hkm'
  have hkj3 : k' ≠ j₃ := Ne.symm hjk
  have hmj3 : m' ≠ j₃ := Ne.symm hjm
  have hang := angle_at_vertexT D hab hac hbc S.hM e.1 hkm' hkj3 hmj3
  have hop := vertex_dist_casesT D S.hM e.1 hmj3
  have hcase : (D.tile e.1).localAngle X0 = α ∨ (D.tile e.1).localAngle X0 = β ∨
      (D.tile e.1).localAngle X0 = γ := by
    rw [← hk']
    rcases hop with h | h | h
    · exact Or.inl (hang.1 h)
    · exact Or.inr (Or.inl (hang.2.1 h))
    · exact Or.inr (Or.inr (hang.2.2 h))
  have hnz : (D.tile e.1).localAngle X0 ≠ 0 := by
    rcases hcase with h | h | h
    · rw [h]; exact S.hα.ne'
    · rw [h]; exact hβpos.ne'
    · rw [h]; exact hγpos.ne'
  have hlen := edge_len_at S e.1 hkm' hkj3 hmj3
  refine ⟨e.1, k', m', t0, n1, hkm', hk', ht0, hm', hnz, hcase, ?_, ?_, ?_⟩
  · intro h; exact hlen.1 (by rw [hk']; exact h)
  · intro h; exact hlen.2 (by rw [hk']; exact h)
  · intro i
    have h1 := hFsub ((D.tile e.1).pts i)
    have h2 := hFsub W
    have h3 := hle i
    nlinarith [hσσ]

/-- the target total at a vertex -/
theorem vertex_total (D : Dissection N) (k : Fin 3) :
    ∑ i, (D.tile i).localAngle (D.target.pts k) =
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) := by
  rw [D.sum_localAngle_eq (D.target.pts k), D.target.localAngle_vertex k]

/-- the data of a tile across a ray with an `a`- or `c`-edge on it -/
def RayTileAC (D : CongruentDissection N) (u v : ℕ) (X0 Y W : Plane) (t1 : Fin N) : Prop :=
  ∃ (e : Fin N) (k' m' : Fin 3) (t : ℝ), e ≠ t1 ∧ k' ≠ m' ∧ (D.tile e).pts k' = X0 ∧ 0 < t ∧
    (D.tile e).pts m' = AffineMap.lineMap X0 Y t ∧
    (dist ((D.tile e).pts k') ((D.tile e).pts m') = (u : ℝ) ^ 2 ∨
      dist ((D.tile e).pts k') ((D.tile e).pts m') = (u : ℝ) * v) ∧
    (∀ i, cross (Y - X0) ((D.tile e).pts i - X0) * cross (Y - X0) (W - X0) ≤ 0)

/-- **The apex.**  At a vertex `X₀` of the target whose total angle is `π - 2α`, a tile `T₁` with `α` and the edge `[X₀, Y]`:
the tile across the ray has `β` and an `a`- or `c`-edge on it. -/
theorem apex_ray_tile (S : SetupT D u v α β γ L ax ay)
    {X0 Y : Plane} (φ : Plane → ℝ)
    (hφl : ∀ (p q : Plane) (t : ℝ), φ (AffineMap.lineMap p q t) = φ p + t * (φ q - φ p))
    (hφ : ∀ q ∈ D.target.carrier, 0 ≤ φ q) (hφ0 : φ X0 = 0) (hφY : 0 < φ Y)
    (hint : openSegment ℝ X0 Y ⊆ interior D.target.carrier)
    (htot : ∑ i, (D.tile i).localAngle X0 = Real.pi - 2 * α)
    {t1 : Fin N} {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j)
    (hk : (D.tile t1).pts k = X0) (hm : (D.tile t1).pts m = Y)
    (hα1 : (D.tile t1).localAngle X0 = α) :
    RayTileAC D u v X0 Y ((D.tile t1).pts j) t1 ∧
      ∃ e : Fin N, e ≠ t1 ∧ (D.tile e).localAngle X0 = β := by
  obtain ⟨e, k', m', t, n1, hkm', hk', ht, hm', hnz, hcase, hlα, hlβ, hside⟩ :=
    ray_across_tile S φ hφl hφ hφ0 hφY hint hkm hkj hmj hk hm
  have h3α : 3 * α < Real.pi := by
    have hβpos : 0 < β := by
      have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
      have e' : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
      rw [e'] at h; exact h
    have := S.hβ; linarith
  have hβ' := residue_beta_total D.toDissection D.model (fun i => (D.tiles_congruent i).symm) α S.hirr
    (S.hM.hα') (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α (Θ := Real.pi - 2 * α) htot {t1}
    (by rw [Finset.sum_singleton, hα1]; ring) e (by simpa using n1) hnz
  have hb : (D.tile e).localAngle X0 = β := hβ'.trans S.hβ.symm
  exact ⟨⟨e, k', m', t, n1, hkm', hk', ht, hm', hlβ hb, hside⟩, e, n1, hb⟩

#print axioms ray_across_tile
#print axioms apex_ray_tile
#print axioms across_angle
#print axioms edge_len_at
end Erdos634.Draft.ThmDRun
