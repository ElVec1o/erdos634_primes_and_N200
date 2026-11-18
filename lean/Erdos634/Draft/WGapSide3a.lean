/-
Draft/WGapSide3a.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 [SIDE-3]).
Not imported by any aggregate.  Module P-B1: the LEFT variants of the wedge filler: `ray_filler` / `no_straddle` / `filler_alpha` for a known tile `t0` on the RIGHT of the ray `X -> Y`
(`cross (Y-X) (Z-X) < 0`); the filler is then on the LEFT.  (The mirror lattice reverses orientation, so at the boundary point `p'(j,0)` the known tile `D'(j-1,0)` is on the right of the
ray along `l'_j`, and the free alpha-wedge on its left.)  Copies of `ray_filler`, `no_straddle`, `filler_alpha` with the functional `crossL (X - Y)` in place of `crossL (Y - X)`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapCase1b

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

theorem crossL_neg_ne {X Y : Plane} (hXY : X ≠ Y) : crossL (X - Y) ≠ 0 :=
  crossL_ne_zero (sub_ne_zero.mpr hXY)

/-- `ray_filler`, known tile on the RIGHT: the tile `τ ≠ t₀` on the LEFT has vertices `X`, `X + t (Y - X)` -/
theorem ray_filler_left (D : CongruentDissection N) {X Y P' Z : Plane} {t₀ : Fin N} (hXY : X ≠ Y)
    (hV : HasV D t₀ X Y Z) (hZ : cross (Y - X) (Z - X) < 0)
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    (hint : openSegment ℝ X Y ⊆ interior D.target.carrier)
    (hclamp : ∀ ed ∈ D.lineChain (crossL (X - Y)) (cross (X - Y) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y) :
    ∃ (τ : Fin N) (k m : Fin 3) (t : ℝ), τ ≠ t₀ ∧ k ≠ m ∧ (D.tile τ).pts k = X ∧ 0 < t ∧
      (D.tile τ).pts m = AffineMap.lineMap X Y t ∧
      ∀ j, 0 ≤ cross (Y - X) ((D.tile τ).pts j - X) := by
  have hu : X - Y ≠ 0 := sub_ne_zero.mpr hXY
  have hF := crossL_ne_zero hu
  have hcr : ∀ v : Plane, cross (X - Y) v = -cross (Y - X) v := by
    intro v; simp [cross]; ring
  have hcl : ∀ v : Plane, crossL (X - Y) v = -cross (Y - X) v := by
    intro v; rw [crossL_apply, hcr]
  have hfX : crossL (X - Y) X = cross (X - Y) X := crossL_apply _ _
  have hcX : cross (Y - X) X = cross (Y - X) X := rfl
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
  have hwall : ∀ y ∈ openSegment ℝ X Y, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hV
    refine seg_wall D.toDissection (t := t₀) hkm ?_
    rw [hk, hm]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨ed, hed, k, m, t, hkm, hk, ht, hm, hle, -, -⟩ :=
    next_tile D.toDissection (crossL (X - Y)) hF (cross (X - Y) X) hXY hfX hfY hfP' hXP hint hwall hclamp
  have hge : ∀ j, 0 ≤ cross (Y - X) ((D.tile ed.1).pts j - X) := by
    intro j
    have := hle j
    rw [hcl] at this
    have h2 : cross (Y - X) ((D.tile ed.1).pts j) = cross (Y - X) ((D.tile ed.1).pts j - X) + cross (Y - X) X := by
      rw [← cross_add_right]; congr 1; abel
    rw [hcr] at this
    rw [h2] at this
    linarith
  refine ⟨ed.1, k, m, t, ?_, hkm, hk, ht, hm, hge⟩
  rintro rfl
  obtain ⟨kk, mm, jj, hkm', hkj', hmj', hk', hm', hj'⟩ := hV
  have := hge jj
  rw [hj'] at this
  linarith

/-- `no_straddle` for the functional `crossL (X - Y)` -/
theorem no_straddle_left (D : Dissection N) {X Y P' : Plane} (hXY : X ≠ Y)
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    {Ω θ : ℝ} (hΩ : ∑ i, (D.tile i).localAngle X = Ω) (K : Finset (Fin N))
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - θ) (hθ : θ < Real.pi)
    (hKlt : ∀ k ∈ K, (D.tile k).localAngle X < Real.pi) :
    ∀ ed ∈ D.lineChain (crossL (X - Y)) (cross (X - Y) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y := by
  intro ed hed hs
  have hu : X - Y ≠ 0 := sub_ne_zero.mpr hXY
  have hF := crossL_ne_zero hu
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
  obtain ⟨-, hang, -⟩ := straddle_data D (crossL (X - Y)) hF (cross (X - Y) X) hXY hfX hfY hfP' hXP hed hs
  have hnot : ed.1 ∉ K := fun hm => absurd (hKlt _ hm) (by rw [hang]; exact lt_irrefl _)
  have hsd := Finset.sum_sdiff (Finset.subset_univ K) (f := fun i => (D.tile i).localAngle X)
  have hle : (D.tile ed.1).localAngle X ≤ ∑ i ∈ Finset.univ \ K, (D.tile i).localAngle X :=
    Finset.single_le_sum (f := fun i => (D.tile i).localAngle X) (fun j _ => Tri.localAngle_nonneg _ _)
      (by simp [hnot])
  rw [hang] at hle
  have h1 : ∑ i, (D.tile i).localAngle X = Ω := hΩ
  have h2 : ∑ i ∈ K, (D.tile i).localAngle X = Ω - θ := hK
  simp only at hsd
  linarith

section fillerleft

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **FILLER, wedge `α`** (W2, W3).  Setting as `ray_filler`: the known tile `t₀` (counted in `K`) lies on the LEFT of the ray `X → Y`; the other
tiles of `K` have no vertex on the open ray (PART D, from sign facts); the free wedge is `α`.  Then the tile adjacent to the ray is an `α`-tile
`τ ∉ K`, with vertices `X`, `P` (on the ray), `W` (right of the line), `|PW| = a`, `{|XP|, |XW|} = {b, c}`. -/
theorem filler_alpha_left (S : SetupG D e f α β γ L ax ay) {X Y Z P' : Plane} {t₀ : Fin N} (hXY : X ≠ Y)
    (hV : HasV D t₀ X Y Z) (hZ : cross (Y - X) (Z - X) < 0)
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    (hint : openSegment ℝ X Y ⊆ interior D.target.carrier)
    (hclamp : ∀ ed ∈ D.lineChain (crossL (X - Y)) (cross (X - Y) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y)
    {Ω : ℝ} (hΩ : ∑ i, (D.tile i).localAngle X = Ω) (K : Finset (Fin N))
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - α)
    (hKray : ∀ k ∈ K, k ≠ t₀ → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap X Y s) :
    ∃ τ : Fin N, τ ∉ K ∧ ∃ P W : Plane, HasV D τ X P W ∧ (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap X Y s) ∧
      0 < cross (Y - X) (W - X) ∧ (D.tile τ).localAngle X = α ∧ dist P W = (e : ℝ) * f ∧
      ((dist X P = (f : ℝ) ^ 2 ∧ dist X W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
        (dist X P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist X W = (f : ℝ) ^ 2)) := by
  obtain ⟨τ, k, m, t, hτ, hkm, hk, ht, hm, hle⟩ := ray_filler_left D hXY hV hZ hP' hXP hint hclamp
  obtain ⟨n, hnk, hnm⟩ := fin3_third k m hkm
  have hkn : k ≠ n := hnk.symm
  have hmn : m ≠ n := hnm.symm
  have hτK : τ ∉ K := fun h => hKray τ h hτ m t ht hm
  have hne := tri_cross_ne (D.tile τ) hkm hkn hmn
  have hmX : (D.tile τ).pts m - (D.tile τ).pts k = t • (Y - X) := by
    rw [hm, hk, AffineMap.lineMap_apply]; simp
  have hneg : 0 < cross (Y - X) ((D.tile τ).pts n - X) := by
    rcases lt_or_eq_of_le (hle n) with h | h
    · exact h
    · exfalso; apply hne
      rw [hmX, cross_smul_left', hk, ← h]; ring
  have hvc := vertex_angle_cases S τ hkm hkn hmn
  have hcnt := wedge_alpha S hΩ hK (angles_lt_pi S).1
  have hmemτ : τ ∈ Finset.univ \ K := by simp [hτK]
  have hangα : (D.tile τ).localAngle ((D.tile τ).pts k) = α := by
    rcases hvc with h | h | h
    · exact h
    · exfalso
      have h0 := hcnt.2.1
      unfold cnt at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      exact h0 hmemτ (by rw [← hk]; exact h)
    · exfalso
      have h0 := hcnt.2.2
      unfold cnt at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      exact h0 hmemτ (by rw [← hk]; exact h)
  obtain ⟨hopp, hsd⟩ := sides_of_alpha S τ hkm hkn hmn hangα
  rw [hk] at hangα hsd
  refine ⟨τ, hτK, (D.tile τ).pts m, (D.tile τ).pts n, ⟨k, m, n, hkm, hkn, hmn, hk, rfl, rfl⟩,
    ⟨t, ht, hm⟩, hneg, hangα, hopp, ?_⟩
  rcases hsd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

end fillerleft

end Erdos634.Draft.WGapStmt
