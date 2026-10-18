import Mathlib.Tactic
import Erdos634.Draft.ThmDRayTile

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (2): the interior `γ`-stop and the `α | α` junction  

* `stop_ray_tile` : the interior `γ`-stop; the tile across the `b`-ray of `T₁` has `β` and an `a`- or `c`-edge on the ray.
* `alphaalpha_ray_tile` : at an `α | α` junction on a side (`T₁`, `T₂` with `α`, `X₀ ∈ ]W, Z[`), the tile across the `b`-ray of `T₁` or the
  tile across the `b`-ray of `T₂` has an `a`- or `c`-edge on its ray.  (If both tiles across have `b` on the ray, they are the same `α`-tile
  with two `b`-edges at one vertex, impossible.)
-/

open scoped Classical
open EuclideanGeometry
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg Erdos634.Draft.APrimeLegBuild

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem angle_of_vertex3 (T : Tri) {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) {X0 Y W : Plane}
    {θ : ℝ} (hk : T.pts k = X0) (hm : T.pts m = Y) (hj : T.pts j = W) (hθ : T.localAngle X0 = θ) :
    ∠ Y X0 W = θ := by
  have := localAngle_vertex3 T hkm hkj hmj
  rw [hk, hm, hj] at this
  rw [← this, hθ]

theorem h3alpha (S : SetupT D u v α β γ L ax ay) : 3 * α < Real.pi := by
  have hβpos : 0 < β := by
    have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
    have e' : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
    rw [e'] at h; exact h
  have := S.hβ; linarith

/-- the interior `γ`-stop, with the edge length -/
theorem stop_ray_tile (S : SetupT D u v α β γ L ax ay)
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
    RayTileAC D u v X0 Y ((D.tile t1).pts j) t1 ∧
      ∃ e : Fin N, e ≠ t1 ∧ e ≠ t2 ∧ (D.tile e).localAngle X0 = β := by
  have h3α := h3alpha S
  have hWX : (D.tile t1).pts j ≠ X0 := by
    rw [← hk]; exact fun h => hkj ((D.tile t1).indep.injective h).symm
  have hsb : Sbtw ℝ ((D.tile t1).pts j) X0 Z := sbtw_of_openSegment hWZ hWX
  have hA1 : ∠ Y X0 ((D.tile t1).pts j) = α :=
    angle_of_vertex3 (D.tile t1) hkm hkj hmj hk hm rfl hα1
  obtain ⟨e, k', m', t, n1, hkm', hk', ht, hm', hnz, hcase, hlα, hlβ, hside⟩ :=
    ray_across_tile S φ hφl hφ hφ0 hφY hint hkm hkj hmj hk hm
  have n2 : e ≠ t2 := by
    intro he2
    subst he2
    have := across_angle hsb hA1 (by linarith [S.hα, Real.pi_pos]) ht hkm' hk' hm' hZ
    -- the angle of e at X0 is π - α, but it is γ = 2α
    have h2 : (D.tile e).localAngle X0 = γ := hγ2
    rw [h2, S.hγ] at this
    linarith [S.hα, Real.pi_pos]
  have n12 : t1 ≠ t2 := by
    intro h; subst h
    rw [hα1] at hγ2; exact alpha_ne_gamma S hγ2
  have htot := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hX hXv
  have hsum : ∑ i ∈ ({t1, t2} : Finset (Fin N)), (D.tile i).localAngle X0
      = Real.pi - (Real.pi - 3 * α) := by
    rw [Finset.sum_insert (by simp [n12]), Finset.sum_singleton, hα1, hγ2, S.hγ]; ring
  have hβ' := residue_beta_total D.toDissection D.model (fun i => (D.tiles_congruent i).symm) α S.hirr
    (S.hM.hα') (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α (Θ := Real.pi) htot {t1, t2}
    (by rw [hsum]) e (by simp [n1, n2]) hnz
  have hb : (D.tile e).localAngle X0 = β := hβ'.trans S.hβ.symm
  exact ⟨⟨e, k', m', t, n1, hkm', hk', ht, hm', hlβ hb, hside⟩, e, n1, n2, hb⟩

/-- the rest at an `α|α` junction is not `γ`, and has at most one `α` -/
theorem no_rest (S : SetupT D u v α β γ L ax ay) (T' : Finset (Fin N)) (x : Plane)
    (hbound : ∀ i ∈ T', (D.tile i).localAngle x ≤ Real.pi - 2 * α)
    (hT' : ∑ i ∈ T', (D.tile i).localAngle x = Real.pi - 4 * α) : False := by
  have hcases : ∀ i ∈ T', (D.tile i).localAngle x = 0 ∨ (D.tile i).localAngle x = α ∨
      (D.tile i).localAngle x = Real.pi - 3 * α ∨ (D.tile i).localAngle x = 2 * α := by
    intro i hi
    have hle' := hbound i hi
    rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) x with ⟨j, hj, hval⟩ | h2pi | hpi' | h0
    · obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
      rw [hval, hk]
      fin_cases k
      · right; left; exact S.hM.hα'
      · right; right; left; exact S.hM.hβ'.trans S.hβ
      · right; right; right; exact S.hM.hγ'.trans S.hγ
    · exfalso; rw [h2pi] at hle'; linarith [S.hα, Real.pi_pos]
    · exfalso; rw [hpi'] at hle'; linarith [S.hα, Real.pi_pos]
    · exact Or.inl h0
  obtain ⟨X, Y, Z, hXYZ⟩ := Erdos634.PinPlumbing.sum_of_values_real T' (fun i => (D.tile i).localAngle x)
    α (Real.pi - 3 * α) (2 * α) hcases
  rw [hT'] at hXYZ
  have := cnt_eq α S.hirr X Y Z (-4) 1 (by push_cast; linarith)
  omega

theorem rest_facts (S : SetupT D u v α β γ L ax ay) (x : Plane) (t1 t2 : Fin N)
    (hsum : ∑ i, (D.tile i).localAngle x = Real.pi)
    (hS : (D.tile t1).localAngle x + (D.tile t2).localAngle x = 2 * α) (n12 : t1 ≠ t2) :
    (∀ G, G ≠ t1 → G ≠ t2 → (D.tile G).localAngle x ≠ 2 * α) ∧
    (∀ G1 G2, G1 ≠ t1 → G1 ≠ t2 → G2 ≠ t1 → G2 ≠ t2 → G1 ≠ G2 →
      (D.tile G1).localAngle x = α → (D.tile G2).localAngle x = α → False) := by
  classical
  set T : Finset (Fin N) := Finset.univ \ {t1, t2} with hT
  have hTsum : ∑ i ∈ T, (D.tile i).localAngle x = Real.pi - 2 * α := by
    have := Finset.sum_sdiff (Finset.subset_univ ({t1, t2} : Finset (Fin N)))
      (f := fun i => (D.tile i).localAngle x)
    rw [Finset.sum_insert (by simp [n12]), Finset.sum_singleton] at this
    linarith
  have hnn : ∀ i, 0 ≤ (D.tile i).localAngle x := fun i => (D.tile i).localAngle_nonneg x
  have hbd : ∀ i ∈ T, (D.tile i).localAngle x ≤ Real.pi - 2 * α := by
    intro i hi
    have := Finset.single_le_sum (fun m _ => hnn m) hi
    linarith
  have hmem : ∀ G, G ≠ t1 → G ≠ t2 → G ∈ T := by
    intro G h1 h2
    simp [hT, h1, h2]
  constructor
  · intro G h1 h2 hG
    have hGT := hmem G h1 h2
    refine no_rest S (T.erase G) x (fun i hi => hbd i (Finset.mem_of_mem_erase hi)) ?_
    have := Finset.add_sum_erase T (fun i => (D.tile i).localAngle x) hGT
    beta_reduce at this
    rw [hG] at this; linarith
  · intro G1 G2 h11 h12 h21 h22 h12' hG1 hG2
    have hG1T := hmem G1 h11 h12
    have hG2T : G2 ∈ T.erase G1 := Finset.mem_erase.mpr ⟨Ne.symm h12', hmem G2 h21 h22⟩
    refine no_rest S ((T.erase G1).erase G2) x
      (fun i hi => hbd i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))) ?_
    have e1 := Finset.add_sum_erase T (fun i => (D.tile i).localAngle x) hG1T
    have e2 := Finset.add_sum_erase (T.erase G1) (fun i => (D.tile i).localAngle x) hG2T
    beta_reduce at e1 e2
    rw [hG1] at e1; rw [hG2] at e2; linarith

/-- **The `α | α` junction.** -/
theorem alphaalpha_ray_tile (S : SetupT D u v α β γ L ax ay)
    {X0 Y1 Y2 : Plane} (hX : X0 ∈ frontier D.target.carrier) (hXv : X0 ∉ Set.range D.target.pts)
    (φ : Plane → ℝ)
    (hφl : ∀ (p q : Plane) (t : ℝ), φ (AffineMap.lineMap p q t) = φ p + t * (φ q - φ p))
    (hφ : ∀ q ∈ D.target.carrier, 0 ≤ φ q) (hφ0 : φ X0 = 0) (hφY1 : 0 < φ Y1) (hφY2 : 0 < φ Y2)
    (hint1 : openSegment ℝ X0 Y1 ⊆ interior D.target.carrier)
    (hint2 : openSegment ℝ X0 Y2 ⊆ interior D.target.carrier)
    {t1 t2 : Fin N} {k m j k₂ m₂ j₂ : Fin 3}
    (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) (hkm₂ : k₂ ≠ m₂) (hkj₂ : k₂ ≠ j₂) (hmj₂ : m₂ ≠ j₂)
    (hk : (D.tile t1).pts k = X0) (hm : (D.tile t1).pts m = Y1)
    (hk₂ : (D.tile t2).pts k₂ = X0) (hm₂ : (D.tile t2).pts m₂ = Y2)
    (hα1 : (D.tile t1).localAngle X0 = α) (hα2 : (D.tile t2).localAngle X0 = α)
    (hWZ : X0 ∈ openSegment ℝ ((D.tile t1).pts j) ((D.tile t2).pts j₂)) :
    RayTileAC D u v X0 Y1 ((D.tile t1).pts j) t1 ∨ RayTileAC D u v X0 Y2 ((D.tile t2).pts j₂) t2 := by
  have h3α := h3alpha S
  set W := (D.tile t1).pts j with hW
  set Z := (D.tile t2).pts j₂ with hZ
  have hWX : W ≠ X0 := by
    rw [← hk]; exact fun h => hkj ((D.tile t1).indep.injective h).symm
  have hsb : Sbtw ℝ W X0 Z := sbtw_of_openSegment hWZ hWX
  have hA1 : ∠ Y1 X0 W = α := angle_of_vertex3 (D.tile t1) hkm hkj hmj hk hm rfl hα1
  have hA2 : ∠ Y2 X0 Z = α := angle_of_vertex3 (D.tile t2) hkm₂ hkj₂ hmj₂ hk₂ hm₂ rfl hα2
  have hπ : ∠ W X0 Z = Real.pi := hsb.angle₁₂₃_eq_pi
  have n12 : t1 ≠ t2 := by
    intro h; subst h
    -- the same tile with W, Z on opposite sides of X0 at a common vertex: its angle would be π
    have hZX : Z ≠ X0 := fun h => hsb.ne_right h.symm
    have hk2 : k₂ = k := (D.tile t1).indep.injective (hk₂.trans hk.symm)
    subst hk2
    have key : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → ∀ b' c' : Fin 3, a ≠ b' → a ≠ c' → b' ≠ c' →
        (b = b' ∧ c = c') ∨ (b = c' ∧ c = b') := by decide
    rcases key _ _ _ hkm hkj hmj _ _ hkm₂ hkj₂ hmj₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- j₂ = j: Z = W
      have : Z = W := by rw [hZ, hW, h2]
      rw [this] at hπ
      rw [EuclideanGeometry.angle_self_of_ne hWX] at hπ
      linarith [Real.pi_pos]
    · -- j₂ = m: Z = Y1 (j₂ = m, m₂ = j), the angle ∠ W X0 Y1 = α but = π
      have : Z = Y1 := by rw [hZ, ← hm, h1]
      rw [this, angle_comm, hA1] at hπ
      linarith [S.hα, Real.pi_pos]
  have htot := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hX hXv
  have hrest := rest_facts S X0 t1 t2 htot (by rw [hα1, hα2]; ring) n12
  obtain ⟨e1, k1, m1, s1, n11, hkm1, hk1, hs1, hm1, hnz1, hc1, hlα1, hlβ1, hside1⟩ :=
    ray_across_tile S φ hφl hφ hφ0 hφY1 hint1 hkm hkj hmj hk hm
  obtain ⟨e2, k2, m2, s2, n22, hkm2, hk2, hs2, hm2, hnz2, hc2, hlα2, hlβ2, hside2⟩ :=
    ray_across_tile S φ hφl hφ hφ0 hφY2 hint2 hkm₂ hkj₂ hmj₂ hk₂ hm₂
  have hπα : ∀ θ, θ = α → θ ≠ Real.pi := by
    intro θ h; rw [h]; linarith [S.hα, Real.pi_pos]
  -- e1 is not t2
  have n12' : e1 ≠ t2 := by
    intro he
    subst he
    have := across_angle hsb hA1 (hπα _ rfl) hs1 hkm1 hk1 hm1 (k2 := j₂) rfl
    rw [hα2] at this
    linarith [S.hα, Real.pi_pos]
  have n21' : e2 ≠ t1 := by
    intro he
    subst he
    have := across_angle hsb.symm hA2 (hπα _ rfl) hs2 hkm2 hk2 hm2 (k2 := j) rfl
    rw [hα1] at this
    linarith [S.hα, Real.pi_pos]
  by_cases hac1 : dist ((D.tile e1).pts k1) ((D.tile e1).pts m1) = (u : ℝ) ^ 2 ∨
      dist ((D.tile e1).pts k1) ((D.tile e1).pts m1) = (u : ℝ) * v
  · left; exact ⟨e1, k1, m1, s1, n11, hkm1, hk1, hs1, hm1, hac1, hside1⟩
  by_cases hac2 : dist ((D.tile e2).pts k2) ((D.tile e2).pts m2) = (u : ℝ) ^ 2 ∨
      dist ((D.tile e2).pts k2) ((D.tile e2).pts m2) = (u : ℝ) * v
  · right; exact ⟨e2, k2, m2, s2, n22, hkm2, hk2, hs2, hm2, hac2, hside2⟩
  exfalso
  have hα_e1 : (D.tile e1).localAngle X0 = α := by
    rcases hc1 with h | h | h
    · exact h
    · exact absurd (hlβ1 h) hac1
    · exact absurd (by rw [← S.hγ]; exact h) (hrest.1 e1 n11 n12')
  have hα_e2 : (D.tile e2).localAngle X0 = α := by
    rcases hc2 with h | h | h
    · exact h
    · exact absurd (hlβ2 h) hac2
    · exact absurd (by rw [← S.hγ]; exact h) (hrest.1 e2 n21' n22)
  have he12 : e1 = e2 := by
    by_contra hne
    exact hrest.2 e1 e2 n11 n12' n21' n22 hne hα_e1 hα_e2
  subst he12
  have hb1 : dist ((D.tile e1).pts k1) ((D.tile e1).pts m1) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
    rcases hlα1 hα_e1 with h | h
    · exact h
    · exact absurd (Or.inr h) hac1
  have hb2 : dist ((D.tile e1).pts k2) ((D.tile e1).pts m2) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
    rcases hlα2 hα_e2 with h | h
    · exact h
    · exact absurd (Or.inr h) hac2
  have hkk : k2 = k1 := (D.tile e1).indep.injective (hk2.trans hk1.symm)
  subst hkk
  by_cases hmm : m2 = m1
  · subst hmm
    have hY : AffineMap.lineMap X0 Y1 s1 = AffineMap.lineMap X0 Y2 s2 := hm1.symm.trans hm2
    have a1 : ∠ W X0 (AffineMap.lineMap X0 Y1 s1) = α := by
      rw [angle_ray hs1, angle_comm]; exact hA1
    have a2 : ∠ W X0 (AffineMap.lineMap X0 Y2 s2) = Real.pi - α := by
      rw [angle_ray hs2]
      have hsum := angle_add_angle_eq_pi_of_angle_eq_pi Y2 hπ
      rw [hA2, angle_comm] at hsum
      linarith
    rw [hY] at a1
    linarith [S.hα, Real.pi_pos]
  · have hd := sides_of_b_edgeT D S.tile S.hM e1 hkm2 hkm1 hmm hb2
    rcases hd with ⟨s1', s2'⟩ | ⟨s1', s2'⟩
    · rw [dist_comm] at s1'
      have := S.tile.hab
      rw [hb1] at s1'
      exact this (by linarith)
    · rw [dist_comm] at s1'
      have := S.tile.bc
      rw [hb1] at s1'
      exact this (by linarith)

#print axioms stop_ray_tile
#print axioms alphaalpha_ray_tile
#print axioms rest_facts
end Erdos634.Draft.ThmDRun
