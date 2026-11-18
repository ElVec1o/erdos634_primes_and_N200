/-
Draft/WGapCase3c.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 Case 3: "its open part is in int Delta ... contains no interior point of a tile").
Not imported by any aggregate.  Module P-D4: `run_hint_wall`: the open run `(Y, X0)` on `l'_c`, `Y = X0 - m u`, is interior to the target and contains no interior point of a tile, from the near-side tiles `D'(c-1, js+i)`, `i < m`
(their `b`-edges tile the run: `seg_wall`) and the far-side `c`-edge tile `phi0` at `X0` (the midpoint `z` of the first `b`-step is in the relative interior of an edge of BOTH `D'(c-1,js)` and `phi0`: two straight angles,
`interior_of_sum`; the rest by convexity, `openSegment_subset_union`).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapCase3b

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

section case3c

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 2000000 in
theorem run_hint_wall (S : SetupG D e f α β γ L ax ay) {c js m : ℕ} (hc1 : 1 ≤ c) (hm1 : 1 ≤ m)
    (hflip : FlipAt D e f c js)
    (hnear : ∀ i' : ℕ, js ≤ i' → i' < js + m → DTM D (e : ℝ) f 1 0 ((c - 1 : ℕ) : ℝ) (i' : ℝ)) :
    openSegment ℝ (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f c js) (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ)) ⊆
      interior D.target.carrier ∧
    ∀ y ∈ openSegment ℝ (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f c js) (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨O, E1, E2, hm⟩ := mpG_affine he0 hef
  obtain ⟨φ, hφ⟩ := hflip
  set X₀ := mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) with hX₀
  set u := ub e f c js with hu
  have hc1' : ((c - 1 : ℕ) : ℝ) + 1 = (c : ℝ) := by rw [Nat.cast_sub hc1]; simp
  have hpt : ∀ t : ℝ, mpG (e : ℝ) f 1 0 (c : ℝ) ((js : ℝ) + t) = X₀ - t • u := by
    intro t
    rw [hX₀, hu]; unfold ub; simp only [hm]
    ext x; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  -- near tiles in raw form
  have hnr : ∀ i : ℕ, i < m → ∃ t, HasV D t (X₀ - (i : ℝ) • u) (mpG (e : ℝ) f 1 0 ((c : ℝ) - 1) ((js : ℝ) + i + 1))
      (X₀ - ((i : ℝ) + 1) • u) := by
    intro i hi
    obtain ⟨t, ht⟩ := hnear (js + i) (by omega) (by omega)
    refine ⟨t, ?_⟩
    have hcs : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by rw [Nat.cast_sub hc1]; simp
    rw [hcs] at ht
    push_cast at ht
    refine hasV_congr ht ?_ ?_ ?_
    · rw [← hpt]; exact mpG_congr' (by ring) (by ring)
    · exact mpG_congr' rfl (by ring)
    · rw [← hpt]; exact mpG_congr' (by ring) (by ring)
  have hX0t : X₀ ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := hnr 0 (by omega)
    simpa using ht.mem₁
  have hYt : X₀ - (m : ℝ) • u ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := hnr (m - 1) (by omega)
    have := ht.mem₃
    have e1 : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by rw [Nat.cast_sub hm1]; simp
    rwa [e1] at this
  -- the wall
  have hwall : ∀ y ∈ openSegment ℝ (X₀ - (m : ℝ) • u) X₀, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    have hy' : y ∈ openSegment ℝ X₀ (X₀ + (m : ℝ) • (-u)) := by
      rw [openSegment_symm]
      convert hy using 2
      ext x; simp [sub_eq_add_neg]
    obtain ⟨i, hi, hyi⟩ := chord_point_step X₀ (-u) hm1 hy'
    obtain ⟨t, ht⟩ := hnr i hi
    have hseg : y ∈ segment ℝ (X₀ - (i : ℝ) • u) (X₀ - ((i : ℝ) + 1) • u) := by
      convert hyi using 2 <;> (first | (ext x; simp [sub_eq_add_neg]; done) | (ext x; simp [sub_eq_add_neg]; ring))
    obtain ⟨k, m', j', hkm, hkj, hmj, hk, hm', hj'⟩ := ht
    refine seg_wall D.toDissection (t := t) hkj ?_
    rw [hk, hj']; exact hseg
  refine ⟨?_, hwall⟩
  -- the interior point z
  obtain ⟨t0, ht0⟩ := hnr 0 (by omega)
  simp only [Nat.cast_zero, zero_smul, sub_zero, zero_add, one_smul] at ht0
  set z : Plane := X₀ - (1 / 2 : ℝ) • u with hz
  have hzn : z ∈ openSegment ℝ (X₀ - u) X₀ := by
    have := lin_openSeg X₀ u (a := 1) (b := 0) (t := 1 / 2) one_ne_zero (Or.inl ⟨by norm_num, by norm_num⟩)
    rw [hz]; simpa using this
  have hzf : z ∈ openSegment ℝ X₀ (mpG (e : ℝ) f 1 0 (c : ℝ) ((js : ℝ) + 1 / nuG (e : ℝ) f)) := by
    have hν0 := nuG_pos he0 hef
    have hν1 := nuG_lt_one he0 hef
    have := lin_openSeg X₀ u (a := 0) (b := 1 / nuG (e : ℝ) f) (t := 1 / 2)
      (by have := one_div_pos.mpr hν0; linarith) (Or.inr ⟨by norm_num, by rw [lt_div_iff₀ hν0]; linarith⟩)
    rw [hpt, hz]; simpa using this
  have hana : (D.tile t0).localAngle z = Real.pi := hasV_localAngle_pi ht0.rot hzn
  have hanb : (D.tile φ).localAngle z = Real.pi := hasV_localAngle_pi hφ.swap hzf
  have hν0 := nuG_pos he0 hef
  have hne : t0 ≠ φ := by
    obtain ⟨i, hi⟩ := hasV_second ht0
    refine HasV.ne_of_vertex hφ hi ?_ ?_ ?_
    · intro h; obtain ⟨h1, -⟩ := mpG_inj he0 hef h; linarith
    · intro h; obtain ⟨h1, -⟩ := mpG_inj he0 hef h; linarith
    · intro h; obtain ⟨h1, -⟩ := mpG_inj he0 hef h; linarith
  have hC0t : mpG (e : ℝ) f 1 0 (c : ℝ) ((js : ℝ) + 1 / nuG (e : ℝ) f) ∈ D.target.carrier := hφ.mem₃
  have hzt : z ∈ D.target.carrier := D.target.convex.openSegment_subset hX0t hC0t hzf
  have hzint : z ∈ interior D.target.carrier := by
    refine interior_of_sum D.toDissection hzt {t0, φ} ?_
    rw [Finset.sum_pair hne, hana, hanb]
    linarith [Real.pi_pos]
  have hzr : z ∈ range (AffineMap.lineMap (X₀ - (m : ℝ) • u) X₀ : ℝ → Plane) := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    refine ⟨1 - 1 / (2 * m), ?_⟩
    rw [hz, AffineMap.lineMap_apply]
    ext x
    simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    ring
  intro y hy
  rcases openSegment_subset_union _ _ hzr hy with h | h | h
  · rw [h]; exact hzint
  · rw [openSegment_symm] at h
    exact openSeg_interior D.toDissection hzint hYt h
  · exact openSeg_interior D.toDissection hzint hX0t h

end case3c

end Erdos634.Draft.WGapStmt
