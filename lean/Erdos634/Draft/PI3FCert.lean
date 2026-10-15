/-
Draft/PI3FCert.lean -- Theorem T, stage (b): the finite certificate, in the
direction-class setting of `E60VMod3`, together with the PER-EDGE position data of a tile and of the target.

Mathematics.  The certificate of the paper argument uses a type- and level-dependent weight
`f(τ, u, w)`.  Computing the null space of the 216 tile-type constraints over `GZ = ℤ/6 × ℤ/3` shows that the
weight can be taken as the simplest possible one:
```
    F(τ, x)  =  [τ ≠ a] · gV(x),        gV(j, k) = [j = 0] − [j = 3]      (independent of the α-level k)
```
For EVERY tile type `(t, o, x)` (both chiralities, every coset), the three edges of the tile give
`Σ_k F(type of edge k, class of edge k) = coef gV (b) + coef gV (c) = 0`: this is exactly `E60V.coef_bc`, already in the
library (there it served a length-weighted identity).  The boundary value of an equilateral target is `gV(0)+gV(2)+gV(4) = 1`,
carried only by side `0` (`target_side_weight`).

* `rhoBC`, `tile_count_zero`   the per-tile count certificate (a restatement of `coef_bc`);
* `omega_odd`                  the integer direction weight `d ↦ gV(pos d)` is odd;
* `tile_edge_pos`              per-edge: type `t(k+2)` of edge `k` and its direction class `pk o t x k`;
* `target_side_weight`         the weight of target side `j` is `[j = 0]`.
No sorry, no native_decide.
-/
import Erdos634.Draft.E60VMod3
import Erdos634.Draft.PI3FStatement

open scoped Classical

namespace Erdos634.Draft.PI3F

open Erdos634.Geometry Erdos634.Geometry.Row5Hr0 Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.E60Mod9 Erdos634.Draft.CompositeE5Gen Erdos634.Draft.E60V

/-- **The finite certificate (count form).**  For every tile type, the signed count of `{b, c}`-edges vanishes. -/
theorem tile_count_zero : ∀ t : Fin 3 → Fin 3, Function.Injective t → ∀ (o : Bool) (x : GZ),
    ∑ k : Fin 3, rhoBC (t (k + 2)) * gV (pk o t x k) = 0 := by
  intro t ht o x
  have hpt : ∀ (u : Fin 3) (g : ℤ), rhoBC u * g = (if u = 1 then g else 0) + (if u = 2 then g else 0) := by
    intro u g
    fin_cases u <;> simp [rhoBC]
  have : ∑ k : Fin 3, rhoBC (t (k + 2)) * gV (pk o t x k)
      = coef gV t (pk o t x) 1 + coef gV t (pk o t x) 2 := by
    unfold coef
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hpt _ _
  rw [this]
  exact coef_bc t ht o x

/-- The boundary value of the certificate. -/
theorem boundary_value : gV (0, 0) + gV (2, 0) + gV (4, 0) = 1 := gV_boundary

section W

variable (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (anc : Real.Angle)

/-- The integer direction weight `d ↦ gV (pos d)` is odd. -/
theorem omega_odd (d : Dir) :
    gV (pos α hα anc (Dir.neg d).angle) = - gV (pos α hα anc d.angle) := by
  rw [Dir.angle_neg, pos_add α hα anc _ (Gc α hα anc).pi_mem, Lam_pi]
  exact gV_odd _

/-- **Per-edge data of a tile.**  Edge `k` (from `pts k` to `pts (k+1)`) has length `![a,b,c] (t (k+2))` and its
left-hand direction has class `pk o t x k`. -/
theorem tile_edge_pos (T : Tri) {a b c : ℝ} (hS : T.SixtyData α a b c)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L) :
    ∃ t : Fin 3 → Fin 3, Function.Injective t ∧ (∀ k, T.oppLen k = ![a, b, c] (t k)) ∧
      ∃ (o : Bool) (x : GZ), ∀ k : Fin 3, pos α hα anc (T.leftUnit k).angle = pk o t x k := by
  obtain ⟨t, ht, hlen, hext⟩ := tile_type α hα anc T hS h
  refine ⟨t, ht, hlen, ?_⟩
  rcases T.det_pos_or_neg with hT | hT
  · refine ⟨true, pos α hα anc (T.leftUnit 0).angle, fun k => ?_⟩
    have t1 := T.leftUnit_turn_of_pos hT 0
    have t2 := T.leftUnit_turn_of_pos hT 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t1 t2
    have p1 : pos α hα anc (T.leftUnit 1).angle = pos α hα anc (T.leftUnit 0).angle + ext α hα anc T h 1 := by
      rw [t1, pos_add α hα anc _ (T.pi_sub_angleAt_mem (Gc α hα anc) h 1)]; rfl
    have p2 : pos α hα anc (T.leftUnit 2).angle
        = pos α hα anc (T.leftUnit 0).angle + ext α hα anc T h 1 + ext α hα anc T h 2 := by
      rw [t2, pos_add α hα anc _ (T.pi_sub_angleAt_mem (Gc α hα anc) h 2), p1]; rfl
    fin_cases k
    · simp [pk, posP]
    · simp [pk, posP, p1, hext]
    · simp [pk, posP, p2, hext]
  · refine ⟨false, pos α hα anc (T.leftUnit 2).angle, fun k => ?_⟩
    have t0 := T.leftUnit_turn_of_neg hT 0
    have t1 := T.leftUnit_turn_of_neg hT 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t0 t1
    have p1 : pos α hα anc (T.leftUnit 1).angle = pos α hα anc (T.leftUnit 2).angle + ext α hα anc T h 2 := by
      rw [t1, pos_add α hα anc _ (T.pi_sub_angleAt_mem (Gc α hα anc) h 2)]; rfl
    have p0 : pos α hα anc (T.leftUnit 0).angle
        = pos α hα anc (T.leftUnit 2).angle + ext α hα anc T h 2 + ext α hα anc T h 1 := by
      rw [t0, pos_add α hα anc _ (T.pi_sub_angleAt_mem (Gc α hα anc) h 1), p1]; rfl
    fin_cases k
    · simp [pk, posM, p0, hext]
    · simp [pk, posM, p1, hext]
    · simp [pk, posM]

end W

/-- **The weight of the target sides.**  Anchored at the direction of side `0`, the class weight of the left-hand direction
of target side `j` is `[j = 0]` (the two other sides carry classes `2` and `4`). -/
theorem target_side_weight {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (j : Fin 3) :
    gV (pos α hα (D.target.leftUnit 0).angle (D.target.leftUnit j).angle) = if j = 0 then 1 else 0 := by
  set anc := (D.target.leftUnit 0).angle with hanc
  have e3 : Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α := by push_cast; ring
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L := by
    intro k; rw [hP k, e3]; exact wAt_mem _ _ _ _ _ _
  have hext : ∀ k, ext α hα anc D.target htarget k = (2, 0) := by
    intro k
    unfold ext
    have := Lam_of_eq α hα anc (Real.pi - D.target.angleAt k) 2 0
      (by rw [hP k]; push_cast; ring) (D.target.pi_sub_angleAt_mem (Gc α hα anc) htarget k)
    rw [this]; decide
  have h0 : pos α hα anc (D.target.leftUnit 0).angle = 0 := pos_anchor α hα anc
  rcases D.target.det_pos_or_neg with hT | hT
  · have t1 := D.target.leftUnit_turn_of_pos hT 0
    have t2 := D.target.leftUnit_turn_of_pos hT 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t1 t2
    have p1 : pos α hα anc (D.target.leftUnit 1).angle
        = pos α hα anc (D.target.leftUnit 0).angle + ext α hα anc D.target htarget 1 := by
      rw [t1, pos_add α hα anc _ (D.target.pi_sub_angleAt_mem (Gc α hα anc) htarget 1)]; rfl
    have p2 : pos α hα anc (D.target.leftUnit 2).angle
        = pos α hα anc (D.target.leftUnit 0).angle + ext α hα anc D.target htarget 1
          + ext α hα anc D.target htarget 2 := by
      rw [t2, pos_add α hα anc _ (D.target.pi_sub_angleAt_mem (Gc α hα anc) htarget 2), p1]; rfl
    fin_cases j
    · simp only [Fin.zero_eta, if_true]; rw [h0]; decide
    · simp only [Fin.mk_one]
      rw [p1, h0, hext 1]; decide
    · simp only [Fin.reduceFinMk]
      rw [p2, h0, hext 1, hext 2]; decide
  · have hrel := pos_rel_neg α hα anc D.target hT htarget
    rw [h0, hext 1, hext 2] at hrel
    have hy : pos α hα anc (D.target.leftUnit 2).angle = (2, 0) := by
      revert hrel
      generalize pos α hα anc (D.target.leftUnit 2).angle = y
      revert y
      decide
    have t1 := D.target.leftUnit_turn_of_neg hT 1
    simp only [show (1:Fin 3) + 1 = 2 from rfl] at t1
    have p1 : pos α hα anc (D.target.leftUnit 1).angle
        = pos α hα anc (D.target.leftUnit 2).angle + ext α hα anc D.target htarget 2 := by
      rw [t1, pos_add α hα anc _ (D.target.pi_sub_angleAt_mem (Gc α hα anc) htarget 2)]; rfl
    fin_cases j
    · simp only [Fin.zero_eta, if_true]; rw [h0]; decide
    · simp only [Fin.mk_one]
      rw [p1, hy, hext 2]; decide
    · simp only [Fin.reduceFinMk]
      rw [hy]; decide

end Erdos634.Draft.PI3F

#print axioms Erdos634.Draft.PI3F.tile_count_zero
#print axioms Erdos634.Draft.PI3F.omega_odd
#print axioms Erdos634.Draft.PI3F.tile_edge_pos
#print axioms Erdos634.Draft.PI3F.target_side_weight
