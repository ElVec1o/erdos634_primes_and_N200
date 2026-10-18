import Mathlib.Tactic
import Erdos634.Draft.ThmDHalfNear
import Erdos634.Draft.ThmDRunNext
import Erdos634.MarchFlank

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D': the far-side fan at a diagonal vertex, over the lattice  

R-mirror row step (`thmD_lean.md`, fifth agent), vertex layer.  For the lattice of `ThmDRunLattice` and the
diagonal `GST = -lvT s` (the `a`-edges `[lp (ξ+1) η, lp ξ (η+1)]` with `ξ+η+1 = s`):

* `leftHP_iff_GST` — with `u = (-ε) • d`, `d = lp ξ (η+1) - lp (ξ+1) η`, the left half plane of `(p,u)` is `GST ≤ GST p`;
* `vertexfan_T` — at the interior diagonal vertex `p = lp (ξ+1) η`, the two near tiles `U(ξ,η)` and `U(ξ+1,η-1)` cover the
  diagonal near `p` and lie on the near side; any two distinct far-side tiles with prescribed angles at `p` leave a `Fan`;
* `pinfan_ang` — the same at a frontier non-vertex of the target (`APrimeLeg.junction_fan`, in terms of `Ang`).
-/

open scoped Classical
open Metric
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.TilePlacement Erdos634.Draft.SideRun Set
  Erdos634.Draft.ThmDHalf Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N}

theorem cross_smul_left' (k : ℝ) (a b : Plane) : cross (k • a) b = k * cross a b := by
  unfold cross; simp only [PiLp.smul_apply, smul_eq_mul]; ring

/-- `hasV_mem`: the vertices of a tile named by `HasV` lie in its carrier. -/
theorem hasV_mem {t : Fin N} {A B C : Plane} (h : HasV D t A B C) :
    A ∈ (D.tile t).carrier ∧ B ∈ (D.tile t).carrier ∧ C ∈ (D.tile t).carrier := by
  obtain ⟨k, m, j, -, -, -, hk, hm, hj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← hk]; exact subset_convexHull ℝ _ ⟨k, rfl⟩
  · rw [← hm]; exact subset_convexHull ℝ _ ⟨m, rfl⟩
  · rw [← hj]; exact subset_convexHull ℝ _ ⟨j, rfl⟩

/-- Alternative cover hypothesis: the two near tiles may be assigned to the two sides in either order. -/
theorem hcov_of_segments_or {N : ℕ} (D : Dissection N) (p u : Plane) (hu : u ≠ 0) {r0 : ℝ}
    (hr0 : r0 ≤ ‖u‖) (t1 t2 : Fin N)
    (hp1 : p ∈ (D.tile t1).carrier) (hp2 : p ∈ (D.tile t2).carrier)
    (h1 : p + u ∈ (D.tile t1).carrier ∧ p - u ∈ (D.tile t2).carrier ∨
          p + u ∈ (D.tile t2).carrier ∧ p - u ∈ (D.tile t1).carrier)
    (hR1 : (D.tile t1).carrier ⊆ RightHP p u) (hR2 : (D.tile t2).carrier ⊆ RightHP p u) :
    ∀ c : Plane, cross u (c - p) = 0 → c ∈ ball p r0 →
      ∃ j, c ∈ (D.tile j).carrier ∧ (D.tile j).carrier ⊆ RightHP p u := by
  rcases h1 with ⟨a, b⟩ | ⟨a, b⟩
  · exact hcov_of_segments D p u hu hr0 t1 t2 hp1 a hp2 b hR1 hR2
  · exact hcov_of_segments D p u hu hr0 t2 t1 hp2 a hp1 b hR2 hR1

section lat

variable {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- the direction vector of an `a`-edge, oriented from the lower to the upper end -/
noncomputable def dvecT (u v ε x ξ η : ℝ) : Plane := lpT u v ε x ξ (η + 1) - lpT u v ε x (ξ + 1) η

theorem leftHP_iff_GST (hε : ε ^ 2 = 1) (ξ η : ℝ) (p y : Plane) :
    y ∈ LeftHP p ((-ε) • dvecT u v ε x ξ η) ↔ GST u v ε y ≤ GST u v ε p := by
  unfold LeftHP dvecT
  simp only [mem_setOf_eq]
  rw [cross_smul_left', cross_mT hε, map_sub]
  constructor
  · intro h; nlinarith [hε]
  · intro h; nlinarith [hε]

theorem rightHP_iff_GST (hε : ε ^ 2 = 1) (ξ η : ℝ) (p y : Plane) :
    y ∈ RightHP p ((-ε) • dvecT u v ε x ξ η) ↔ GST u v ε p ≤ GST u v ε y := by
  unfold RightHP dvecT
  simp only [mem_setOf_eq]
  rw [cross_smul_left', cross_mT hε, map_sub]
  constructor
  · intro h; nlinarith [hε]
  · intro h; nlinarith [hε]

theorem dvecT_ne (S : SetupT D u v α β γ L ax ay) {ξ η : ℝ} : dvecT (u : ℝ) (v : ℝ) ε x ξ η ≠ 0 := by
  unfold dvecT
  refine sub_ne_zero.mpr (lpT_ne_eta S.u0 S.uv' S.v2 ?_)
  linarith

theorem lp_minus_d {ε x : ℝ} (ξ η : ℝ) :
    lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η - dvecT (u : ℝ) (v : ℝ) ε x ξ η
      = lpT (u : ℝ) (v : ℝ) ε x (ξ + 2) (η - 1) := by
  have h := lp_extT (u : ℝ) (v : ℝ) ε x (ξ + 1) η ξ (η + 1) 1
  have e : lpT (u : ℝ) (v : ℝ) ε x (ξ + 1 + 1 * (ξ + 1 - ξ)) (η + 1 * (η - (η + 1)))
      = lpT (u : ℝ) (v : ℝ) ε x (ξ + 2) (η - 1) := lpT_congr (by ring) (by ring)
  rw [e] at h
  rw [← h]; unfold dvecT; rw [one_smul]; abel

theorem lp_plus_d {ε x : ℝ} (ξ η : ℝ) :
    lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η + dvecT (u : ℝ) (v : ℝ) ε x ξ η
      = lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1) := by
  unfold dvecT; abel

theorem carrier_sub_right {t : Fin N} {A B C : Plane} (hε : ε ^ 2 = 1) (h : HasV D t A B C) (ξ η : ℝ) (p : Plane)
    (hA : GST (u : ℝ) (v : ℝ) ε p ≤ GST (u : ℝ) (v : ℝ) ε A)
    (hB : GST (u : ℝ) (v : ℝ) ε p ≤ GST (u : ℝ) (v : ℝ) ε B)
    (hC : GST (u : ℝ) (v : ℝ) ε p ≤ GST (u : ℝ) (v : ℝ) ε C) :
    (D.tile t).carrier ⊆ RightHP p ((-ε) • dvecT (u : ℝ) (v : ℝ) ε x ξ η) := by
  refine carrier_subset_of_pts (convex_rightHP _ _) _ (fun j => ?_)
  rw [rightHP_iff_GST hε ξ η p]
  exact h.all (P := fun y => GST (u : ℝ) (v : ℝ) ε p ≤ GST (u : ℝ) (v : ℝ) ε y) hA hB hC j

theorem carrier_sub_left {t : Fin N} (hε : ε ^ 2 = 1) (ξ η : ℝ) (p : Plane)
    (h : ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ GST (u : ℝ) (v : ℝ) ε p) :
    (D.tile t).carrier ⊆ LeftHP p ((-ε) • dvecT (u : ℝ) (v : ℝ) ε x ξ η) := by
  refine carrier_subset_of_pts (convex_leftHP _ _) _ (fun j => ?_)
  rw [leftHP_iff_GST hε ξ η p]
  exact h j

/-- **The far-side fan at an interior diagonal vertex.** -/
theorem vertexfan_T (C : CtxBaseT D u v α β γ L ax ay ε x) {ξ η : ℝ}
    (hint : lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η ∈ interior D.target.carrier)
    {n1 n2 tW tE : Fin N}
    (hn1 : HasV D n1 (lpT (u : ℝ) (v : ℝ) ε x ξ η) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)))
    (hn2 : HasV D n2 (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 2) (η - 1))
      (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η))
    (hWL : ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile tW).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1))
    (hEL : ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile tE).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1))
    (hWE : tW ≠ tE) (a a' : Ang)
    (hWa : (D.tile tW).localAngle (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) = angVal α a)
    (hEa : (D.tile tE).localAngle (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) = angVal α a') :
    ∃ m : Cnt, Fan (Cnt.add (Cnt.add a.cnt a'.cnt) m) := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv := S.v2
  have hGp : GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      = -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1) := by
    rw [GST_lp hε]; congr 2; ring
  have hd0 : dvecT (u : ℝ) (v : ℝ) ε x ξ η ≠ 0 := dvecT_ne S
  have hw0 : (-ε) • dvecT (u : ℝ) (v : ℝ) ε x ξ η ≠ 0 :=
    smul_ne_zero (neg_ne_zero.mpr (eps_neT hε)) hd0
  have hwn : 0 < ‖(-ε) • dvecT (u : ℝ) (v : ℝ) ε x ξ η‖ := norm_pos_iff.mpr hw0
  have i11 : GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      ≤ GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x ξ η) := by
    rw [hGp, GST_lp hε]
    have := lvT_le (u := (u : ℝ)) (v := (v : ℝ)) (ε := ε) (x := x) (s := ξ + η) (s' := ξ + η + 1)
      hu huv hv (by linarith)
    linarith
  have i13 : GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      ≤ GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)) := by
    rw [hGp, GST_lp hε]
    have e : ξ + (η + 1) = ξ + η + 1 := by ring
    rw [e]
  have i21 : GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      ≤ GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η - 1)) := by
    rw [hGp, GST_lp hε]
    have := lvT_le (u := (u : ℝ)) (v := (v : ℝ)) (ε := ε) (x := x) (s := ξ + 1 + (η - 1)) (s' := ξ + η + 1)
      hu huv hv (by linarith)
    linarith
  have i22 : GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      ≤ GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x (ξ + 2) (η - 1)) := by
    rw [hGp, GST_lp hε]
    have := lvT_le (u := (u : ℝ)) (v := (v : ℝ)) (ε := ε) (x := x) (s := ξ + 2 + (η - 1)) (s' := ξ + η + 1)
      hu huv hv (by linarith)
    linarith
  have hR1 := carrier_sub_right (u := u) (v := v) (x := x) hε hn1 ξ η
    (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) i11 le_rfl i13
  have hR2 := carrier_sub_right (u := u) (v := v) (x := x) hε hn2 ξ η
    (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) i21 i22 le_rfl
  -- the ball
  obtain ⟨t, htsub, htopen, hpt⟩ := mem_interior.mp hint
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp htopen _ hpt
  have hr0 : 0 < min r ‖(-ε) • dvecT (u : ℝ) (v : ℝ) ε x ξ η‖ := lt_min hr hwn
  have hball : ball (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (min r ‖(-ε) • dvecT (u : ℝ) (v : ℝ) ε x ξ η‖)
      ⊆ D.target.carrier := (ball_subset_ball (min_le_left _ _)).trans (hrsub.trans htsub)
  -- covering
  have hmem1 := hasV_mem hn1
  have hmem2 := hasV_mem hn2
  have hpd := lp_plus_d (u := u) (v := v) (ε := ε) (x := x) ξ η
  have hmd := lp_minus_d (u := u) (v := v) (ε := ε) (x := x) ξ η
  have hcov := hcov_of_segments_or D.toDissection (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
    ((-ε) • dvecT (u : ℝ) (v : ℝ) ε x ξ η) hw0 (r0 := min r ‖(-ε) • dvecT (u : ℝ) (v : ℝ) ε x ξ η‖) (min_le_right _ _) n1 n2 hmem1.2.1 hmem2.2.2
    (by
      rcases C.hε with h | h
      · right
        have hw' : (-ε) • dvecT (u : ℝ) (v : ℝ) ε x ξ η = -dvecT (u : ℝ) (v : ℝ) ε x ξ η := by
          rw [h]; simp
        refine ⟨?_, ?_⟩
        · rw [hw', ← sub_eq_add_neg, hmd]; exact hmem2.2.1
        · rw [hw', sub_neg_eq_add, hpd]; exact hmem1.2.2
      · left
        have hw' : (-ε) • dvecT (u : ℝ) (v : ℝ) ε x ξ η = dvecT (u : ℝ) (v : ℝ) ε x ξ η := by
          rw [h]; simp
        refine ⟨?_, ?_⟩
        · rw [hw', hpd]; exact hmem1.2.2
        · rw [hw', hmd]; exact hmem2.2.1)
    hR1 hR2
  have hWL' := carrier_sub_left (u := u) (v := v) (x := x) (t := tW) hε ξ η (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
    (fun j => by rw [hGp]; exact hWL j)
  have hEL' := carrier_sub_left (u := u) (v := v) (x := x) (t := tE) hε ξ η (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
    (fun j => by rw [hGp]; exact hEL j)
  have hβpos : 0 < β := by
    have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
    have e : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
    rw [e] at h; exact h
  have h3α : 3 * α < Real.pi := by rw [S.hβ] at hβpos; linarith
  exact farside_fan_vertex D.toDissection D.model (fun i => (D.tiles_congruent i).symm) α S.hirr S.hM.hα'
    (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α _ _ hw0 hr0 hball hcov tW tE hWE hWL' hEL' a a' hWa hEa

end lat

/-! ### The fan at a frontier point -/

theorem exists_OE_r (a : Ang) : ∃ e : OE, e.r = a := by
  cases a
  · exact ⟨.bm, rfl⟩
  · exact ⟨.am, rfl⟩
  · exact ⟨.ap, rfl⟩

theorem exists_OE_l (a : Ang) : ∃ e : OE, e.l = a := by
  cases a
  · exact ⟨.bp, rfl⟩
  · exact ⟨.ap, rfl⟩
  · exact ⟨.am, rfl⟩

/-- **Fan at a frontier non-vertex** in terms of `Ang` (`APrimeLeg.junction_fan`). -/
theorem pinfan_ang {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hA1 : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = 2 * α)
    (hα : 0 < α) (h3α : 3 * α < Real.pi) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts)
    (tW tE : Fin N) (hWE : tW ≠ tE) (a a' : Ang)
    (hW : (D.tile tW).localAngle p = angVal α a) (hE : (D.tile tE).localAngle p = angVal α a') :
    ∃ m : Cnt, Fan (Cnt.add (Cnt.add a.cnt a'.cnt) m) := by
  obtain ⟨e, he⟩ := exists_OE_r a
  obtain ⟨e', he'⟩ := exists_OE_l a'
  have := junction_fan D.toDissection D.model (fun i => (D.tiles_congruent i).symm) α hirr hA0 hA1 hA2 hα h3α
    hp hv tW tE hWE e e' (by rw [he]; exact hW) (by rw [he']; exact hE)
  rw [he, he'] at this
  exact this

#print axioms vertexfan_T
#print axioms pinfan_ang
end Erdos634.Draft.ThmDRun
