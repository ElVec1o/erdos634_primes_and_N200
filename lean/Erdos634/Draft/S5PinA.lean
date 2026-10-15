/-
Draft/S5PinA.lean -- helpers for the pinned `c`-tile argument.

Contents: index facts on `Fin 3`; the local angle at a vertex with the other two vertices named in any order;
`localAngle ≤ 2π`; a sum of lengths in `{a, b, c}` as a word; the corner figure `x α + y β + z γ = α + β`;
the bundle `Ctx` of tile data and its first consequences (opposite side ↔ angle); supplementary angles at a
point strictly between two others on a line.

No sorry, no native_decide.
-/
import Erdos634.Draft.TraceCovering
import Erdos634.Draft.GLIWall
import Erdos634.Draft.CornerParaBase
import Erdos634.Draft.LemmaCFigures
import Erdos634.Draft.NearBaseVertex
import Erdos634.GammaTrapLt

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Placement

namespace Erdos634.Draft.S5Pin

variable {N : ℕ}

/-! ## Index facts on `Fin 3` -/

theorem fin3_other : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
    (x + 1 = y ∧ x + 2 = z) ∨ (x + 1 = z ∧ x + 2 = y) := by decide

theorem fin3_cover : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z → ∀ m : Fin 3, m = x ∨ m = y ∨ m = z := by
  decide

theorem fin3_shift : ∀ x : Fin 3, x + 1 + 1 = x + 2 ∧ x + 2 + 1 = x ∧ x + 2 + 2 = x + 1 ∧ x + 1 + 2 = x := by
  decide

theorem fin3_ne : ∀ x : Fin 3, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 := by decide

/-! ## Local angles -/

/-- the local angle at a vertex, the other two vertices named in any order -/
theorem localAngle_three (T : Tri) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    T.localAngle (T.pts i) = cornerAngle (T.pts j) (T.pts i) (T.pts k) := by
  rw [Tri.localAngle_vertex]
  rcases fin3_other i j k hij hik hjk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; unfold cornerAngle; exact EuclideanGeometry.angle_comm _ _ _

theorem localAngle_le_two_pi (T : Tri) (p : Plane) : T.localAngle p ≤ 2 * Real.pi := by
  have hpi := Real.pi_pos
  rcases Erdos634.PinPlumbing.localAngle_cases T p with ⟨j, -, h⟩ | h | h | h
  · rw [h]; unfold cornerAngle
    have := EuclideanGeometry.angle_le_pi (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))
    linarith
  · rw [h]
  · rw [h]; linarith
  · rw [h]; positivity

/-- a point with a positive weight on each of two vertices of an edge is not on another line of the triangle:
its coordinates at the two endpoints are positive -/
theorem coord_openSegment (T : Tri) (m : Fin 3) {x p q : Plane} (hx : x ∈ openSegment ℝ p q) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ s + t = 1 ∧ T.basis.coord m x = s * T.basis.coord m p + t * T.basis.coord m q := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
  refine ⟨s, t, hs, ht, hst, ?_⟩
  have h := Convex.combo_affine_apply (f := T.basis.coord m) (x := p) (y := q) hst
  simpa [smul_eq_mul] using h

/-- a point whose coordinates vanish off `m` is the vertex `m` -/
theorem eq_vertex_of_coords (T : Tri) (y : Plane) (m : Fin 3) (h : ∀ j, j ≠ m → T.basis.coord j y = 0) :
    y = T.pts m := by
  have hsum : ∑ i, T.basis.coord i y = 1 := T.basis.sum_coord_apply_eq_one y
  have hq : ∑ i, T.basis.coord i y • T.pts i = y := T.basis.linear_combination_coord_eq_self y
  rw [Fin.sum_univ_three] at hsum hq
  fin_cases m
  · have h1 := h 1 (by decide); have h2 := h 2 (by decide)
    rw [h1, h2] at hsum hq
    have h0 : T.basis.coord 0 y = 1 := by linarith
    rw [h0] at hq; simpa using hq.symm
  · have h1 := h 0 (by decide); have h2 := h 2 (by decide)
    rw [h1, h2] at hsum hq
    have h0 : T.basis.coord 1 y = 1 := by linarith
    rw [h0] at hq; simpa using hq.symm
  · have h1 := h 0 (by decide); have h2 := h 1 (by decide)
    rw [h1, h2] at hsum hq
    have h0 : T.basis.coord 2 y = 1 := by linarith
    rw [h0] at hq; simpa using hq.symm

/-- an affine functional on the plane, as linear part plus value at the origin -/
theorem aff_apply (A : Plane →ᵃ[ℝ] ℝ) (y : Plane) : A y = A.linear y + A 0 := by
  have := congrFun (AffineMap.decomp A) y
  simpa using this

theorem aff_sub (A : Plane →ᵃ[ℝ] ℝ) (p q : Plane) : A.linear (p - q) = A p - A q := by
  rw [aff_apply A p, aff_apply A q, map_sub]; ring

/-! ## Words -/

/-- a sum of lengths in `{a, b, c}` is a word, with the number of `c`-terms exposed -/
theorem sum_abc {ι : Type*} (S : Finset ι) (len : ι → ℝ) (a b c : ℝ)
    (h : ∀ e ∈ S, len e = a ∨ len e = b ∨ len e = c) :
    ∃ x y : ℕ, x + y + (S.filter (fun e => len e = c)).card = S.card ∧
      ∑ e ∈ S, len e = x * a + y * b + ((S.filter (fun e => len e = c)).card : ℝ) * c := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp, by simp⟩
  | insert e S he ih =>
    obtain ⟨x, y, hcard, hsum⟩ := ih (fun e' he' => h e' (Finset.mem_insert_of_mem he'))
    rw [Finset.sum_insert he, Finset.card_insert_of_notMem he, hsum]
    by_cases hc : len e = c
    · refine ⟨x, y, ?_, ?_⟩
      · rw [Finset.filter_insert, if_pos hc, Finset.card_insert_of_notMem
          (fun hm => he (Finset.mem_filter.mp hm).1)]
        omega
      · rw [Finset.filter_insert, if_pos hc, Finset.card_insert_of_notMem
          (fun hm => he (Finset.mem_filter.mp hm).1), hc]
        push_cast; ring
    · rcases h e (Finset.mem_insert_self e S) with ha | hb | hc'
      · refine ⟨x + 1, y, ?_, ?_⟩
        · rw [Finset.filter_insert, if_neg hc]; omega
        · rw [Finset.filter_insert, if_neg hc, ha]; push_cast; ring
      · refine ⟨x, y + 1, ?_, ?_⟩
        · rw [Finset.filter_insert, if_neg hc]; omega
        · rw [Finset.filter_insert, if_neg hc, hb]; push_cast; ring
      · exact absurd hc' hc

/-! ## The tile data -/

/-- Tile data of the `2π/3`-free family `γ = 2α + β`, `3α + 2β = π`: model angles and sides, and the two word facts
(`a` and `b` are not sums of two or more tile sides). -/
structure Ctx (D : CongruentDissection N) (α β γ a b c : ℝ) : Prop where
  hA : Erdos634.MarchSlots.AngleData α β γ
  hs0 : sideOpp D.model 0 = a
  hs1 : sideOpp D.model 1 = b
  hs2 : sideOpp D.model 2 = c
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α
  hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β
  hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ
  hwa : ∀ x y z : ℕ, a = x * a + y * b + z * c → x + y + z = 1
  hwb : ∀ x y z : ℕ, b = x * a + y * b + z * c → x + y + z = 1

namespace Ctx

variable {D : CongruentDissection N} {α β γ a b c : ℝ} (X : Ctx D α β γ a b c)
include X

theorem scalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m' := by
  intro m m' hmm
  fin_cases m <;> fin_cases m' <;>
    first
    | exact absurd rfl hmm
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]; rw [X.hs0, X.hs1]; exact X.hab)
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]; rw [X.hs0, X.hs2]; exact X.hac)
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]; rw [X.hs1, X.hs0]; exact X.hab.symm)
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]; rw [X.hs1, X.hs2]; exact X.hbc)
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]; rw [X.hs2, X.hs0]; exact X.hac.symm)
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]; rw [X.hs2, X.hs1]; exact X.hbc.symm)

theorem sum_pi : α + β + γ = Real.pi := by
  have h1 := X.hA.hγdef; have h2 := X.hA.hrel; linarith

theorem gpos : 0 < γ := by
  have h1 := X.hA.hγdef; have h2 := X.hA.hα; have h3 := X.hA.hβ; linarith

/-- every tile edge has length `a`, `b` or `c` -/
theorem len_cases (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = a ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = b ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = c := by
  obtain ⟨j, hj⟩ := Erdos634.Geometry.exists_matching_side D i k
  fin_cases j
  · left; rw [hj]; exact X.hs0
  · right; left; rw [hj]; exact X.hs1
  · right; right; rw [hj]; exact X.hs2

/-- **angle at a vertex ↔ opposite side** -/
theorem opp_of_angle (i : Fin N) (j : Fin 3) :
    ((D.tile i).localAngle ((D.tile i).pts j) = α ∧
        dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = a) ∨
    ((D.tile i).localAngle ((D.tile i).pts j) = β ∧
        dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = b) ∨
    ((D.tile i).localAngle ((D.tile i).pts j) = γ ∧
        dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = c) := by
  have hL := Erdos634.CornerPara.localAngle_of_oppSide D X.hab X.hac X.hbc X.hs0 X.hs1 X.hs2 X.hα' X.hβ' X.hγ' i j
  have hc := X.len_cases i (j + 1)
  rw [(fin3_shift j).1] at hc
  rcases hc with h | h | h
  · exact Or.inl ⟨hL.1 h, h⟩
  · exact Or.inr (Or.inl ⟨hL.2.1 h, h⟩)
  · exact Or.inr (Or.inr ⟨hL.2.2 h, h⟩)

/-- the same with the three vertices named -/
theorem opp_of_angle' (i : Fin N) (j k l : Fin 3) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ((D.tile i).localAngle ((D.tile i).pts j) = α ∧ dist ((D.tile i).pts k) ((D.tile i).pts l) = a) ∨
    ((D.tile i).localAngle ((D.tile i).pts j) = β ∧ dist ((D.tile i).pts k) ((D.tile i).pts l) = b) ∨
    ((D.tile i).localAngle ((D.tile i).pts j) = γ ∧ dist ((D.tile i).pts k) ((D.tile i).pts l) = c) := by
  have h := X.opp_of_angle i j
  rcases fin3_other j k l hjk hjl hkl with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at h; exact h
  · rw [h1, h2, dist_comm] at h; exact h

end Ctx

/-! ## The corner figure `α + β` -/

/-- `x α + y β + z γ = α + β` forces `(x, y, z) = (1, 1, 0)` -/
theorem corner_fig_arith {α β γ : ℝ} (hA : Erdos634.MarchSlots.AngleData α β γ) (x y z : ℕ)
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = α + β) : x = 1 ∧ y = 1 ∧ z = 0 := by
  have hpi := Real.pi_pos
  have hγ := hA.hγdef
  have hrel := hA.hrel
  have key : ((2 * (x : ℤ) + z - 3 * y + 1 : ℤ) : ℝ) * α + (((y : ℤ) + z - 1 : ℤ) : ℝ) * Real.pi = 0 := by
    push_cast
    rw [hγ] at h
    have hβ : β = (Real.pi - 3 * α) / 2 := by linarith
    rw [hβ] at h
    linarith
  by_cases hm : (2 * (x : ℤ) + z - 3 * y + 1 : ℤ) = 0
  · rw [hm] at key
    have h2 : (((y : ℤ) + z - 1 : ℤ) : ℝ) = 0 := by
      have : (((y : ℤ) + z - 1 : ℤ) : ℝ) * Real.pi = 0 := by simpa using key
      exact (mul_eq_zero.mp this).resolve_right hpi.ne'
    have h3 : ((y : ℤ) + z - 1 : ℤ) = 0 := by exact_mod_cast h2
    omega
  · exfalso
    apply hA.hirr
    refine ⟨-(((y : ℤ) + z - 1 : ℤ) : ℚ) / ((2 * (x : ℤ) + z - 3 * y + 1 : ℤ) : ℚ), ?_⟩
    have hmR : ((2 * (x : ℤ) + z - 3 * y + 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hm
    push_cast at key hmR ⊢
    rw [div_mul_eq_mul_div, eq_div_iff hmR]
    linarith

/-! ## Supplementary angles -/

/-- If `W` is strictly between `P` and `Q` on a line, the angles `∠ P W G` and `∠ Q W G` are supplementary. -/
theorem supp_angle {P W Q G : Plane} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hPQ : P ≠ Q)
    (hW : W = P + t • (Q - P)) :
    cornerAngle P W G + cornerAngle Q W G = Real.pi := by
  have hS : Sbtw ℝ P W Q := by
    refine ⟨⟨t, ⟨ht0.le, ht1.le⟩, ?_⟩, ?_, ?_⟩
    · rw [hW, AffineMap.lineMap_apply]; simp [add_comm]
    · intro h
      have h1 : t • (Q - P) = 0 := by rw [hW] at h; simpa using h
      rcases smul_eq_zero.mp h1 with h2 | h2
      · exact ht0.ne' h2
      · exact hPQ (sub_eq_zero.mp h2).symm
    · intro h
      have h1 : (1 - t) • (Q - P) = 0 := by
        have : P + t • (Q - P) = Q := by rw [← hW]; exact h
        have h2 : (1 - t) • (Q - P) = Q - (P + t • (Q - P)) := by module
        rw [h2, this, sub_self]
      rcases smul_eq_zero.mp h1 with h2 | h2
      · linarith
      · exact hPQ (sub_eq_zero.mp h2).symm
  have hpi := hS.angle₁₂₃_eq_pi
  have := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi G hpi
  unfold cornerAngle
  rw [EuclideanGeometry.angle_comm P W G, EuclideanGeometry.angle_comm Q W G]
  exact this

end Erdos634.Draft.S5Pin
