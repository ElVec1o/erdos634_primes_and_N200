import Mathlib.Tactic
import Erdos634.Draft.G3CSixtyControl
import Erdos634.Draft.T30LL3Corner

open scoped Classical

/-!
# The N = 1440 witness for `l3_corner`

On the 1440-tiling `G3CSixtyControl.D` (equilateral target, tile (5,8,7), lattice `(X,v) ↦ (X, v√3)`), at the target corner `O = (0,0)` with the tiles
`T = ((0,0),(26880,0),(8400,8400))`, `T₃ = ((26880,0),(53760,0),(35280,8400))`, `T₄ = ((8400,8400),(35280,8400),(16800,16800))`
(doubled corner, `a = 26880`, `b = 16800`, `c = 23520`; the model with `α, β` swapped), every hypothesis of `l3_corner` is discharged and its conclusion holds.
The word hypothesis for `2c` is false for the tile `(3,5,7)` (`3·3 + 5 = 14`).
-/

namespace Erdos634.C2Forward.Wit

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.G3CSixtyControl
open Erdos634.CertCoord
open Erdos634.Draft.FluxPaperWitness (cornerAngle_mem')
open Erdos634.Draft.G3CEqui60n1440 (cert cert_ok)

theorem sixty_swap {T : Tri} {α a b c : ℝ} (h : T.SixtyData α a b c) :
    T.SixtyData (2 * Real.pi / 3 - α) b a c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have e0 : (σ * Equiv.swap (0 : Fin 3) 1) 0 = σ 1 := by simp [Equiv.Perm.mul_apply]
  have e1 : (σ * Equiv.swap (0 : Fin 3) 1) 1 = σ 0 := by simp [Equiv.Perm.mul_apply]
  have e2 : (σ * Equiv.swap (0 : Fin 3) 1) 2 = σ 2 := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  refine ⟨σ * Equiv.swap 0 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0]; exact h1
  · rw [e0]; exact o1
  · rw [e1, h0]; ring
  · rw [e1]; exact o0
  · rw [e2]; exact h2
  · rw [e2]; exact o2

theorem irr_swap {α : ℝ} (h : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    ¬ ∃ r : ℚ, 2 * Real.pi / 3 - α = (r : ℝ) * Real.pi := by
  rintro ⟨r, hr⟩
  exact h ⟨2 / 3 - r, by push_cast; linarith⟩

theorem angle_pi3 (T : Tri) (j : Fin 3) (s1 s2 s0 : ℕ) (h1 : T.oppLen (j + 1) = s1)
    (h2 : T.oppLen (j + 2) = s2) (h0 : T.oppLen j = s0) (p1 : 0 < s1) (p2 : 0 < s2)
    (hs : (s1 : ℤ) ^ 2 + s2 ^ 2 = s0 ^ 2 + s1 * s2) : T.angleAt j = Real.pi / 3 := by
  have hpi := Real.pi_pos
  have q1 : (0 : ℝ) < s1 := by exact_mod_cast p1
  have q2 : (0 : ℝ) < s2 := by exact_mod_cast p2
  have hc := cos_angleAt_opp T j (by rw [h1]; exact q1) (by rw [h2]; exact q2)
  rw [h1, h2, h0] at hc
  have hsR : (s1 : ℝ) ^ 2 + s2 ^ 2 = s0 ^ 2 + s1 * s2 := by exact_mod_cast hs
  have key : Real.cos (T.angleAt j) = 1 / 2 := by
    rw [hc]; field_simp; linarith
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by positivity, by linarith⟩
    (key.trans Real.cos_pi_div_three.symm)

theorem tile_pi3_zero (t : LT) (ht : t ∈ cert.leaves)
    (h1 : d2 (vtx t 2) (vtx t 0) = (16800 : ℤ) ^ 2) (h2 : d2 (vtx t 0) (vtx t 1) = (26880 : ℤ) ^ 2)
    (h0 : d2 (vtx t 1) (vtx t 2) = (23520 : ℤ) ^ 2) :
    ∃ i : Fin cert.leaves.length, (∀ k, (D.tile i).pts k = toPt (vtx t k)) ∧
      (D.tile i).angleAt 0 = Real.pi / 3 := by
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp ht
  have hp : ∀ k, (D.tile ⟨n, hn⟩).pts k = toPt (vtx cert.leaves[n] k) := fun k =>
    triOf_pts _ (pos_of_mem cert_ok (List.getElem_mem hn)) k
  refine ⟨⟨n, hn⟩, hp, angle_pi3 _ 0 16800 26880 23520 ?_ ?_ ?_ (by norm_num) (by norm_num) (by norm_num)⟩
  · unfold Tri.oppLen; rw [hp, hp]; exact dist_toPt_nat _ _ _ h1
  · unfold Tri.oppLen; rw [hp, hp]; exact dist_toPt_nat _ _ _ h2
  · unfold Tri.oppLen; rw [hp, hp]; exact dist_toPt_nat _ _ _ h0

theorem toPt_sub_smul (p q r s : LP) (c : ℝ) (h1 : (p.1 : ℝ) - q.1 = c * (r.1 - s.1))
    (h2 : (p.2 : ℝ) - q.2 = c * (r.2 - s.2)) : toPt p - toPt q = c • (toPt r - toPt s) := by
  ext i
  fin_cases i
  · simp [toPt, rx, mkPt]; linarith
  · simp [toPt, ry, mkPt]; linear_combination Real.sqrt 3 * h2

theorem tpt (k : Fin 3) : D.target.pts k = toPt (vtx cert.target k) := by
  rw [cd_target cert cert_ok]; exact triOf_pts _ _ k

/-- Word hypothesis for `2c` on the tile `(8,5,7)·3360` (positive). -/
theorem word2 : ∀ x y z : ℕ, (x : ℝ) * (3360 * 8) + y * (3360 * 5) + z * (3360 * 7) = 2 * (3360 * 7) →
    x = 0 ∧ y = 0 ∧ z = 2 := by
  intro x y z h
  have : (8 * x + 5 * y + 7 * z : ℝ) = 14 := by linarith
  have h' : 8 * x + 5 * y + 7 * z = 14 := by exact_mod_cast this
  omega

/-- For the tile `(3,5,7)` the word hypothesis for `2c` fails (`3·3 + 5 = 14`). -/
theorem word2_fails_357 : ¬ ∀ x y z : ℕ, (x : ℝ) * 3 + y * 5 + z * 7 = 2 * 7 → x = 0 ∧ y = 0 ∧ z = 2 := by
  intro h
  have := h 3 1 0 (by norm_num)
  omega


theorem stl {i : Fin cert.leaves.length} {X u : Plane} {x : ℝ} (hX : (D.tile i).pts 0 = X)
    (hang : (D.tile i).angleAt 0 = Real.pi / 3) (hu : (D.tile i).pts (0 + 1) - X = u)
    (hd : dist X ((D.tile i).pts (0 + 1)) = x) : SideTileLen D X u x :=
  ⟨i, 0, hX, hang, Or.inl ⟨by rw [← hu], hd⟩⟩

theorem stl2 {i : Fin cert.leaves.length} {X u : Plane} {x : ℝ} (hX : (D.tile i).pts 0 = X)
    (hang : (D.tile i).angleAt 0 = Real.pi / 3) (hu : (D.tile i).pts (0 + 2) - X = u)
    (hd : dist X ((D.tile i).pts (0 + 2)) = x) : SideTileLen D X u x :=
  ⟨i, 0, hX, hang, Or.inr ⟨by rw [← hu], hd⟩⟩

def t0 : LT := ((0, 0), (26880, 0), (8400, 8400))
def t3 : LT := ((26880, 0), (53760, 0), (35280, 8400))
def t4 : LT := ((8400, 8400), (35280, 8400), (16800, 16800))

theorem t0_mem : t0 ∈ cert.leaves := by decide +kernel
theorem t3_mem : t3 ∈ cert.leaves := by decide +kernel
theorem t4_mem : t4 ∈ cert.leaves := by decide +kernel

theorem a_ne_c : (3360 * 8 : ℝ) ≠ 3360 * 7 := by norm_num

/-- **L3-b closed on a real dissection.**  `l3_corner` applied to `G3CSixtyControl.D` at the corner `(0,0)`: every hypothesis is discharged. -/
theorem l3_witness : ∃ i : Fin cert.leaves.length,
    SideTile D ((D.tile i).pts (0 + 1) + ((D.tile i).pts (0 + 1) - D.target.pts 0))
      ((D.tile i).pts (0 + 1) - D.target.pts 0) (3360 * 8) (3360 * 5) := by
  obtain ⟨i0, hp0, ha0⟩ := tile_pi3_zero t0 t0_mem (by decide) (by decide) (by decide)
  obtain ⟨i3, hp3, ha3⟩ := tile_pi3_zero t3 t3_mem (by decide) (by decide) (by decide)
  obtain ⟨i4, hp4, ha4⟩ := tile_pi3_zero t4 t4_mem (by decide) (by decide) (by decide)
  have hT0 : D.target.pts 0 = toPt (0, 0) := by rw [tpt]; rfl
  have hT1 : D.target.pts 1 = toPt (806400, 0) := by rw [tpt]; rfl
  have hT2 : D.target.pts 2 = toPt (403200, 403200) := by rw [tpt]; rfl
  have hP : (D.tile i0).pts (0 + 1) = toPt (26880, 0) := by rw [hp0]; rfl
  have hQ : (D.tile i0).pts (0 + 2) = toPt (8400, 8400) := by rw [hp0]; rfl
  have hO : (D.tile i0).pts 0 = D.target.pts 0 := by rw [hp0, hT0]; rfl
  refine ⟨i0, l3_corner D (α := 2 * Real.pi / 3 - α) (a := 3360 * 8) (b := 3360 * 5) (c := 3360 * 7)
    (irr_swap α_irr) (sixty_swap data) a_ne_c (by norm_num) (by norm_num) word2 i0 0 0 1 2
    (by decide) (by decide) (by decide) hO ha0 (p := 1 / 30) (r := 1 / 48) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rw [hP, hT1, hT0]; exact toPt_sub_smul _ _ _ _ _ (by norm_num) (by norm_num)
  · rw [hQ, hT2, hT0]; exact toPt_sub_smul _ _ _ _ _ (by norm_num) (by norm_num)
  · rw [hT0, hP]; have := dist_toPt_nat (0, 0) (26880, 0) 26880 (by decide)
    rw [this]; norm_num
  · rw [hT0, hQ]; have := dist_toPt_nat (0, 0) (8400, 8400) 16800 (by decide)
    rw [this]; norm_num
  · rw [hT0, hT1]; have := dist_toPt_nat (0, 0) (806400, 0) 806400 (by decide)
    rw [this]; norm_num
  · rw [hT0, hT2]; have := dist_toPt_nat (0, 0) (403200, 403200) 806400 (by decide)
    rw [this]; norm_num
  · refine stl (hX := ?_) ha3 ?_ ?_
    · rw [hp3, hP]; rfl
    · rw [hp3, hP, hT0]
      show toPt (53760, 0) - toPt (26880, 0) = _
      have := toPt_sub_smul (53760, 0) (26880, 0) (26880, 0) (0, 0) 1 (by norm_num) (by norm_num)
      rw [one_smul] at this; exact this
    · rw [hp3, hP]
      show dist (toPt (26880, 0)) (toPt (53760, 0)) = _
      have := dist_toPt_nat (26880, 0) (53760, 0) 26880 (by decide)
      rw [this]; norm_num
  · refine stl2 (hX := ?_) ha4 ?_ ?_
    · rw [hp4, hQ]; rfl
    · rw [hp4, hQ, hT0]
      show toPt (16800, 16800) - toPt (8400, 8400) = _
      have := toPt_sub_smul (16800, 16800) (8400, 8400) (8400, 8400) (0, 0) 1 (by norm_num) (by norm_num)
      rw [one_smul] at this; exact this
    · rw [hp4, hQ]
      show dist (toPt (8400, 8400)) (toPt (16800, 16800)) = _
      have := dist_toPt_nat (8400, 8400) (16800, 16800) 16800 (by decide)
      rw [this]; norm_num

end Erdos634.C2Forward.Wit

#print axioms Erdos634.C2Forward.Wit.l3_witness
#print axioms Erdos634.C2Forward.Wit.word2_fails_357
