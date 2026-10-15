import Erdos634.Draft.ColumnLinesGeom
import Erdos634.Draft.UnifyAngles
import Erdos634.Draft.LemCensusFormal
import Erdos634.OrderForcing

/-!
# Cover pieces of a horizontal `a`-edge, and the six tiles at a lattice point

Coordinate facts about the corner lattice `ℤ(a,0) + ℤ·c·u` (`ColumnLinesGeom.lat`).

**Cover pieces.**  Let the horizontal `a`-edge `[P, Q]`, `P = lat k (j+1)`, `Q = lat (k+1) (j+1)`,
lie on the line of row `j + 1`.  A tile below it with that edge has its third vertex (its *foot*)
on the line of row `j`, at distances `{b, c}` from `P` and `Q`:

* `direct_foot` : the foot `lat (k+1) j`, with `|PR| = b`, `|QR| = c`; it is the lattice point at
  `(k+1)a` from the row origin;
* `mirrored_foot` : the foot `mfoot`, with `|PR| = c`, `|QR| = b`, at `ka + 2·c·u_x` from the row
  origin, and `mfoot_abscissa` : `ka + 2·c·u_x = (k+3)a − e³/f`;
* `foot_unique` : these are the only points of the line of row `j` with those distances;
* `mfoot_not_lattice` : for coprime `1 ≤ e < f` the mirrored foot is not a lattice point of the row;
* `mfoot_base_not_int` : at row `1` (`j = 0`) its abscissa on the base is not an integer.

**The six tiles at a lattice point** (`brick_mate_six`): the six lattice triangles around `lat i j`
have at that point the angles `β, α, γ, β, α, γ` (given by their cosines), so the figure is
`{2α, 2β, 2γ}`.

**The charge** (`charge_real`): in a congruent dissection of a base-`β` target, of any size and
with any number of tiles, a junction of figure `{3α, 2β}` forces at least two vertices of figure
`{β, 3γ}`.  This is `LemCensusFormal.lem_census_exact` read at `n₂ ≥ 1`.

Standard axioms, no `sorry`.
-/

open scoped Classical
open Erdos634 Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord
open Erdos634.Draft.ColumnLinesGeom

namespace Erdos634.Draft.MirroredFoot

/-- The mirrored foot under the `a`-edge `[lat k (j+1), lat (k+1) (j+1)]`. -/
noncomputable def mfoot (e f k j : ℝ) : Plane :=
  mkPt (k * (e * f) + (j + 2) * (sideA e f).1) (j * (sideA e f).2)

theorem sq_c {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (sideA e f).1 ^ 2 + (sideA e f).2 ^ 2 = (f ^ 2) ^ 2 := by
  have h := congrArg (fun x : ℝ => x ^ 2) (dist_c_edge he hef)
  simp only at h
  unfold lat at h
  rw [dist_sq_mkPt] at h
  rw [← h]; ring

theorem eq_of_sq' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 = y ^ 2) : x = y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

/-- **The direct foot.** -/
theorem direct_foot {e f : ℝ} (he : 0 < e) (hef : e < f) (k j : ℝ) :
    dist (lat e f k (j + 1)) (lat e f (k + 1) j) = f ^ 2 - e ^ 2 ∧
    dist (lat e f (k + 1) (j + 1)) (lat e f (k + 1) j) = f ^ 2 :=
  ⟨(lattice_triangle he hef k j).2.1, (lattice_triangle he hef (k + 1) j).1⟩

/-- **The mirrored foot**: at distance `c` from the left end and `b` from the right end. -/
theorem mirrored_foot {e f : ℝ} (he : 0 < e) (hef : e < f) (k j : ℝ) :
    dist (lat e f k (j + 1)) (mfoot e f k j) = f ^ 2 ∧
    dist (lat e f (k + 1) (j + 1)) (mfoot e f k j) = f ^ 2 - e ^ 2 ∧
    (mfoot e f k j) 1 = (lat e f 0 j) 1 := by
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hp : (0:ℝ) < f ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · apply eq_of_sq' dist_nonneg hp.le
    unfold lat mfoot
    rw [dist_sq_mkPt, ← sq_c he hef]; ring
  · apply eq_of_sq' dist_nonneg hb.le
    unfold lat mfoot
    rw [dist_sq_mkPt, ← dir_sq he hef]; ring
  · rw [lat_one]; simp [mfoot]

/-- **The feet are the only ones.**  A point `R` on the line of row `j` is determined by its
distances to the two ends of the edge: if `|PR| = c`, `|QR| = b` it is the mirrored foot, and if
`|PR| = b`, `|QR| = c` it is the direct foot. -/
theorem foot_unique {e f : ℝ} (he : 0 < e) (hef : e < f) (k j x : ℝ) :
    (dist (lat e f k (j + 1)) (mkPt x (j * (sideA e f).2)) = f ^ 2 →
      dist (lat e f (k + 1) (j + 1)) (mkPt x (j * (sideA e f).2)) = f ^ 2 - e ^ 2 →
      mkPt x (j * (sideA e f).2) = mfoot e f k j) ∧
    (dist (lat e f k (j + 1)) (mkPt x (j * (sideA e f).2)) = f ^ 2 - e ^ 2 →
      dist (lat e f (k + 1) (j + 1)) (mkPt x (j * (sideA e f).2)) = f ^ 2 →
      mkPt x (j * (sideA e f).2) = lat e f (k + 1) j) := by
  have hf : 0 < f := lt_trans he hef
  have ha : 0 < e * f := mul_pos he hf
  have hc2 := sq_c he hef
  have hb2 := dir_sq he hef
  -- squared distances from the two ends
  have hP : dist (lat e f k (j + 1)) (mkPt x (j * (sideA e f).2)) ^ 2
      = (k * (e * f) + (j + 1) * (sideA e f).1 - x) ^ 2 + (sideA e f).2 ^ 2 := by
    unfold lat; rw [dist_sq_mkPt]; ring
  have hQ : dist (lat e f (k + 1) (j + 1)) (mkPt x (j * (sideA e f).2)) ^ 2
      = ((k + 1) * (e * f) + (j + 1) * (sideA e f).1 - x) ^ 2 + (sideA e f).2 ^ 2 := by
    unfold lat; rw [dist_sq_mkPt]; ring
  constructor
  · intro h1 h2
    rw [h1] at hP; rw [h2] at hQ
    have hx : x = k * (e * f) + (j + 2) * (sideA e f).1 := by
      have h3 : (e * f) * (x - (k * (e * f) + (j + 2) * (sideA e f).1)) = 0 := by
        nlinarith [hP, hQ, hc2, hb2]
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 ha.ne'
      · linarith
    rw [hx]; rfl
  · intro h1 h2
    rw [h1] at hP; rw [h2] at hQ
    have hx : x = (k + 1) * (e * f) + j * (sideA e f).1 := by
      have h3 : (e * f) * (x - ((k + 1) * (e * f) + j * (sideA e f).1)) = 0 := by
        nlinarith [hP, hQ, hc2, hb2]
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 ha.ne'
      · linarith
    rw [hx]; rfl

/-- The abscissa of the mirrored foot from the row origin: `ka + 2·c·u_x = (k+3)a − e³/f`. -/
theorem mfoot_abscissa {e f : ℝ} (he : 0 < e) (hef : e < f) (k j : ℝ) :
    (mfoot e f k j) 0 - (lat e f 0 j) 0 = (k + 3) * (e * f) - e ^ 3 / f := by
  have hf : 0 < f := lt_trans he hef
  rw [lat_zero]
  simp only [mfoot, mkPt_zero]
  unfold sideA baseLen Nq
  field_simp
  ring

/-- **The mirrored foot is not a lattice point** of its row, at a coprime member with `f ≥ 2`. -/
theorem mfoot_not_lattice {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (k i : ℤ) (j : ℝ) :
    mfoot (e : ℝ) f k j ≠ lat (e : ℝ) f i j := by
  have he' : (0:ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hef' : (e:ℝ) < f := by exact_mod_cast hef
  have hf' : (0:ℝ) < f := lt_trans he' hef'
  intro h
  have h0 := congrArg (fun p : Plane => p 0) h
  simp only at h0
  have hab := mfoot_abscissa he' hef' (k:ℝ) j
  rw [h0, lat_zero, lat_zero] at hab
  -- `(i − k − 3)·e·f = −e³/f`, so `(k + 3 − i)·f² = e²`
  have hkey : ((k:ℝ) + 3 - i) * (f:ℝ) ^ 2 = (e:ℝ) ^ 2 := by
    have h1 : ((i:ℝ) - k - 3) * ((e:ℝ) * f) = -((e:ℝ) ^ 3 / f) := by linarith
    have h2 : ((i:ℝ) - k - 3) * ((e:ℝ) * f) * f = -((e:ℝ) ^ 3) := by
      rw [h1]; field_simp
    have h3 : (e:ℝ) * (((k:ℝ) + 3 - i) * (f:ℝ) ^ 2) = (e:ℝ) * (e:ℝ) ^ 2 := by nlinarith
    exact mul_left_cancel₀ he'.ne' h3
  have hZ : (k + 3 - i) * (f:ℤ) ^ 2 = (e:ℤ) ^ 2 := by exact_mod_cast hkey
  have hdvd : ((f * f : ℕ) : ℤ) ∣ ((e * e : ℕ) : ℤ) := ⟨k + 3 - i, by push_cast; linarith⟩
  have hdvdN : f * f ∣ e * e := Int.natCast_dvd_natCast.mp hdvd
  exact (Erdos634.OrderForcing.alpha_vertex_gap_gen (by omega) hco).1 hdvdN

/-- **At row `1` the mirrored foot is on the base at a non-integer abscissa.** -/
theorem mfoot_base_not_int {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (k z : ℤ) :
    (mfoot (e : ℝ) f k 0) 1 = 0 ∧ (mfoot (e : ℝ) f k 0) 0 ≠ (z : ℝ) := by
  have he' : (0:ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hef' : (e:ℝ) < f := by exact_mod_cast hef
  have hf' : (0:ℝ) < f := lt_trans he' hef'
  refine ⟨by simp [mfoot], fun h => ?_⟩
  have hab := mfoot_abscissa he' hef' (k:ℝ) 0
  rw [h, lat_zero] at hab
  -- `e³ = f·((k+3)·e·f − z)`
  have hkey : (e:ℝ) ^ 3 = (f:ℝ) * (((k:ℝ) + 3) * ((e:ℝ) * f) - z) := by
    have h1 : (e:ℝ) ^ 3 / f = ((k:ℝ) + 3) * ((e:ℝ) * f) - z := by linarith
    rw [← h1]; field_simp
  have hZ : (e:ℤ) ^ 3 = (f:ℤ) * ((k + 3) * ((e:ℤ) * f) - z) := by exact_mod_cast hkey
  have hdvd : ((f : ℕ) : ℤ) ∣ ((e * e * e : ℕ) : ℤ) :=
    ⟨(k + 3) * ((e:ℤ) * f) - z, by push_cast; linarith⟩
  have hdvdN : f ∣ e * e * e := Int.natCast_dvd_natCast.mp hdvd
  exact (Erdos634.OrderForcing.alpha_vertex_gap_gen (by omega) hco).2 hdvdN

/-- The case `e = 1` (`lem:charge`): the mirrored foot is `1/f` short of `(k+3)a`. -/
theorem mfoot_abscissa_e1 {f : ℝ} (hf : 1 < f) (k j : ℝ) :
    (mfoot 1 f k j) 0 - (lat 1 f 0 j) 0 = (k + 3) * f - 1 / f := by
  have := mfoot_abscissa (e := 1) one_pos hf k j
  rw [this]; ring

/-! ## The six tiles at a lattice point -/

theorem lat_dist_a {e f : ℝ} (he : 0 < e) (hef : e < f) (i j : ℝ) :
    dist (lat e f i j) (lat e f (i + 1) j) = e * f := dist_a_edge he hef i j

theorem lat_dist_c {e f : ℝ} (he : 0 < e) (hef : e < f) (i j : ℝ) :
    dist (lat e f i j) (lat e f i (j + 1)) = f ^ 2 := by
  rw [dist_comm]; exact (lattice_triangle he hef i j).1

theorem lat_dist_b {e f : ℝ} (he : 0 < e) (hef : e < f) (i j : ℝ) :
    dist (lat e f (i + 1) j) (lat e f i (j + 1)) = f ^ 2 - e ^ 2 := by
  rw [dist_comm]; exact (lattice_triangle he hef i j).2.1

/-- **The six lattice triangles around `O = lat i j`** have at `O`, in counterclockwise order from
the positive horizontal direction, the angles `β, α, γ, β, α, γ` (stated by their cosines). -/
theorem brick_mate_six {e f : ℝ} (he : 0 < e) (hef : e < f) (i j : ℝ) :
    let O := lat e f i j
    let cA := (2 * f ^ 2 - e ^ 2) / (2 * f ^ 2)
    let cB := e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3)
    let cG := -e / (2 * f)
    Real.cos (cornerAngle (lat e f (i + 1) j) O (lat e f i (j + 1))) = cB ∧
    Real.cos (cornerAngle (lat e f (i - 1) (j + 1)) O (lat e f i (j + 1))) = cA ∧
    Real.cos (cornerAngle (lat e f (i - 1) j) O (lat e f (i - 1) (j + 1))) = cG ∧
    Real.cos (cornerAngle (lat e f (i - 1) j) O (lat e f i (j - 1))) = cB ∧
    Real.cos (cornerAngle (lat e f (i + 1) (j - 1)) O (lat e f i (j - 1))) = cA ∧
    Real.cos (cornerAngle (lat e f (i + 1) j) O (lat e f (i + 1) (j - 1))) = cG := by
  intro O cA cB cG
  have a1 : dist (lat e f (i + 1) j) O = e * f := by rw [dist_comm]; exact lat_dist_a he hef i j
  have a2 : dist (lat e f (i - 1) j) O = e * f := by
    have := lat_dist_a he hef (i - 1) j; rwa [sub_add_cancel] at this
  have c1 : dist (lat e f i (j + 1)) O = f ^ 2 := by rw [dist_comm]; exact lat_dist_c he hef i j
  have c2 : dist (lat e f i (j - 1)) O = f ^ 2 := by
    have := lat_dist_c he hef i (j - 1); rwa [sub_add_cancel] at this
  have b1 : dist (lat e f (i - 1) (j + 1)) O = f ^ 2 - e ^ 2 := by
    have := lat_dist_b he hef (i - 1) j; rw [sub_add_cancel] at this
    rw [dist_comm]; exact this
  have b2 : dist (lat e f (i + 1) (j - 1)) O = f ^ 2 - e ^ 2 := by
    have := lat_dist_b he hef i (j - 1); rwa [sub_add_cancel] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Erdos634.Draft.UnifyAngles.cos_beta_general _ _ _ e f he hef a1 c1 (lat_dist_b he hef i j)
  · refine Erdos634.Draft.UnifyAngles.cos_alpha_general _ _ _ e f he hef b1 c1 ?_
    have := lat_dist_a he hef (i - 1) (j + 1); rwa [sub_add_cancel] at this
  · refine Erdos634.Draft.UnifyAngles.cos_gamma_general _ _ _ e f he hef a2 b1 ?_
    exact lat_dist_c he hef (i - 1) j
  · refine Erdos634.Draft.UnifyAngles.cos_beta_general _ _ _ e f he hef a2 c2 ?_
    have := lat_dist_b he hef (i - 1) (j - 1)
    rw [sub_add_cancel, sub_add_cancel] at this
    rw [dist_comm]; exact this
  · refine Erdos634.Draft.UnifyAngles.cos_alpha_general _ _ _ e f he hef b2 c2 ?_
    have := lat_dist_a he hef i (j - 1); rw [dist_comm]; exact this
  · refine Erdos634.Draft.UnifyAngles.cos_gamma_general _ _ _ e f he hef a1 b2 ?_
    have := lat_dist_c he hef (i + 1) (j - 1); rw [sub_add_cancel] at this
    rw [dist_comm]; exact this

/-! ## The charge, for a real dissection -/

open Erdos634.Draft.LemCensusFormal in
/-- **The charge step, at every scale.**  In a congruent dissection of an isosceles
target with base angles `β` (any size, any number of tiles), one junction of figure `{3α, 2β}`
forces at least two vertices of figure `{β, 3γ}`. -/
theorem charge_real {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ}
    (hA : Erdos634.MarchSlots.AngleData α β γ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (a : Fin 3)
    (hb₁ : cornerAngle (D.target.pts (a + 1 + 1)) (D.target.pts (a + 1))
      (D.target.pts (a + 1 + 2)) = β)
    (hb₂ : cornerAngle (D.target.pts (a + 2 + 1)) (D.target.pts (a + 2))
      (D.target.pts (a + 2 + 2)) = β)
    (hn2 : 1 ≤ cnt D α β γ (3, 2, 0)) : 2 ≤ cnt D α β γ (0, 1, 3) := by
  obtain ⟨-, -, -, -, hid, -⟩ := lem_census_exact D hA hmα hmβ hmγ a hb₁ hb₂
  omega

end Erdos634.Draft.MirroredFoot
