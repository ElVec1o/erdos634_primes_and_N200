/-
Draft/CevianAtomFull.lean -- the cevian atom decomposition for every member `(e, f)` and every `m ≥ 1`.

Tile `(a, b, c) = (ef, f² − e², f²)`; `Δ_m`: base `m e (3f² − e²)`, legs `m f³` (`AddLawFull.DTn`).
On the base take `Q` at distance `f a m = m e f²` from one base corner and `P` at the same distance from the other.
The two cevians from the apex to `Q` and `P` cut `Δ_m` into

* two triangles with sides `f m (a, b, c)` (`WestT`, `EastT`): the tile scaled by `f m`, `(f m)²` tiles each;
* the atom `A_m` (`AtomT`): isosceles, base `m e b`, legs `m f b`, apex angle `α` (`atom_apex`).

The piece `W_m = WestT ∪ AtomT` (`WPiece`) has sides `m e (2f² − e²)`, `m f b`, `m f³` and angles `β`, `α + β`, `2α`
at the base corner, at `P` and at the apex (`W_angle_B`, `W_angle_P`, `W_angle_A`).

`prop_cevianatom`: a dissection of the atom `A_m` into `N_A` copies of the tile gives a dissection of `Δ_m` into
`2 (f m)² + N_A` copies.  `cevian_count`: with `N_A = b m²` the total is `m² (3f² − e²)`.

The member `(1, 2)` is also covered by a different construction (`CVGCevianCutGen.cevian_cut_gen`); this file is the
general member.  Hypotheses witnessed in `CevianAtomWitness.lean` (the certified 48-tile atom `A_4` of `(1, 2)`).
No sorry, no native_decide.
-/
import Erdos634.Draft.AddLawFull
import Erdos634.Draft.G3CAng
import Erdos634.Draft.FDBBaseBetaE1

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.CevianAtomFull

open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WideColFull Erdos634.Draft.AddLawFull
open Erdos634.Draft.FDBBaseBetaE1 (HasSides congruent_of_hasSides)

/-! ## Fans in skew coordinates -/

/-- the triangle with base `[x₁, x₂]` on the first axis and apex `(A, B)` -/
def fan (x₁ x₂ A B : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {(x₁, 0), (x₂, 0), (A, B)}

/-- two cevians from the apex cut the frame triangle into three fans -/
theorem LT_fans (A B q p : ℝ) (hB : 0 < B) (hq : 0 < q) (hqp : q < p) (hpA : p < A) :
    (fan 0 q A B ∪ fan q p A B) ∪ fan p A A B = WBrickF.LT A B := by
  have hA : 0 < A := by linarith
  apply Set.Subset.antisymm
  · have hmem : ∀ x : ℝ, 0 ≤ x → x ≤ A → ((x, 0) : ℝ × ℝ) ∈ WBrickF.LT A B := fun x h0 h1 =>
      ⟨h0, h1, le_refl _, by show (0 : ℝ) * A ≤ x * B; nlinarith [mul_nonneg h0 hB.le]⟩
    have hapex : ((A, B) : ℝ × ℝ) ∈ WBrickF.LT A B :=
      ⟨hA.le, le_refl _, hB.le, by show B * A ≤ A * B; linarith [mul_comm A B]⟩
    have hsub : ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ ≤ A → 0 ≤ x₂ → x₂ ≤ A → fan x₁ x₂ A B ⊆ WBrickF.LT A B := by
      intro x₁ x₂ a1 a2 b1 b2
      refine convexHull_min ?_ (WBrickF.LT_convex A B hA hB)
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · exact hmem x₁ a1 a2
      · exact hmem x₂ b1 b2
      · exact hapex
    rintro v ((hv | hv) | hv)
    · exact hsub 0 q le_rfl hA.le hq.le (by linarith) hv
    · exact hsub q p hq.le (by linarith) (by linarith) hpA.le hv
    · exact hsub p A (by linarith) hpA.le hA.le le_rfl hv
  · rintro ⟨s, t⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    by_cases c1 : (s - q) * B ≤ t * (A - q)
    · left; left
      show (s, t) ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (q, 0), (A, B)} : Set (ℝ × ℝ))
      refine S2L.mem_hull3' (q * B) (t * (A - q) - (s - q) * B) (s * B - t * A) (t * q) (mul_pos hq hB)
        (by linarith) (by linarith) (mul_nonneg h3 hq.le) (by ring) (s, t) ?_ ?_
      · show q * B * s = (t * (A - q) - (s - q) * B) * 0 + (s * B - t * A) * q + t * q * A
        ring
      · show q * B * t = (t * (A - q) - (s - q) * B) * 0 + (s * B - t * A) * 0 + t * q * B
        ring
    · push Not at c1
      by_cases c2 : (s - p) * B ≤ t * (A - p)
      · left; right
        show (s, t) ∈ convexHull ℝ ({(q, (0 : ℝ)), (p, 0), (A, B)} : Set (ℝ × ℝ))
        refine S2L.mem_hull3' ((p - q) * B) (t * (A - p) - (s - p) * B) ((s - q) * B - t * (A - q))
          (t * (p - q)) (mul_pos (by linarith) hB) (by linarith) (by linarith)
          (mul_nonneg h3 (by linarith)) (by ring) (s, t) ?_ ?_
        · show (p - q) * B * s
            = (t * (A - p) - (s - p) * B) * q + ((s - q) * B - t * (A - q)) * p + t * (p - q) * A
          ring
        · show (p - q) * B * t
            = (t * (A - p) - (s - p) * B) * 0 + ((s - q) * B - t * (A - q)) * 0 + t * (p - q) * B
          ring
      · push Not at c2
        right
        show (s, t) ∈ convexHull ℝ ({(p, (0 : ℝ)), (A, 0), (A, B)} : Set (ℝ × ℝ))
        refine S2L.mem_hull3' ((A - p) * B) ((A - s) * B) ((s - p) * B - t * (A - p)) (t * (A - p))
          (mul_pos (by linarith) hB) (mul_nonneg (by linarith) hB.le) (by linarith)
          (mul_nonneg h3 (by linarith)) (by ring) (s, t) ?_ ?_
        · show (A - p) * B * s = (A - s) * B * p + ((s - p) * B - t * (A - p)) * A + t * (A - p) * A
          ring
        · show (A - p) * B * t = (A - s) * B * 0 + ((s - p) * B - t * (A - p)) * 0 + t * (A - p) * B
          ring

/-- a fan with base left of `c` lies on one side of the cevian through `(c, 0)` -/
theorem fan_le (x₁ x₂ A B c : ℝ) (hB : 0 < B) (h1 : x₁ ≤ c) (h2 : x₂ ≤ c) :
    ∀ v ∈ fan x₁ x₂ A B, B * v.1 + (-(A - c)) * v.2 ≤ c * B := by
  refine S2L.tri_le B (-(A - c)) (c * B) ?_ ?_ ?_
  · show B * x₁ + -(A - c) * 0 ≤ c * B
    nlinarith
  · show B * x₂ + -(A - c) * 0 ≤ c * B
    nlinarith
  · show B * A + -(A - c) * B ≤ c * B
    nlinarith

theorem fan_ge (x₁ x₂ A B c : ℝ) (hB : 0 < B) (h1 : c ≤ x₁) (h2 : c ≤ x₂) :
    ∀ v ∈ fan x₁ x₂ A B, c * B ≤ B * v.1 + (-(A - c)) * v.2 := by
  refine S2L.tri_ge B (-(A - c)) (c * B) ?_ ?_ ?_
  · show c * B ≤ B * x₁ + -(A - c) * 0
    nlinarith
  · show c * B ≤ B * x₂ + -(A - c) * 0
    nlinarith
  · show c * B ≤ B * A + -(A - c) * B
    nlinarith

theorem fan_disj1 (A B q p : ℝ) (hB : 0 < B) (hq : 0 < q) (hqp : q < p) :
    Disjoint (interior (fan 0 q A B)) (interior (fan q p A B)) :=
  WBrickF.interior_disj_lin B (-(A - q)) (q * B) hB.ne' (fan_le 0 q A B q hB hq.le le_rfl)
    (fan_ge q p A B q hB le_rfl hqp.le)

theorem fan_disj2 (A B q p : ℝ) (hB : 0 < B) (hq : 0 < q) (hqp : q < p) (hpA : p < A) :
    Disjoint (interior (fan 0 q A B ∪ fan q p A B)) (interior (fan p A A B)) := by
  refine WBrickF.interior_disj_lin B (-(A - p)) (p * B) hB.ne' ?_ (fan_ge p A A B p hB le_rfl hpA.le)
  rintro v (hv | hv)
  · exact fan_le 0 q A B p hB (by linarith) hqp.le v hv
  · exact fan_le q p A B p hB hqp.le le_rfl v hv

/-! ## Fan triangles in a frame -/

noncomputable def fanTri (F : ℝ) (hF : 1 < 4 * F ^ 2) (x₁ x₂ A B : ℝ) (hx : x₁ < x₂) (hB : 0 < B) : Tri :=
  S2G.triC F hF (x₁, 0) (x₂, 0) (A, B) (by
    intro h
    have hp := mul_pos (sub_pos.2 hx) hB
    dsimp only at h
    linarith)

theorem fanTri_pts (F : ℝ) (hF : 1 < 4 * F ^ 2) (x₁ x₂ A B : ℝ) (hx : x₁ < x₂) (hB : 0 < B) :
    (fanTri F hF x₁ x₂ A B hx hB).pts = ![Phi F (x₁, 0), Phi F (x₂, 0), Phi F (A, B)] := by
  simp only [fanTri, S2G.triC_pts]

theorem carrier_fanTri (F : ℝ) (hF : 1 < 4 * F ^ 2) (x₁ x₂ A B : ℝ) (hx : x₁ < x₂) (hB : 0 < B) :
    (fanTri F hF x₁ x₂ A B hx hB).carrier = Phi F '' fan x₁ x₂ A B :=
  S2G.carrier_triC _ _ _ _ _ _

section real

variable {E Fv m : ℝ}

/-- distances in the frame `Phi (Fr E Fv)`, in denominator-free form -/
theorem dist_Fr (he : 0 < E) (hef : E < Fv) (a b : ℝ × ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h : ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) * Fv ^ 3
        - (a.1 - b.1) * (a.2 - b.2) * (E * (3 * Fv ^ 2 - E ^ 2)) = L ^ 2 * Fv ^ 3) :
    dist (Phi (Fr E Fv) a) (Phi (Fr E Fv) b) = L := by
  have hf0 : Fv ≠ 0 := (he.trans hef).ne'
  have hz : ∀ z : ℝ, z / Fr E Fv = -(z * (E * (3 * Fv ^ 2 - E ^ 2)) / Fv ^ 3) := by
    intro z
    unfold Fr
    rw [div_neg, div_div_eq_mul_div]
  refine Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg hL ?_
  refine mul_right_cancel₀ (pow_ne_zero 3 hf0) ?_
  rw [S2G.sq_Phi' (hFr he hef), hz, ← h]
  have h3 : (a.1 - b.1) * (a.2 - b.2) * (E * (3 * Fv ^ 2 - E ^ 2)) / Fv ^ 3 * Fv ^ 3
      = (a.1 - b.1) * (a.2 - b.2) * (E * (3 * Fv ^ 2 - E ^ 2)) := div_mul_cancel₀ _ (pow_ne_zero 3 hf0)
  linear_combination (-1 : ℝ) * h3

/-- the three sides of a fan triangle, from two polynomial identities -/
theorem fanTri_dist (he : 0 < E) (hef : E < Fv) (x₁ x₂ A B : ℝ) (hx : x₁ < x₂) (hB : 0 < B) (L1 L2 : ℝ)
    (h1 : 0 ≤ L1) (h2 : 0 ≤ L2)
    (e1 : ((x₂ - A) ^ 2 + (0 - B) ^ 2) * Fv ^ 3 - (x₂ - A) * (0 - B) * (E * (3 * Fv ^ 2 - E ^ 2))
        = L1 ^ 2 * Fv ^ 3)
    (e2 : ((A - x₁) ^ 2 + (B - 0) ^ 2) * Fv ^ 3 - (A - x₁) * (B - 0) * (E * (3 * Fv ^ 2 - E ^ 2))
        = L2 ^ 2 * Fv ^ 3) :
    dist ((fanTri (Fr E Fv) (hFr he hef) x₁ x₂ A B hx hB).pts 0)
        ((fanTri (Fr E Fv) (hFr he hef) x₁ x₂ A B hx hB).pts 1) = x₂ - x₁ ∧
    dist ((fanTri (Fr E Fv) (hFr he hef) x₁ x₂ A B hx hB).pts 1)
        ((fanTri (Fr E Fv) (hFr he hef) x₁ x₂ A B hx hB).pts 2) = L1 ∧
    dist ((fanTri (Fr E Fv) (hFr he hef) x₁ x₂ A B hx hB).pts 2)
        ((fanTri (Fr E Fv) (hFr he hef) x₁ x₂ A B hx hB).pts 0) = L2 := by
  have hp := fanTri_pts (Fr E Fv) (hFr he hef) x₁ x₂ A B hx hB
  have p0 : (fanTri (Fr E Fv) (hFr he hef) x₁ x₂ A B hx hB).pts 0 = Phi (Fr E Fv) (x₁, 0) := by
    rw [hp]; rfl
  have p1 : (fanTri (Fr E Fv) (hFr he hef) x₁ x₂ A B hx hB).pts 1 = Phi (Fr E Fv) (x₂, 0) := by
    rw [hp]; rfl
  have p2 : (fanTri (Fr E Fv) (hFr he hef) x₁ x₂ A B hx hB).pts 2 = Phi (Fr E Fv) (A, B) := by
    rw [hp]; rfl
  rw [p0, p1, p2]
  exact ⟨dist_Fr he hef (x₁, 0) (x₂, 0) (x₂ - x₁) (sub_pos.2 hx).le (by dsimp only; ring),
    dist_Fr he hef (x₂, 0) (A, B) L1 h1 e1, dist_Fr he hef (A, B) (x₁, 0) L2 h2 e2⟩

/-! ## The four triangles of the cut -/

theorem hb_pos (he : 0 < E) (hef : E < Fv) : 0 < Fv ^ 2 - E ^ 2 := by
  nlinarith [mul_pos (sub_pos.2 hef) (add_pos (he.trans hef) he)]

theorem hq_pos (he : 0 < E) (hef : E < Fv) (hm : 0 < m) : 0 < m * (E * Fv ^ 2) :=
  mul_pos hm (mul_pos he (pow_pos (he.trans hef) 2))

theorem hqp (he : 0 < E) (hef : E < Fv) (hm : 0 < m) :
    m * (E * Fv ^ 2) < m * (E * (2 * Fv ^ 2 - E ^ 2)) :=
  mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (by linarith [hb_pos he hef]) he) hm

theorem hpA (he : 0 < E) (hef : E < Fv) (hm : 0 < m) :
    m * (E * (2 * Fv ^ 2 - E ^ 2)) < m * (E * (3 * Fv ^ 2 - E ^ 2)) :=
  mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (by linarith [pow_pos (he.trans hef) 2]) he) hm

theorem hB_pos (he : 0 < E) (hef : E < Fv) (hm : 0 < m) : 0 < m * Fv ^ 3 :=
  mul_pos hm (pow_pos (he.trans hef) 3)

/-- the scaled tile at the base corner `(0, 0)`: vertices corner, `Q`, apex -/
noncomputable def WestT (E Fv m : ℝ) (he : 0 < E) (hef : E < Fv) (hm : 0 < m) : Tri :=
  fanTri (Fr E Fv) (hFr he hef) 0 (m * (E * Fv ^ 2)) (m * (E * (3 * Fv ^ 2 - E ^ 2))) (m * Fv ^ 3)
    (hq_pos he hef hm) (hB_pos he hef hm)

/-- the atom: vertices `Q`, `P`, apex -/
noncomputable def AtomT (E Fv m : ℝ) (he : 0 < E) (hef : E < Fv) (hm : 0 < m) : Tri :=
  fanTri (Fr E Fv) (hFr he hef) (m * (E * Fv ^ 2)) (m * (E * (2 * Fv ^ 2 - E ^ 2)))
    (m * (E * (3 * Fv ^ 2 - E ^ 2))) (m * Fv ^ 3) (hqp he hef hm) (hB_pos he hef hm)

/-- the scaled tile at the other base corner: vertices `P`, corner, apex -/
noncomputable def EastT (E Fv m : ℝ) (he : 0 < E) (hef : E < Fv) (hm : 0 < m) : Tri :=
  fanTri (Fr E Fv) (hFr he hef) (m * (E * (2 * Fv ^ 2 - E ^ 2))) (m * (E * (3 * Fv ^ 2 - E ^ 2)))
    (m * (E * (3 * Fv ^ 2 - E ^ 2))) (m * Fv ^ 3) (hpA he hef hm) (hB_pos he hef hm)

/-- the piece `W_m`: vertices corner, `P`, apex -/
noncomputable def WPiece (E Fv m : ℝ) (he : 0 < E) (hef : E < Fv) (hm : 0 < m) : Tri :=
  fanTri (Fr E Fv) (hFr he hef) 0 (m * (E * (2 * Fv ^ 2 - E ^ 2))) (m * (E * (3 * Fv ^ 2 - E ^ 2)))
    (m * Fv ^ 3) ((hq_pos he hef hm).trans (hqp he hef hm)) (hB_pos he hef hm)

theorem hfmb (he : 0 < E) (hef : E < Fv) (hm : 0 < m) : 0 ≤ m * (Fv * (Fv ^ 2 - E ^ 2)) :=
  (mul_pos hm (mul_pos (he.trans hef) (hb_pos he hef))).le

/-- sides of `WestT`: `f m a`, `f m b` (the cevian), `f m c` -/
theorem WestT_sides (he : 0 < E) (hef : E < Fv) (hm : 0 < m) :
    dist ((WestT E Fv m he hef hm).pts 0) ((WestT E Fv m he hef hm).pts 1) = m * (E * Fv ^ 2) ∧
    dist ((WestT E Fv m he hef hm).pts 1) ((WestT E Fv m he hef hm).pts 2) = m * (Fv * (Fv ^ 2 - E ^ 2)) ∧
    dist ((WestT E Fv m he hef hm).pts 2) ((WestT E Fv m he hef hm).pts 0) = m * Fv ^ 3 := by
  obtain ⟨a1, a2, a3⟩ := fanTri_dist he hef 0 (m * (E * Fv ^ 2)) (m * (E * (3 * Fv ^ 2 - E ^ 2)))
    (m * Fv ^ 3) (hq_pos he hef hm) (hB_pos he hef hm) (m * (Fv * (Fv ^ 2 - E ^ 2))) (m * Fv ^ 3)
    (hfmb he hef hm) (hB_pos he hef hm).le (by ring) (by ring)
  exact ⟨by rw [← sub_zero (m * (E * Fv ^ 2))]; exact a1, a2, a3⟩

/-- sides of the atom: base `m e b`, legs `m f b` -/
theorem AtomT_sides (he : 0 < E) (hef : E < Fv) (hm : 0 < m) :
    dist ((AtomT E Fv m he hef hm).pts 0) ((AtomT E Fv m he hef hm).pts 1) = m * (E * (Fv ^ 2 - E ^ 2)) ∧
    dist ((AtomT E Fv m he hef hm).pts 1) ((AtomT E Fv m he hef hm).pts 2) = m * (Fv * (Fv ^ 2 - E ^ 2)) ∧
    dist ((AtomT E Fv m he hef hm).pts 2) ((AtomT E Fv m he hef hm).pts 0) = m * (Fv * (Fv ^ 2 - E ^ 2)) := by
  obtain ⟨a1, a2, a3⟩ := fanTri_dist he hef (m * (E * Fv ^ 2)) (m * (E * (2 * Fv ^ 2 - E ^ 2)))
    (m * (E * (3 * Fv ^ 2 - E ^ 2))) (m * Fv ^ 3) (hqp he hef hm) (hB_pos he hef hm)
    (m * (Fv * (Fv ^ 2 - E ^ 2))) (m * (Fv * (Fv ^ 2 - E ^ 2))) (hfmb he hef hm) (hfmb he hef hm)
    (by ring) (by ring)
  refine ⟨?_, a2, a3⟩
  rw [show m * (E * (Fv ^ 2 - E ^ 2)) = m * (E * (2 * Fv ^ 2 - E ^ 2)) - m * (E * Fv ^ 2) by ring]
  exact a1

/-- sides of `EastT`: `f m a`, `f m c`, `f m b` (the cevian) -/
theorem EastT_sides (he : 0 < E) (hef : E < Fv) (hm : 0 < m) :
    dist ((EastT E Fv m he hef hm).pts 0) ((EastT E Fv m he hef hm).pts 1) = m * (E * Fv ^ 2) ∧
    dist ((EastT E Fv m he hef hm).pts 1) ((EastT E Fv m he hef hm).pts 2) = m * Fv ^ 3 ∧
    dist ((EastT E Fv m he hef hm).pts 2) ((EastT E Fv m he hef hm).pts 0) = m * (Fv * (Fv ^ 2 - E ^ 2)) := by
  obtain ⟨a1, a2, a3⟩ := fanTri_dist he hef (m * (E * (2 * Fv ^ 2 - E ^ 2)))
    (m * (E * (3 * Fv ^ 2 - E ^ 2))) (m * (E * (3 * Fv ^ 2 - E ^ 2))) (m * Fv ^ 3) (hpA he hef hm)
    (hB_pos he hef hm) (m * Fv ^ 3) (m * (Fv * (Fv ^ 2 - E ^ 2))) (hB_pos he hef hm).le (hfmb he hef hm)
    (by ring) (by ring)
  refine ⟨?_, a2, a3⟩
  rw [show m * (E * Fv ^ 2) = m * (E * (3 * Fv ^ 2 - E ^ 2)) - m * (E * (2 * Fv ^ 2 - E ^ 2)) by ring]
  exact a1

/-- sides of `W_m`: `m e (2f² − e²)`, `m f b` (the cevian), `m f³` -/
theorem WPiece_sides (he : 0 < E) (hef : E < Fv) (hm : 0 < m) :
    dist ((WPiece E Fv m he hef hm).pts 0) ((WPiece E Fv m he hef hm).pts 1)
      = m * (E * (2 * Fv ^ 2 - E ^ 2)) ∧
    dist ((WPiece E Fv m he hef hm).pts 1) ((WPiece E Fv m he hef hm).pts 2) = m * (Fv * (Fv ^ 2 - E ^ 2)) ∧
    dist ((WPiece E Fv m he hef hm).pts 2) ((WPiece E Fv m he hef hm).pts 0) = m * Fv ^ 3 := by
  obtain ⟨a1, a2, a3⟩ := fanTri_dist he hef 0 (m * (E * (2 * Fv ^ 2 - E ^ 2)))
    (m * (E * (3 * Fv ^ 2 - E ^ 2))) (m * Fv ^ 3) ((hq_pos he hef hm).trans (hqp he hef hm))
    (hB_pos he hef hm) (m * (Fv * (Fv ^ 2 - E ^ 2))) (m * Fv ^ 3) (hfmb he hef hm) (hB_pos he hef hm).le
    (by ring) (by ring)
  exact ⟨by rw [← sub_zero (m * (E * (2 * Fv ^ 2 - E ^ 2)))]; exact a1, a2, a3⟩

/-! ## Angles -/

theorem angle_mem (T : Tri) (j : Fin 3) : 0 ≤ T.angleAt j ∧ T.angleAt j ≤ Real.pi :=
  Erdos634.Draft.FluxPaperWitness.cornerAngle_mem' _ _ _

/-- the law of cosines at the three vertices, from the three side lengths -/
theorem cos_angles (T : Tri) {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h01 : dist (T.pts 0) (T.pts 1) = x) (h12 : dist (T.pts 1) (T.pts 2) = y)
    (h20 : dist (T.pts 2) (T.pts 0) = z) :
    Real.cos (T.angleAt 0) = (z ^ 2 + x ^ 2 - y ^ 2) / (2 * z * x) ∧
    Real.cos (T.angleAt 1) = (x ^ 2 + y ^ 2 - z ^ 2) / (2 * x * y) ∧
    Real.cos (T.angleAt 2) = (y ^ 2 + z ^ 2 - x ^ 2) / (2 * y * z) := by
  have o0 : T.oppLen 0 = y := h12
  have o1 : T.oppLen 1 = z := h20
  have o2 : T.oppLen 2 = x := h01
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  have e02 : (0 : Fin 3) + 2 = 2 := rfl
  have e11 : (1 : Fin 3) + 1 = 2 := rfl
  have e12 : (1 : Fin 3) + 2 = 0 := rfl
  have e21 : (2 : Fin 3) + 1 = 0 := rfl
  have e22 : (2 : Fin 3) + 2 = 1 := rfl
  have c0 := Erdos634.Draft.G3CAng.cos_angleAt_opp T 0 (by rw [e01, o1]; exact hz) (by rw [e02, o2]; exact hx)
  have c1 := Erdos634.Draft.G3CAng.cos_angleAt_opp T 1 (by rw [e11, o2]; exact hx) (by rw [e12, o0]; exact hy)
  have c2 := Erdos634.Draft.G3CAng.cos_angleAt_opp T 2 (by rw [e21, o0]; exact hy) (by rw [e22, o1]; exact hz)
  rw [e01, e02, o0, o1, o2] at c0
  rw [e11, e12, o0, o1, o2] at c1
  rw [e21, e22, o0, o1, o2] at c2
  exact ⟨c0, c1, c2⟩

/-- cosines of the tile: `γ` at `pts 0`, `β` at `pts 1`, `α` at `pts 2` -/
theorem MT_cos (he : 0 < E) (hef : E < Fv) :
    Real.cos ((MT E Fv he hef).angleAt 0) = (-E) / (2 * Fv) ∧
    Real.cos ((MT E Fv he hef).angleAt 1) = E * (3 * Fv ^ 2 - E ^ 2) / (2 * Fv ^ 3) ∧
    Real.cos ((MT E Fv he hef).angleAt 2) = (2 * Fv ^ 2 - E ^ 2) / (2 * Fv ^ 2) := by
  have hf : 0 < Fv := he.trans hef
  have hb := hb_pos he hef
  obtain ⟨s1, s2, s3⟩ := MT_sides he hef
  obtain ⟨c0, c1, c2⟩ := cos_angles (MT E Fv he hef) (mul_pos he hf) (pow_pos hf 2) hb s1 s2 s3
  refine ⟨?_, ?_, ?_⟩
  · rw [c0, div_eq_div_iff (by positivity) (by positivity)]
    ring
  · rw [c1, div_eq_div_iff (by positivity) (by positivity)]
    ring
  · rw [c2, div_eq_div_iff (by positivity) (by positivity)]
    ring

/-- **the apex angle of the atom is the angle `α` of the tile** (opposite its side `a`) -/
theorem atom_apex (he : 0 < E) (hef : E < Fv) (hm : 0 < m) :
    (AtomT E Fv m he hef hm).angleAt 2 = (MT E Fv he hef).angleAt 2 := by
  have hf : 0 < Fv := he.trans hef
  have hb := hb_pos he hef
  obtain ⟨s1, s2, s3⟩ := AtomT_sides he hef hm
  obtain ⟨-, -, c2⟩ := cos_angles (AtomT E Fv m he hef hm) (mul_pos hm (mul_pos he hb))
    (mul_pos hm (mul_pos hf hb)) (mul_pos hm (mul_pos hf hb)) s1 s2 s3
  refine Erdos634.Draft.G3CAng.angle_eq_of_cos 2 2 ?_
  rw [c2, (MT_cos he hef).2.2, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- the angle of `W_m` at the base corner is `β` -/
theorem W_angle_B (he : 0 < E) (hef : E < Fv) (hm : 0 < m) :
    (WPiece E Fv m he hef hm).angleAt 0 = (MT E Fv he hef).angleAt 1 := by
  have hf : 0 < Fv := he.trans hef
  have hb := hb_pos he hef
  have h2 : 0 < 2 * Fv ^ 2 - E ^ 2 := by nlinarith [pow_pos hf 2]
  obtain ⟨s1, s2, s3⟩ := WPiece_sides he hef hm
  obtain ⟨c0, -, -⟩ := cos_angles (WPiece E Fv m he hef hm) (mul_pos hm (mul_pos he h2))
    (mul_pos hm (mul_pos hf hb)) (mul_pos hm (pow_pos hf 3)) s1 s2 s3
  refine Erdos634.Draft.G3CAng.angle_eq_of_cos 0 1 ?_
  rw [c0, (MT_cos he hef).2.1, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- the angle of `W_m` at `P` is `α + β` -/
theorem W_angle_P (he : 0 < E) (hef : E < Fv) (hm : 0 < m) :
    (WPiece E Fv m he hef hm).angleAt 1 = (MT E Fv he hef).angleAt 2 + (MT E Fv he hef).angleAt 1 := by
  have hf : 0 < Fv := he.trans hef
  have hb := hb_pos he hef
  have h2 : 0 < 2 * Fv ^ 2 - E ^ 2 := by nlinarith [pow_pos hf 2]
  obtain ⟨s1, s2, s3⟩ := WPiece_sides he hef hm
  obtain ⟨-, c1, -⟩ := cos_angles (WPiece E Fv m he hef hm) (mul_pos hm (mul_pos he h2))
    (mul_pos hm (mul_pos hf hb)) (mul_pos hm (pow_pos hf 3)) s1 s2 s3
  have hsum := (MT E Fv he hef).angleAt_sum
  have hm0 := angle_mem (MT E Fv he hef) 0
  have hc : Real.cos ((WPiece E Fv m he hef hm).angleAt 1)
      = Real.cos (Real.pi - (MT E Fv he hef).angleAt 0) := by
    rw [Real.cos_pi_sub, (MT_cos he hef).1, c1, ← neg_div, neg_neg,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have h := Real.injOn_cos (angle_mem (WPiece E Fv m he hef hm) 1)
    (⟨by linarith [hm0.2], by linarith [hm0.1]⟩ :
      Real.pi - (MT E Fv he hef).angleAt 0 ∈ Set.Icc 0 Real.pi) hc
  rw [h]
  linarith

/-- the angle of `W_m` at the apex is `2α` -/
theorem W_angle_A (he : 0 < E) (hef : E < Fv) (hm : 0 < m) :
    (WPiece E Fv m he hef hm).angleAt 2 = 2 * (MT E Fv he hef).angleAt 2 := by
  have hf : 0 < Fv := he.trans hef
  have hf0 : Fv ≠ 0 := hf.ne'
  have hb := hb_pos he hef
  have h2 : 0 < 2 * Fv ^ 2 - E ^ 2 := by nlinarith [pow_pos hf 2]
  obtain ⟨s1, s2, s3⟩ := WPiece_sides he hef hm
  obtain ⟨-, -, c2⟩ := cos_angles (WPiece E Fv m he hef hm) (mul_pos hm (mul_pos he h2))
    (mul_pos hm (mul_pos hf hb)) (mul_pos hm (pow_pos hf 3)) s1 s2 s3
  have hα := (MT_cos he hef).2.2
  have hαm := angle_mem (MT E Fv he hef) 2
  have hαpos : 0 < Real.cos ((MT E Fv he hef).angleAt 2) := by
    rw [hα]
    exact div_pos h2 (by positivity)
  have hα2 : (MT E Fv he hef).angleAt 2 ≤ Real.pi / 2 := by
    by_contra hcon
    push Not at hcon
    have := Real.cos_neg_of_pi_div_two_lt_of_lt hcon (by linarith [hαm.2, Real.pi_pos])
    linarith
  have hc : Real.cos ((WPiece E Fv m he hef hm).angleAt 2)
      = Real.cos (2 * (MT E Fv he hef).angleAt 2) := by
    rw [Real.cos_two_mul, hα, c2]
    have e1 : 2 * ((2 * Fv ^ 2 - E ^ 2) / (2 * Fv ^ 2)) ^ 2 - 1
        = (2 * Fv ^ 4 - 4 * E ^ 2 * Fv ^ 2 + E ^ 4) / (2 * Fv ^ 4) := by
      field_simp
      ring
    rw [e1, div_eq_div_iff (by positivity) (by positivity)]
    ring
  exact Real.injOn_cos (angle_mem (WPiece E Fv m he hef hm) 2)
    (⟨by linarith [hαm.1], by linarith⟩ : 2 * (MT E Fv he hef).angleAt 2 ∈ Set.Icc 0 Real.pi) hc

end real

/-! ## The tiling transfer -/

def sw01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

theorem sw01_0 : sw01 0 = 1 := by decide
theorem sw01_1 : sw01 1 = 0 := by decide
theorem sw01_2 : sw01 2 = 2 := by decide

def sw02 : Equiv.Perm (Fin 3) := Equiv.swap 0 2

theorem sw02_0 : sw02 0 = 2 := by decide
theorem sw02_1 : sw02 1 = 1 := by decide
theorem sw02_2 : sw02 2 = 0 := by decide

/-- SSS with the first two vertices of the second triangle exchanged -/
theorem cong_swap01 {T U : Tri} (h01 : dist (T.pts 0) (T.pts 1) = dist (U.pts 1) (U.pts 0))
    (h12 : dist (T.pts 1) (T.pts 2) = dist (U.pts 0) (U.pts 2))
    (h20 : dist (T.pts 2) (T.pts 0) = dist (U.pts 2) (U.pts 1)) : T.Congruent U := by
  refine (Erdos634.SssCongruent.congruent_of_dist_three (U := U.relabel sw01) ?_ ?_ ?_).trans
    (U.congruent_relabel sw01).symm
  · rw [Tri.relabel_pts, Tri.relabel_pts, sw01_0, sw01_1]
    exact h01
  · rw [Tri.relabel_pts, Tri.relabel_pts, sw01_1, sw01_2]
    exact h12
  · rw [Tri.relabel_pts, Tri.relabel_pts, sw01_2, sw01_0]
    exact h20

/-- the atom `A_m` for natural parameters -/
noncomputable def AtomTn (e f m : ℕ) (he : 1 ≤ e) (hef : e < f) (hm : 1 ≤ m) : Tri :=
  AtomT (e : ℝ) (f : ℝ) (m : ℝ) (Nat.cast_pos.2 he) (Nat.cast_lt.2 hef) (Nat.cast_pos.2 hm)

theorem AtomTn_sides (e f m : ℕ) (he : 1 ≤ e) (hef : e < f) (hm : 1 ≤ m) :
    dist ((AtomTn e f m he hef hm).pts 0) ((AtomTn e f m he hef hm).pts 1)
      = (m : ℝ) * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
    dist ((AtomTn e f m he hef hm).pts 1) ((AtomTn e f m he hef hm).pts 2)
      = (m : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
    dist ((AtomTn e f m he hef hm).pts 2) ((AtomTn e f m he hef hm).pts 0)
      = (m : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) :=
  AtomT_sides _ _ _

/-- **Region form.**  A tiling of the atom `A_m` gives a tiling of `Δ_m` with `2 (f m)²` more tiles. -/
theorem cevian_region (e f m : ℕ) (he : 1 ≤ e) (hef : e < f) (hm : 1 ≤ m) {NA : ℕ}
    (RA : RTiling (AtomTn e f m he hef hm).carrier (MTn e f he hef) NA) :
    Nonempty (RTiling (DTn e f m he hef hm).carrier (MTn e f he hef)
      (f * m * (f * m) + NA + f * m * (f * m))) := by
  have heR : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.2 he
  have hefR : (e : ℝ) < (f : ℝ) := Nat.cast_lt.2 hef
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
  have hK : 0 < f * m := Nat.mul_pos (by omega) hm
  have hφ := hFr heR hefR
  obtain ⟨s1, s2, s3⟩ := MTn_sides e f he hef
  obtain ⟨w1, w2, w3⟩ := WestT_sides heR hefR hmR
  obtain ⟨x1, x2, x3⟩ := EastT_sides heR hefR hmR
  have tg : (WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target
      = Erdos634.Subdivision.bigTri _ _ _ (WtoDeltaF.indep_eta (MTn e f he hef)) (f * m) hK := rfl
  have l01 : dist ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 0)
      ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 1)
      = (m : ℝ) * ((e : ℝ) * (f : ℝ) ^ 2) := by
    rw [tg, WtoDeltaF.big_d01, s1]
    push_cast
    ring
  have l12 : dist ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 1)
      ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 2) = (m : ℝ) * (f : ℝ) ^ 3 := by
    rw [tg, WtoDeltaF.big_d12, s2]
    push_cast
    ring
  have l20 : dist ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 2)
      ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target.pts 0)
      = (m : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    rw [tg, WtoDeltaF.big_d20, s3]
    push_cast
    ring
  have cE : ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target).Congruent
      (EastT (e : ℝ) (f : ℝ) (m : ℝ) heR hefR hmR) :=
    Erdos634.SssCongruent.congruent_of_dist_three (by rw [l01, x1]) (by rw [l12, x2]) (by rw [l20, x3])
  have cW : ((WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK).target).Congruent
      (WestT (e : ℝ) (f : ℝ) (m : ℝ) heR hefR hmR) :=
    cong_swap01 (by rw [l01, dist_comm, w1]) (by rw [l12, dist_comm, w3]) (by rw [l20, dist_comm, w2])
  obtain ⟨RW⟩ := WtoDeltaF.seed_of_cd (WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK) _ (MTn e f he hef) cW
    (Tri.Congruent.refl _)
  obtain ⟨RE⟩ := WtoDeltaF.seed_of_cd (WtoDeltaF.ladderCD (MTn e f he hef) (f * m) hK) _ (MTn e f he hef) cE
    (Tri.Congruent.refl _)
  have RW' := RTiling.cast (carrier_fanTri _ _ _ _ _ _ _ _) RW
  have RA' := RTiling.cast (carrier_fanTri (Fr (e : ℝ) (f : ℝ)) hφ ((m : ℝ) * ((e : ℝ) * (f : ℝ) ^ 2))
    ((m : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    ((m : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((m : ℝ) * (f : ℝ) ^ 3)
    (hqp heR hefR hmR) (hB_pos heR hefR hmR)) RA
  have RE' := RTiling.cast (carrier_fanTri _ _ _ _ _ _ _ _) RE
  have d1 := S2G.disjoint_image' hφ (fan_disj1 ((m : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    ((m : ℝ) * (f : ℝ) ^ 3) ((m : ℝ) * ((e : ℝ) * (f : ℝ) ^ 2))
    ((m : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) (hB_pos heR hefR hmR) (hq_pos heR hefR hmR)
    (hqp heR hefR hmR))
  have U1 := union RW' RA' d1
  rw [← Set.image_union] at U1
  have d2 := S2G.disjoint_image' hφ (fan_disj2 ((m : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    ((m : ℝ) * (f : ℝ) ^ 3) ((m : ℝ) * ((e : ℝ) * (f : ℝ) ^ 2))
    ((m : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) (hB_pos heR hefR hmR) (hq_pos heR hefR hmR)
    (hqp heR hefR hmR) (hpA heR hefR hmR))
  have U2 := union U1 RE' d2
  rw [← Set.image_union, LT_fans _ _ _ _ (hB_pos heR hefR hmR) (hq_pos heR hefR hmR) (hqp heR hefR hmR)
    (hpA heR hefR hmR)] at U2
  exact ⟨RTiling.cast (carrier_DT _ _ heR hefR _ hmR).symm U2⟩

/-- **`prop:cevianatom`.**  Let `1 ≤ e < f`, `m ≥ 1`, tile `(a, b, c) = (ef, f² − e², f²)`.  If the atom `A_m`
(legs `m f b`, base `m e b`) is dissected into `N_A` triangles congruent to the tile, then `Δ_m` (base
`m e (3f² − e²)`, legs `m f³`) is dissected into `2 (f m)² + N_A` triangles congruent to the tile.  Triangles are
given by their side lengths in any vertex order, as in the atom theorems of the main paper. -/
theorem prop_cevianatom (e f m : ℕ) (he : 1 ≤ e) (hef : e < f) (hm : 1 ≤ m) {NA : ℕ}
    (D : CongruentDissection NA)
    (hT : HasSides D.target ((m : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((m : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((m : ℝ) * ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))))
    (hM : HasSides D.model ((e : ℝ) * (f : ℝ)) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ D' : CongruentDissection (f * m * (f * m) + NA + f * m * (f * m)),
      D'.target = DTn e f m he hef hm ∧ D'.model = MTn e f he hef := by
  obtain ⟨a1, a2, a3⟩ := AtomTn_sides e f m he hef hm
  obtain ⟨s1, s2, s3⟩ := MTn_sides e f he hef
  have cT : D.target.Congruent (AtomTn e f m he hef hm) := congruent_of_hasSides hT a2 a3 a1
  have cM : D.model.Congruent (MTn e f he hef) := by
    refine (congruent_of_hasSides hM (U := (MTn e f he hef).relabel sw02) ?_ ?_ ?_).trans
      ((MTn e f he hef).congruent_relabel sw02).symm
    · rw [Tri.relabel_pts, Tri.relabel_pts, sw02_1, sw02_2, dist_comm]
      exact s1
    · rw [Tri.relabel_pts, Tri.relabel_pts, sw02_2, sw02_0, dist_comm]
      exact s3
    · rw [Tri.relabel_pts, Tri.relabel_pts, sw02_0, sw02_1, dist_comm]
      exact s2
  obtain ⟨RA⟩ := WtoDeltaF.seed_of_cd D _ _ cT cM
  obtain ⟨U⟩ := cevian_region e f m he hef hm RA
  exact ⟨toCD U, rfl, rfl⟩

/-- the count: two scaled tiles and an atom with `b m²` tiles make `m² N₁` -/
theorem cevian_count (e f m : ℕ) (hef : e < f) :
    f * m * (f * m) + (f ^ 2 - e ^ 2) * m ^ 2 + f * m * (f * m) = m ^ 2 * (3 * f ^ 2 - e ^ 2) := by
  have h1 : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  have h2 : e ^ 2 ≤ 3 * f ^ 2 := by omega
  zify [h1, h2]
  ring

end Erdos634.Draft.CevianAtomFull

#print axioms Erdos634.Draft.CevianAtomFull.atom_apex
#print axioms Erdos634.Draft.CevianAtomFull.W_angle_A
#print axioms Erdos634.Draft.CevianAtomFull.prop_cevianatom
