-- Draft/G3RCAngles.lean. No sorry/native_decide/axioms.
-- Generic angle bookkeeping for the 30-60-90 model `((0,2),(-2,0),(0,0))` on the G3CCert lattice
-- (lattice (X,v) <-> real (X, v sqrt3)), used by the real T-junction controls G3RC1/2/4Tiling.
-- Opposite squared sides of the model: 4, 12, 16 (angles pi/6, pi/3, pi/2 at vertices 0,1,2).
import Erdos634.Draft.G3CAng
import Erdos634.Draft.KConjLemmaK

namespace Erdos634.Draft.G3RCAngles

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.FluxPaperWitness

/-- squared (lattice) length of the side opposite to vertex `k` -/
def oppSq (t : LT) (k : Fin 3) : ℤ := d2 (vtx t (k + 1)) (vtx t (k + 2))

theorem oppLen_sq (t : LT) (h : 0 < cross t.1 t.2.1 t.2.2) (k : Fin 3) :
    (triOf t h).oppLen k ^ 2 = (oppSq t k : ℝ) := by
  rw [oppLen_triOf, dist_sq_toPt]; rfl

/-- cos of an angle from the three squared opposite sides -/
theorem cos_opp (T : Tri) (j : Fin 3) (A B C P : ℝ) (hA : T.oppLen j ^ 2 = A)
    (hB : T.oppLen (j + 1) ^ 2 = B) (hC : T.oppLen (j + 2) ^ 2 = C) (hB0 : 0 < B) (hC0 : 0 < C)
    (hP : 0 < P) (hP2 : P ^ 2 = B * C) :
    Real.cos (T.angleAt j) = (B + C - A) / (2 * P) := by
  have s1 : 0 < T.oppLen (j + 1) := by
    have := oppLen_pos T (j + 1)
    rcases this.lt_or_eq with h | h
    · exact h
    · rw [← h] at hB; nlinarith
  have s2 : 0 < T.oppLen (j + 2) := by
    have := oppLen_pos T (j + 2)
    rcases this.lt_or_eq with h | h
    · exact h
    · rw [← h] at hC; nlinarith
  rw [cos_angleAt_opp T j s1 s2]
  have hPe : T.oppLen (j + 1) * T.oppLen (j + 2) = P := by
    have : (T.oppLen (j + 1) * T.oppLen (j + 2)) ^ 2 = P ^ 2 := by rw [mul_pow, hB, hC, hP2]
    exact (pow_left_inj₀ (by positivity) hP.le two_ne_zero).mp this
  rw [hA, hB, hC, ← hPe]
  congr 1; ring

theorem ang_val (T : Tri) (j : Fin 3) (A B C P θ : ℝ) (hA : T.oppLen j ^ 2 = A)
    (hB : T.oppLen (j + 1) ^ 2 = B) (hC : T.oppLen (j + 2) ^ 2 = C) (hB0 : 0 < B) (hC0 : 0 < C)
    (hP : 0 < P) (hP2 : P ^ 2 = B * C) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi)
    (hc : (B + C - A) / (2 * P) = Real.cos θ) : T.angleAt j = θ := by
  have := cos_opp T j A B C P hA hB hC hB0 hC0 hP hP2
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨h0, h1⟩ (this.trans hc)

theorem s3sq' : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

/-- angle π/6 : opposite² 4, others {12,16}. -/
theorem ang_a (T : Tri) (j : Fin 3) (A B C : ℝ) (hA : T.oppLen j ^ 2 = A)
    (hB : T.oppLen (j + 1) ^ 2 = B) (hC : T.oppLen (j + 2) ^ 2 = C)
    (h : A = 4 ∧ ((B = 12 ∧ C = 16) ∨ (B = 16 ∧ C = 12))) : T.angleAt j = Real.pi / 6 := by
  have s := s3pos; have s2 := s3sq'
  obtain ⟨rfl, hbc⟩ := h
  have hpos : 0 < Real.pi := Real.pi_pos
  rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ang_val T j _ _ _ (8 * Real.sqrt 3) _ hA hB hC (by norm_num) (by norm_num) (by positivity)
      (by nlinarith) (by positivity) (by linarith) ?_
    rw [Real.cos_pi_div_six]; field_simp; nlinarith
  · refine ang_val T j _ _ _ (8 * Real.sqrt 3) _ hA hB hC (by norm_num) (by norm_num) (by positivity)
      (by nlinarith) (by positivity) (by linarith) ?_
    rw [Real.cos_pi_div_six]; field_simp; nlinarith

/-- angle π/3 : opposite² 12, others {4,16}. -/
theorem ang_b (T : Tri) (j : Fin 3) (A B C : ℝ) (hA : T.oppLen j ^ 2 = A)
    (hB : T.oppLen (j + 1) ^ 2 = B) (hC : T.oppLen (j + 2) ^ 2 = C)
    (h : A = 12 ∧ ((B = 4 ∧ C = 16) ∨ (B = 16 ∧ C = 4))) : T.angleAt j = Real.pi / 3 := by
  obtain ⟨rfl, hbc⟩ := h
  have hpos : 0 < Real.pi := Real.pi_pos
  rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ang_val T j _ _ _ 8 _ hA hB hC (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by positivity) (by linarith) ?_
    rw [Real.cos_pi_div_three]; norm_num
  · refine ang_val T j _ _ _ 8 _ hA hB hC (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by positivity) (by linarith) ?_
    rw [Real.cos_pi_div_three]; norm_num

/-- angle π/2 : opposite² 16, others {4,12}. -/
theorem ang_c (T : Tri) (j : Fin 3) (A B C : ℝ) (hA : T.oppLen j ^ 2 = A)
    (hB : T.oppLen (j + 1) ^ 2 = B) (hC : T.oppLen (j + 2) ^ 2 = C)
    (h : A = 16 ∧ ((B = 4 ∧ C = 12) ∨ (B = 12 ∧ C = 4))) : T.angleAt j = Real.pi / 2 := by
  have s := s3pos; have s2 := s3sq'
  obtain ⟨rfl, hbc⟩ := h
  have hpos : 0 < Real.pi := Real.pi_pos
  rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ang_val T j _ _ _ (4 * Real.sqrt 3) _ hA hB hC (by norm_num) (by norm_num) (by positivity)
      (by nlinarith) (by positivity) (by linarith) ?_
    rw [Real.cos_pi_div_two]; norm_num
  · refine ang_val T j _ _ _ (4 * Real.sqrt 3) _ hA hB hC (by norm_num) (by norm_num) (by positivity)
      (by nlinarith) (by positivity) (by linarith) ?_
    rw [Real.cos_pi_div_two]; norm_num

/-- the three opposite squared sides of a tile are a permutation of (4,12,16) -/
def goodT (t : LT) : Prop :=
  (oppSq t 0 = 4 ∧ oppSq t 1 = 12 ∧ oppSq t 2 = 16) ∨ (oppSq t 0 = 4 ∧ oppSq t 1 = 16 ∧ oppSq t 2 = 12) ∨
  (oppSq t 0 = 12 ∧ oppSq t 1 = 4 ∧ oppSq t 2 = 16) ∨ (oppSq t 0 = 12 ∧ oppSq t 1 = 16 ∧ oppSq t 2 = 4) ∨
  (oppSq t 0 = 16 ∧ oppSq t 1 = 4 ∧ oppSq t 2 = 12) ∨ (oppSq t 0 = 16 ∧ oppSq t 1 = 12 ∧ oppSq t 2 = 4)

instance (t : LT) : Decidable (goodT t) := by unfold goodT; infer_instance

/-- model-angle index of the corner `v` of a tile: opposite² 4 ↦ 0 (π/6), 12 ↦ 1 (π/3), 16 ↦ 2 (π/2) -/
def midx (t : LT) (v : Fin 3) : Fin 3 := if oppSq t v = 4 then 0 else if oppSq t v = 12 then 1 else 2

theorem tile_angle (t : LT) (h : 0 < cross t.1 t.2.1 t.2.2) (hg : goodT t) (v : Fin 3) :
    (triOf t h).angleAt v = (![1, 2, 3] : Fin 3 → ℕ) (midx t v) * Real.pi / (6 : ℕ) := by
  have oA := oppLen_sq t h v; have oB := oppLen_sq t h (v + 1); have oC := oppLen_sq t h (v + 2)
  unfold goodT at hg
  rcases hg with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;>
  · fin_cases v <;> simp [midx, a, b, c] at oA oB oC ⊢ <;>
    first
    | (have := ang_a (triOf t h) _ _ _ _ oA oB oC (by simp [a, b, c]); linarith)
    | (have := ang_b (triOf t h) _ _ _ _ oA oB oC (by simp [a, b, c]); linarith)
    | (have := ang_c (triOf t h) _ _ _ _ oA oB oC (by simp [a, b, c]); linarith)

end Erdos634.Draft.G3RCAngles
