-- The Beeson III Thm 10 layout (p = 1) for tile (q, q²-1, q²), in the skew frame Φ_q
-- (g1 = (1,0), g2 = u(θ), cos θ = 1/(2q)), as exact skew coordinates (rational functions of q).
--
-- Skew coordinates (b := q²-1):
--   A=(0,0)  B=((3q²-1)b,0)  C=(q²b, -q(2q²-1))      -- target triangle
--   P=(q⁴,0) U=(2q²b,0)      Q=(q²b,-qb)  R=(2q²b,-qb)  W=(q⁴,-qb)
-- Pieces:  T1=A,Q,C  T2=A,Q,P  T3=R,Q,C  (scale q², q⁴ tiles each),  T4=P,W,Q (scale q),
--          T5=B,U,R (scale q²-1),  T6 = Φ[q⁴,2q²b]×[-qb,0] (parallelogram of 2·q(q²-2)·q tiles).
-- For real q ≥ 2: all vertex coordinates; the six regions lie in the target hull;
-- the 15 pairs of regions have disjoint interiors (6 separating lines); non-degeneracy of every piece.
import Erdos634.Draft.S2LCore

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.S2L
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF

def pA : ℝ × ℝ := (0, 0)
def pB (q : ℝ) : ℝ × ℝ := ((3 * q ^ 2 - 1) * (q ^ 2 - 1), 0)
def pC (q : ℝ) : ℝ × ℝ := (q ^ 2 * (q ^ 2 - 1), -(q * (2 * q ^ 2 - 1)))
def pP (q : ℝ) : ℝ × ℝ := (q ^ 4, 0)
def pU (q : ℝ) : ℝ × ℝ := (2 * q ^ 2 * (q ^ 2 - 1), 0)
def pQ (q : ℝ) : ℝ × ℝ := (q ^ 2 * (q ^ 2 - 1), -(q * (q ^ 2 - 1)))
def pR (q : ℝ) : ℝ × ℝ := (2 * q ^ 2 * (q ^ 2 - 1), -(q * (q ^ 2 - 1)))
def pW (q : ℝ) : ℝ × ℝ := (q ^ 4, -(q * (q ^ 2 - 1)))

/-- hulls of the five triangular pieces and the rectangle. -/
def H1 (q : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pA, pQ q, pC q}
def H2 (q : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pA, pQ q, pP q}
def H3 (q : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pR q, pQ q, pC q}
def H4 (q : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pP q, pW q, pQ q}
def H5 (q : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pB q, pU q, pR q}
def H6 (q : ℝ) : Set (ℝ × ℝ) := Rect (q ^ 4) (2 * q ^ 2 * (q ^ 2 - 1)) (-(q * (q ^ 2 - 1))) 0
def HT (q : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pA, pB q, pC q}

section facts
variable {q : ℝ} (hq : 2 ≤ q)
include hq

theorem q_pos : 0 < q := by linarith
theorem q2_ge : 4 ≤ q ^ 2 := by nlinarith
theorem b_pos : 0 < q ^ 2 - 1 := by nlinarith
theorem q4_ge : 16 ≤ q ^ 4 := by nlinarith [q2_ge hq]

/-! ### membership of the vertices in the target hull -/

theorem pP_mem : pP q ∈ HT q := by
  have h := q_pos hq; have h4 := q2_ge hq
  have hb := b_pos hq
  have hd : 0 < (q ^ 2 - 1) * (3 * q ^ 2 - 1) := by nlinarith
  refine mem_hull3' (A := pA) (B := pB q) (C := pC q) ((q ^ 2 - 1) * (3 * q ^ 2 - 1))
    ((q ^ 2 - 1) * (3 * q ^ 2 - 1) - q ^ 4) (q ^ 4) 0 hd (by nlinarith) (by positivity) le_rfl
    (by ring) _ ?_ ?_
  · simp only [pP, pA, pB, pC]; ring
  · simp only [pP, pA, pB, pC]; ring

theorem pU_mem : pU q ∈ HT q := by
  have h := q_pos hq; have h4 := q2_ge hq
  have hb := b_pos hq
  have hd : 0 < 3 * q ^ 2 - 1 := by nlinarith
  refine mem_hull3' (A := pA) (B := pB q) (C := pC q) (3 * q ^ 2 - 1)
    (q ^ 2 - 1) (2 * q ^ 2) 0 hd hb.le (by positivity) le_rfl (by ring) _ ?_ ?_
  · simp only [pU, pA, pB, pC]; ring
  · simp only [pU, pA, pB, pC]; ring

theorem pQ_mem : pQ q ∈ HT q := by
  have h := q_pos hq; have h4 := q2_ge hq
  have hb := b_pos hq
  have hd : 0 < 3 * q ^ 2 - 1 := by nlinarith
  have hd2 : 0 < 2 * q ^ 2 - 1 := by nlinarith
  refine mem_hull3' (A := pA) (B := pB q) (C := pC q) ((2 * q ^ 2 - 1) * (3 * q ^ 2 - 1))
    (q ^ 2 * (2 * q ^ 2 - 1)) (q ^ 4) ((q ^ 2 - 1) * (3 * q ^ 2 - 1)) (by positivity)
    (by positivity) (by positivity) (by positivity) (by ring) _ ?_ ?_
  · simp only [pQ, pA, pB, pC]; ring
  · simp only [pQ, pA, pB, pC]; ring

theorem pR_mem : pR q ∈ HT q := by
  have h := q_pos hq; have h4 := q2_ge hq
  have hb := b_pos hq
  have hd2 : 0 < 2 * q ^ 2 - 1 := by nlinarith
  refine mem_hull3' (A := pA) (B := pB q) (C := pC q) (2 * q ^ 2 - 1) 0 (q ^ 2) (q ^ 2 - 1)
    hd2 le_rfl (by positivity) hb.le (by ring) _ ?_ ?_
  · simp only [pR, pA, pB, pC]; ring
  · simp only [pR, pA, pB, pC]; ring

omit hq in
theorem pA_mem : pA ∈ HT q :=
  subset_convexHull ℝ _ (by simp)
omit hq in
theorem pB_mem : pB q ∈ HT q :=
  subset_convexHull ℝ _ (by simp)
omit hq in
theorem pC_mem : pC q ∈ HT q :=
  subset_convexHull ℝ _ (by simp)

theorem pW_mem : pW q ∈ HT q := by
  have hb := b_pos hq
  have h1 : 1 < q ^ 2 - 1 := by nlinarith [q2_ge hq]
  have := (convex_convexHull ℝ ({pA, pB q, pC q} : Set (ℝ × ℝ))) (pQ_mem hq) (pR_mem hq)
    (a := 1 - 1 / (q ^ 2 - 1)) (b := 1 / (q ^ 2 - 1))
    (by rw [sub_nonneg, div_le_one hb]; exact h1.le) (by positivity) (by ring)
  convert this using 1
  have h := q_pos hq
  ext
  · simp only [pW, pQ, pR, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; field_simp; ring
  · simp only [pW, pQ, pR, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; field_simp; ring

/-! ### containment in the target -/

theorem sub1 : H1 q ⊆ HT q := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  exacts [pA_mem, pQ_mem hq, pC_mem]
theorem sub2 : H2 q ⊆ HT q := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  exacts [pA_mem, pQ_mem hq, pP_mem hq]
theorem sub3 : H3 q ⊆ HT q := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  exacts [pR_mem hq, pQ_mem hq, pC_mem]
theorem sub4 : H4 q ⊆ HT q := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  exacts [pP_mem hq, pW_mem hq, pQ_mem hq]
theorem sub5 : H5 q ⊆ HT q := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  exacts [pB_mem, pU_mem hq, pR_mem hq]
theorem sub6 : H6 q ⊆ HT q := by
  have hb := b_pos hq
  have h := q_pos hq
  have h4 := q2_ge hq
  refine rect_subset (convex_convexHull ℝ _) (by nlinarith) (by nlinarith) ?_ ?_ ?_ ?_
  · exact pW_mem hq
  · exact pR_mem hq
  · exact pP_mem hq
  · exact pU_mem hq

/-! ### separating lines -/


/-! functional `x + q y` (line `A Q`) -/
theorem H1_aq : ∀ p ∈ H1 q, 1 * p.1 + q * p.2 ≤ 0 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_le (A := pA) (B := pQ q) (C := pC q) 1 q 0 (by simp [pA]) (by simp [pQ]; nlinarith)
    (by simp [pC]; nlinarith [pow_pos h 4])
theorem H2_aq : ∀ p ∈ H2 q, 0 ≤ 1 * p.1 + q * p.2 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_ge (A := pA) (B := pQ q) (C := pP q) 1 q 0 (by simp [pA]) (by simp [pQ]; nlinarith)
    (by simp [pP]; positivity)
theorem H4_aq : ∀ p ∈ H4 q, 0 ≤ 1 * p.1 + q * p.2 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_ge (A := pP q) (B := pW q) (C := pQ q) 1 q 0 (by simp [pP]; positivity)
    (by simp [pW]; nlinarith) (by simp [pQ]; nlinarith)
theorem H5_aq : ∀ p ∈ H5 q, 0 ≤ 1 * p.1 + q * p.2 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  have h3 : 0 < 3 * q ^ 2 - 1 := by nlinarith
  exact tri_ge (A := pB q) (B := pU q) (C := pR q) 1 q 0
    (by simp [pB]; positivity) (by simp [pU]; positivity)
    (by simp [pR]; nlinarith [mul_pos (pow_pos h 2) hb])
theorem H6_aq : ∀ p ∈ H6 q, 0 ≤ 1 * p.1 + q * p.2 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  rintro p ⟨a1, a2, a3, a4⟩
  nlinarith [mul_le_mul_of_nonneg_left a3 h.le]

/-! horizontal line `y = -q(q²-1)` -/
theorem H3_y : ∀ p ∈ H3 q, p.2 ≤ -(q * (q ^ 2 - 1)) := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_snd_le (A := pR q) (B := pQ q) (C := pC q) _ (by simp [pR]) (by simp [pQ])
    (by simp [pC]; nlinarith [pow_pos h 3])
theorem H2_y : ∀ p ∈ H2 q, -(q * (q ^ 2 - 1)) ≤ p.2 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_snd_ge (A := pA) (B := pQ q) (C := pP q) _ (by simp [pA]; nlinarith [mul_pos h hb])
    (by simp [pQ]) (by simp [pP]; nlinarith [mul_pos h hb])
theorem H4_y : ∀ p ∈ H4 q, -(q * (q ^ 2 - 1)) ≤ p.2 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_snd_ge (A := pP q) (B := pW q) (C := pQ q) _ (by simp [pP]; nlinarith [mul_pos h hb])
    (by simp [pW]) (by simp [pQ])
theorem H5_y : ∀ p ∈ H5 q, -(q * (q ^ 2 - 1)) ≤ p.2 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_snd_ge (A := pB q) (B := pU q) (C := pR q) _ (by simp [pB]; nlinarith [mul_pos h hb])
    (by simp [pU]; nlinarith [mul_pos h hb]) (by simp [pR])
theorem H6_y : ∀ p ∈ H6 q, -(q * (q ^ 2 - 1)) ≤ p.2 := by
  rintro p ⟨a1, a2, a3, a4⟩; exact a3

/-! vertical line `x = q²(q²-1)` -/
theorem H1_x : ∀ p ∈ H1 q, p.1 ≤ q ^ 2 * (q ^ 2 - 1) := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_fst_le (A := pA) (B := pQ q) (C := pC q) _ (by simp [pA]; nlinarith [mul_pos (pow_pos h 2) hb])
    (by simp [pQ]) (by simp [pC])
theorem H3_x : ∀ p ∈ H3 q, q ^ 2 * (q ^ 2 - 1) ≤ p.1 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_fst_ge (A := pR q) (B := pQ q) (C := pC q) _ (by simp [pR]; nlinarith [mul_pos (pow_pos h 2) hb])
    (by simp [pQ]) (by simp [pC])

/-! line `Q P`: `g = -(q²-1) x + q y`, `g ≥ -q⁴(q²-1)` on `H2`, `≤` on `H4,H5,H6` -/
theorem H2_g : ∀ p ∈ H2 q, -(q ^ 4 * (q ^ 2 - 1)) ≤ (-(q ^ 2 - 1)) * p.1 + q * p.2 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_ge (A := pA) (B := pQ q) (C := pP q) _ _ _ (by simp [pA]; nlinarith [mul_pos (pow_pos h 4) hb])
    (by simp [pQ]; nlinarith) (by simp [pP]; nlinarith)
theorem H4_g : ∀ p ∈ H4 q, (-(q ^ 2 - 1)) * p.1 + q * p.2 ≤ -(q ^ 4 * (q ^ 2 - 1)) := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_le (A := pP q) (B := pW q) (C := pQ q) _ _ _ (by simp [pP]; nlinarith)
    (by simp [pW]; nlinarith [mul_pos (pow_pos h 2) hb]) (by simp [pQ]; nlinarith)
theorem H5_g : ∀ p ∈ H5 q, (-(q ^ 2 - 1)) * p.1 + q * p.2 ≤ -(q ^ 4 * (q ^ 2 - 1)) := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  have hf : 0 ≤ 2 * q ^ 4 - 4 * q ^ 2 + 1 := by nlinarith
  have hq2 : 0 ≤ q ^ 2 - 2 := by nlinarith
  have hq22 : 0 ≤ q ^ 2 * (q ^ 2 - 1) := by positivity
  exact tri_le (A := pB q) (B := pU q) (C := pR q) _ _ _
    (by simp [pB]; nlinarith [mul_nonneg hb.le hf])
    (by simp [pU]; nlinarith [mul_nonneg (mul_nonneg hb.le (sq_nonneg q)) hq2])
    (by simp [pR]; nlinarith [mul_nonneg hb.le hq22])
theorem H6_g : ∀ p ∈ H6 q, (-(q ^ 2 - 1)) * p.1 + q * p.2 ≤ -(q ^ 4 * (q ^ 2 - 1)) := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  rintro p ⟨a1, a2, a3, a4⟩
  nlinarith [mul_le_mul_of_nonneg_left a1 hb.le, mul_nonneg h.le (neg_nonneg.mpr a4)]

/-! vertical lines `x = q⁴`, `x = 2q²(q²-1)` -/
theorem H4_x : ∀ p ∈ H4 q, p.1 ≤ q ^ 4 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_fst_le (A := pP q) (B := pW q) (C := pQ q) _ (by simp [pP]) (by simp [pW])
    (by simp [pQ]; nlinarith)
theorem H5_x : ∀ p ∈ H5 q, q ^ 4 ≤ p.1 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_fst_ge (A := pB q) (B := pU q) (C := pR q) _ (by simp [pB]; nlinarith)
    (by simp [pU]; nlinarith) (by simp [pR]; nlinarith)
theorem H6_x : ∀ p ∈ H6 q, q ^ 4 ≤ p.1 := by
  rintro p ⟨a1, a2, a3, a4⟩; exact a1
theorem H6_x' : ∀ p ∈ H6 q, p.1 ≤ 2 * q ^ 2 * (q ^ 2 - 1) := by
  rintro p ⟨a1, a2, a3, a4⟩; exact a2
theorem H5_x' : ∀ p ∈ H5 q, 2 * q ^ 2 * (q ^ 2 - 1) ≤ p.1 := by
  have h := q_pos hq; have h4 := q2_ge hq; have hb := b_pos hq
  exact tri_fst_ge (A := pB q) (B := pU q) (C := pR q) _ (by simp [pB]; nlinarith [mul_pos hb hb])
    (by simp [pU]) (by simp [pR])

/-! ### the 15 pairs -/
theorem d12 : Disjoint (interior (Phi q '' H1 q)) (interior (Phi q '' H2 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_lin 1 q 0 one_ne_zero (H1_aq hq) (H2_aq hq))
theorem d14 : Disjoint (interior (Phi q '' H1 q)) (interior (Phi q '' H4 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_lin 1 q 0 one_ne_zero (H1_aq hq) (H4_aq hq))
theorem d15 : Disjoint (interior (Phi q '' H1 q)) (interior (Phi q '' H5 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_lin 1 q 0 one_ne_zero (H1_aq hq) (H5_aq hq))
theorem d16 : Disjoint (interior (Phi q '' H1 q)) (interior (Phi q '' H6 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_lin 1 q 0 one_ne_zero (H1_aq hq) (H6_aq hq))
theorem d13 : Disjoint (interior (Phi q '' H1 q)) (interior (Phi q '' H3 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_fst _ (H1_x hq) (H3_x hq))
theorem d32 : Disjoint (interior (Phi q '' H3 q)) (interior (Phi q '' H2 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_snd _ (H3_y hq) (H2_y hq))
theorem d34 : Disjoint (interior (Phi q '' H3 q)) (interior (Phi q '' H4 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_snd _ (H3_y hq) (H4_y hq))
theorem d35 : Disjoint (interior (Phi q '' H3 q)) (interior (Phi q '' H5 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_snd _ (H3_y hq) (H5_y hq))
theorem d36 : Disjoint (interior (Phi q '' H3 q)) (interior (Phi q '' H6 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_snd _ (H3_y hq) (H6_y hq))
theorem d42 : Disjoint (interior (Phi q '' H4 q)) (interior (Phi q '' H2 q)) := by
  have hq1 : 1 < q := by linarith
  have hb := b_pos hq
  exact disjoint_image hq1 (interior_disj_lin (-(q ^ 2 - 1)) q _ (by linarith) (H4_g hq) (H2_g hq))
theorem d52 : Disjoint (interior (Phi q '' H5 q)) (interior (Phi q '' H2 q)) := by
  have hq1 : 1 < q := by linarith
  have hb := b_pos hq
  exact disjoint_image hq1 (interior_disj_lin (-(q ^ 2 - 1)) q _ (by linarith) (H5_g hq) (H2_g hq))
theorem d62 : Disjoint (interior (Phi q '' H6 q)) (interior (Phi q '' H2 q)) := by
  have hq1 : 1 < q := by linarith
  have hb := b_pos hq
  exact disjoint_image hq1 (interior_disj_lin (-(q ^ 2 - 1)) q _ (by linarith) (H6_g hq) (H2_g hq))
theorem d45 : Disjoint (interior (Phi q '' H4 q)) (interior (Phi q '' H5 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_fst _ (H4_x hq) (H5_x hq))
theorem d46 : Disjoint (interior (Phi q '' H4 q)) (interior (Phi q '' H6 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_fst _ (H4_x hq) (H6_x hq))
theorem d65 : Disjoint (interior (Phi q '' H6 q)) (interior (Phi q '' H5 q)) := by
  have hq1 : 1 < q := by linarith
  exact disjoint_image hq1 (interior_disj_fst _ (H6_x' hq) (H5_x' hq))

end facts

end Erdos634.Draft.S2L
