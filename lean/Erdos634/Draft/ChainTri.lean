-- Draft/ChainTri.lean -- CHAIN LEMMA, part 2: for a strictly counter-clockwise triangle the crossing sum `kapTri` is a {0,1}-valued
-- function, equal to 1 on the open triangle and 0 outside the closed triangle (every z, no genericity).  UNAUDITED.  No sorry.
-- Credit: Ramanujan-rows session (chain lemma), the AI assistant (frame), Beeson-Rosu, Paliy.
import Erdos634.Draft.ChainKap

open scoped Classical
namespace Erdos634.Draft.Chain

noncomputable def kapTri (a b c z : ℝ × ℝ) : ℤ := kap a b z + kap b c z + kap c a z

theorem kapTri_rot (a b c z : ℝ × ℝ) : kapTri b c a z = kapTri a b c z := by unfold kapTri; ring

theorem crs_rot (a b c : ℝ × ℝ) : crs b c a = crs a b c := by unfold crs; ring

/-- the three edge crosses sum to the area form -/
theorem crs_sum (a b c z : ℝ × ℝ) : crs a b z + crs b c z + crs c a z = crs a b c := by unfold crs; ring

/-- barycentric identity for the height -/
theorem bary_y (a b c z : ℝ × ℝ) :
    crs a b c * z.2 = crs b c z * a.2 + crs c a z * b.2 + crs a b z * c.2 := by unfold crs; ring

/-- height identities -/
theorem idy (a b c z : ℝ × ℝ) :
    (c.2 - a.2) * crs a b z + (b.2 - a.2) * crs c a z = (z.2 - a.2) * crs a b c := by unfold crs; ring

theorem idy2 (a b c z : ℝ × ℝ) :
    (z.2 - a.2) * crs b c z = crs c a z * (b.2 - z.2) + crs a b z * (c.2 - z.2) := by unfold crs; ring

/-- The conclusion shape shared by all cases. -/
def TriGood (a b c z : ℝ × ℝ) : Prop :=
  (0 ≤ kapTri a b c z ∧ kapTri a b c z ≤ 1) ∧
  (0 < crs a b z → 0 < crs b c z → 0 < crs c a z → kapTri a b c z = 1) ∧
  (kapTri a b c z ≠ 0 → 0 ≤ crs a b z ∧ 0 ≤ crs b c z ∧ 0 ≤ crs c a z)

theorem TriGood_rot {a b c z : ℝ × ℝ} (h : TriGood b c a z) : TriGood a b c z := by
  unfold TriGood at *
  rw [kapTri_rot] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun x y w => h2 y w x, fun hn => ?_⟩
  obtain ⟨u, v, w⟩ := h3 hn
  exact ⟨w, u, v⟩

/-- pattern: `a` weakly below, `b`, `c` strictly above the line of `z`. -/
theorem triA (a b c z : ℝ × ℝ) (hD : 0 < crs a b c) (ha : a.2 ≤ z.2) (hb : z.2 < b.2) (hc : z.2 < c.2) :
    TriGood a b c z := by
  have p1 : 0 < b.2 - a.2 := by linarith
  have p2 : a.2 - c.2 < 0 := by linarith
  have k1 : kap a b z = if 0 < crs a b z then 1 else 0 := by
    have : (0 < (b.2 - a.2) * crs a b z) ↔ 0 < crs a b z := mul_pos_iff_of_pos_left p1
    unfold kap; simp only [this, low, ha, if_true, not_le.2 hb]; simp
  have k2 : kap b c z = 0 := kap_zero_of_low (by simp [low, not_le.2 hb, not_le.2 hc])
  have k3 : kap c a z = if crs c a z < 0 then -1 else 0 := by
    have : (0 < (a.2 - c.2) * crs c a z) ↔ crs c a z < 0 := by
      constructor
      · intro h; by_contra hh; rw [not_lt] at hh; nlinarith
      · intro h; nlinarith
    unfold kap; simp only [this, low, ha, if_true, not_le.2 hc]; simp
  have hs := crs_sum a b c z
  have hy := bary_y a b c z
  have key : kapTri a b c z = (if 0 < crs a b z then 1 else 0) - (if crs c a z < 0 then 1 else 0) := by
    unfold kapTri; rw [k1, k2, k3]; split_ifs <;> simp
  have hyy : 0 ≤ z.2 - a.2 := by linarith
  have hcon : ¬ (crs a b z ≤ 0 ∧ crs c a z < 0) := by
    rintro ⟨h1, h3⟩
    unfold crs at *
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c.2 - a.2) (by linarith : (0:ℝ) ≤ -((b.1 - a.1) * (z.2 - a.2) - (b.2 - a.2) * (z.1 - a.1))),
      mul_pos (by linarith : (0:ℝ) < b.2 - a.2) (by linarith : (0:ℝ) < ((c.1 - a.1) * (z.2 - a.2) - (c.2 - a.2) * (z.1 - a.1))), mul_nonneg hyy hD.le]
  refine ⟨?_, ?_, ?_⟩
  · rw [key]
    by_cases h1 : 0 < crs a b z <;> by_cases h3 : crs c a z < 0
    · simp [h1, h3]
    · simp [h1, h3]
    · exact (hcon ⟨not_lt.mp h1, h3⟩).elim
    · simp [h1, h3]
  · intro u v w; rw [key]; simp [u, not_lt.mpr w.le]
  · intro hn
    rw [key] at hn
    by_cases h1 : 0 < crs a b z <;> by_cases h3 : crs c a z < 0
    · simp [h1, h3] at hn
    · have h3' : 0 ≤ crs c a z := not_lt.mp h3
      refine ⟨h1.le, ?_, h3'⟩
      by_contra h2; rw [not_le] at h2
      have e1 : crs c a z * b.2 + crs a b z * c.2 = crs a b c * z.2 - crs b c z * a.2 := by linarith
      have : 0 < (z.2 - a.2) * crs b c z := by
        rw [idy2 a b c z]
        nlinarith [mul_nonneg h3' (by linarith : (0:ℝ) ≤ b.2 - z.2), mul_pos h1 (by linarith : (0:ℝ) < c.2 - z.2)]
      nlinarith [mul_nonneg hyy (by linarith : (0:ℝ) ≤ -crs b c z)]
    · exact (hcon ⟨not_lt.mp h1, h3⟩).elim
    · simp [h1, h3] at hn

/-- pattern: `a` strictly above, `b`, `c` weakly below the line of `z`. -/
theorem triB (a b c z : ℝ × ℝ) (hD : 0 < crs a b c) (ha : z.2 < a.2) (hb : b.2 ≤ z.2) (hc : c.2 ≤ z.2) :
    TriGood a b c z := by
  have p1 : b.2 - a.2 < 0 := by linarith
  have p2 : 0 < a.2 - c.2 := by linarith
  have k1 : kap a b z = if crs a b z < 0 then -1 else 0 := by
    have : (0 < (b.2 - a.2) * crs a b z) ↔ crs a b z < 0 := by
      constructor
      · intro h; by_contra hh; rw [not_lt] at hh; nlinarith
      · intro h; nlinarith
    unfold kap; simp only [this, low, hb, if_true, not_le.2 ha]; simp
  have k2 : kap b c z = 0 := kap_zero_of_low (by simp [low, hb, hc])
  have k3 : kap c a z = if 0 < crs c a z then 1 else 0 := by
    have : (0 < (a.2 - c.2) * crs c a z) ↔ 0 < crs c a z := mul_pos_iff_of_pos_left p2
    unfold kap; simp only [this, low, hc, if_true, not_le.2 ha]; simp
  have key : kapTri a b c z = (if 0 < crs c a z then 1 else 0) - (if crs a b z < 0 then 1 else 0) := by
    unfold kapTri; rw [k1, k2, k3]; split_ifs <;> simp
  have hyy : z.2 - a.2 < 0 := by linarith
  have hcon : ¬ (crs c a z ≤ 0 ∧ crs a b z < 0) := by
    rintro ⟨h3, h1⟩
    have := idy a b c z
    nlinarith [mul_pos_of_neg_of_neg (by linarith : c.2 - a.2 < 0) h1, mul_nonneg_of_nonpos_of_nonpos (by linarith : b.2 - a.2 ≤ 0) h3,
      mul_neg_of_neg_of_pos hyy hD]
  refine ⟨?_, ?_, ?_⟩
  · rw [key]
    by_cases h1 : 0 < crs c a z <;> by_cases h3 : crs a b z < 0
    · simp [h1, h3]
    · simp [h1, h3]
    · exact (hcon ⟨not_lt.mp h1, h3⟩).elim
    · simp [h1, h3]
  · intro u v w; rw [key]; simp [w, not_lt.mpr u.le]
  · intro hn
    rw [key] at hn
    by_cases h1 : 0 < crs c a z <;> by_cases h3 : crs a b z < 0
    · simp [h1, h3] at hn
    · have h3' : 0 ≤ crs a b z := not_lt.mp h3
      refine ⟨h3', ?_, h1.le⟩
      by_contra h2; rw [not_le] at h2
      have h4 := idy2 a b c z
      have h5 : crs c a z * (b.2 - z.2) + crs a b z * (c.2 - z.2) ≤ 0 := by
        nlinarith [mul_nonneg h1.le (by linarith : (0:ℝ) ≤ z.2 - b.2), mul_nonneg h3' (by linarith : (0:ℝ) ≤ z.2 - c.2)]
      nlinarith [mul_pos_of_neg_of_neg hyy h2]
    · exact (hcon ⟨not_lt.mp h1, h3⟩).elim
    · simp [h1, h3] at hn

theorem triLow (a b c z : ℝ × ℝ) (hD : 0 < crs a b c) (ha : a.2 ≤ z.2) (hb : b.2 ≤ z.2) (hc : c.2 ≤ z.2) :
    TriGood a b c z := by
  have k : kapTri a b c z = 0 := by
    unfold kapTri
    rw [kap_zero_of_low (by simp [low, ha, hb]), kap_zero_of_low (by simp [low, hb, hc]), kap_zero_of_low (by simp [low, ha, hc])]; simp
  have no : ¬ (0 < crs a b z ∧ 0 < crs b c z ∧ 0 < crs c a z) := by
    rintro ⟨u, v, w⟩
    have hy := bary_y a b c z
    have hs := crs_sum a b c z
    have t1 : 0 ≤ crs b c z * (z.2 - a.2) := mul_nonneg v.le (by linarith)
    have t2 : 0 ≤ crs c a z * (z.2 - b.2) := mul_nonneg w.le (by linarith)
    have t3 : 0 ≤ crs a b z * (z.2 - c.2) := mul_nonneg u.le (by linarith)
    have s0 : crs b c z * (z.2 - a.2) + crs c a z * (z.2 - b.2) + crs a b z * (z.2 - c.2) = 0 := by
      have : crs a b c * z.2 = (crs a b z + crs b c z + crs c a z) * z.2 := by rw [hs]
      nlinarith
    have za : z.2 - a.2 = 0 := by
      by_contra h; have : 0 < crs b c z * (z.2 - a.2) := mul_pos v (lt_of_le_of_ne (by linarith) (Ne.symm h)); linarith
    have zb : z.2 - b.2 = 0 := by
      by_contra h; have : 0 < crs c a z * (z.2 - b.2) := mul_pos w (lt_of_le_of_ne (by linarith) (Ne.symm h)); linarith
    have zc : z.2 - c.2 = 0 := by
      by_contra h; have : 0 < crs a b z * (z.2 - c.2) := mul_pos u (lt_of_le_of_ne (by linarith) (Ne.symm h)); linarith
    have : crs a b c = 0 := by
      unfold crs
      have e1 : b.2 - a.2 = 0 := by linarith
      have e2 : c.2 - a.2 = 0 := by linarith
      rw [e1, e2]; ring
    linarith
  refine ⟨by rw [k]; simp, fun u v w => absurd ⟨u, v, w⟩ no, fun h => (h k).elim⟩

theorem triHigh (a b c z : ℝ × ℝ) (hD : 0 < crs a b c) (ha : z.2 < a.2) (hb : z.2 < b.2) (hc : z.2 < c.2) :
    TriGood a b c z := by
  have k : kapTri a b c z = 0 := by
    unfold kapTri
    rw [kap_zero_of_low (by simp [low, not_le.2 ha, not_le.2 hb]), kap_zero_of_low (by simp [low, not_le.2 hb, not_le.2 hc]),
      kap_zero_of_low (by simp [low, not_le.2 ha, not_le.2 hc])]; simp
  have no : ¬ (0 < crs a b z ∧ 0 < crs b c z ∧ 0 < crs c a z) := by
    rintro ⟨u, v, w⟩
    have hy := bary_y a b c z
    have hs := crs_sum a b c z
    have t1 : 0 < crs b c z * (a.2 - z.2) := mul_pos v (by linarith)
    have t2 : 0 < crs c a z * (b.2 - z.2) := mul_pos w (by linarith)
    have t3 : 0 < crs a b z * (c.2 - z.2) := mul_pos u (by linarith)
    have : crs a b c * z.2 = (crs a b z + crs b c z + crs c a z) * z.2 := by rw [hs]
    nlinarith
  refine ⟨by rw [k]; simp, fun u v w => absurd ⟨u, v, w⟩ no, fun h => (h k).elim⟩

/-- **Triangle lemma.** For a strictly counter-clockwise triangle, `kapTri` is `{0,1}`-valued, `1` on the open triangle
(all three edge crosses positive), and `0` unless all three crosses are `>= 0`.  Valid for EVERY point `z`. -/
theorem tri_good (a b c z : ℝ × ℝ) (hD : 0 < crs a b c) : TriGood a b c z := by
  have hD2 : 0 < crs b c a := by rw [crs_rot]; exact hD
  have hD3 : 0 < crs c a b := by rw [crs_rot, crs_rot]; exact hD
  by_cases ha : a.2 ≤ z.2 <;> by_cases hb : b.2 ≤ z.2 <;> by_cases hc : c.2 ≤ z.2
  · exact triLow a b c z hD ha hb hc
  · exact TriGood_rot (TriGood_rot (triB c a b z hD3 (not_le.mp hc) ha hb))
  · exact TriGood_rot (triB b c a z hD2 (not_le.mp hb) hc ha)
  · exact triA a b c z hD ha (not_le.mp hb) (not_le.mp hc)
  · exact triB a b c z hD (not_le.mp ha) hb hc
  · exact TriGood_rot (triA b c a z hD2 hb (not_le.mp hc) (not_le.mp ha))
  · exact TriGood_rot (TriGood_rot (triA c a b z hD3 hc (not_le.mp ha) (not_le.mp hb)))
  · exact triHigh a b c z hD (not_le.mp ha) (not_le.mp hb) (not_le.mp hc)

end Erdos634.Draft.Chain
