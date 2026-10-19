-- Draft/ChainKap.lean -- CHAIN LEMMA, part 1: the horizontal-ray crossing function `kap` of an oriented segment, its antisymmetry and
-- additivity over collinear subdivision.  UNAUDITED.  No sorry.
-- Credit: the chain (winding-number) lemma is the Ramanujan-rows session's (project working notes), audited SOUND-WITH-FIX
-- 2026-10-19); the integer skew frame is Fable's; frame idea Beeson-Rosu; W/beta framework Paliy.
import Mathlib.Tactic

open scoped Classical
namespace Erdos634.Draft.Chain

/-- cross product `(q - p) x (r - p)`. -/
def crs (p q r : ℝ × ℝ) : ℝ := (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- `1` if `p` lies weakly below the horizontal line through `z`, else `0`. -/
noncomputable def low (p z : ℝ × ℝ) : ℤ := if p.2 ≤ z.2 then 1 else 0

/-- Signed crossing of the horizontal ray from `z` to `+infinity` with the oriented segment `p -> q`
(half-open in `y`; crossing strictly to the right of `z`). -/
noncomputable def kap (p q z : ℝ × ℝ) : ℤ := if 0 < (q.2 - p.2) * crs p q z then low p z - low q z else 0

theorem crs_swap (p q z : ℝ × ℝ) : crs q p z = - crs p q z := by unfold crs; ring

theorem kap_swap (p q z : ℝ × ℝ) : kap q p z = - kap p q z := by
  have h : (p.2 - q.2) * crs q p z = (q.2 - p.2) * crs p q z := by rw [crs_swap]; ring
  unfold kap; rw [h]; split_ifs <;> ring

theorem kap_self (p z : ℝ × ℝ) : kap p p z = 0 := by simp [kap]

/-- master identity for collinear triples -/
theorem crs_master (a b c z : ℝ × ℝ) (h : crs a b c = 0) :
    (b.2 - a.2) * crs a c z = (c.2 - a.2) * crs a b z := by
  unfold crs at h ⊢; linear_combination (-(z.2 - a.2)) * h

theorem cond_congr (a b c z : ℝ × ℝ) (h : crs a b c = 0) (hb : a.2 ≠ b.2) (hc : a.2 ≠ c.2) :
    (0 < (b.2 - a.2) * crs a b z ↔ 0 < (c.2 - a.2) * crs a c z) := by
  have M := crs_master a b c z h
  have hb' : 0 < (b.2 - a.2) ^ 2 := by positivity
  have hc' : 0 < (c.2 - a.2) ^ 2 := by positivity
  have key : (c.2 - a.2) * crs a c z * (b.2 - a.2) ^ 2 = (b.2 - a.2) * crs a b z * (c.2 - a.2) ^ 2 := by
    have : (c.2 - a.2) * crs a c z * (b.2 - a.2) ^ 2 = (c.2 - a.2) * (b.2 - a.2) * ((b.2 - a.2) * crs a c z) := by ring
    rw [this, M]; ring
  constructor
  · intro H
    have : 0 < (b.2 - a.2) * crs a b z * (c.2 - a.2) ^ 2 := mul_pos H hc'
    rw [← key] at this
    exact (mul_pos_iff_of_pos_right hb').mp this
  · intro H
    have : 0 < (c.2 - a.2) * crs a c z * (b.2 - a.2) ^ 2 := mul_pos H hb'
    rw [key] at this
    exact (mul_pos_iff_of_pos_right hc').mp this

theorem low_cases (p z : ℝ × ℝ) : low p z = 0 ∨ low p z = 1 := by unfold low; split_ifs <;> simp

theorem ne_of_low_ne {p q z : ℝ × ℝ} (h : low p z ≠ low q z) : p.2 ≠ q.2 := by
  intro e; apply h; unfold low; rw [e]

theorem kap_zero_of_low {p q z : ℝ × ℝ} (h : low p z = low q z) : kap p q z = 0 := by
  unfold kap; rw [h]; simp

theorem kap_eq_of_cond (a b c z : ℝ × ℝ) (h : crs a b c = 0) (hb : a.2 ≠ b.2) (hc : a.2 ≠ c.2)
    (hl : low b z = low c z) : kap a b z = kap a c z := by
  unfold kap
  rw [if_congr (cond_congr a b c z h hb hc) rfl rfl, hl]

theorem crs_p1 {p q r : ℝ × ℝ} (h : crs p q r = 0) : crs r q p = 0 := by
  unfold crs at *; linear_combination (-1 : ℝ) * h

theorem crs_p2 {p q r : ℝ × ℝ} (h : crs p q r = 0) : crs q p r = 0 := by
  unfold crs at *; linear_combination (-1 : ℝ) * h

/-- **Additivity of `kap` over collinear subdivision**, any order of the three points on their line. -/
theorem kap_add (p q r z : ℝ × ℝ) (h : crs p q r = 0) : kap p q z + kap q r z = kap p r z := by
  by_cases e1 : low p z = low q z
  · by_cases e2 : low q z = low r z
    · rw [kap_zero_of_low e1, kap_zero_of_low e2, kap_zero_of_low (e1.trans e2)]; simp
    · have hqr : q.2 ≠ r.2 := ne_of_low_ne e2
      have hpr : p.2 ≠ r.2 := ne_of_low_ne (by rw [e1]; exact e2)
      rw [kap_zero_of_low e1, zero_add, kap_swap r q z, kap_swap r p z]
      congr 1
      exact kap_eq_of_cond r q p z (crs_p1 h) hqr.symm hpr.symm e1.symm
  · by_cases e2 : low q z = low r z
    · have hpq : p.2 ≠ q.2 := ne_of_low_ne e1
      have hpr : p.2 ≠ r.2 := ne_of_low_ne (by rw [← e2]; exact e1)
      rw [kap_zero_of_low e2, add_zero]
      exact kap_eq_of_cond p q r z h hpq hpr e2
    · have hpq : p.2 ≠ q.2 := ne_of_low_ne e1
      have hqr : q.2 ≠ r.2 := ne_of_low_ne e2
      have e3 : low p z = low r z := by
        rcases low_cases p z with a | a <;> rcases low_cases q z with b | b <;> rcases low_cases r z with c | c <;> omega
      rw [kap_zero_of_low e3, kap_swap q p z]
      have := kap_eq_of_cond q p r z (crs_p2 h) hpq.symm hqr e3
      rw [this]; ring

end Erdos634.Draft.Chain
