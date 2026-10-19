-- Draft/ThmWSc.lean — natural scales of the six pieces of the template (Theorem W) with their real-valued relations.  UNAUDITED.  No sorry.
import Erdos634.Draft.ThmWHyp
namespace Erdos634.Draft.ThmW

/-- the integer scales (side multiples) of the six pieces, tied to the real parameters -/
structure Sc (e f M t r q : ℝ) where
  K0 : ℕ
  S0 : ℕ
  K1 : ℕ
  K2 : ℕ
  K3 : ℕ
  S3 : ℕ
  s4 : ℕ
  x4 : ℕ
  K5 : ℕ
  S5 : ℕ
  hK0 : (K0 : ℝ) = f * M
  hS0 : (S0 : ℝ) = e * t
  hK1 : (K1 : ℝ) = f * M - e * r
  hK2 : (K2 : ℝ) = f * t
  hK3 : (K3 : ℝ) = f * (r - t)
  hS3 : (S3 : ℝ) = f * r - e * M
  hs4 : (s4 : ℝ) = f * (r - t)
  hx4 : (x4 : ℝ) = f * t - e * q
  hK5 : (K5 : ℝ) = f * q - e * t
  hS5 : (S5 : ℝ) = f * q - e * r
  pK0 : 0 < K0
  pK1 : 0 < K1
  pK2 : 0 < K2
  pK3 : 0 < K3
  pK5 : 0 < K5
  lS0 : S0 ≤ K0
  lS3 : S3 ≤ K3
  lS5 : S5 ≤ K5

theorem sig (K S : ℕ) (hK : 0 < K) (hS : S ≤ K) : 0 ≤ (S : ℝ) / (K : ℝ) ∧ (S : ℝ) / (K : ℝ) ≤ 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨by positivity, (div_le_one hK').mpr (by exact_mod_cast hS)⟩

theorem sig0 (K : ℕ) (hK : 0 < K) : 0 ≤ ((0 : ℕ) : ℝ) / (K : ℝ) ∧ ((0 : ℕ) : ℝ) / (K : ℝ) ≤ 1 := sig K 0 hK (Nat.zero_le _)

theorem cutgen (S K : ℝ) (hK : K ≠ 0) (x y c : ℝ) (h : S * (y - x) = (c - x) * K) : x + (S / K) * (y - x) = c := by
  have : S / K * (y - x) = c - x := by
    rw [div_mul_eq_mul_div, div_eq_iff hK]; linarith
  linarith

end Erdos634.Draft.ThmW
