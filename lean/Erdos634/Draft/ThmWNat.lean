-- Draft/ThmWNat.lean — Theorem W, natural-number interface: `WP` parameters => `WTilable e f M`.  UNAUDITED.  No sorry.
-- Credit: Paliy (W/beta framework), Beeson-Rosu (S2L skew frame); template found by our engine `bto`.
import Erdos634.Draft.ThmWCore

open scoped Classical
open Erdos634.Geometry
open Erdos634.Draft.CollarG (WTilable)

namespace Erdos634.Draft.ThmW
open Erdos634.Draft.WFrameF Erdos634.Draft.WBrickF

/-- the integer scales exist when the sign conditions hold -/
theorem exists_Sc (e f M t r q : ℕ) (h : WP (e : ℝ) f M t r q) : Nonempty (Sc (e : ℝ) f M t r q) := by
  have c3 := h.c3; have c4 := h.c4; have c5 := h.c5; have c6 := h.c6; have c7 := h.c7
  have htr := h.htr
  have x1 := WP.a_x1 h; have x2 := WP.a_x2 h
  have n3 : e * M > f * t := by exact_mod_cast (by linarith : (f : ℝ) * t < e * M)
  have n4 : f * r > e * M := by exact_mod_cast (by linarith : (e : ℝ) * M < f * r)
  have n5 : f * M > e * r := by exact_mod_cast (by linarith : (e : ℝ) * r < f * M)
  have n6 : f * q > e * r := by exact_mod_cast (by linarith : (e : ℝ) * r < f * q)
  have n7 : f * t > e * q := by exact_mod_cast (by linarith : (e : ℝ) * q < f * t)
  have n8 : t < r := by exact_mod_cast htr
  have n9 : f * M > e * t := by exact_mod_cast (by linarith : (e : ℝ) * t < f * M)
  have n10 : f * q > e * t := by exact_mod_cast (by linarith : (e : ℝ) * t < f * q)
  have hf0 : 0 < f := by exact_mod_cast h.hf
  have ht0 : 0 < t := by exact_mod_cast h.ht
  have hM0 : 0 < M := by exact_mod_cast h.hM
  refine ⟨{ K0 := f * M, S0 := e * t, K1 := f * M - e * r, K2 := f * t, K3 := f * (r - t), S3 := f * r - e * M,
            s4 := f * (r - t), x4 := f * t - e * q, K5 := f * q - e * t, S5 := f * q - e * r,
            hK0 := by first | (push_cast; ring) | push_cast, hS0 := by first | (push_cast; ring) | push_cast,
            hK1 := by rw [Nat.cast_sub n5.le]; push_cast; ring,
            hK2 := by first | (push_cast; ring) | push_cast,
            hK3 := by rw [Nat.cast_mul, Nat.cast_sub n8.le] <;> ring,
            hS3 := by rw [Nat.cast_sub n4.le]; push_cast; ring,
            hs4 := by rw [Nat.cast_mul, Nat.cast_sub n8.le] <;> ring,
            hx4 := by rw [Nat.cast_sub n7.le]; push_cast; ring,
            hK5 := by rw [Nat.cast_sub n10.le]; push_cast; ring,
            hS5 := by rw [Nat.cast_sub n6.le]; push_cast; ring,
            pK0 := Nat.mul_pos hf0 hM0, pK1 := Nat.sub_pos_of_lt n5, pK2 := Nat.mul_pos hf0 ht0,
            pK3 := Nat.mul_pos hf0 (Nat.sub_pos_of_lt n8), pK5 := Nat.sub_pos_of_lt n10,
            lS0 := n9.le, lS3 := ?_, lS5 := ?_ }⟩
  · -- f r - e M ≤ f (r - t)
    rw [Nat.mul_sub]; omega
  · have : e * t ≤ e * r := Nat.mul_le_mul_left e n8.le
    omega

/-- **Core, natural form.** -/
theorem wTilable_of_WP (e f M t r q : ℕ) (he : 1 ≤ e) (hef : e < f) (h : WP (e : ℝ) f M t r q) :
    WTilable e f M := by
  obtain ⟨z⟩ := exists_Sc e f M t r q h
  have hF : 1 < (f : ℝ) / e := by
    have : (0 : ℝ) < e := by exact_mod_cast he
    rw [lt_div_iff₀ this]; simpa using (by exact_mod_cast hef : (e : ℝ) < f)
  have hA : (0 : ℝ) < e * f := mul_pos h.he h.hf
  have hB : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith [WP.a_g h, WP.a_s h, mul_pos (WP.a_g h) (WP.a_s h)]
  obtain ⟨D, hM, hT⟩ := exists_dissection_W e f M t r q h z hF hA hB
  have hN : (∑ a : Fin 6, cntF z a) = (2 * f ^ 2 - e ^ 2) * M ^ 2 := by
    have hc := sum_cnt_real e f M t r q h z
    have hle : e ^ 2 ≤ 2 * f ^ 2 := by nlinarith
    have : (((∑ a : Fin 6, cntF z a : ℕ)) : ℝ) = (((2 * f ^ 2 - e ^ 2) * M ^ 2 : ℕ) : ℝ) := by
      rw [hc]; push_cast [Nat.cast_sub hle]; ring
    exact_mod_cast this
  refine Erdos634.Draft.DebtB.wTilable_of_pack he hef hN rfl hF (e * f) (f ^ 2 - e ^ 2) hA hB rfl rfl D _ hT hM ?_
  -- sides of the target
  have hf0 : (f : ℝ) ≠ 0 := h.hf.ne'
  have he0 : (e : ℝ) ≠ 0 := h.he.ne'
  have hM0 := h.hM
  have hpos := mul_pos (WP.a_g h) (WP.a_s h)
  have hk := WP.a_k h
  refine Erdos634.Draft.DebtB.hasSides_triC_o1 hF _ _ _ _ (x := (M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (y := (M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) (z := (M : ℝ) * (f : ℝ) ^ 3)
    (by positivity) (by have := mul_pos hM0 (mul_pos h.he hk); linarith) (by positivity) ?_ ?_ ?_
  · simp only [Erdos634.Draft.DebtB.sqf, pt_B]; field_simp; ring
  · simp only [Erdos634.Draft.DebtB.sqf, pt_B, pt_A]; field_simp; ring
  · simp only [Erdos634.Draft.DebtB.sqf, pt_B, pt_A]; field_simp; ring

end Erdos634.Draft.ThmW
