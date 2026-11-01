/-
Draft/ZhangInst40.lean -- **40 non-squarefree tile counts <= 10^6 from Zhang Prop 10(2)** (38 via Prop 10(2)) and Prop 11(2) (419328, 591318), UNAUDITED.

Credit: the construction is Y. X. Zhang, "Tiling triangles with 2 pi/3 angles" (arXiv 2512.22696), Prop 10(2) (formal: `ZhangSporadic.zhang_prop10_2`,
equiconstructibility hypothesis from `ZhangThm4.zhang_thm4`).  What is ours: the tile-uniform exit to `TileCount`
(`zhang_prop10_2_tileCount`) and the instantiation at the values listed in internal working notes (sweep) and S5 (this file).

`zhang_prop10_2_tileCount`: for naturals `a b c` with `c*c = a*a + b*b + a*b`, `Nat.Coprime a b` and `3*((c*c-a-b)/(a*b)+1) <= m`,
`m*m*((a+b)*(a+2*b))` is a tile count (`TileCount` = `Nonempty (CongruentDissection _)`; the target is the triangle
`S=(-m b^2,0), C, E` of Prop 10(2); the exit map is `CongruentRegionDissection.toCongruentDissection` after `TriSet_eq_carrier`).
Hypothesis witnesses: every instance below discharges all hypotheses by `norm_num` (coprimality, Eisenstein relation, threshold); the negative
controls at the end show the threshold and coprimality hypotheses bite.  No sorry, no native_decide.  Nothing imports this file; not in `All`.
-/
import Erdos634.Draft.ZhangSporadic
import Erdos634.Draft.ZhangRat5Tiled
import Erdos634.Draft.ZhangProp11b
import Erdos634.Draft.TileCountFamilies

namespace Erdos634.Draft.ZhangInst40
open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.ZhangPara Erdos634.ZhangSporadic Erdos634.ZhangThm4 Erdos634.ZhangL1
open Erdos634.ZhangRat4 Erdos634.ZhangProp11b
open Erdos634.Draft.TileCountFamilies (TileCount)

theorem zhang_prop10_2_tileCount (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcab : c * c = a * a + b * b + a * b) (hcop : Nat.Coprime a b)
    (m : ℕ) (hm : 3 * ((c * c - a - b) / (a * b) + 1) ≤ m) :
    TileCount (m * m * ((a + b) * (a + 2 * b))) := by
  have hm0 : 0 < m := by
    have : 0 < 3 * ((c * c - a - b) / (a * b) + 1) := by positivity
    omega
  have hE := zhang_thm4 a b c ha hb hc hcab hcop m hm
  obtain ⟨C, hCr, hCm⟩ := zhang_prop10_2 a b m ha hb hm0 hE
  have hzs := zs_pos
  have hma : (0 : ℝ) < m := by exact_mod_cast hm0
  have haa : (0 : ℝ) < a := by exact_mod_cast ha
  have hbb : (0 : ℝ) < b := by exact_mod_cast hb
  have hdet : 0 < det3 (-((m : ℝ) * b * b)) 0
        (((m : ℝ) * ((a : ℝ) * b)) + (m : ℝ) * (a + b) * a / 2)
        (-((m : ℝ) * (a + b) * a * zs / 2))
        (((m : ℝ) * ((a : ℝ) * b)) / 2) (((m : ℝ) * ((a : ℝ) * b)) * zs / 2) := by
    have e : det3 (-((m : ℝ) * b * b)) 0
        (((m : ℝ) * ((a : ℝ) * b)) + (m : ℝ) * (a + b) * a / 2)
        (-((m : ℝ) * (a + b) * a * zs / 2))
        (((m : ℝ) * ((a : ℝ) * b)) / 2) (((m : ℝ) * ((a : ℝ) * b)) * zs / 2)
        = zs * (((m : ℝ) * ((a : ℝ) * b) + (m : ℝ) * (a + b) * a / 2 + (m : ℝ) * b * b) * ((m : ℝ) * ((a : ℝ) * b) / 2)
            + ((m : ℝ) * ((a : ℝ) * b) / 2 + (m : ℝ) * b * b) * ((m : ℝ) * (a + b) * a / 2)) := by
      simp only [det3]; ring
    rw [e]; positivity
  exact ⟨C.toCongruentDissection _ (hCr.trans (TriSet_eq_carrier hdet))⟩

theorem tileCount_174825 : TileCount 174825 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 15 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_198912 : TileCount 198912 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 16 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_224553 : TileCount 224553 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 17 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_251748 : TileCount 251748 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 18 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_280497 : TileCount 280497 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 19 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_310800 : TileCount 310800 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 20 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_342657 : TileCount 342657 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 21 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_376068 : TileCount 376068 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 22 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_411033 : TileCount 411033 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 23 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_447552 : TileCount 447552 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 24 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_485625 : TileCount 485625 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 25 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_525252 : TileCount 525252 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 26 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_566433 : TileCount 566433 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 27 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_609168 : TileCount 609168 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 28 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_653457 : TileCount 653457 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 29 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_699300 : TileCount 699300 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 30 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_746697 : TileCount 746697 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 31 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_795648 : TileCount 795648 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 32 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_846153 : TileCount 846153 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 33 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_898212 : TileCount 898212 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 34 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_951825 : TileCount 951825 := by
  have h := zhang_prop10_2_tileCount 5 16 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 35 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_297360 : TileCount 297360 := by
  have h := zhang_prop10_2_tileCount 11 24 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 12 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_348985 : TileCount 348985 := by
  have h := zhang_prop10_2_tileCount 11 24 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 13 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_404740 : TileCount 404740 := by
  have h := zhang_prop10_2_tileCount 11 24 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 14 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_464625 : TileCount 464625 := by
  have h := zhang_prop10_2_tileCount 11 24 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 15 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_528640 : TileCount 528640 := by
  have h := zhang_prop10_2_tileCount 11 24 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 16 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_596785 : TileCount 596785 := by
  have h := zhang_prop10_2_tileCount 11 24 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 17 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_669060 : TileCount 669060 := by
  have h := zhang_prop10_2_tileCount 11 24 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 18 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_745465 : TileCount 745465 := by
  have h := zhang_prop10_2_tileCount 11 24 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 19 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_826000 : TileCount 826000 := by
  have h := zhang_prop10_2_tileCount 11 24 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 20 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_910665 : TileCount 910665 := by
  have h := zhang_prop10_2_tileCount 11 24 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 21 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_999460 : TileCount 999460 := by
  have h := zhang_prop10_2_tileCount 11 24 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 22 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_573696 : TileCount 573696 := by
  have h := zhang_prop10_2_tileCount 13 35 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 12 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_673296 : TileCount 673296 := by
  have h := zhang_prop10_2_tileCount 13 35 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 13 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_780864 : TileCount 780864 := by
  have h := zhang_prop10_2_tileCount 13 35 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 14 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_896400 : TileCount 896400 := by
  have h := zhang_prop10_2_tileCount 13 35 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 15 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_744480 : TileCount 744480 := by
  have h := zhang_prop10_2_tileCount 16 39 49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 12 (by norm_num)
  norm_num at h
  exact h

theorem tileCount_873730 : TileCount 873730 := by
  have h := zhang_prop10_2_tileCount 16 39 49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 13 (by norm_num)
  norm_num at h
  exact h

/-! ### Zhang Prop 11(2): the triangle `A C B` with `3 (a+b)(b+2a) m^2` tiles, for `m` in the semigroup `<b, c>` (`b = a + d`) -/

theorem exists_pts (p q r : ℝ) (hp : 0 < p) (h : 0 < q ^ 2 - ((p ^ 2 + q ^ 2 - r ^ 2) / (2 * p)) ^ 2) :
    ∃ Ax Ay Bx By Dx Dy : ℝ, 0 < det3 Ax Ay Dx Dy Bx By ∧ (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = p ^ 2 ∧
      (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = q ^ 2 ∧ (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = r ^ 2 := by
  set u := (p ^ 2 + q ^ 2 - r ^ 2) / (2 * p) with hu
  have hv := Real.sq_sqrt h.le
  have hvp : 0 < Real.sqrt (q ^ 2 - u ^ 2) := Real.sqrt_pos.mpr h
  refine ⟨p, 0, u, -Real.sqrt (q ^ 2 - u ^ 2), 0, 0, ?_, ?_, ?_, ?_⟩
  · simp only [det3]; nlinarith
  · ring
  · nlinarith
  · have hpu : 2 * p * u = p ^ 2 + q ^ 2 - r ^ 2 := by rw [hu]; field_simp
    nlinarith

theorem zhang_prop11_2_tileCount (a d c m : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d))
    (hm : 0 < m) (hS : AdmS a d c m) :
    TileCount (((a + d) + 2 * a) * (a + 2 * (a + d)) * (m * m) + (((a + d) + 2 * a) * m) * (((a + d) + 2 * a) * m)) := by
  have hb : 0 < a + d := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < ((a + d : ℕ) : ℝ) := by exact_mod_cast hb
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcabR : (c : ℝ) * c = a * a + ((a + d : ℕ) : ℝ) * ((a + d : ℕ) : ℝ) + a * ((a + d : ℕ) : ℝ) := by exact_mod_cast hcab
  set bb : ℝ := ((a + d : ℕ) : ℝ) with hbb
  set p : ℝ := (bb + 2 * a) * m * bb with hp
  set q : ℝ := (a + 2 * bb) * a * m with hq
  set r : ℝ := (a ^ 2 + a * bb + bb ^ 2) * m with hr
  have hp0 : 0 < p := by positivity
  have key : 4 * p ^ 2 * q ^ 2 - (p ^ 2 + q ^ 2 - r ^ 2) ^ 2
      = 3 * a ^ 2 * bb ^ 2 * ((bb + 2 * a) * (a + 2 * bb)) ^ 2 * m ^ 4 := by
    rw [hp, hq, hr]; ring
  have hpos : 0 < q ^ 2 - ((p ^ 2 + q ^ 2 - r ^ 2) / (2 * p)) ^ 2 := by
    have e : q ^ 2 - ((p ^ 2 + q ^ 2 - r ^ 2) / (2 * p)) ^ 2
        = (3 * a ^ 2 * bb ^ 2 * ((bb + 2 * a) * (a + 2 * bb)) ^ 2 * m ^ 4) / (4 * p ^ 2) := by
      rw [← key]; field_simp; ring
    rw [e]; positivity
  obtain ⟨Ax, Ay, Bx, By, Dx, Dy, hD, hAD, hBD, hAB⟩ := exists_pts p q r hp0 hpos
  have hT := prop11_2_tiled_S a d c m ha hd hcab hcop hm hS Ax Ay Bx By Dx Dy hD
    (by rw [hAD, hp]) (by rw [hBD, hq]) (by rw [hAB, hr])
  obtain ⟨C, hCr, hCm⟩ := zhang_prop11_2_core a (a + d) m ha hb hm Ax Ay Bx By Dx Dy hD
    (by rw [hAD, hp]) (by rw [hBD, hq]) (by rw [hAB, hr]) hT
  have hdet : 0 < det3 Ax Ay (Dx + ((bb + 2 * a) / (a + 2 * bb)) * (Dx - Bx))
      (Dy + ((bb + 2 * a) / (a + 2 * bb)) * (Dy - By)) Bx By := by
    have e : det3 Ax Ay (Dx + ((bb + 2 * a) / (a + 2 * bb)) * (Dx - Bx))
      (Dy + ((bb + 2 * a) / (a + 2 * bb)) * (Dy - By)) Bx By
        = (1 + (bb + 2 * a) / (a + 2 * bb)) * det3 Ax Ay Dx Dy Bx By := by
      simp only [det3]; ring
    rw [e]; positivity
  exact ⟨C.toCongruentDissection _ (hCr.trans (TriSet_eq_carrier hdet))⟩

/-- Prop 11(2), tile (5,16,19), `m = 16 = 16 * 1 + 19 * 0`: `3 (21) (26) 16^2 + ... = 419328` (in the form `(B+2A)(A+2B)m^2 + ((B+2A)m)^2`). -/
theorem tileCount_419328 : TileCount 419328 := by
  have h := zhang_prop11_2_tileCount 5 11 19 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨1, 0, by norm_num⟩
  norm_num at h
  exact h

/-- Prop 11(2), tile (5,16,19), `m = 19 = 16 * 0 + 19 * 1`. -/
theorem tileCount_591318 : TileCount 591318 := by
  have h := zhang_prop11_2_tileCount 5 11 19 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨0, 1, by norm_num⟩
  norm_num at h
  exact h

/-- negative control for Prop 11(2): `m = 17` is NOT in the semigroup `<16, 19>`, so `AdmS 5 11 19 17` is refutable. -/
example : ¬ AdmS 5 11 19 17 := by
  rintro ⟨i, j, h⟩
  have : i ≤ 1 := by omega
  have : j ≤ 0 := by omega
  interval_cases i <;> interval_cases j <;> omega


/-! ### Negative controls: the hypotheses bite -/
/-- below the threshold (tile (5,16,19): threshold 15). -/
example : ¬ (3 * ((19 * 19 - 5 - 16) / (5 * 16) + 1) ≤ 14) := by norm_num
/-- the threshold for (5,16,19) is exactly 15 and 15 is admissible. -/
example : 3 * ((19 * 19 - 5 - 16) / (5 * 16) + 1) = 15 := by norm_num
/-- non-coprime scaled tile (10,32,38): relation holds but `Nat.Coprime` fails. -/
example : (38 : ℕ) * 38 = 10 * 10 + 32 * 32 + 10 * 32 ∧ ¬ Nat.Coprime 10 32 := by norm_num
/-- a non-Eisenstein triple fails the relation. -/
example : ¬ ((20 : ℕ) * 20 = 5 * 5 + 16 * 16 + 5 * 16) := by norm_num

end Erdos634.Draft.ZhangInst40

#print axioms Erdos634.Draft.ZhangInst40.tileCount_174825
#print axioms Erdos634.Draft.ZhangInst40.tileCount_198912
#print axioms Erdos634.Draft.ZhangInst40.tileCount_224553
#print axioms Erdos634.Draft.ZhangInst40.tileCount_251748
#print axioms Erdos634.Draft.ZhangInst40.tileCount_280497
#print axioms Erdos634.Draft.ZhangInst40.tileCount_297360
#print axioms Erdos634.Draft.ZhangInst40.tileCount_310800
#print axioms Erdos634.Draft.ZhangInst40.tileCount_342657
#print axioms Erdos634.Draft.ZhangInst40.tileCount_348985
#print axioms Erdos634.Draft.ZhangInst40.tileCount_376068
#print axioms Erdos634.Draft.ZhangInst40.tileCount_404740
#print axioms Erdos634.Draft.ZhangInst40.tileCount_411033
#print axioms Erdos634.Draft.ZhangInst40.tileCount_447552
#print axioms Erdos634.Draft.ZhangInst40.tileCount_464625
#print axioms Erdos634.Draft.ZhangInst40.tileCount_485625
#print axioms Erdos634.Draft.ZhangInst40.tileCount_525252
#print axioms Erdos634.Draft.ZhangInst40.tileCount_528640
#print axioms Erdos634.Draft.ZhangInst40.tileCount_566433
#print axioms Erdos634.Draft.ZhangInst40.tileCount_573696
#print axioms Erdos634.Draft.ZhangInst40.tileCount_596785
#print axioms Erdos634.Draft.ZhangInst40.tileCount_609168
#print axioms Erdos634.Draft.ZhangInst40.tileCount_653457
#print axioms Erdos634.Draft.ZhangInst40.tileCount_669060
#print axioms Erdos634.Draft.ZhangInst40.tileCount_673296
#print axioms Erdos634.Draft.ZhangInst40.tileCount_699300
#print axioms Erdos634.Draft.ZhangInst40.tileCount_744480
#print axioms Erdos634.Draft.ZhangInst40.tileCount_745465
#print axioms Erdos634.Draft.ZhangInst40.tileCount_746697
#print axioms Erdos634.Draft.ZhangInst40.tileCount_780864
#print axioms Erdos634.Draft.ZhangInst40.tileCount_795648
#print axioms Erdos634.Draft.ZhangInst40.tileCount_826000
#print axioms Erdos634.Draft.ZhangInst40.tileCount_846153
#print axioms Erdos634.Draft.ZhangInst40.tileCount_873730
#print axioms Erdos634.Draft.ZhangInst40.tileCount_896400
#print axioms Erdos634.Draft.ZhangInst40.tileCount_898212
#print axioms Erdos634.Draft.ZhangInst40.tileCount_910665
#print axioms Erdos634.Draft.ZhangInst40.tileCount_951825
#print axioms Erdos634.Draft.ZhangInst40.tileCount_999460
#print axioms Erdos634.Draft.ZhangInst40.zhang_prop10_2_tileCount
#print axioms Erdos634.Draft.ZhangInst40.zhang_prop11_2_tileCount
#print axioms Erdos634.Draft.ZhangInst40.tileCount_419328
#print axioms Erdos634.Draft.ZhangInst40.tileCount_591318
