/-
Draft/ZhangTrap.lean — second layer of the tile-uniform formalisation of Zhang's Theorem 4: parallelogram columns
(`col1`, `col2`: `a × ab`, `b × ab` parallelograms cut into `2a`, `2b` tiles), the parallelogram `p × ab` for `p` in the
numerical semigroup `⟨a, b⟩` (`paraPc`), a *row* (basic trapezoid + parallelogram, `rowPc`), and the *ideal trapezoid*
`trapPc` of `k` rows (short side `a²+b²+W`, leg `k·ab`).

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.ZhangBase

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Tset Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.ZhangTrap
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.Draft.S2L (mem_hull3' tri_le tri_ge tri_fst_le tri_fst_ge tri_snd_le tri_snd_ge pack_exists)
open Erdos634.Draft.WBrickF (interior_disj_lin)
open Erdos634.Draft.F4All (hf1)
open Erdos634.Draft.ZhangBase

/-- the bounding parallelogram: top-left corner `(x0, y0)`, height `a b` downwards, slanted sides `X + Y = const`,
width `wd`. -/
def Bp (a b x0 y0 wd : ℝ) : Set (ℝ × ℝ) :=
  {p | y0 - a * b ≤ p.2 ∧ p.2 ≤ y0 ∧ x0 + y0 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ x0 + y0 + wd}

section cols
variable {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
include ha hb

/-- column of width `a`: `a` cells `a × b` stacked along the slanted direction. -/
theorem col1 (ka : ℕ) (hka : 0 < ka) (eka : (ka : ℝ) = a) (x0 y0 : ℝ) :
    Pc (Mo a b ha hb) (Bp a b x0 y0 a) (2 * ka) := by
  obtain ⟨l, rfl⟩ : ∃ l, ka = l + 1 := ⟨ka - 1, by omega⟩
  have hab := mul_pos ha hb
  have hd : ((a, (0 : ℝ)) : ℝ × ℝ).1 * ((b, -b) : ℝ × ℝ).2 - ((a, (0 : ℝ)) : ℝ × ℝ).2 * ((b, -b) : ℝ × ℝ).1 ≠ 0 := by
    intro h; simp only at h; nlinarith
  have c1 : (TL hf1 (a, (0 : ℝ)) (b, -b) hd).Congruent (Mo a b ha hb) := by
    unfold TL Mo
    refine triC_cong hf1 _ _ _ _ _ _ _ _ ?_ ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, div_one] <;> ring
  have c2 : (TU hf1 (a, (0 : ℝ)) (b, -b) hd).Congruent (Mo a b ha hb) := by
    unfold TU Mo
    refine triC_cong hf1 _ _ _ _ _ _ _ _ ?_ ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, div_one] <;> ring
  have G := gridT (ThH hf1 (a, (0 : ℝ)) (b, -b) hd) (ThH_add hf1 (a, (0 : ℝ)) (b, -b) hd) (A := 1) (B := 1)
    one_pos one_pos (cellRT hf1 (a, (0 : ℝ)) (b, -b) hd (Mo a b ha hb) c1 c2) 0 l
  rw [ThH_image] at G
  have G' := RegionTiling.map G (IsometryEquiv.addRight (Phi 1 (x0, y0)))
  rw [Erdos634.Draft.EqSemigroup.shift_phi] at G'
  refine ⟨_, ?_, ⟨RTiling.castN (by ring) G'⟩⟩
  rintro _ ⟨_, ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩, rfl⟩
  simp only [Lam, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Nat.cast_zero,
    zero_add, one_mul] at h1 h2 h3 h4 ⊢
  push_cast at eka
  have e1 : z.2 * b ≤ ((l : ℝ) + 1) * b := mul_le_mul_of_nonneg_right h4 hb.le
  have e2 : 0 ≤ z.2 * b := mul_nonneg h3 hb.le
  have e3 : z.1 * a ≤ 1 * a := mul_le_mul_of_nonneg_right h2 ha.le
  have e4 : 0 ≤ z.1 * a := mul_nonneg h1 ha.le
  rw [eka] at e1
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> nlinarith


/-- column of width `b`: `b` cells `b × a` stacked along the slanted direction. -/
theorem col2 (kb : ℕ) (hkb : 0 < kb) (ekb : (kb : ℝ) = b) (x0 y0 : ℝ) :
    Pc (Mo a b ha hb) (Bp a b x0 y0 b) (2 * kb) := by
  obtain ⟨l, rfl⟩ : ∃ l, kb = l + 1 := ⟨kb - 1, by omega⟩
  have hab := mul_pos ha hb
  have hd : ((a, -a) : ℝ × ℝ).1 * ((b, (0 : ℝ)) : ℝ × ℝ).2 - ((a, -a) : ℝ × ℝ).2 * ((b, (0 : ℝ)) : ℝ × ℝ).1 ≠ 0 := by
    intro h; simp only at h; nlinarith
  have c1 : (TL hf1 (a, -a) (b, (0 : ℝ)) hd).Congruent (Mo a b ha hb) := by
    unfold TL Mo
    refine triC_cong hf1 _ _ _ _ _ _ _ _ ?_ ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, div_one] <;> ring
  have c2 : (TU hf1 (a, -a) (b, (0 : ℝ)) hd).Congruent (Mo a b ha hb) := by
    unfold TU Mo
    refine triC_cong hf1 _ _ _ _ _ _ _ _ ?_ ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, div_one] <;> ring
  have G := gridT (ThH hf1 (a, -a) (b, (0 : ℝ)) hd) (ThH_add hf1 (a, -a) (b, (0 : ℝ)) hd) (A := 1) (B := 1)
    one_pos one_pos (cellRT hf1 (a, -a) (b, (0 : ℝ)) hd (Mo a b ha hb) c1 c2) l 0
  rw [ThH_image] at G
  have G' := RegionTiling.map G (IsometryEquiv.addRight (Phi 1 (x0, y0)))
  rw [Erdos634.Draft.EqSemigroup.shift_phi] at G'
  refine ⟨_, ?_, ⟨RTiling.castN (by ring) G'⟩⟩
  rintro _ ⟨_, ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩, rfl⟩
  simp only [Lam, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Nat.cast_zero,
    zero_add, one_mul] at h1 h2 h3 h4 ⊢
  push_cast at ekb
  have e1 : z.1 * a ≤ ((l : ℝ) + 1) * a := mul_le_mul_of_nonneg_right h2 ha.le
  have e2 : 0 ≤ z.1 * a := mul_nonneg h1 ha.le
  have e3 : z.2 * b ≤ 1 * b := mul_le_mul_of_nonneg_right h4 hb.le
  have e4 : 0 ≤ z.2 * b := mul_nonneg h3 hb.le
  rw [ekb] at e1
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> nlinarith


end cols

/-! ### the semigroup `⟨a, b⟩` and the parallelogram -/

inductive InSG (a b : ℕ) : ℕ → Prop
  | zero : InSG a b 0
  | addA {w : ℕ} : InSG a b w → InSG a b (w + a)
  | addB {w : ℕ} : InSG a b w → InSG a b (w + b)

theorem InSG.mulB {a b W : ℕ} (h : InSG a b W) (n : ℕ) : InSG a b (W + n * b) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have := ih.addB
    rwa [show W + n * b + b = W + (n + 1) * b by ring] at this

theorem InSG.addKAB {a b W : ℕ} (h : InSG a b W) (k : ℕ) : InSG a b (W + k * (a * b)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have := ih.mulB a
    rwa [show W + k * (a * b) + a * b = W + (k + 1) * (a * b) by ring] at this

/-- the model tile `(a, b, c)` for natural `a, b`. -/
noncomputable def Mn (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : TriG :=
  Mo (a : ℝ) (b : ℝ) (Nat.cast_pos.2 ha) (Nat.cast_pos.2 hb)

section nat
variable {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
include ha hb

/-- the parallelogram of width `W ∈ ⟨a, b⟩` and height `ab` (top-left corner `(x0, y0)`): `2W` tiles. -/
theorem paraPc {W : ℕ} (hW : InSG a b W) : ∀ x0 y0 : ℝ, Pc (Mn a b ha hb) (Bp (a : ℝ) (b : ℝ) x0 y0 (W : ℝ)) (2 * W) := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hab := mul_pos haR hbR
  induction hW with
  | zero => intro x0 y0; exact Pc.zero _ _
  | @addA w hw ih =>
    intro x0 y0
    have P := (ih x0 y0).glueLin (col1 haR hbR a ha rfl (x0 + w) y0) 1 1 (x0 + y0 + w) one_ne_zero
      (fun p hp => by have := hp.2.2.2; linarith) (fun p hp => by have := hp.2.2.1; linarith)
      (B := Bp (a : ℝ) (b : ℝ) x0 y0 ((w + a : ℕ) : ℝ))
      (by
        rintro p (hp | hp)
        · obtain ⟨h1, h2, h3, h4⟩ := hp
          push_cast
          refine ⟨h1, h2, h3, by linarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hp
          push_cast
          refine ⟨h1, h2, by linarith [(Nat.cast_nonneg w : (0:ℝ) ≤ w)], by linarith⟩)
    exact P.castN (by ring)
  | @addB w hw ih =>
    intro x0 y0
    have P := (ih x0 y0).glueLin (col2 haR hbR b hb rfl (x0 + w) y0) 1 1 (x0 + y0 + w) one_ne_zero
      (fun p hp => by have := hp.2.2.2; linarith) (fun p hp => by have := hp.2.2.1; linarith)
      (B := Bp (a : ℝ) (b : ℝ) x0 y0 ((w + b : ℕ) : ℝ))
      (by
        rintro p (hp | hp)
        · obtain ⟨h1, h2, h3, h4⟩ := hp
          push_cast
          refine ⟨h1, h2, h3, by linarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b)]⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hp
          push_cast
          refine ⟨h1, h2, by linarith [(Nat.cast_nonneg w : (0:ℝ) ≤ w)], by linarith⟩)
    exact P.castN (by ring)

end nat

/-! ### the row and the ideal trapezoid -/

def Brow (a b h W : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ h ≤ p.2 ∧ p.2 ≤ h + a * b ∧ p.1 + p.2 ≤ h + (a ^ 2 + b ^ 2) + W + a * b}

def Btrap (a b h0 W0 k : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ h0 ≤ p.2 ∧ p.2 ≤ h0 + k * (a * b) ∧ p.1 + p.2 ≤ h0 + (a ^ 2 + b ^ 2) + W0 + k * (a * b)}

/-- tile count of a trapezoid of `k` rows. -/
def cntT (a b c W0 : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (a * a + b * b + c * c + 2 * (W0 + k * (a * b))) + cntT a b c W0 k

theorem cntT_closed (a b c W0 k : ℕ) :
    cntT a b c W0 k + a * b * k = k * (a * a + b * b + c * c + 2 * W0) + a * b * k * k := by
  induction k with
  | zero => simp [cntT]
  | succ k ih => simp only [cntT]; nlinarith [ih]

section nat2
variable {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
include ha hb hc

theorem hcpos : 0 < c := by
  have : 0 < c ^ 2 := by rw [hc]; positivity
  exact Nat.pos_of_ne_zero (fun h => by simp [h] at this)

/-- a row: basic trapezoid + parallelogram of width `W ∈ ⟨a,b⟩`; `a²+b²+c²+2W` tiles. -/
theorem rowPc {W : ℕ} (hW : InSG a b W) (h : ℝ) :
    Pc (Mn a b ha hb) (Brow (a : ℝ) (b : ℝ) h (W : ℝ)) (a * a + b * b + c * c + 2 * W) := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hcR : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + a * b + (b : ℝ) ^ 2 := by exact_mod_cast hc
  have hab := mul_pos haR hbR
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have P1 := basic_real haR hbR a b c ha hb (hcpos ha hb hc) rfl rfl hcR ((0 : ℝ), h)
  have P2 := paraPc ha hb hW ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) (h + (a : ℝ) * b)
  have P := P1.glueLin P2 1 1 (h + ((a : ℝ) ^ 2 + a * b + (b : ℝ) ^ 2)) one_ne_zero
    (fun p hp => by have := hp.2.2.2; simp only at this; linarith)
    (fun p hp => by have := hp.2.2.1; linarith)
    (B := Brow (a : ℝ) (b : ℝ) h (W : ℝ))
    (by
      rintro p (hp | hp)
      · obtain ⟨h1, h2, h3, h4⟩ := hp
        simp only at h1 h2 h3 h4
        refine ⟨h1, h2, h3, by linarith⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hp
        refine ⟨by nlinarith [sq_nonneg (a : ℝ), sq_nonneg (b : ℝ)], by linarith, by linarith, by linarith⟩)
  exact P


/-- the ideal trapezoid of `k` rows (short side `a²+b²+W0`, `W0 ∈ ⟨a,b⟩`, leg `k a b`). -/
theorem trapPc {W0 : ℕ} (hW0 : InSG a b W0) (k : ℕ) :
    ∀ h0 : ℝ, Pc (Mn a b ha hb) (Btrap (a : ℝ) (b : ℝ) h0 (W0 : ℝ) (k : ℝ)) (cntT a b c W0 k) := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hab := mul_pos haR hbR
  have hW : (0 : ℝ) ≤ W0 := Nat.cast_nonneg W0
  induction k with
  | zero => intro h0; exact Pc.zero _ _
  | succ k ih =>
    intro h0
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have P := (rowPc ha hb hc (hW0.addKAB k) h0).glueY (ih (h0 + (a : ℝ) * b)) (h0 + (a : ℝ) * b)
      (fun p hp => hp.2.2.1) (fun p hp => hp.2.1)
      (B := Btrap (a : ℝ) (b : ℝ) h0 (W0 : ℝ) ((k + 1 : ℕ) : ℝ))
      (by
        rintro p (hp | hp)
        · obtain ⟨h1, h2, h3, h4⟩ := hp
          push_cast at h4 ⊢
          refine ⟨h1, h2, by nlinarith, by nlinarith⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hp
          push_cast
          refine ⟨h1, by linarith, by nlinarith, by nlinarith⟩)
    exact P

end nat2

end Erdos634.Draft.ZhangTrap
