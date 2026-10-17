/-
Draft/ZhangBase.lean — first layer of the tile-uniform formalisation of Zhang's Theorem 4 (arXiv:2512.22696): the
`Pc` calculus ("some subset of the bounding set `B` is tiled by `N` copies of the model"), the model tile
`Mo a b = triC 1 hf1 (0,0) (a,b) (0,b)` (a `2π/3` tile with sides `a, b, c`, `c² = a²+ab+b²`), ladder pieces
(`ladRT`) and the *basic ideal trapezoid* `basicPc`: the trapezoid with parallel sides `a²+b²` and `c²` and leg `ab`
is the union of three ladder triangles (scales `a`, `b`, `c`), `a²+b²+c²` tiles.

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.EqSemigroup

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Tset Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.ZhangBase
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.Draft.S2L (mem_hull3' tri_le tri_ge tri_fst_le tri_fst_ge tri_snd_le tri_snd_ge pack_exists)
open Erdos634.Draft.WBrickF (interior_disj_lin)
open Erdos634.Draft.F4All (hf1)

abbrev TriG := Erdos634.Geometry.Tri

/-! ### the `Pc` calculus -/

/-- some subset of `B` (in skew coordinates) is tiled by `N` copies of `M`. -/
def Pc (M : TriG) (B : Set (ℝ × ℝ)) (N : ℕ) : Prop :=
  ∃ S : Set (ℝ × ℝ), S ⊆ B ∧ Nonempty (RTiling (Phi 1 '' S) M N)

theorem Pc.mono {M : TriG} {B B' : Set (ℝ × ℝ)} {N : ℕ} (h : Pc M B N) (hB : B ⊆ B') : Pc M B' N := by
  obtain ⟨S, hS, hR⟩ := h
  exact ⟨S, hS.trans hB, hR⟩

theorem Pc.castN {M : TriG} {B : Set (ℝ × ℝ)} {N N' : ℕ} (h : Pc M B N) (e : N = N') : Pc M B N' := e ▸ h

theorem Pc.zero (M : TriG) (B : Set (ℝ × ℝ)) : Pc M B 0 :=
  ⟨∅, Set.empty_subset _, ⟨RTiling.mk (fun i => i.elim0) (by simp) (fun i => i.elim0) (fun i => i.elim0)⟩⟩

theorem Pc.glue {M : TriG} {B1 B2 : Set (ℝ × ℝ)} {N1 N2 : ℕ} (h1 : Pc M B1 N1) (h2 : Pc M B2 N2)
    (hd : Disjoint (interior B1) (interior B2)) {B : Set (ℝ × ℝ)} (hB : B1 ∪ B2 ⊆ B) : Pc M B (N1 + N2) := by
  obtain ⟨S1, hS1, ⟨R1⟩⟩ := h1
  obtain ⟨S2, hS2, ⟨R2⟩⟩ := h2
  refine ⟨S1 ∪ S2, (Set.union_subset_union hS1 hS2).trans hB, ⟨?_⟩⟩
  have hd' : Disjoint (interior S1) (interior S2) := hd.mono (interior_mono hS1) (interior_mono hS2)
  exact RTiling.cast (Set.image_union _ _ _).symm (union R1 R2 (disjoint_image' hf1 hd'))

theorem Pc.glueLin {M : TriG} {B1 B2 : Set (ℝ × ℝ)} {N1 N2 : ℕ} (h1 : Pc M B1 N1) (h2 : Pc M B2 N2)
    (α β γ : ℝ) (hα : α ≠ 0) (hB1 : ∀ p ∈ B1, α * p.1 + β * p.2 ≤ γ) (hB2 : ∀ p ∈ B2, γ ≤ α * p.1 + β * p.2)
    {B : Set (ℝ × ℝ)} (hB : ∀ p, p ∈ B1 ∨ p ∈ B2 → p ∈ B) : Pc M B (N1 + N2) :=
  h1.glue h2 (interior_disj_lin α β γ hα hB1 hB2) (fun p hp => hB p hp)

theorem Pc.glueY {M : TriG} {B1 B2 : Set (ℝ × ℝ)} {N1 N2 : ℕ} (h1 : Pc M B1 N1) (h2 : Pc M B2 N2)
    (γ : ℝ) (hB1 : ∀ p ∈ B1, p.2 ≤ γ) (hB2 : ∀ p ∈ B2, γ ≤ p.2)
    {B : Set (ℝ × ℝ)} (hB : ∀ p, p ∈ B1 ∨ p ∈ B2 → p ∈ B) : Pc M B (N1 + N2) :=
  h1.glue h2 (interior_disj_snd γ hB1 hB2) (fun p hp => hB p hp)

/-! ### the model tile and ladder pieces -/

/-- the `2π/3` tile with sides `a, b` and third side `√(a²+ab+b²)`. -/
noncomputable def Mo (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : TriG :=
  triC 1 hf1 0 (a, b) (0, b) (by
    intro h; have := mul_pos ha hb
    simp only [Prod.fst_zero, Prod.snd_zero] at h; nlinarith)

open MeasureTheory in
theorem vol_Mo (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : volume (Mo a b ha hb).carrier
    = ENNReal.ofReal (|sD 1 / (2 * 1)| * (a * b)) * volume Erdos634.AreaDet.stdCarrier := by
  unfold Mo
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  simp only [Prod.fst_zero, Prod.snd_zero]
  rw [show (a - 0) * (b - 0) - (0 - 0) * (b - 0) = a * b by ring, abs_of_pos (mul_pos ha hb)]

/-- a triangle `O, V1, V2` with squared form-sides `k²(a²+ab+b²), k²a², k²b²` is `k²` tiles `Mo a b`. -/
noncomputable def ladRT (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (O V1 V2 : ℝ × ℝ) (k : ℕ) (hk : 0 < k)
    (hd : (V1.1 - O.1) * (V2.2 - O.2) - (V2.1 - O.1) * (V1.2 - O.2) ≠ 0)
    (H01 : (O.1 - V1.1) ^ 2 + (O.2 - V1.2) ^ 2 + (O.1 - V1.1) * (O.2 - V1.2) = (k : ℝ) ^ 2 * (a ^ 2 + a * b + b ^ 2))
    (H12 : (V1.1 - V2.1) ^ 2 + (V1.2 - V2.2) ^ 2 + (V1.1 - V2.1) * (V1.2 - V2.2) = (k : ℝ) ^ 2 * a ^ 2)
    (H20 : (V2.1 - O.1) ^ 2 + (V2.2 - O.2) ^ 2 + (V2.1 - O.1) * (V2.2 - O.2) = (k : ℝ) ^ 2 * b ^ 2) :
    RTiling (Phi 1 '' convexHull ℝ {O, V1, V2}) (Mo a b ha hb) (k * k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := hk'.ne'
  refine scaledRT 1 hf1 O V1 V2 k hk hd _ ?_
  unfold baseTri Mo
  refine triC_cong hf1 _ _ _ _ _ _ _ _ ?_ ?_ ?_
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_zero, Prod.snd_zero, div_one]
    field_simp
    linear_combination H01
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_zero, Prod.snd_zero, div_one]
    field_simp
    linear_combination H12
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_zero, Prod.snd_zero, div_one]
    field_simp
    linear_combination H20


/-! ### the basic ideal trapezoid -/
section basic
variable (a b : ℝ)

/-- the trapezoid `O, O+(c²,0), O+(a²+b²,ab), O+(0,ab)` (short side `a²+b²`, long side `c²`, leg `ab`, two angles `π/3`). -/
def pB (O : ℝ × ℝ) : ℝ × ℝ := (O.1 + (a ^ 2 + a * b + b ^ 2), O.2)
def pC (O : ℝ × ℝ) : ℝ × ℝ := (O.1 + (a ^ 2 + b ^ 2), O.2 + a * b)
def pD (O : ℝ × ℝ) : ℝ × ℝ := (O.1, O.2 + a * b)
def pE (O : ℝ × ℝ) : ℝ × ℝ := (O.1 + a ^ 2, O.2 + a * b)

def Bb (O : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | O.1 ≤ p.1 ∧ O.2 ≤ p.2 ∧ p.2 ≤ O.2 + a * b ∧ p.1 + p.2 ≤ O.1 + O.2 + (a ^ 2 + a * b + b ^ 2)}

variable {a b}
variable (ha : 0 < a) (hb : 0 < b)
include ha hb

theorem hull_Bb (O : ℝ × ℝ) {x y z : ℝ × ℝ} (hx : x ∈ Bb a b O) (hy : y ∈ Bb a b O) (hz : z ∈ Bb a b O) :
    convexHull ℝ {x, y, z} ⊆ Bb a b O := by
  intro p hp
  refine ⟨tri_fst_ge _ hx.1 hy.1 hz.1 p hp, tri_snd_ge _ hx.2.1 hy.2.1 hz.2.1 p hp,
    tri_snd_le _ hx.2.2.1 hy.2.2.1 hz.2.2.1 p hp, ?_⟩
  have := tri_le (A := x) (B := y) (C := z) 1 1 (O.1 + O.2 + (a ^ 2 + a * b + b ^ 2))
    (by simpa using hx.2.2.2) (by simpa using hy.2.2.2) (by simpa using hz.2.2.2) p hp
  simpa using this

theorem O_mem (O : ℝ × ℝ) : O ∈ Bb a b O := by
  have := mul_pos ha hb
  refine ⟨le_rfl, le_rfl, by linarith, by nlinarith [sq_nonneg a, sq_nonneg b]⟩
theorem B_mem (O : ℝ × ℝ) : pB a b O ∈ Bb a b O := by
  have := mul_pos ha hb
  refine ⟨by simp only [pB]; nlinarith [sq_nonneg a, sq_nonneg b], by simp only [pB]; linarith,
    by simp only [pB]; linarith, by simp only [pB]; linarith⟩
theorem C_mem (O : ℝ × ℝ) : pC a b O ∈ Bb a b O := by
  have := mul_pos ha hb
  refine ⟨by simp only [pC]; nlinarith [sq_nonneg a, sq_nonneg b], by simp only [pC]; linarith,
    by simp only [pC]; linarith, by simp only [pC]; linarith⟩
theorem D_mem (O : ℝ × ℝ) : pD a b O ∈ Bb a b O := by
  have := mul_pos ha hb
  refine ⟨by simp only [pD]; linarith, by simp only [pD]; linarith,
    by simp only [pD]; linarith, by simp only [pD]; nlinarith [sq_nonneg a, sq_nonneg b]⟩
theorem E_mem (O : ℝ × ℝ) : pE a b O ∈ Bb a b O := by
  have := mul_pos ha hb
  refine ⟨by simp only [pE]; nlinarith [sq_nonneg a, sq_nonneg b], by simp only [pE]; linarith,
    by simp only [pE]; linarith, by simp only [pE]; nlinarith [sq_nonneg a, sq_nonneg b]⟩


theorem basic_real (ka kb kc : ℕ) (hka : 0 < ka) (hkb : 0 < kb) (hkc : 0 < kc)
    (eka : (ka : ℝ) = a) (ekb : (kb : ℝ) = b) (ekc : (kc : ℝ) ^ 2 = a ^ 2 + a * b + b ^ 2) (O : ℝ × ℝ) :
    Pc (Mo a b ha hb) (Bb a b O) (ka * ka + kb * kb + kc * kc) := by
  have hab := mul_pos ha hb
  have hc2 : 0 < a ^ 2 + a * b + b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  -- the three ladder triangles
  have R1 := ladRT a b ha hb O (pE a b O) (pD a b O) ka hka
    (by simp only [pE, pD]; intro h; nlinarith [mul_pos (pow_pos ha 3) hb])
    (by rw [eka]; simp only [pE, pD]; ring) (by rw [eka]; simp only [pE, pD]; ring)
    (by rw [eka]; simp only [pE, pD]; ring)
  have R2 := ladRT a b ha hb (pE a b O) (pB a b O) (pC a b O) kb hkb
    (by simp only [pE, pB, pC]; intro h; nlinarith [mul_pos ha (pow_pos hb 3)])
    (by rw [ekb]; simp only [pE, pB, pC]; ring) (by rw [ekb]; simp only [pE, pB, pC]; ring)
    (by rw [ekb]; simp only [pE, pB, pC]; ring)
  have R3 := ladRT a b ha hb (pB a b O) O (pE a b O) kc hkc
    (by simp only [pE, pB]; intro h; nlinarith [mul_pos hc2 hab])
    (by rw [ekc]; simp only [pE, pB]; ring) (by rw [ekc]; simp only [pE, pB]; ring)
    (by rw [ekc]; simp only [pE, pB]; ring)
  have P1 : Pc (Mo a b ha hb) (convexHull ℝ {O, pE a b O, pD a b O}) (ka * ka) := ⟨_, subset_rfl, ⟨R1⟩⟩
  have P2 : Pc (Mo a b ha hb) (convexHull ℝ {pE a b O, pB a b O, pC a b O}) (kb * kb) := ⟨_, subset_rfl, ⟨R2⟩⟩
  have P3 : Pc (Mo a b ha hb) (convexHull ℝ {pB a b O, O, pE a b O}) (kc * kc) := ⟨_, subset_rfl, ⟨R3⟩⟩
  have s1 := hull_Bb ha hb O (O_mem ha hb O) (E_mem ha hb O) (D_mem ha hb O)
  have s2 := hull_Bb ha hb O (E_mem ha hb O) (B_mem ha hb O) (C_mem ha hb O)
  have s3 := hull_Bb ha hb O (B_mem ha hb O) (O_mem ha hb O) (E_mem ha hb O)
  -- line L1 : b X - a Y = b O.1 - a O.2  separates T1 (≤) from T3 (≥)
  have l1a : ∀ p ∈ convexHull ℝ {O, pE a b O, pD a b O}, b * p.1 + (-a) * p.2 ≤ b * O.1 + (-a) * O.2 :=
    tri_le _ _ _ (by nlinarith) (by simp only [pE]; nlinarith) (by simp only [pD]; nlinarith [mul_pos ha hab])
  have l1b : ∀ p ∈ convexHull ℝ {pB a b O, O, pE a b O}, b * O.1 + (-a) * O.2 ≤ b * p.1 + (-a) * p.2 :=
    tri_ge _ _ _ (by simp only [pB]; nlinarith [mul_pos hb hc2]) (by nlinarith) (by simp only [pE]; nlinarith)
  -- line L2 : a X + (a+b) Y = γ2 : T1, T3 below ; T2 above
  have l2a : ∀ p ∈ convexHull ℝ {O, pE a b O, pD a b O},
      a * p.1 + (a + b) * p.2 ≤ a * O.1 + (a + b) * O.2 + a * (a ^ 2 + a * b + b ^ 2) :=
    tri_le _ _ _ (by nlinarith [mul_pos ha hc2]) (by simp only [pE]; nlinarith)
      (by simp only [pD]; nlinarith [mul_pos ha hc2, pow_pos ha 3, mul_pos (pow_pos ha 2) hb])
  have l2b : ∀ p ∈ convexHull ℝ {pB a b O, O, pE a b O},
      a * p.1 + (a + b) * p.2 ≤ a * O.1 + (a + b) * O.2 + a * (a ^ 2 + a * b + b ^ 2) :=
    tri_le _ _ _ (by simp only [pB]; nlinarith) (by nlinarith [mul_pos ha hc2]) (by simp only [pE]; nlinarith)
  have l2c : ∀ p ∈ convexHull ℝ {pE a b O, pB a b O, pC a b O},
      a * O.1 + (a + b) * O.2 + a * (a ^ 2 + a * b + b ^ 2) ≤ a * p.1 + (a + b) * p.2 :=
    tri_ge _ _ _ (by simp only [pE]; nlinarith) (by simp only [pB]; nlinarith)
      (by simp only [pC]; nlinarith [mul_pos ha (pow_pos hb 2), pow_pos ha 3, mul_pos (pow_pos ha 2) hb])
  have P13 := P1.glueLin P3 b (-a) (b * O.1 + (-a) * O.2) hb.ne' l1a l1b
    (B := {p | p ∈ Bb a b O ∧ a * p.1 + (a + b) * p.2 ≤ a * O.1 + (a + b) * O.2 + a * (a ^ 2 + a * b + b ^ 2)})
    (by
      rintro p (hp | hp)
      · exact ⟨s1 hp, l2a p hp⟩
      · exact ⟨s3 hp, l2b p hp⟩)
  have P123 := P13.glueLin P2 a (a + b) (a * O.1 + (a + b) * O.2 + a * (a ^ 2 + a * b + b ^ 2)) ha.ne'
    (fun p hp => hp.2) l2c (B := Bb a b O)
    (by
      rintro p (hp | hp)
      · exact hp.1
      · exact s2 hp)
  exact P123.castN (by ring)

end basic
end Erdos634.Draft.ZhangBase
