/-
Draft/ZhangEqui.lean — **Zhang's Theorem 4, tile-uniform**: for a `2π/3` tile `(a, b, c)`, `c² = a² + ab + b²`, the
equilateral triangle of side `ab (r+s+t)` is cut into `ab (r+s+t)²` tiles whenever `r ab`, `s ab`, `t ab` each lie in
`a² + b² + ⟨a, b⟩` (`zhang_equi`).  Consequently `ab m²` is a tile count for every `m ≥ 3 t₀`, where `t₀ ab ∈ a²+b²+⟨a,b⟩`
(`zhang_equi_m`).

Construction (Zhang, arXiv:2512.22696, Thm 4; this is the formal, tile-uniform statement).  Three "ideal trapezoids"
(`ZhangTrap.trapPc`: short side `x ∈ {r,s,t}·ab`, `k ∈ {r,s,t}` rows of a basic piece `a²+b²+c²` + a parallelogram
`(x - a² - b²) × ab`) arranged as a pinwheel (the rotations `rotB`, `rotC` of `ZhangRot`).

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.ZhangRot

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Tset Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.ZhangEqui
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.Draft.S2L (pack_exists)
open Erdos634.Draft.WBrickF (interior_disj_lin)
open Erdos634.Draft.F4All (hf1)
open Erdos634.Draft.ZhangBase Erdos634.Draft.ZhangTrap Erdos634.Draft.ZhangRot
open Erdos634.Draft.EqSemigroup (eqTri carrier_eqTri vol_eqTri)
open Erdos634.Draft.TileCountFamilies (TileCount)

theorem cnt_trap (a b c W t k : ℕ) (hc' : c * c = a * a + a * b + b * b) (ht : t * (a * b) = a * a + b * b + W) :
    cntT a b c W k = a * b * (k * (2 * t + k)) := by
  have h := cntT_closed a b c W k
  zify at h hc' ht ⊢
  linear_combination h + (k : ℤ) * hc' - 2 * (k : ℤ) * ht


open MeasureTheory in
/-- **The pinwheel.** -/
theorem equi_dissection {a b c r s t Wr Ws Wt : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hr : r * (a * b) = a * a + b * b + Wr) (hs : s * (a * b) = a * a + b * b + Ws)
    (ht : t * (a * b) = a * a + b * b + Wt) (gr : InSG a b Wr) (gs : InSG a b Ws) (gt : InSG a b Wt) :
    ∃ hL : 0 < a * b * (r + s + t), ∃ D : CongruentDissection (a * b * (r + s + t) ^ 2),
      D.model = Mn a b ha hb ∧ D.target = eqTri (a * b * (r + s + t)) hL := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hab : (0 : ℝ) < (a : ℝ) * b := mul_pos haR hbR
  have hc' : c * c = a * a + a * b + b * b := by nlinarith [hc]
  have hr0 : 0 < r := Nat.pos_of_ne_zero (by
    rintro rfl; rw [zero_mul] at hr
    have : 0 < a * a + b * b + Wr := by positivity
    omega)
  have hL : 0 < a * b * (r + s + t) := Nat.mul_pos (Nat.mul_pos ha hb) (by omega)
  refine ⟨hL, ?_⟩
  have hLR : (((a * b * (r + s + t) : ℕ)) : ℝ) = (a : ℝ) * b * ((r : ℝ) + s + t) := by push_cast; ring
  have hrR : (r : ℝ) * ((a : ℝ) * b) = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + Wr := by
    have := congrArg (Nat.cast : ℕ → ℝ) hr; push_cast at this; linarith [this]
  have hsR : (s : ℝ) * ((a : ℝ) * b) = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + Ws := by
    have := congrArg (Nat.cast : ℕ → ℝ) hs; push_cast at this; linarith [this]
  have htR : (t : ℝ) * ((a : ℝ) * b) = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + Wt := by
    have := congrArg (Nat.cast : ℕ → ℝ) ht; push_cast at this; linarith [this]
  have hr0R : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs0R : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have ht0R : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  set L : ℕ := a * b * (r + s + t) with hLdef
  -- the three trapezoids
  have PA := trapPc ha hb hc gt r 0
  have PB0 := trapPc ha hb hc gr s 0
  have PC0 := trapPc ha hb hc gs t 0
  have PB := Pc.map PB0 (rotB (L : ℝ)) (rotC (L : ℝ)) (rotC_rotB _) (rotB_rotC _) (rotB_q _)
  have PC := Pc.map PC0 (rotC (L : ℝ)) (rotB (L : ℝ)) (rotB_rotC _) (rotC_rotB _) (rotC_q _)
  obtain ⟨SA, hSA, ⟨RA⟩⟩ := PA
  obtain ⟨SB, hSB, ⟨RB⟩⟩ := PB
  obtain ⟨SC, hSC, ⟨RC⟩⟩ := PC
  have bA : ∀ p ∈ SA, 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ r * ((a : ℝ) * b) ∧
      p.1 + p.2 ≤ (t + r) * ((a : ℝ) * b) := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hSA hp
    refine ⟨h1, h2, by linarith, by linarith⟩
  have bB : ∀ p ∈ SB, 0 ≤ p.2 ∧ (L : ℝ) - s * ((a : ℝ) * b) ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ (L : ℝ) ∧
      t * ((a : ℝ) * b) ≤ p.1 := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := hSB hp
    obtain ⟨h1, h2, h3, h4⟩ := hu
    simp only [rotB]
    refine ⟨h1, by linarith, by linarith, by linarith⟩
  have bC : ∀ p ∈ SC, 0 ≤ p.1 ∧ p.1 ≤ t * ((a : ℝ) * b) ∧ r * ((a : ℝ) * b) ≤ p.2 ∧
      p.1 + p.2 ≤ (L : ℝ) := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := hSC hp
    obtain ⟨h1, h2, h3, h4⟩ := hu
    simp only [rotC]
    refine ⟨h2, by linarith, by linarith, by linarith⟩
  -- pairwise disjointness
  have dAC : Disjoint (interior SA) (interior SC) :=
    interior_disj_snd (r * ((a : ℝ) * b)) (fun p hp => (bA p hp).2.2.1) (fun p hp => (bC p hp).2.2.1)
  have dAB : Disjoint (interior SA) (interior SB) :=
    interior_disj_lin 1 1 ((t + r) * ((a : ℝ) * b)) one_ne_zero
      (fun p hp => by have := (bA p hp).2.2.2; linarith)
      (fun p hp => by
        have := (bB p hp).2.1
        have e : (L : ℝ) - s * ((a : ℝ) * b) = (t + r) * ((a : ℝ) * b) := by rw [hLR]; ring
        linarith)
  have dCB : Disjoint (interior SC) (interior SB) :=
    interior_disj_fst (t * ((a : ℝ) * b)) (fun p hp => (bC p hp).2.1) (fun p hp => (bB p hp).2.2.2)
  have hsubT : ∀ x : ℝ × ℝ, (0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ (L : ℝ)) → x ∈ Tset (L : ℝ) := fun x h => h
  have sA : SA ⊆ Tset (L : ℝ) := fun p hp => by
    obtain ⟨h1, h2, h3, h4⟩ := bA p hp
    refine ⟨h1, h2, ?_⟩
    rw [hLR]; nlinarith [mul_nonneg hs0R hab.le]
  have sB : SB ⊆ Tset (L : ℝ) := fun p hp => by
    obtain ⟨h1, h2, h3, h4⟩ := bB p hp
    refine ⟨by nlinarith [mul_nonneg ht0R hab.le], h1, h3⟩
  have sC : SC ⊆ Tset (L : ℝ) := fun p hp => by
    obtain ⟨h1, h2, h3, h4⟩ := bC p hp
    refine ⟨h1, by nlinarith [mul_nonneg hr0R hab.le], h4⟩
  -- counts
  have hNtot : cntT a b c Wt r + cntT a b c Wr s + cntT a b c Ws t = a * b * (r + s + t) ^ 2 := by
    rw [cnt_trap a b c Wt t r hc' ht, cnt_trap a b c Wr r s hc' hr, cnt_trap a b c Ws s t hc' hs]; ring
  have hsum : ∑ i : Fin 3, (![cntT a b c Wt r, cntT a b c Wr s, cntT a b c Ws t] : Fin 3 → ℕ) i
      = a * b * (r + s + t) ^ 2 := by
    rw [← hNtot]; simp [Fin.sum_univ_three]
  have key := pack_exists (M := Mn a b ha hb) (T := eqTri L hL)
    (![Phi 1 '' SA, Phi 1 '' SB, Phi 1 '' SC])
    (![cntT a b c Wt r, cntT a b c Wr s, cntT a b c Ws t])
    (fun i => match i with
      | ⟨0, _⟩ => RA
      | ⟨1, _⟩ => RB
      | ⟨2, _⟩ => RC
      | ⟨k + 3, h⟩ => absurd h (by omega))
    (by
      intro i j hij
      exact match i, j with
        | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hij
        | ⟨0, _⟩, ⟨1, _⟩ => disjoint_image' hf1 dAB
        | ⟨0, _⟩, ⟨2, _⟩ => disjoint_image' hf1 dAC
        | ⟨1, _⟩, ⟨0, _⟩ => (disjoint_image' hf1 dAB).symm
        | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hij
        | ⟨1, _⟩, ⟨2, _⟩ => (disjoint_image' hf1 dCB).symm
        | ⟨2, _⟩, ⟨0, _⟩ => (disjoint_image' hf1 dAC).symm
        | ⟨2, _⟩, ⟨1, _⟩ => disjoint_image' hf1 dCB
        | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hij
        | ⟨k + 3, h⟩, _ => absurd h (by omega)
        | _, ⟨k + 3, h⟩ => absurd h (by omega))
    (by
      intro i
      rw [carrier_eqTri]
      exact match i with
        | ⟨0, _⟩ => Set.image_mono sA
        | ⟨1, _⟩ => Set.image_mono sB
        | ⟨2, _⟩ => Set.image_mono sC
        | ⟨k + 3, h⟩ => absurd h (by omega))
    (by
      rw [hsum]
      unfold Mn
      rw [vol_Mo, vol_eqTri, ← mul_assoc, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 2
      rw [hLR]; push_cast; ring)
  rw [hsum] at key
  exact key


/-! ### the statements -/

theorem _root_.Erdos634.Draft.ZhangTrap.InSG.mulA {a b W : ℕ} (h : InSG a b W) (n : ℕ) : InSG a b (W + n * a) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have := ih.addA
    rwa [show W + n * a + a = W + (n + 1) * a by ring] at this

theorem InSG.lin (a b i j : ℕ) : InSG a b (i * a + j * b) := by
  have h := ((InSG.zero (a := a) (b := b)).mulA i).mulB j
  simpa using h

/-- the Frobenius condition of Zhang's Theorem 4 for the multiplier `t`: `t·ab ∈ a² + b² + ⟨a, b⟩`. -/
def Frob (a b t : ℕ) : Prop := ∃ i j : ℕ, t * (a * b) = a * a + b * b + i * a + j * b

theorem Frob.succ {a b t : ℕ} (h : Frob a b t) : Frob a b (t + 1) := by
  obtain ⟨i, j, h⟩ := h
  exact ⟨i + b, j, by nlinarith [h]⟩

theorem Frob.add {a b t : ℕ} (h : Frob a b t) (n : ℕ) : Frob a b (t + n) := by
  induction n with
  | zero => simpa using h
  | succ n ih => exact ih.succ

/-- **Zhang's Theorem 4, tile-uniform** (arXiv:2512.22696, Thm 4; formal statement here): let `(a, b, c)` be a `2π/3`
tile (`c² = a² + ab + b²`) and `r, s, t` with `r ab, s ab, t ab ∈ a² + b² + ⟨a, b⟩`.  The equilateral triangle of side
`ab (r+s+t)` is cut into `ab (r+s+t)²` copies of the tile. -/
theorem zhang_equi_dissection (a b c r s t : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hr : Frob a b r) (hs : Frob a b s) (ht : Frob a b t) :
    ∃ hL : 0 < a * b * (r + s + t), ∃ D : CongruentDissection (a * b * (r + s + t) ^ 2),
      D.model = Mn a b ha hb ∧ D.target = eqTri (a * b * (r + s + t)) hL := by
  obtain ⟨i1, j1, hr⟩ := hr
  obtain ⟨i2, j2, hs⟩ := hs
  obtain ⟨i3, j3, ht⟩ := ht
  exact equi_dissection ha hb hc (Wr := i1 * a + j1 * b) (Ws := i2 * a + j2 * b) (Wt := i3 * a + j3 * b)
    (by linarith) (by linarith) (by linarith) (InSG.lin a b i1 j1) (InSG.lin a b i2 j2) (InSG.lin a b i3 j3)

theorem zhang_equi (a b c r s t : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hr : Frob a b r) (hs : Frob a b s) (ht : Frob a b t) : TileCount (a * b * (r + s + t) ^ 2) := by
  obtain ⟨-, D, -, -⟩ := zhang_equi_dissection a b c r s t ha hb hc hr hs ht
  exact ⟨D⟩

/-- **Every `m ≥ 3 t₀`**: if `t₀ ab ∈ a² + b² + ⟨a, b⟩` then `ab m²` is a tile count for all `m ≥ 3 t₀`. -/
theorem zhang_equi_m (a b c t0 m : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (h0 : Frob a b t0) (hm : 3 * t0 ≤ m) : TileCount (a * b * m ^ 2) := by
  have := zhang_equi a b c t0 t0 (t0 + (m - 3 * t0)) ha hb hc h0 h0 (h0.add _)
  rwa [show t0 + t0 + (t0 + (m - 3 * t0)) = m by omega] at this

/-- (3,5,7): `t₀ = 3` (`45 = 9 + 25 + 2·3 + 1·5`), so `15 m²` for every `m ≥ 9`; `m = 9` is the side-135 tiling (1215 tiles). -/
theorem zhang_357 (m : ℕ) (hm : 9 ≤ m) : TileCount (15 * m ^ 2) := by
  have := zhang_equi_m 3 5 7 3 m (by norm_num) (by norm_num) (by norm_num) ⟨2, 1, by norm_num⟩ (by omega)
  simpa using this

example : TileCount 1215 := by simpa using zhang_357 9 le_rfl

/-- (7,8,13): `t₀ = 3` (`168 = 49 + 64 + 1·7 + 6·8`), so `56 m²` for every `m ≥ 9` (`m = 9`: 4536 tiles). -/
theorem zhang_7813 (m : ℕ) (hm : 9 ≤ m) : TileCount (56 * m ^ 2) := by
  have := zhang_equi_m 7 8 13 3 m (by norm_num) (by norm_num) (by norm_num) ⟨1, 6, by norm_num⟩ (by omega)
  simpa using this

example : TileCount 4536 := by simpa using zhang_7813 9 le_rfl

end Erdos634.Draft.ZhangEqui

#print axioms Erdos634.Draft.ZhangEqui.equi_dissection
#print axioms Erdos634.Draft.ZhangEqui.zhang_equi
#print axioms Erdos634.Draft.ZhangEqui.zhang_equi_m
#print axioms Erdos634.Draft.ZhangEqui.zhang_357
#print axioms Erdos634.Draft.ZhangEqui.zhang_7813
