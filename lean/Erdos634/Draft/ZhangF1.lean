/-
Draft/ZhangF1.lean — Zhang's Proposition 9 (arXiv:2512.22696), tile-uniform: from the equilateral triangle of side
`m a b` tiled by `a b m²` tiles `(a, b, c)` (`ZhangEqui`), gluing one copy of the tile scaled by `m b` (sides
`m a b, m b², m b c`) on a side gives the triangle with sides `(m a b, m b c, m b (a + b))`, cut into `b (a + b) m²` tiles
(`zhang_f1`).

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.ZhangEqui

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Tset Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.ZhangF1
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.Draft.S2L (mem_hull3' tri_le tri_ge tri_fst_le tri_fst_ge tri_snd_le tri_snd_ge pack_exists)
open Erdos634.Draft.WBrickF (interior_disj_lin)
open Erdos634.Draft.F4All (hf1)
open Erdos634.Draft.ZhangBase Erdos634.Draft.ZhangTrap Erdos634.Draft.ZhangEqui
open Erdos634.Draft.EqSemigroup (eqTri carrier_eqTri vol_eqTri hull_Tset)
open Erdos634.Draft.TileCountFamilies (TileCount)

section real
variable (A B m : ℝ)

/-- `O = (0,0)`, `C = (L, 0)`, `D = (0, L)`, `B' = (-g, L+g)` with `L = m A B`, `g = m B²`. -/
def fO : ℝ × ℝ := (0, 0)
def fC : ℝ × ℝ := (m * A * B, 0)
def fD : ℝ × ℝ := (0, m * A * B)
def fB : ℝ × ℝ := (-(m * B ^ 2), m * A * B + m * B ^ 2)

variable {A B m} (hA : 0 < A) (hB : 0 < B) (hm : 0 < m)
include hA hB hm

theorem pos_L : 0 < m * A * B := by positivity
theorem pos_g : 0 < m * B ^ 2 := by positivity

theorem detT : ((fB A B m).1 - fO.1) * ((fC A B m).2 - fO.2) - ((fC A B m).1 - fO.1) * ((fB A B m).2 - fO.2) ≠ 0 := by
  have := pos_L hA hB hm
  have := pos_g hA hB hm
  simp only [fB, fC, fO]; intro h; nlinarith

theorem detR : ((fO).1 - (fB A B m).1) * ((fD A B m).2 - (fB A B m).2)
    - ((fD A B m).1 - (fB A B m).1) * ((fO).2 - (fB A B m).2) ≠ 0 := by
  have := pos_L hA hB hm
  have := pos_g hA hB hm
  simp only [fB, fD, fO]; intro h; nlinarith

/-- the target `O B' C` (sides `m a b`, `m b c`, `m b (a+b)`). -/
noncomputable def tgt : TriG := triC 1 hf1 fO (fB A B m) (fC A B m) (detT hA hB hm)

theorem sub_tgt {S : Set (ℝ × ℝ)} (hS : S ⊆ convexHull ℝ {fO, fB A B m, fC A B m}) :
    Phi 1 '' S ⊆ (tgt hA hB hm).carrier := by
  rw [tgt, carrier_triC]; exact Set.image_mono hS

theorem mem_fO : fO ∈ convexHull ℝ ({fO, fB A B m, fC A B m} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)
theorem mem_fB : fB A B m ∈ convexHull ℝ ({fO, fB A B m, fC A B m} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)
theorem mem_fC : fC A B m ∈ convexHull ℝ ({fO, fB A B m, fC A B m} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)
theorem mem_fD : fD A B m ∈ convexHull ℝ ({fO, fB A B m, fC A B m} : Set (ℝ × ℝ)) := by
  have := pos_L hA hB hm
  have := pos_g hA hB hm
  exact mem_hull3' (A := fO) (B := fB A B m) (C := fC A B m) (m * A * B + m * B ^ 2)
    0 (m * A * B) (m * B ^ 2) (by linarith) le_rfl (by linarith) (by linarith) (by ring) (fD A B m)
    (by simp only [fD, fB, fC, fO]; ring) (by simp only [fD, fB, fC, fO]; ring)

theorem hull_sub {x y z : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ ({fO, fB A B m, fC A B m} : Set (ℝ × ℝ)))
    (hy : y ∈ convexHull ℝ ({fO, fB A B m, fC A B m} : Set (ℝ × ℝ)))
    (hz : z ∈ convexHull ℝ ({fO, fB A B m, fC A B m} : Set (ℝ × ℝ))) :
    convexHull ℝ ({x, y, z} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({fO, fB A B m, fC A B m} : Set (ℝ × ℝ)) := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem subE : Tset (m * A * B) ⊆ convexHull ℝ ({fO, fB A B m, fC A B m} : Set (ℝ × ℝ)) := by
  rw [← hull_Tset _ (pos_L hA hB hm)]
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  · exact mem_fO hA hB hm
  · exact mem_fC hA hB hm
  · exact mem_fD hA hB hm

open MeasureTheory in
theorem f1_real (k N : ℕ) (hk : 0 < k) (ek : (k : ℝ) = m * B)
    (hN : (N : ℝ) * (A * B) = (m * A * B) ^ 2)
    (RE : RTiling (Phi 1 '' Tset (m * A * B)) (Mo A B hA hB) N) :
    ∃ D : CongruentDissection (N + k * k), D.model = Mo A B hA hB ∧ D.target = tgt hA hB hm := by
  have hL := pos_L hA hB hm
  have hg := pos_g hA hB hm
  have RT := ladRT A B hA hB (fB A B m) fO (fD A B m) k hk (by simpa using detR hA hB hm)
    (by rw [ek]; simp only [fB, fD, fO]; ring)
    (by rw [ek]; simp only [fB, fD, fO]; ring)
    (by rw [ek]; simp only [fB, fD, fO]; ring)
  have hsum : ∑ a : Fin 2, (![N, k * k] : Fin 2 → ℕ) a = N + k * k := by
    simp [Fin.sum_univ_two]
  have bT : ∀ p ∈ convexHull ℝ ({fB A B m, fO, fD A B m} : Set (ℝ × ℝ)), p.1 ≤ 0 := fun p hp =>
    tri_fst_le 0 (by simp [fB]; linarith) (by simp [fO]) (by simp [fD]) p hp
  have bE : ∀ p ∈ Tset (m * A * B), 0 ≤ p.1 := fun p hp => hp.1
  have dTE : Disjoint (interior (Phi 1 '' convexHull ℝ ({fB A B m, fO, fD A B m} : Set (ℝ × ℝ))))
      (interior (Phi 1 '' Tset (m * A * B))) :=
    disjoint_image' hf1 (interior_disj_fst 0 bT bE)
  have sT : convexHull ℝ ({fB A B m, fO, fD A B m} : Set (ℝ × ℝ)) ⊆
      convexHull ℝ ({fO, fB A B m, fC A B m} : Set (ℝ × ℝ)) :=
    hull_sub hA hB hm (mem_fB hA hB hm) (mem_fO hA hB hm) (mem_fD hA hB hm)
  have key := pack_exists (M := Mo A B hA hB) (T := tgt hA hB hm)
    (![Phi 1 '' Tset (m * A * B), Phi 1 '' convexHull ℝ ({fB A B m, fO, fD A B m} : Set (ℝ × ℝ))])
    (![N, k * k])
    (fun i => match i with
      | ⟨0, _⟩ => RE
      | ⟨1, _⟩ => RT
      | ⟨k + 2, h⟩ => absurd h (by omega))
    (by
      intro i j hij
      exact match i, j with
        | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hij
        | ⟨0, _⟩, ⟨1, _⟩ => dTE.symm
        | ⟨1, _⟩, ⟨0, _⟩ => dTE
        | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hij
        | ⟨k + 2, h⟩, _ => absurd h (by omega)
        | _, ⟨k + 2, h⟩ => absurd h (by omega))
    (by
      intro i
      exact match i with
        | ⟨0, _⟩ => sub_tgt hA hB hm (subE hA hB hm)
        | ⟨1, _⟩ => sub_tgt hA hB hm sT
        | ⟨k + 2, h⟩ => absurd h (by omega))
    (by
      rw [hsum, vol_Mo, tgt, vol_triC, ← mul_assoc, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 2
      simp only [fB, fC, fO]
      have e : (-(m * B ^ 2) - 0) * (0 - 0) - (m * A * B - 0) * (m * A * B + m * B ^ 2 - 0)
          = -((m * A * B) * (m * A * B + m * B ^ 2)) := by ring
      rw [e, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (m * A * B) * (m * A * B + m * B ^ 2))]
      push_cast
      have e2 : ((N : ℝ) + k * k) * (A * B) = (m * A * B) * (m * A * B + m * B ^ 2) := by
        rw [show (k : ℝ) * k = (m * B) ^ 2 by rw [ek]; ring]; linear_combination hN
      calc ((N : ℝ) + k * k) * (|sD 1 / (2 * 1)| * (A * B))
          = |sD 1 / (2 * 1)| * (((N : ℝ) + k * k) * (A * B)) := by ring
        _ = _ := by rw [e2])
  rw [hsum] at key
  exact key

end real

/-! ### the natural-number statements -/

/-- **Zhang's Proposition 9, tile-uniform**: the triangle `(m a b, m b c, m b (a+b))`, `m = r+s+t`, is cut into
`b (a + b) m²` tiles `(a, b, c)` whenever `r, s, t` satisfy the Frobenius condition. -/
theorem zhang_f1_dissection (a b c r s t : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hr : Frob a b r) (hs : Frob a b s) (ht : Frob a b t) :
    ∃ (hA : (0 : ℝ) < a) (hB : (0 : ℝ) < b) (hm : (0 : ℝ) < ((r + s + t : ℕ) : ℝ)),
      ∃ D : CongruentDissection (b * (a + b) * (r + s + t) ^ 2),
        D.model = Mo (a : ℝ) (b : ℝ) hA hB ∧ D.target = tgt hA hB hm := by
  obtain ⟨hL, D, hmod, htgt⟩ := zhang_equi_dissection a b c r s t ha hb hc hr hs ht
  have haR : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hm0 : 0 < r + s + t := by
    by_contra h
    have : r + s + t = 0 := by omega
    rw [this] at hL; simp at hL
  have hmR : (0 : ℝ) < ((r + s + t : ℕ) : ℝ) := Nat.cast_pos.2 hm0
  have RE : RTiling (Phi 1 '' Tset (((r + s + t : ℕ) : ℝ) * a * b)) (Mo (a : ℝ) (b : ℝ) haR hbR)
      (a * b * (r + s + t) ^ 2) := by
    refine RegionTiling.remodel (RTiling.cast ?_ (RegionTiling.ofCD D)) (by rw [hmod]; exact Tri.Congruent.refl _)
    rw [htgt, carrier_eqTri]; push_cast
    rw [show (a : ℝ) * b * ((r : ℝ) + s + t) = ((r : ℝ) + s + t) * a * b by ring]
  have hk : 0 < (r + s + t) * b := Nat.mul_pos hm0 hb
  obtain ⟨D2, h1, h2⟩ := f1_real haR hbR hmR ((r + s + t) * b) (a * b * (r + s + t) ^ 2) hk (by push_cast; ring)
    (by push_cast; ring) RE
  have e : a * b * (r + s + t) ^ 2 + (r + s + t) * b * ((r + s + t) * b) = b * (a + b) * (r + s + t) ^ 2 := by ring
  obtain ⟨N', hN', D3, h3, h4⟩ : ∃ N', N' = b * (a + b) * (r + s + t) ^ 2 ∧
      ∃ D3 : CongruentDissection N', D3.model = Mo (a : ℝ) (b : ℝ) haR hbR ∧ D3.target = tgt haR hbR hmR :=
    ⟨_, e, D2, h1, h2⟩
  subst hN'
  exact ⟨haR, hbR, hmR, D3, h3, h4⟩

theorem zhang_f1 (a b c r s t : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hr : Frob a b r) (hs : Frob a b s) (ht : Frob a b t) : TileCount (b * (a + b) * (r + s + t) ^ 2) := by
  obtain ⟨-, -, -, D, -⟩ := zhang_f1_dissection a b c r s t ha hb hc hr hs ht
  exact ⟨D⟩

theorem zhang_f1_m (a b c t0 m : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (h0 : Frob a b t0) (hm : 3 * t0 ≤ m) : TileCount (b * (a + b) * m ^ 2) := by
  have := zhang_f1 a b c t0 t0 (t0 + (m - 3 * t0)) ha hb hc h0 h0 (h0.add _)
  rwa [show t0 + t0 + (t0 + (m - 3 * t0)) = m by omega] at this

/-- (3,5,7): `40 m²` for every `m ≥ 9`. -/
theorem zhang_f1_357 (m : ℕ) (hm : 9 ≤ m) : TileCount (40 * m ^ 2) := by
  have := zhang_f1_m 3 5 7 3 m (by norm_num) (by norm_num) (by norm_num) ⟨2, 1, by norm_num⟩ (by omega)
  simpa using this

end Erdos634.Draft.ZhangF1

#print axioms Erdos634.Draft.ZhangF1.f1_real
#print axioms Erdos634.Draft.ZhangF1.zhang_f1
#print axioms Erdos634.Draft.ZhangF1.zhang_f1_357
