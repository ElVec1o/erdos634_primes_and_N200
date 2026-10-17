/-
Draft/ZhangIso.lean — Zhang's Proposition 8 (arXiv:2512.22696), tile-uniform: from the equilateral triangle of side
`m a b` tiled by `a b m²` tiles `(a, b, c)` (`ZhangEqui`), gluing two copies of the tile scaled by `m a` onto two sides
gives the isosceles triangle with sides `(m a c, m a c, m a (b + 2a))`, cut into `a (b + 2a) m²` tiles
(`zhang_iso_dissection`).  For `(a, b, c) = (3, 5, 7)` this is `Draft.Iso357Semigroup`.

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.ZhangEqui

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Tset Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.ZhangIso
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.Draft.S2L (mem_hull3' tri_le tri_ge tri_fst_le tri_fst_ge tri_snd_le tri_snd_ge pack_exists)
open Erdos634.Draft.WBrickF (interior_disj_lin)
open Erdos634.Draft.F4All (hf1)
open Erdos634.Draft.ZhangBase Erdos634.Draft.ZhangTrap Erdos634.Draft.ZhangEqui
open Erdos634.Draft.EqSemigroup (eqTri carrier_eqTri vol_eqTri hull_Tset)
open Erdos634.Draft.TileCountFamilies (TileCount)

section real
variable (A B m : ℝ)

def Pp : ℝ × ℝ := (0, -(m * A ^ 2))
def Rp : ℝ × ℝ := (0, m * A * B + m * A ^ 2)
def Qq : ℝ × ℝ := (m * A * B, 0)
def P0 : ℝ × ℝ := (0, 0)
def R0 : ℝ × ℝ := (0, m * A * B)

variable {A B m} (hA : 0 < A) (hB : 0 < B) (hm : 0 < m)
include hA hB hm

theorem pos_L : 0 < m * A * B := by positivity
theorem pos_h : 0 < m * A ^ 2 := by positivity

theorem detT : ((Rp A B m).1 - (Pp A m).1) * ((Qq A B m).2 - (Pp A m).2)
    - ((Qq A B m).1 - (Pp A m).1) * ((Rp A B m).2 - (Pp A m).2) ≠ 0 := by
  have := pos_L hA hB hm
  have := pos_h hA hB hm
  simp only [Rp, Pp, Qq]; intro h; nlinarith

theorem detA : ((Pp A m).1 - (Qq A B m).1) * ((P0).2 - (Qq A B m).2)
    - ((P0).1 - (Qq A B m).1) * ((Pp A m).2 - (Qq A B m).2) ≠ 0 := by
  have := pos_L hA hB hm
  have := pos_h hA hB hm
  simp only [Pp, Qq, P0]; intro h; nlinarith

theorem detB : ((Rp A B m).1 - (Qq A B m).1) * ((R0 A B m).2 - (Qq A B m).2)
    - ((R0 A B m).1 - (Qq A B m).1) * ((Rp A B m).2 - (Qq A B m).2) ≠ 0 := by
  have := pos_L hA hB hm
  have := pos_h hA hB hm
  simp only [Rp, Qq, R0]; intro h; nlinarith

/-- the isosceles target `P' R' Q`. -/
noncomputable def tgt : TriG := triC 1 hf1 (Pp A m) (Rp A B m) (Qq A B m) (detT hA hB hm)


theorem sub_tgt {S : Set (ℝ × ℝ)} (hS : S ⊆ convexHull ℝ {Pp A m, Rp A B m, Qq A B m}) :
    Phi 1 '' S ⊆ (tgt hA hB hm).carrier := by
  rw [tgt, carrier_triC]; exact Set.image_mono hS

theorem hull_sub {x y z : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ)))
    (hy : y ∈ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ)))
    (hz : z ∈ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ))) :
    convexHull ℝ ({x, y, z} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ)) := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem mem_Pp : Pp A m ∈ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)
theorem mem_Rp : Rp A B m ∈ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)
theorem mem_Qq : Qq A B m ∈ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)
theorem mem_P0 : P0 ∈ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ)) := by
  have := pos_L hA hB hm
  have := pos_h hA hB hm
  exact mem_hull3' (A := Pp A m) (B := Rp A B m) (C := Qq A B m) (m * A * B + 2 * (m * A ^ 2))
    (m * A * B + m * A ^ 2) (m * A ^ 2) 0 (by linarith) (by linarith) (by linarith) le_rfl (by ring) P0
    (by simp only [P0, Pp, Rp, Qq]; ring) (by simp only [P0, Pp, Rp, Qq]; ring)
theorem mem_R0 : R0 A B m ∈ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ)) := by
  have := pos_L hA hB hm
  have := pos_h hA hB hm
  exact mem_hull3' (A := Pp A m) (B := Rp A B m) (C := Qq A B m) (m * A * B + 2 * (m * A ^ 2))
    (m * A ^ 2) (m * A * B + m * A ^ 2) 0 (by linarith) (by linarith) (by linarith) le_rfl (by ring) (R0 A B m)
    (by simp only [R0, Pp, Rp, Qq]; ring) (by simp only [R0, Pp, Rp, Qq]; ring)

theorem subE : Tset (m * A * B) ⊆ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ)) := by
  rw [← hull_Tset _ (pos_L hA hB hm)]
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  · exact mem_P0 hA hB hm
  · exact mem_Qq hA hB hm
  · exact mem_R0 hA hB hm

open MeasureTheory in
theorem iso_real (k N : ℕ) (hk : 0 < k) (ek : (k : ℝ) = m * A)
    (hN : (N : ℝ) * (A * B) = (m * A * B) ^ 2)
    (RE : RTiling (Phi 1 '' Tset (m * A * B)) (Mo A B hA hB) N) :
    ∃ D : CongruentDissection (N + k * k + k * k), D.model = Mo A B hA hB ∧ D.target = tgt hA hB hm := by
  have hL := pos_L hA hB hm
  have hh := pos_h hA hB hm
  have RA := ladRT A B hA hB (Qq A B m) (Pp A m) P0 k hk (by simpa using detA hA hB hm)
    (by rw [ek]; simp only [Pp, P0, Qq]; ring)
    (by rw [ek]; simp only [Pp, P0, Qq]; ring)
    (by rw [ek]; simp only [Pp, P0, Qq]; ring)
  have RB := ladRT A B hA hB (Qq A B m) (Rp A B m) (R0 A B m) k hk (by simpa using detB hA hB hm)
    (by rw [ek]; simp only [Rp, R0, Qq]; ring)
    (by rw [ek]; simp only [Rp, R0, Qq]; ring)
    (by rw [ek]; simp only [Rp, R0, Qq]; ring)
  have hsum : ∑ a : Fin 3, (![N, k * k, k * k] : Fin 3 → ℕ) a = N + k * k + k * k := by
    simp [Fin.sum_univ_three]
  have bA : ∀ p ∈ convexHull ℝ ({Qq A B m, Pp A m, P0} : Set (ℝ × ℝ)), p.2 ≤ 0 ∧ 0 ≤ p.1 := fun p hp =>
    ⟨tri_snd_le 0 (by simp [Qq]) (by simp [Pp]; linarith) (by simp [P0]) p hp,
     tri_fst_ge 0 (by simp [Qq]; linarith) (by simp [Pp]) (by simp [P0]) p hp⟩
  have bB : ∀ p ∈ convexHull ℝ ({Qq A B m, Rp A B m, R0 A B m} : Set (ℝ × ℝ)),
      0 ≤ p.2 ∧ m * A * B ≤ p.1 + p.2 := fun p hp =>
    ⟨tri_snd_ge 0 (by simp [Qq]) (by simp [Rp]; linarith) (by simp [R0]; linarith) p hp,
     by have := tri_ge (A := Qq A B m) (B := Rp A B m) (C := R0 A B m) 1 1 (m * A * B)
          (by simp [Qq]) (by simp [Rp]; linarith) (by simp [R0]) p hp
        simpa using this⟩
  have bE : ∀ p ∈ Tset (m * A * B), 0 ≤ p.2 ∧ p.1 + p.2 ≤ m * A * B := fun p hp => ⟨hp.2.1, hp.2.2⟩
  have dEA : Disjoint (interior (Phi 1 '' Tset (m * A * B)))
      (interior (Phi 1 '' convexHull ℝ ({Qq A B m, Pp A m, P0} : Set (ℝ × ℝ)))) :=
    disjoint_image' hf1 (interior_disj_snd 0 (fun p hp => (bA p hp).1) (fun p hp => (bE p hp).1)).symm
  have dEB : Disjoint (interior (Phi 1 '' Tset (m * A * B)))
      (interior (Phi 1 '' convexHull ℝ ({Qq A B m, Rp A B m, R0 A B m} : Set (ℝ × ℝ)))) :=
    disjoint_image' hf1 (interior_disj_lin 1 1 (m * A * B) one_ne_zero
      (fun p hp => by linarith [(bE p hp).2]) (fun p hp => by linarith [(bB p hp).2]))
  have dAB : Disjoint (interior (Phi 1 '' convexHull ℝ ({Qq A B m, Pp A m, P0} : Set (ℝ × ℝ))))
      (interior (Phi 1 '' convexHull ℝ ({Qq A B m, Rp A B m, R0 A B m} : Set (ℝ × ℝ)))) :=
    disjoint_image' hf1 (interior_disj_snd 0 (fun p hp => (bA p hp).1) (fun p hp => (bB p hp).1))
  have sA : convexHull ℝ ({Qq A B m, Pp A m, P0} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ)) :=
    hull_sub hA hB hm (mem_Qq hA hB hm) (mem_Pp hA hB hm) (mem_P0 hA hB hm)
  have sB : convexHull ℝ ({Qq A B m, Rp A B m, R0 A B m} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({Pp A m, Rp A B m, Qq A B m} : Set (ℝ × ℝ)) :=
    hull_sub hA hB hm (mem_Qq hA hB hm) (mem_Rp hA hB hm) (mem_R0 hA hB hm)
  have key := pack_exists (M := Mo A B hA hB) (T := tgt hA hB hm)
    (![Phi 1 '' Tset (m * A * B), Phi 1 '' convexHull ℝ ({Qq A B m, Pp A m, P0} : Set (ℝ × ℝ)),
       Phi 1 '' convexHull ℝ ({Qq A B m, Rp A B m, R0 A B m} : Set (ℝ × ℝ))])
    (![N, k * k, k * k])
    (fun i => match i with
      | ⟨0, _⟩ => RE
      | ⟨1, _⟩ => RA
      | ⟨2, _⟩ => RB
      | ⟨k + 3, h⟩ => absurd h (by omega))
    (by
      intro i j hij
      exact match i, j with
        | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hij
        | ⟨0, _⟩, ⟨1, _⟩ => dEA
        | ⟨0, _⟩, ⟨2, _⟩ => dEB
        | ⟨1, _⟩, ⟨0, _⟩ => dEA.symm
        | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hij
        | ⟨1, _⟩, ⟨2, _⟩ => dAB
        | ⟨2, _⟩, ⟨0, _⟩ => dEB.symm
        | ⟨2, _⟩, ⟨1, _⟩ => dAB.symm
        | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hij
        | ⟨k + 3, h⟩, _ => absurd h (by omega)
        | _, ⟨k + 3, h⟩ => absurd h (by omega))
    (by
      intro i
      exact match i with
        | ⟨0, _⟩ => sub_tgt hA hB hm (subE hA hB hm)
        | ⟨1, _⟩ => sub_tgt hA hB hm sA
        | ⟨2, _⟩ => sub_tgt hA hB hm sB
        | ⟨k + 3, h⟩ => absurd h (by omega))
    (by
      rw [hsum, vol_Mo, tgt, vol_triC, ← mul_assoc, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 2
      simp only [Pp, Rp, Qq]
      have e : (0 - 0) * (0 - -(m * A ^ 2)) - (m * A * B - 0) * (m * A * B + m * A ^ 2 - -(m * A ^ 2))
          = -((m * A * B) * (m * A * B + 2 * (m * A ^ 2))) := by ring
      rw [e, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (m * A * B) * (m * A * B + 2 * (m * A ^ 2)))]
      push_cast
      have e2 : ((N : ℝ) + k * k + k * k) * (A * B) = (m * A * B) * (m * A * B + 2 * (m * A ^ 2)) := by
        rw [show (k : ℝ) * k = (m * A) ^ 2 by rw [ek]; ring]; linear_combination hN
      calc ((N : ℝ) + k * k + k * k) * (|sD 1 / (2 * 1)| * (A * B))
          = |sD 1 / (2 * 1)| * (((N : ℝ) + k * k + k * k) * (A * B)) := by ring
        _ = _ := by rw [e2])
  rw [hsum] at key
  exact key

end real

/-! ### the natural-number statements -/

/-- **Zhang's Proposition 8, tile-uniform**: the isosceles triangle with sides `(m a c, m a c, m a (b+2a))`,
`m = r+s+t`, is cut into `a (b + 2a) m²` tiles `(a, b, c)` whenever `r, s, t` satisfy the Frobenius condition. -/
theorem zhang_iso_dissection (a b c r s t : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hr : Frob a b r) (hs : Frob a b s) (ht : Frob a b t) :
    ∃ (hA : (0 : ℝ) < a) (hB : (0 : ℝ) < b) (hm : (0 : ℝ) < ((r + s + t : ℕ) : ℝ)),
      ∃ D : CongruentDissection (a * (b + 2 * a) * (r + s + t) ^ 2),
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
  have hk : 0 < (r + s + t) * a := Nat.mul_pos hm0 ha
  obtain ⟨D2, h1, h2⟩ := iso_real haR hbR hmR ((r + s + t) * a) (a * b * (r + s + t) ^ 2) hk (by push_cast; ring)
    (by push_cast; ring) RE
  have e : a * b * (r + s + t) ^ 2 + (r + s + t) * a * ((r + s + t) * a) + (r + s + t) * a * ((r + s + t) * a)
      = a * (b + 2 * a) * (r + s + t) ^ 2 := by ring
  obtain ⟨N', hN', D3, h3, h4⟩ : ∃ N', N' = a * (b + 2 * a) * (r + s + t) ^ 2 ∧
      ∃ D3 : CongruentDissection N', D3.model = Mo (a : ℝ) (b : ℝ) haR hbR ∧ D3.target = tgt haR hbR hmR :=
    ⟨_, e, D2, h1, h2⟩
  subst hN'
  exact ⟨haR, hbR, hmR, D3, h3, h4⟩

theorem zhang_iso (a b c r s t : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hr : Frob a b r) (hs : Frob a b s) (ht : Frob a b t) : TileCount (a * (b + 2 * a) * (r + s + t) ^ 2) := by
  obtain ⟨-, -, -, D, -⟩ := zhang_iso_dissection a b c r s t ha hb hc hr hs ht
  exact ⟨D⟩

theorem zhang_iso_m (a b c t0 m : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (h0 : Frob a b t0) (hm : 3 * t0 ≤ m) : TileCount (a * (b + 2 * a) * m ^ 2) := by
  have := zhang_iso a b c t0 t0 (t0 + (m - 3 * t0)) ha hb hc h0 h0 (h0.add _)
  rwa [show t0 + t0 + (t0 + (m - 3 * t0)) = m by omega] at this

/-- (3,5,7): `33 m²` for every `m ≥ 9`. -/
theorem zhang_iso_357 (m : ℕ) (hm : 9 ≤ m) : TileCount (33 * m ^ 2) := by
  have := zhang_iso_m 3 5 7 3 m (by norm_num) (by norm_num) (by norm_num) ⟨2, 1, by norm_num⟩ (by omega)
  simpa using this

end Erdos634.Draft.ZhangIso

#print axioms Erdos634.Draft.ZhangIso.iso_real
#print axioms Erdos634.Draft.ZhangIso.zhang_iso
#print axioms Erdos634.Draft.ZhangIso.zhang_iso_357
