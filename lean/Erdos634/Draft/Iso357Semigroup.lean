/-
Draft/Iso357Semigroup.lean — **the isosceles semigroup of the `2π/3` tile `(3, 5, 7)`**: for every nonzero `m` in the numerical
semigroup `⟨4, 9⟩` the isosceles triangle with sides `(21 m, 21 m, 33 m)` is cut into `33 m²` copies of the tile `(3, 5, 7)`;
hence `33 m²` is a tile count (`iso357_semigroup`; `m = 4` gives `528`, `m = 8` gives `2112`).

Construction (Zhang, arXiv:2512.22696, Prop. 8(2)).  In the 60-degree skew frame `Φ_1` (Eisenstein coordinates) put
the equilateral triangle `E = P R Q` with `P = (0,0)`, `R = (0,15m)`, `Q = (15m,0)`, tiled by `15 m²` tiles
(`Draft.EqSemigroup.eq357_semigroup`, whose seeds are Paliy's side-60 tiling and the Herdt / Zhang side-135 tiling).
On its sides `P Q` and `R Q` glue two copies of the tile scaled by `3m` (each tiled by `(3m)² = 9m²` tiles, `scaledRT`):
`A = Q P' P` with `P' = (0,-9m)` and `B = Q R' R` with `R' = (0,24m)`.  Since `P', P, R, R'` are collinear, `A ∪ E ∪ B` is the
triangle `P' R' Q` with sides `P'R' = 33 m`, `R'Q = Q P' = 21 m`.  Count `15 m² + 9 m² + 9 m² = 33 m²`.

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.EqSemigroup

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Tset Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.Iso357Semigroup
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.Draft.S2L (mem_hull3' tri_le tri_ge tri_fst_le tri_fst_ge tri_snd_le tri_snd_ge pack_exists)
open Erdos634.Draft.WBrickF (interior_disj_lin)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides congruent_of_hasSides)
open Erdos634.Draft.TileCountFamilies (TileCount)
open Erdos634.Draft.F4All (hf1)
open Erdos634.Draft.EqSemigroup (Mod357 Mod_12 Mod_20 Mod_01 dPhi1 EqD eqTri carrier_eqTri vol_Mod357 eq357_semigroup eqD_semigroup)

/-- a triangle of skew vertices `a, V1, V2` with squared sides `(3k)², (5k)², (7k)²` is `k²` tiles `(3,5,7)`. -/
noncomputable def pieceRT (a V1 V2 : ℝ × ℝ) (k : ℕ) (hk : 0 < k)
    (hd : (V1.1 - a.1) * (V2.2 - a.2) - (V2.1 - a.1) * (V1.2 - a.2) ≠ 0)
    (H12 : (V1.1 - V2.1) ^ 2 + (V1.2 - V2.2) ^ 2 + (V1.1 - V2.1) * (V1.2 - V2.2) = ((k : ℝ) * 3) ^ 2)
    (H20 : (V2.1 - a.1) ^ 2 + (V2.2 - a.2) ^ 2 + (V2.1 - a.1) * (V2.2 - a.2) = ((k : ℝ) * 5) ^ 2)
    (H01 : (a.1 - V1.1) ^ 2 + (a.2 - V1.2) ^ 2 + (a.1 - V1.1) * (a.2 - V1.2) = ((k : ℝ) * 7) ^ 2) :
    RTiling (Phi 1 '' convexHull ℝ {a, V1, V2}) Mod357 (k * k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := hk'.ne'
  refine scaledRT 1 hf1 a V1 V2 k hk hd Mod357 ?_
  refine congruent_of_hasSides (a := 3) (b := 5) (c := 7) ⟨Equiv.refl _, ?_, ?_, ?_⟩ Mod_12 Mod_20 Mod_01 <;>
    simp only [Equiv.refl_apply, baseTri, triC_pts]
  · refine dPhi1 _ _ _ (by norm_num) ?_
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    field_simp
    linear_combination H12
  · refine dPhi1 _ _ _ (by norm_num) ?_
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    field_simp
    linear_combination H20
  · refine dPhi1 _ _ _ (by norm_num) ?_
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    field_simp
    linear_combination H01

/-! ### the layout, parameter `M = m` real -/
def Pp (M : ℝ) : ℝ × ℝ := (0, -(9 * M))
def Rp (M : ℝ) : ℝ × ℝ := (0, 24 * M)
def Qq (M : ℝ) : ℝ × ℝ := (15 * M, 0)
def P0 : ℝ × ℝ := (0, 0)
def R0 (M : ℝ) : ℝ × ℝ := (0, 15 * M)

theorem detT {M : ℝ} (hM : 0 < M) :
    ((Rp M).1 - (Pp M).1) * ((Qq M).2 - (Pp M).2) - ((Qq M).1 - (Pp M).1) * ((Rp M).2 - (Pp M).2) ≠ 0 := by
  simp only [Rp, Pp, Qq]; nlinarith [mul_pos hM hM]

theorem detA {M : ℝ} (hM : 0 < M) :
    ((Pp M).1 - (Qq M).1) * (P0.2 - (Qq M).2) - (P0.1 - (Qq M).1) * ((Pp M).2 - (Qq M).2) ≠ 0 := by
  simp only [Pp, Qq, P0]; nlinarith [mul_pos hM hM]

theorem detB {M : ℝ} (hM : 0 < M) :
    ((Rp M).1 - (Qq M).1) * ((R0 M).2 - (Qq M).2) - ((R0 M).1 - (Qq M).1) * ((Rp M).2 - (Qq M).2) ≠ 0 := by
  simp only [Rp, Qq, R0]; nlinarith [mul_pos hM hM]

/-- the target `P' R' Q`. -/
noncomputable def tgt (M : ℝ) (hM : 0 < M) : Erdos634.Geometry.Tri :=
  triC 1 hf1 (Pp M) (Rp M) (Qq M) (detT hM)

theorem sub_tgt {M : ℝ} (hM : 0 < M) {S : Set (ℝ × ℝ)} (hS : S ⊆ convexHull ℝ {Pp M, Rp M, Qq M}) :
    Phi 1 '' S ⊆ (tgt M hM).carrier := by
  rw [tgt, carrier_triC]; exact Set.image_mono hS

theorem hull_sub {M : ℝ} (hM : 0 < M) {x y z : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ)))
    (hy : y ∈ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ)))
    (hz : z ∈ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ))) :
    convexHull ℝ ({x, y, z} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ)) := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem mem_Pp {M : ℝ} : Pp M ∈ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)
theorem mem_Rp {M : ℝ} : Rp M ∈ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)
theorem mem_Qq {M : ℝ} : Qq M ∈ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ)) :=
  subset_convexHull ℝ _ (by simp)
theorem mem_P0 {M : ℝ} (hM : 0 < M) : P0 ∈ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ)) :=
  mem_hull3' (A := Pp M) (B := Rp M) (C := Qq M) 33 24 9 0 (by norm_num) (by norm_num) (by norm_num) le_rfl
    (by norm_num) P0 (by simp only [P0, Pp, Rp, Qq]; ring) (by simp only [P0, Pp, Rp, Qq]; ring)
theorem mem_R0 {M : ℝ} (hM : 0 < M) : R0 M ∈ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ)) :=
  mem_hull3' (A := Pp M) (B := Rp M) (C := Qq M) 33 9 24 0 (by norm_num) (by norm_num) (by norm_num) le_rfl
    (by norm_num) (R0 M) (by simp only [R0, Pp, Rp, Qq]; ring) (by simp only [R0, Pp, Rp, Qq]; ring)

theorem subE {M : ℝ} (hM : 0 < M) : Tset (15 * M) ⊆ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ)) := by
  rw [← EqSemigroup.hull_Tset _ (by positivity)]
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  · exact mem_P0 hM
  · exact mem_Qq
  · exact mem_R0 hM

theorem eq_hull_Tset {M : ℝ} (hM : 0 < M) :
    convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (15 * M, 0), (0, 15 * M)} : Set (ℝ × ℝ)) = Tset (15 * M) :=
  EqSemigroup.hull_Tset _ (by positivity)

open MeasureTheory in
theorem iso_real {M : ℝ} (hM : 0 < M) (m : ℕ) (hmM : (m : ℝ) = M) (hm0 : 0 < m)
    (RE : RTiling (Phi 1 '' Tset (15 * M)) Mod357 (15 * m * m)) :
    ∃ D : CongruentDissection (33 * m ^ 2), D.model = Mod357 ∧ D.target = tgt M hM := by
  have hk0 : 0 < 3 * m := by omega
  have hkR : ((3 * m : ℕ) : ℝ) = 3 * M := by push_cast; rw [hmM]
  have RA := pieceRT (Qq M) (Pp M) P0 (3 * m) hk0 (by simpa using detA hM)
    (by rw [hkR]; simp only [Pp, P0]; ring)
    (by rw [hkR]; simp only [P0, Qq]; ring)
    (by rw [hkR]; simp only [Qq, Pp]; ring)
  have RB := pieceRT (Qq M) (Rp M) (R0 M) (3 * m) hk0 (by simpa using detB hM)
    (by rw [hkR]; simp only [Rp, R0]; ring)
    (by rw [hkR]; simp only [R0, Qq]; ring)
    (by rw [hkR]; simp only [Qq, Rp]; ring)
  have hsum : ∑ a : Fin 3, (![15 * m * m, 3 * m * (3 * m), 3 * m * (3 * m)] : Fin 3 → ℕ) a = 33 * m ^ 2 := by
    simp [Fin.sum_univ_three]; ring
  -- half-plane bounds
  have bA : ∀ p ∈ convexHull ℝ ({Qq M, Pp M, P0} : Set (ℝ × ℝ)), p.2 ≤ 0 ∧ 0 ≤ p.1 := fun p hp =>
    ⟨tri_snd_le 0 (by simp [Qq]) (by simp [Pp]; linarith) (by simp [P0]) p hp,
     tri_fst_ge 0 (by simp [Qq]; linarith) (by simp [Pp]) (by simp [P0]) p hp⟩
  have bB : ∀ p ∈ convexHull ℝ ({Qq M, Rp M, R0 M} : Set (ℝ × ℝ)), 0 ≤ p.2 ∧ 15 * M ≤ p.1 + p.2 := fun p hp =>
    ⟨tri_snd_ge 0 (by simp [Qq]) (by simp [Rp]; linarith) (by simp [R0]; linarith) p hp,
     by have := tri_ge (A := Qq M) (B := Rp M) (C := R0 M) 1 1 (15 * M)
          (by simp [Qq]) (by simp [Rp]; linarith) (by simp [R0]) p hp
        simpa using this⟩
  have bE : ∀ p ∈ Tset (15 * M), 0 ≤ p.2 ∧ p.1 + p.2 ≤ 15 * M := fun p hp => ⟨hp.2.1, hp.2.2⟩
  have dEA : Disjoint (interior (Phi 1 '' Tset (15 * M)))
      (interior (Phi 1 '' convexHull ℝ ({Qq M, Pp M, P0} : Set (ℝ × ℝ)))) :=
    disjoint_image' hf1 (interior_disj_snd 0 (fun p hp => (bA p hp).1) (fun p hp => (bE p hp).1)).symm
  have dEB : Disjoint (interior (Phi 1 '' Tset (15 * M)))
      (interior (Phi 1 '' convexHull ℝ ({Qq M, Rp M, R0 M} : Set (ℝ × ℝ)))) :=
    disjoint_image' hf1 (interior_disj_lin 1 1 (15 * M) one_ne_zero
      (fun p hp => by linarith [(bE p hp).2]) (fun p hp => by linarith [(bB p hp).2]))
  have dAB : Disjoint (interior (Phi 1 '' convexHull ℝ ({Qq M, Pp M, P0} : Set (ℝ × ℝ))))
      (interior (Phi 1 '' convexHull ℝ ({Qq M, Rp M, R0 M} : Set (ℝ × ℝ)))) :=
    disjoint_image' hf1 (interior_disj_snd 0 (fun p hp => (bA p hp).1) (fun p hp => (bB p hp).1))
  have sA : convexHull ℝ ({Qq M, Pp M, P0} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ)) :=
    hull_sub hM mem_Qq mem_Pp (mem_P0 hM)
  have sB : convexHull ℝ ({Qq M, Rp M, R0 M} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({Pp M, Rp M, Qq M} : Set (ℝ × ℝ)) :=
    hull_sub hM mem_Qq mem_Rp (mem_R0 hM)
  have key := pack_exists (M := Mod357) (T := tgt M hM)
    (![Phi 1 '' Tset (15 * M), Phi 1 '' convexHull ℝ ({Qq M, Pp M, P0} : Set (ℝ × ℝ)),
       Phi 1 '' convexHull ℝ ({Qq M, Rp M, R0 M} : Set (ℝ × ℝ))])
    (![15 * m * m, 3 * m * (3 * m), 3 * m * (3 * m)])
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
        | ⟨0, _⟩ => sub_tgt hM (subE hM)
        | ⟨1, _⟩ => sub_tgt hM sA
        | ⟨2, _⟩ => sub_tgt hM sB
        | ⟨k + 3, h⟩ => absurd h (by omega))
    (by
      rw [hsum, vol_Mod357, tgt, vol_triC, ← mul_assoc, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 2
      simp only [Pp, Rp, Qq]
      have hh : (0 : ℝ) < M * M := mul_pos hM hM
      have e : (0 - 0) * (0 - -(9 * M)) - (15 * M - 0) * (24 * M - -(9 * M)) = -(495 * (M * M)) := by ring
      rw [e, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 495 * (M * M))]
      push_cast
      rw [hmM]
      ring)
  rw [hsum] at key
  exact key

theorem iso_dissection (m : ℕ) (hm : 0 < m) (hE : EqD (15 * m) (15 * m * m)) :
    ∃ D : CongruentDissection (33 * m ^ 2), D.model = Mod357 ∧ D.target = tgt (m : ℝ) (by exact_mod_cast hm) := by
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨-, hL, D, hmod, htgt⟩ := hE
  have RE : RTiling (Phi 1 '' Tset (15 * (m : ℝ))) Mod357 (15 * m * m) := by
    refine RegionTiling.remodel (RTiling.cast ?_ (RegionTiling.ofCD D)) (by rw [hmod]; exact Tri.Congruent.refl _)
    rw [htgt, carrier_eqTri]; push_cast; rfl
  exact iso_real hM m rfl hm RE

/-- **The isosceles semigroup of `(3,5,7)`** (Zhang, Prop. 8(2)): `33 m²` is a tile count for every nonzero `m ∈ ⟨4, 9⟩`;
the triangle `(21 m, 21 m, 33 m)` is cut into `33 m²` tiles `(3,5,7)`. -/
theorem iso357_semigroup {m : ℕ} (hm : m ∈ AddSubmonoid.closure ({4, 9} : Set ℕ)) (hm0 : m ≠ 0) :
    TileCount (33 * m ^ 2) := by
  rcases eqD_semigroup hm with h | h
  · exact absurd h hm0
  · obtain ⟨D, -, -⟩ := iso_dissection m (Nat.pos_of_ne_zero hm0) h
    exact ⟨D⟩

/-- with the sides: target `(33 m, 21 m, 21 m)` on `pts 0 1, 1 2, 2 0`, model tile `(7, 3, 5)`. -/
theorem iso357_semigroup_sides {m : ℕ} (hm : m ∈ AddSubmonoid.closure ({4, 9} : Set ℕ)) (hm0 : m ≠ 0) :
    ∃ D : CongruentDissection (33 * m ^ 2),
      dist (D.target.pts 0) (D.target.pts 1) = 33 * m ∧ dist (D.target.pts 1) (D.target.pts 2) = 21 * m ∧
      dist (D.target.pts 2) (D.target.pts 0) = 21 * m ∧
      dist (D.model.pts 0) (D.model.pts 1) = 7 ∧ dist (D.model.pts 1) (D.model.pts 2) = 3 ∧
      dist (D.model.pts 2) (D.model.pts 0) = 5 := by
  rcases eqD_semigroup hm with h | h
  · exact absurd h hm0
  · have hpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hM : (0 : ℝ) < m := by exact_mod_cast hpos
    obtain ⟨D, hmod, htgt⟩ := iso_dissection m hpos h
    refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [htgt]; simp only [tgt, triC_pts]
      exact dPhi1 _ _ _ (by positivity) (by simp only [Pp, Rp]; ring)
    · rw [htgt]; simp only [tgt, triC_pts]
      exact dPhi1 _ _ _ (by positivity) (by simp only [Rp, Qq]; ring)
    · rw [htgt]; simp only [tgt, triC_pts]
      exact dPhi1 _ _ _ (by positivity) (by simp only [Qq, Pp]; ring)
    · rw [hmod]; exact Mod_01
    · rw [hmod]; exact Mod_12
    · rw [hmod]; exact Mod_20

theorem iso357_m4 : TileCount 528 := by
  have := iso357_semigroup (m := 4) (AddSubmonoid.subset_closure (by simp)) (by norm_num)
  norm_num at this; exact this

theorem iso357_m8 : TileCount 2112 := by
  have h4 : (4 : ℕ) ∈ AddSubmonoid.closure ({4, 9} : Set ℕ) := AddSubmonoid.subset_closure (by simp)
  have := iso357_semigroup (m := 8) (by simpa using add_mem h4 h4) (by norm_num)
  norm_num at this; exact this

end Erdos634.Draft.Iso357Semigroup

#print axioms Erdos634.Draft.Iso357Semigroup.iso357_semigroup
#print axioms Erdos634.Draft.Iso357Semigroup.iso357_semigroup_sides
#print axioms Erdos634.Draft.Iso357Semigroup.iso357_m4
#print axioms Erdos634.Draft.Iso357Semigroup.iso357_m8
