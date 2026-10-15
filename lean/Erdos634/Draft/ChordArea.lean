/-
Draft/ChordArea.lean -- the chord-area lemma for a dissection into congruent triangles.

For ANY congruent dissection (any target, any tile, any number `N` of tiles):

* `volume_side`: if every tile lies weakly on one side of a line, the part of the target on one side of the line
  has the area of the tiles lying on that side;
* `volume_vertex_side`: the part of a triangle on the vertex side of the line parallel to the opposite side at
  ratio `ρ` (the line `coord k = 1 - ρ` in barycentric coordinates) is the homothetic copy of ratio `ρ`, of area
  `ρ²` times the area of the triangle;
* `chord_count`: hence, if no tile crosses that line, `ρ² N` is a natural number (the number of tiles on the
  vertex side);
* `chord_straddled`: if `ρ² N` is not a natural number, some tile has points strictly on both sides of the line;
* `straddle_of_coprime`, `straddle_basebeta`: the arithmetic instance of the paper.  With `N = N₁ m²`,
  `gcd(N₁, f) = 1` and `ρ = M / (m f²)`, the number `ρ² N = N₁ M² / f⁴` is an integer only if `f² ∣ M`.  For the
  base-β member `(e, f)` at scale `m`, `N₁ = 3f² − e²`, and a junction of an equal side at distance
  `d = i a + j c = f (i e + j f)` from the apex has `M = i e + j f`.

Nothing here is vacuous: the hypotheses are a dissection and an arithmetic condition
(`Draft/ChordAreaWitness.lean` instantiates the statement on the kernel-checked 44-tiling).

No sorry, no native_decide.
-/
import Erdos634.CongruentArea
import Erdos634.Dissection

open MeasureTheory Set
open scoped ENNReal Classical

namespace Erdos634.Draft.ChordArea

open Erdos634.Geometry Erdos634.CongruentArea

variable {N : ℕ}

/-- a level set of an affine function with nonzero linear part is a null set -/
theorem volume_level (g : Plane →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0) (c : ℝ) :
    volume {x : Plane | g x = c} = 0 := by
  by_cases hne : ∃ p, g p = c
  · obtain ⟨p, hp⟩ := hne
    have htop : AffineSubspace.mk' p (LinearMap.ker g.linear) ≠ ⊤ := by
      intro h
      apply hg
      refine LinearMap.ext (fun v => ?_)
      have hv : v +ᵥ p ∈ AffineSubspace.mk' p (LinearMap.ker g.linear) := by
        rw [h]; exact AffineSubspace.mem_top ℝ Plane _
      rw [AffineSubspace.mem_mk', vadd_vsub, LinearMap.mem_ker] at hv
      simpa using hv
    refine measure_mono_null ?_ (Measure.addHaar_affineSubspace volume _ htop)
    intro x hx
    have hx' : g x = c := hx
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', LinearMap.mem_ker, AffineMap.linearMap_vsub, hx', hp]
    simp
  · have h0 : {x : Plane | g x = c} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun h => hne ⟨x, h⟩
    rw [h0]; exact measure_empty

/-- **No tile across a line.**  If each tile lies weakly on one side of the line `g = c`, the part of the target
on the side `c ≤ g` has the area of the tiles lying on that side. -/
theorem volume_side (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0) (c : ℝ)
    (hno : ∀ i, (D.tile i).carrier ⊆ {x | c ≤ g x} ∨ (D.tile i).carrier ⊆ {x | g x ≤ c}) :
    volume (D.target.carrier ∩ {x | c ≤ g x})
      = ∑ i, if (D.tile i).carrier ⊆ {x | c ≤ g x} then volume (D.tile i).carrier else 0 := by
  have hHm : MeasurableSet {x : Plane | c ≤ g x} :=
    (isClosed_le continuous_const (AffineMap.continuous_of_finiteDimensional g)).measurableSet
  have hU : D.target.carrier ∩ {x | c ≤ g x}
      = ⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ {x | c ≤ g x}) := by
    rw [← D.covers]
    ext x
    constructor
    · rintro ⟨hx, hxH⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, hi, hxH⟩
    · intro hx
      obtain ⟨i, -, hi, hxH⟩ := mem_iUnion₂.mp hx
      exact ⟨mem_iUnion.mpr ⟨i, hi⟩, hxH⟩
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N))) (f := fun i => (D.tile i).carrier ∩ {x | c ≤ g x})
    (fun i _ j _ hij => by
      show AEDisjoint volume ((D.tile i).carrier ∩ {x | c ≤ g x}) ((D.tile j).carrier ∩ {x | c ≤ g x})
      exact (D.aedisjoint hij).mono inter_subset_left inter_subset_left)
    (fun i _ => ((D.tile i).measurableSet.inter hHm).nullMeasurableSet)
  rw [hU, h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show volume ((D.tile i).carrier ∩ {x | c ≤ g x}) = _
  split_ifs with hi
  · rw [inter_eq_left.mpr hi]
  · have hle := (hno i).resolve_left hi
    refine measure_mono_null ?_ (volume_level g hg c)
    rintro x ⟨hx, hxH⟩
    exact le_antisymm (hle hx) hxH

/-- barycentric coordinates under the homothety about a vertex -/
theorem coord_homothety (T : Tri) (k j : Fin 3) (ρ : ℝ) (x : Plane) :
    T.basis.coord j (AffineMap.homothety (T.pts k) ρ x)
      = ρ * T.basis.coord j x + (1 - ρ) * (if j = k then 1 else 0) := by
  have hA : T.basis.coord j (T.pts k) = if j = k then 1 else 0 := by
    by_cases hjk : j = k
    · subst hjk; rw [if_pos rfl]; exact T.basis.coord_apply_eq j
    · rw [if_neg hjk]; exact T.basis.coord_apply_ne hjk
  rw [AffineMap.homothety_eq_lineMap, AffineMap.apply_lineMap, AffineMap.lineMap_apply, hA]
  simp only [vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  ring

/-- the part of a triangle on the vertex side of the line `coord k = 1 - ρ` is the homothetic copy of ratio `ρ` -/
theorem carrier_inter_coord (T : Tri) (k : Fin 3) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    T.carrier ∩ {x | 1 - ρ ≤ T.basis.coord k x} = AffineMap.homothety (T.pts k) ρ '' T.carrier := by
  have hρne : ρ ≠ 0 := hρ0.ne'
  ext y
  constructor
  · rintro ⟨hy, hyk⟩
    rw [T.carrier_eq_nonneg_coord] at hy
    have hyk' : 1 - ρ ≤ T.basis.coord k y := hyk
    refine ⟨AffineMap.homothety (T.pts k) ρ⁻¹ y, ?_, ?_⟩
    · rw [T.carrier_eq_nonneg_coord]
      intro j
      show 0 ≤ T.basis.coord j (AffineMap.homothety (T.pts k) ρ⁻¹ y)
      rw [coord_homothety]
      by_cases hjk : j = k
      · subst hjk
        rw [if_pos rfl]
        have hid : ρ⁻¹ * T.basis.coord j y + (1 - ρ⁻¹) * 1 = ρ⁻¹ * (T.basis.coord j y - (1 - ρ)) := by
          have h1 : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρne
          linear_combination (-1 : ℝ) * h1
        rw [hid]
        exact mul_nonneg (inv_nonneg.mpr hρ0.le) (by linarith)
      · rw [if_neg hjk]
        have h2 : 0 ≤ ρ⁻¹ * T.basis.coord j y := mul_nonneg (inv_nonneg.mpr hρ0.le) (hy j)
        linarith
    · simp only [AffineMap.homothety_apply, vadd_vsub, smul_smul, mul_inv_cancel₀ hρne, one_smul, vsub_vadd]
  · rintro ⟨x, hx, rfl⟩
    rw [T.carrier_eq_nonneg_coord] at hx
    constructor
    · rw [T.carrier_eq_nonneg_coord]
      intro j
      show 0 ≤ T.basis.coord j (AffineMap.homothety (T.pts k) ρ x)
      rw [coord_homothety]
      have h1 : 0 ≤ ρ * T.basis.coord j x := mul_nonneg hρ0.le (hx j)
      have h2 : 0 ≤ (1 - ρ) * (if j = k then (1 : ℝ) else 0) :=
        mul_nonneg (by linarith) (by split_ifs <;> norm_num)
      linarith
    · show 1 - ρ ≤ T.basis.coord k (AffineMap.homothety (T.pts k) ρ x)
      rw [coord_homothety, if_pos rfl]
      have h1 : 0 ≤ ρ * T.basis.coord k x := mul_nonneg hρ0.le (hx k)
      linarith

/-- the area on the vertex side of the line parallel to the opposite side at ratio `ρ` -/
theorem volume_vertex_side (T : Tri) (k : Fin 3) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    volume (T.carrier ∩ {x | 1 - ρ ≤ T.basis.coord k x}) = ENNReal.ofReal (ρ ^ 2) * volume T.carrier := by
  rw [carrier_inter_coord T k hρ0 hρ1, MeasureTheory.Measure.addHaar_image_homothety]
  have hfr : Module.finrank ℝ Plane = 2 := by simp
  rw [hfr, abs_of_nonneg (sq_nonneg ρ)]

/-- **Chord count.**  In a dissection into `N` congruent triangles, let `k` be a vertex of the target and
`0 < ρ ≤ 1`.  If every tile lies weakly on one side of the line parallel to the side opposite `k` at ratio `ρ`
from `k`, then `ρ² N` is a natural number. -/
theorem chord_count (D : CongruentDissection N) (k : Fin 3) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hno : ∀ i, (D.tile i).carrier ⊆ {x | 1 - ρ ≤ D.target.basis.coord k x} ∨
      (D.tile i).carrier ⊆ {x | D.target.basis.coord k x ≤ 1 - ρ}) :
    ∃ n : ℕ, (n : ℝ) = ρ ^ 2 * N := by
  have h1 := volume_side D.toDissection (D.target.basis.coord k) (D.target.coord_linear_ne_zero k) (1 - ρ) hno
  rw [volume_vertex_side D.target k hρ0 hρ1, congruentDissection_volume_target D] at h1
  have hv : ∀ i, volume (D.tile i).carrier = volume D.model.carrier :=
    fun i => volume_congruent (D.tiles_congruent i)
  simp only [hv] at h1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← mul_assoc] at h1
  have hv0 : volume D.model.carrier ≠ 0 := D.model.volume_pos.ne'
  have hvt : volume D.model.carrier ≠ ⊤ := D.model.volume_ne_top
  have h2 := (ENNReal.mul_left_inj hv0 hvt).mp h1
  have h3 := congrArg ENNReal.toReal h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg ρ), ENNReal.toReal_natCast,
    ENNReal.toReal_natCast] at h3
  exact ⟨_, h3.symm⟩

/-- **Chord straddled.**  If `ρ² N` is not a natural number, some tile has points strictly on both sides of the
line parallel to the side opposite the vertex `k` at ratio `ρ` from `k`. -/
theorem chord_straddled (D : CongruentDissection N) (k : Fin 3) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hnot : ∀ n : ℕ, (n : ℝ) ≠ ρ ^ 2 * N) :
    ∃ i, (∃ x ∈ (D.tile i).carrier, D.target.basis.coord k x < 1 - ρ) ∧
      (∃ y ∈ (D.tile i).carrier, 1 - ρ < D.target.basis.coord k y) := by
  by_contra hcon
  push_neg at hcon
  have hno : ∀ i, (D.tile i).carrier ⊆ {x | 1 - ρ ≤ D.target.basis.coord k x} ∨
      (D.tile i).carrier ⊆ {x | D.target.basis.coord k x ≤ 1 - ρ} := by
    intro i
    by_cases h : ∃ x ∈ (D.tile i).carrier, D.target.basis.coord k x < 1 - ρ
    · right; intro y hy; exact hcon i h y hy
    · left; intro x hx
      push_neg at h
      exact h x hx
  obtain ⟨n, hn⟩ := chord_count D k hρ0 hρ1 hno
  exact hnot n hn

/-- the arithmetic instance: `N = N₁ m²`, `gcd(N₁, f) = 1`, `ρ = M / (m f²)` with `f² ∤ M` -/
theorem straddle_of_coprime (D : CongruentDissection N) (k : Fin 3) {N₁ f m M : ℕ} {ρ : ℝ}
    (hcop : Nat.Coprime N₁ f) (hN : N = N₁ * m ^ 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρ : ρ * (m * f ^ 2) = M) (hnd : ¬ f ^ 2 ∣ M) :
    ∃ i, (∃ x ∈ (D.tile i).carrier, D.target.basis.coord k x < 1 - ρ) ∧
      (∃ y ∈ (D.tile i).carrier, 1 - ρ < D.target.basis.coord k y) := by
  refine chord_straddled D k hρ0 hρ1 (fun n h => ?_)
  have h2 : (n : ℝ) * (f : ℝ) ^ 4 = (N₁ : ℝ) * (M : ℝ) ^ 2 := by
    rw [h, hN, ← hρ]; push_cast; ring
  have h3 : n * f ^ 4 = N₁ * M ^ 2 := by exact_mod_cast h2
  have hdvd : f ^ 4 ∣ N₁ * M ^ 2 := Dvd.intro_left n h3
  have hcop4 : Nat.Coprime (f ^ 4) N₁ := hcop.symm.pow_left 4
  have hdvd2 : f ^ 4 ∣ M ^ 2 := Nat.Coprime.dvd_of_dvd_mul_left hcop4 hdvd
  have hsq : (f ^ 2) ^ 2 ∣ M ^ 2 := by
    have h4 : (f ^ 2) ^ 2 = f ^ 4 := by ring
    rwa [h4]
  exact hnd ((Nat.pow_dvd_pow_iff (by norm_num)).mp hsq)

/-- `gcd(3f² − e², f) = 1` for coprime `e < f` -/
theorem coprime_N1 {e f : ℕ} (hcop : Nat.Coprime e f) (hef : e < f) : Nat.Coprime (3 * f ^ 2 - e ^ 2) f := by
  have hle : e ^ 2 ≤ 3 * f ^ 2 := by
    have := Nat.pow_le_pow_left hef.le 2
    omega
  have hd1 : Nat.gcd (3 * f ^ 2 - e ^ 2) f ∣ 3 * f ^ 2 - e ^ 2 := Nat.gcd_dvd_left _ _
  have hd2 : Nat.gcd (3 * f ^ 2 - e ^ 2) f ∣ f := Nat.gcd_dvd_right _ _
  have hd3 : Nat.gcd (3 * f ^ 2 - e ^ 2) f ∣ 3 * f ^ 2 - e ^ 2 + e ^ 2 := by
    rw [Nat.sub_add_cancel hle]
    exact Dvd.dvd.mul_left (dvd_pow hd2 (by norm_num)) 3
  have hd4 : Nat.gcd (3 * f ^ 2 - e ^ 2) f ∣ e ^ 2 := (Nat.dvd_add_right hd1).mp hd3
  have hc2 : Nat.gcd (e ^ 2) f = 1 := Nat.Coprime.pow_left 2 hcop
  have h1 : Nat.gcd (3 * f ^ 2 - e ^ 2) f ∣ Nat.gcd (e ^ 2) f := Nat.dvd_gcd hd4 hd2
  rw [hc2] at h1
  exact Nat.dvd_one.mp h1

/-- **`prop:straddlegen`.**  In a dissection into `N = (3f² − e²) m²` congruent triangles (coprime `e < f`), for a
vertex `k` of the target and the ratio `ρ = M / (m f²)` with `0 < M ≤ m f²` and `f² ∤ M`, some tile has points
strictly on both sides of the line parallel to the side opposite `k` at ratio `ρ` from `k`. -/
theorem straddle_basebeta (D : CongruentDissection N) (k : Fin 3) {e f m M : ℕ} {ρ : ℝ}
    (hcop : Nat.Coprime e f) (hef : e < f) (hN : N = (3 * f ^ 2 - e ^ 2) * m ^ 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρ : ρ * (m * f ^ 2) = M) (hnd : ¬ f ^ 2 ∣ M) :
    ∃ i, (∃ x ∈ (D.tile i).carrier, D.target.basis.coord k x < 1 - ρ) ∧
      (∃ y ∈ (D.tile i).carrier, 1 - ρ < D.target.basis.coord k y) :=
  straddle_of_coprime D k (coprime_N1 hcop hef) hN hρ0 hρ1 hρ hnd

/-- at scale one every junction strictly between the apex and the base qualifies: `1 ≤ M < f²` gives `f² ∤ M` -/
theorem not_dvd_of_lt {f M : ℕ} (h1 : 1 ≤ M) (h2 : M < f ^ 2) : ¬ f ^ 2 ∣ M :=
  fun h => absurd (Nat.le_of_dvd h1 h) (by omega)

end Erdos634.Draft.ChordArea

#print axioms Erdos634.Draft.ChordArea.chord_straddled
#print axioms Erdos634.Draft.ChordArea.straddle_basebeta
