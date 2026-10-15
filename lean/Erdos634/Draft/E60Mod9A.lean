/-
Draft/E60Mod9A.lean: grid weights with values in an arbitrary function of the position in `ℤ/6 × ℤ/3`.
The existing `GridChar` machinery (FluxWeight/FluxGrids/FluxValue) only builds multiplicative `±1` characters of the direction
lattice `L = ℤ·(π/3) + ℤ·α`.  Cancellation (`Dissection.flux_cancel`) holds for every odd weight `Dir → E`, so here the weight is
`d ↦ g(pos d)` where `pos d ∈ ℤ/6 × ℤ/3` is the class of `d − rep d` under the (well defined, since `α ∉ ℚπ`) hom
`jπ/3 + kα ↦ (j mod 6, k mod 3)`, and `g : ℤ/6 × ℤ/3 → ℤ` is any function with `g(x + (3,0)) = −g(x)`.
Contents: `hom6_ker`, `Lam` (the hom `L → ℤ/6 × ℤ/3`), `pos`, `fW`, oddness, and the tile flux formula for ccw / cw tiles
whose angles lie in `L`:  `T.flux (fW g) = Σ_k oppLen(k+2) · g(pos of leftUnit k)`, positions advanced by the exterior angles.
No sorry, no native_decide.
-/
import Erdos634.Draft.CompositeE5Gen

open scoped Classical

namespace Erdos634.Draft.E60Mod9

open Erdos634.Geometry

abbrev GZ := ZMod 6 × ZMod 3

/-- `(j, k) ↦ (j mod 6, k mod 3)`. -/
def hom6 : ℤ × ℤ →+ GZ where
  toFun p := ((p.1 : ZMod 6), (p.2 : ZMod 3))
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Prod.mk_add_mk]

/-- The kernel condition: `jπ/3 + kα ∈ 2πℤ` with `α ∉ ℚπ` forces `k = 0`, `6 ∣ j`. -/
theorem hom6_ker (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p : ℤ × ℤ)
    (hp : rankMap 3 α p = 0) : hom6 p = 0 := by
  obtain ⟨j, k⟩ := p
  rw [rankMap_apply, Real.Angle.coe_eq_zero_iff] at hp
  obtain ⟨m, hm⟩ := hp
  rw [zsmul_eq_mul] at hm
  have hn' : ((3 : ℕ) : ℝ) ≠ 0 := by norm_num
  have e : (j : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) * ((3 : ℕ) : ℝ) = j * Real.pi := by field_simp
  by_cases hk : k = 0
  · have hk0 : (k : ℝ) = 0 := by exact_mod_cast hk
    have h2 : ((j : ℝ) - 2 * m * ((3 : ℕ) : ℝ)) * Real.pi = 0 := by
      linear_combination (-(((3 : ℕ) : ℝ))) * hm - e - (α * ((3 : ℕ) : ℝ)) * hk0
    have h3 : (j : ℝ) - 2 * m * ((3 : ℕ) : ℝ) = 0 := (mul_eq_zero.mp h2).resolve_right Real.pi_ne_zero
    have hj : j = 6 * m := by
      have h4 : (j : ℝ) = ((6 * m : ℤ) : ℝ) := by push_cast at h3 ⊢; linarith
      exact_mod_cast h4
    subst hk
    show (((j : ℤ) : ZMod 6), (((0 : ℤ)) : ZMod 3)) = 0
    rw [hj]
    have h6 : ((6 * m : ℤ) : ZMod 6) = 0 := by
      push_cast
      have : (6 : ZMod 6) = 0 := by decide
      rw [this, zero_mul]
    rw [h6]
    simp
  · exfalso
    apply hα
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have h1 : (k : ℝ) * ((3 : ℕ) : ℝ) * α = (2 * m * ((3 : ℕ) : ℝ) - j) * Real.pi := by
      linear_combination (-(((3 : ℕ) : ℝ))) * hm - e
    refine ⟨((2 * m * ((3 : ℕ) : ℤ) - j : ℤ) : ℚ) / ((((3 : ℕ) : ℤ) * k : ℤ) : ℚ), ?_⟩
    push_cast at h1 ⊢
    have h3k : ((3 : ℝ) * k) ≠ 0 := mul_ne_zero (by norm_num) hk'
    rw [div_mul_eq_mul_div, eq_div_iff h3k]
    linear_combination h1

/-- `hom6` pushed to the range of `φ`, well defined by the kernel condition (copy of `rangeChar`, target arbitrary). -/
noncomputable def rangeHom {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ Real.Angle)
    (χ : A →+ B) (hker : ∀ a, φ a = 0 → χ a = 0) : φ.range →+ B where
  toFun x := χ (rangePre φ x)
  map_zero' := by
    have h := rangePre_spec φ 0
    exact hker _ (by rw [h]; rfl)
  map_add' := by
    intro x y
    have hx := rangePre_spec φ x
    have hy := rangePre_spec φ y
    have hxy := rangePre_spec φ (x + y)
    have h0 : φ (rangePre φ (x + y) - rangePre φ x - rangePre φ y) = 0 := by
      rw [map_sub, map_sub, hxy, hx, hy, AddSubgroup.coe_add]
      abel
    have h1 := hker _ h0
    rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h1
    exact h1

theorem rangeHom_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ Real.Angle)
    (χ : A →+ B) (hker : ∀ a, φ a = 0 → χ a = 0) (a : A) :
    rangeHom φ χ hker ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ = χ a := by
  show χ (rangePre φ ⟨φ a, _⟩) = χ a
  have hs := rangePre_spec φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have h0 : φ (rangePre φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ - a) = 0 := by
    rw [map_sub, hs]; exact sub_self _
  have h1 := hker _ h0
  rw [map_sub, sub_eq_zero] at h1
  exact h1

section W

variable (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (anc : Real.Angle)

/-- The sign character whose `L`, `rep`, `sub_rep_mem`, `rep_add` are reused. -/
noncomputable abbrev Gc : GridChar ℝ := wAt α hα 0 anc

/-- The hom `L → ℤ/6 × ℤ/3`, `jπ/3 + kα ↦ (j, k)`. -/
noncomputable def Lam : (Gc α hα anc).L →+ GZ :=
  rangeHom (rankMap 3 α) hom6 (hom6_ker α hα)

theorem Lam_apply (j k : ℤ)
    (hmem : (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle) ∈ (Gc α hα anc).L) :
    Lam α hα anc ⟨(((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle), hmem⟩
      = ((j : ZMod 6), (k : ZMod 3)) := by
  have e : (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle) = rankMap 3 α (j, k) := by
    rw [rankMap_apply]; push_cast; ring_nf
  have := rangeHom_apply (rankMap 3 α) hom6 (hom6_ker α hα) (j, k)
  have h2 : (⟨(((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle), hmem⟩ : (Gc α hα anc).L)
      = ⟨rankMap 3 α (j, k), AddMonoidHom.mem_range.mpr ⟨(j, k), rfl⟩⟩ := Subtype.ext e
  rw [h2]
  exact this

/-- The position of an angle: its class in `ℤ/6 × ℤ/3` relative to the coset representative. -/
noncomputable def pos (θ : Real.Angle) : GZ :=
  Lam α hα anc ⟨θ - (Gc α hα anc).rep θ, (Gc α hα anc).sub_rep_mem θ⟩

theorem pos_add (θ : Real.Angle) {l : Real.Angle} (hl : l ∈ (Gc α hα anc).L) :
    pos α hα anc (θ + l) = pos α hα anc θ + Lam α hα anc ⟨l, hl⟩ := by
  unfold pos
  rw [← map_add]
  congr 1
  apply Subtype.ext
  show θ + l - (Gc α hα anc).rep (θ + l) = (θ - (Gc α hα anc).rep θ) + l
  rw [(Gc α hα anc).rep_add θ hl]
  abel

theorem Lam_pi : Lam α hα anc ⟨((Real.pi : ℝ) : Real.Angle), (Gc α hα anc).pi_mem⟩ = (3, 0) := by
  have hmem : ((((3 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α : ℝ) : Real.Angle) ∈ (Gc α hα anc).L :=
    wAt_mem α hα 0 anc 3 0
  have := Lam_apply α hα anc 3 0 hmem
  have h2 : (⟨((Real.pi : ℝ) : Real.Angle), (Gc α hα anc).pi_mem⟩ : (Gc α hα anc).L)
      = ⟨((((3 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α : ℝ) : Real.Angle), hmem⟩ := by
    apply Subtype.ext
    show ((Real.pi : ℝ) : Real.Angle) = _
    congr 1; push_cast; ring
  rw [h2, this]
  simp

/-- The weight `d ↦ g(pos d)`. -/
noncomputable def fW (g : GZ → ℤ) (d : Dir) : ℝ := (g (pos α hα anc d.angle) : ℝ)

theorem fW_odd (g : GZ → ℤ) (hg : ∀ x, g (x + (3, 0)) = - g x) (d : Dir) :
    fW α hα anc g (Dir.neg d) = - fW α hα anc g d := by
  unfold fW
  rw [Dir.angle_neg, pos_add α hα anc _ (Gc α hα anc).pi_mem, Lam_pi, hg]
  push_cast; ring

/-- The position of the exterior angle at vertex `k` of a tile whose angles lie in `L`. -/
noncomputable def ext (T : Tri) (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L)
    (k : Fin 3) : GZ :=
  Lam α hα anc ⟨((Real.pi - T.angleAt k : ℝ) : Real.Angle), T.pi_sub_angleAt_mem (Gc α hα anc) h k⟩

/-- **Tile flux, ccw tile.** -/
theorem tile_flux_pos (g : GZ → ℤ) (T : Tri) (hT : 0 < T.det)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L) :
    T.flux (fW α hα anc g) =
      T.oppLen 2 * (g (pos α hα anc (T.leftUnit 0).angle) : ℝ)
      + T.oppLen 0 * (g (pos α hα anc (T.leftUnit 0).angle + ext α hα anc T h 1) : ℝ)
      + T.oppLen 1 * (g (pos α hα anc (T.leftUnit 0).angle + ext α hα anc T h 1
          + ext α hα anc T h 2) : ℝ) := by
  have t1 := T.leftUnit_turn_of_pos hT 0
  have t2 := T.leftUnit_turn_of_pos hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t1 t2
  have p1 : pos α hα anc (T.leftUnit 1).angle = pos α hα anc (T.leftUnit 0).angle + ext α hα anc T h 1 := by
    rw [t1, pos_add α hα anc _ (T.pi_sub_angleAt_mem (Gc α hα anc) h 1)]; rfl
  have p2 : pos α hα anc (T.leftUnit 2).angle
      = pos α hα anc (T.leftUnit 0).angle + ext α hα anc T h 1 + ext α hα anc T h 2 := by
    rw [t2, pos_add α hα anc _ (T.pi_sub_angleAt_mem (Gc α hα anc) h 2), p1]; rfl
  unfold Tri.flux Tri.oppLen fW
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 2 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl, smul_eq_mul]
  rw [p2, p1]

/-- **Tile flux, cw tile.** -/
theorem tile_flux_neg (g : GZ → ℤ) (T : Tri) (hT : T.det < 0)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L) :
    T.flux (fW α hα anc g) =
      T.oppLen 1 * (g (pos α hα anc (T.leftUnit 2).angle) : ℝ)
      + T.oppLen 0 * (g (pos α hα anc (T.leftUnit 2).angle + ext α hα anc T h 2) : ℝ)
      + T.oppLen 2 * (g (pos α hα anc (T.leftUnit 2).angle + ext α hα anc T h 2
          + ext α hα anc T h 1) : ℝ) := by
  have t0 := T.leftUnit_turn_of_neg hT 0
  have t1 := T.leftUnit_turn_of_neg hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t0 t1
  have p1 : pos α hα anc (T.leftUnit 1).angle = pos α hα anc (T.leftUnit 2).angle + ext α hα anc T h 2 := by
    rw [t1, pos_add α hα anc _ (T.pi_sub_angleAt_mem (Gc α hα anc) h 2)]; rfl
  have p0 : pos α hα anc (T.leftUnit 0).angle
      = pos α hα anc (T.leftUnit 2).angle + ext α hα anc T h 2 + ext α hα anc T h 1 := by
    rw [t0, pos_add α hα anc _ (T.pi_sub_angleAt_mem (Gc α hα anc) h 1), p1]; rfl
  unfold Tri.flux Tri.oppLen fW
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 2 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl, smul_eq_mul]
  rw [p0, p1]
  ring

/-- Position relation of a cw tile: `pos(leftUnit 0) = pos(leftUnit 2) + ext 2 + ext 1`. -/
theorem pos_rel_neg (T : Tri) (hT : T.det < 0)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L) :
    pos α hα anc (T.leftUnit 0).angle
      = pos α hα anc (T.leftUnit 2).angle + ext α hα anc T h 2 + ext α hα anc T h 1 := by
  have t0 := T.leftUnit_turn_of_neg hT 0
  have t1 := T.leftUnit_turn_of_neg hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t0 t1
  have p1 : pos α hα anc (T.leftUnit 1).angle = pos α hα anc (T.leftUnit 2).angle + ext α hα anc T h 2 := by
    rw [t1, pos_add α hα anc _ (T.pi_sub_angleAt_mem (Gc α hα anc) h 2)]; rfl
  rw [t0, pos_add α hα anc _ (T.pi_sub_angleAt_mem (Gc α hα anc) h 1), p1]; rfl

/-- The anchor sits at position `0`. -/
theorem pos_anchor : pos α hα anc anc = 0 := by
  unfold pos
  have hrep : (Gc α hα anc).rep anc = anc := by
    unfold GridChar.rep
    rw [if_pos (by show anc - anc ∈ (Gc α hα anc).L; rw [sub_self]; exact (Gc α hα anc).L.zero_mem)]
    rfl
  have : (⟨anc - (Gc α hα anc).rep anc, (Gc α hα anc).sub_rep_mem anc⟩ : (Gc α hα anc).L) = 0 := by
    apply Subtype.ext
    show anc - (Gc α hα anc).rep anc = 0
    rw [hrep, sub_self]
  rw [this, map_zero]

theorem Lam_of_eq (x : ℝ) (j k : ℤ) (hx : x = (j : ℝ) * (Real.pi / 3) + (k : ℝ) * α)
    (hmem : ((x : ℝ) : Real.Angle) ∈ (Gc α hα anc).L) :
    Lam α hα anc ⟨((x : ℝ) : Real.Angle), hmem⟩ = ((j : ZMod 6), (k : ZMod 3)) := by
  subst hx
  exact Lam_apply α hα anc j k hmem

end W

end Erdos634.Draft.E60Mod9
