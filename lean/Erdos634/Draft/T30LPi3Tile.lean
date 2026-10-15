import Mathlib.Tactic
import Erdos634.VertexFigureReal
import Erdos634.SideWall
import Erdos634.Draft.ChordWord
import Erdos634.Draft.G3CAng
import Erdos634.Draft.FluxERow2Sqfree17
import Erdos634.Draft.G3CSixtyControl

/-!
# The `π/3` tile and its vertex figures on a real dissection

Tile `T30 = (a,b,c) = (9+√21, 9−√21, 12)`, angles `α, β = 2π/3 − α, π/3` opposite `a, b, c`.
This is `Tri.SixtyData α a b c` (`FluxCRow5`; the `π/3` tile, not `TwoPiThreeData`, which is the `2π/3` tile).

* (1) arithmetic `fan_eq`: from `α ∉ ℚπ`, `x α + y β + z π/3 + s π = t π/3 ⇒ x = y ∧ 2y + z + 3s = t`.
  `boundary_cases` (t = 3: `(P,P,P)`, `(α,β,P)`, one straight angle) and `corner_cases` (t = 1: a single `P`).
* (2) real dissection: `boundary_fan_real` (a non-vertex boundary point of a `CongruentDissection` whose model is a
  `SixtyData` tile with `α ∉ ℚπ`: the counts of tiles presenting `α, β, π/3, π` are one of the three figures) and
  `corner_fan_real` (a target corner of angle `π/3`: exactly one tile, presenting `π/3`).
* (3) the concrete tile: `t30_sixty_data` and `t30_alpha_irr`: a `Tri` with opposite sides `(a,b,c)` of `T30` has
  `SixtyData` and `α ∉ ℚπ` (cos α = (3 − √21)/8 ∈ ℚ+ℚ√21, `Row2.lemmaQ_sqfree17`).
* (4) Witness for (2): the certified 1440-tiling of the equilateral triangle of side 240 by the rational
  `π/3` tile (5,8,7) (`G3CSixtyControl.D`, 1440 congruent tiles; `α` irrational) satisfies every hypothesis of (2); the
  conclusions are instantiated there at all 3 target corners and at a boundary non-vertex point.
* Control: `corner_needs_irr`: with `α = π/3` (rational) the corner equation has the spurious solution
  `(x,y,z) = (1,0,0)`, so irrationality is needed.

Not done here: an explicit `Tri` with sides `(9+√21, 9−√21, 12)` (so the hypotheses of (3) are not witnessed by a built
triangle; no real dissection with this tile exists, which is the content of the exclusion), and the geometric facts (reflection of the second tile etc.).
-/

namespace Erdos634.Pi3Tile

open Erdos634.Geometry Erdos634.VertexFigureReal

/-- `α/π` is irrational. -/
def Irr (α : ℝ) : Prop := ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi

theorem irr_split {α : ℝ} (h : Irr α) (u v : ℤ) (huv : (u : ℝ) * α = (v : ℝ) * Real.pi) :
    u = 0 ∧ v = 0 := by
  have hu : u = 0 := by
    by_contra hu0
    apply h
    refine ⟨(v : ℚ) / (u : ℚ), ?_⟩
    have hu' : (u : ℝ) ≠ 0 := by exact_mod_cast hu0
    push_cast
    field_simp
    linarith
  subst hu
  refine ⟨rfl, ?_⟩
  have h0 : (v : ℝ) * Real.pi = 0 := by simpa using huv.symm
  have hpi := Real.pi_pos
  have : (v : ℝ) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · linarith
  exact_mod_cast this

/-- **The fan equation.** -/
theorem fan_eq {α : ℝ} (h : Irr α) (x y z s t : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * (2 * Real.pi / 3 - α) + (z : ℝ) * (Real.pi / 3)
      + (s : ℝ) * Real.pi = (t : ℝ) * (Real.pi / 3)) :
    x = y ∧ 2 * y + z + 3 * s = t := by
  have key := irr_split h (3 * ((x : ℤ) - y)) ((t : ℤ) - 2 * y - z - 3 * s)
    (by push_cast; linear_combination 3 * hsum)
  obtain ⟨h1, h2⟩ := key
  omega

/-- Boundary figure (angle sum `π = 3·π/3`): `(P,P,P)`, `(α,β,P)` or one straight angle. -/
theorem boundary_cases {α : ℝ} (h : Irr α) (x y z s : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * (2 * Real.pi / 3 - α) + (z : ℝ) * (Real.pi / 3)
      + (s : ℝ) * Real.pi = Real.pi) :
    (x = 0 ∧ y = 0 ∧ z = 0 ∧ s = 1) ∨ (x = 0 ∧ y = 0 ∧ z = 3 ∧ s = 0)
      ∨ (x = 1 ∧ y = 1 ∧ z = 1 ∧ s = 0) := by
  have := fan_eq h x y z s 3 (by push_cast; linarith)
  omega

/-- Corner of angle `π/3`: one `P` and nothing else. -/
theorem corner_cases {α : ℝ} (h : Irr α) (x y z s : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * (2 * Real.pi / 3 - α) + (z : ℝ) * (Real.pi / 3)
      + (s : ℝ) * Real.pi = Real.pi / 3) :
    x = 0 ∧ y = 0 ∧ z = 1 ∧ s = 0 := by
  have := fan_eq h x y z s 1 (by push_cast; linarith)
  omega

/-- **Irrationality is needed.**  Without irrationality (`α = π/3`) the corner equation has the spurious solution
`(1,0,0,0)`: the conclusion of `corner_cases` fails. -/
theorem corner_needs_irr :
    ((1 : ℕ) : ℝ) * (Real.pi / 3) + ((0 : ℕ) : ℝ) * (2 * Real.pi / 3 - Real.pi / 3)
      + ((0 : ℕ) : ℝ) * (Real.pi / 3) + ((0 : ℕ) : ℝ) * Real.pi = Real.pi / 3 ∧ ¬ Irr (Real.pi / 3) := by
  refine ⟨by push_cast; ring, ?_⟩
  intro h
  exact h ⟨1 / 3, by push_cast; ring⟩

/-! ## Distinctness of the five angle values, from irrationality -/

section distinct

variable {α : ℝ}

theorem irr_ne (h : Irr α) (r : ℚ) : α ≠ (r : ℝ) * Real.pi := fun e => h ⟨r, e⟩

theorem d_ab (h : Irr α) : α ≠ 2 * Real.pi / 3 - α := fun e =>
  h ⟨1 / 3, by push_cast; linarith⟩
theorem d_ag (h : Irr α) : α ≠ Real.pi / 3 := fun e => h ⟨1 / 3, by push_cast; linarith⟩
theorem d_ap (h : Irr α) : α ≠ Real.pi := fun e => h ⟨1, by push_cast; linarith⟩
theorem d_a0 (h : Irr α) : α ≠ 0 := fun e => h ⟨0, by push_cast; linarith⟩
theorem d_bg (h : Irr α) : 2 * Real.pi / 3 - α ≠ Real.pi / 3 := fun e =>
  h ⟨1 / 3, by push_cast; linarith⟩
theorem d_bp (h : Irr α) : 2 * Real.pi / 3 - α ≠ Real.pi := fun e =>
  h ⟨-1 / 3, by push_cast; linarith⟩
theorem d_b0 (h : Irr α) : 2 * Real.pi / 3 - α ≠ 0 := fun e => h ⟨2 / 3, by push_cast; linarith⟩
theorem d_gp : Real.pi / 3 ≠ Real.pi := by have := Real.pi_pos; intro e; linarith
theorem d_g0 : Real.pi / 3 ≠ 0 := by have := Real.pi_pos; intro e; linarith
theorem d_p0 : Real.pi ≠ 0 := Real.pi_pos.ne'

end distinct

/-! ## Real dissections -/

section real

variable {N : ℕ}

/-- Every corner angle of every tile is `α`, `β` or `π/3`. -/
theorem corner_mem (D : CongruentDissection N) {α a b c : ℝ} (hS : D.model.SixtyData α a b c)
    (i : Fin N) (j : Fin 3) :
    cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
      ∈ ({α, 2 * Real.pi / 3 - α, Real.pi / 3} : Finset ℝ) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
  obtain ⟨τ, h0, -, h1, -, h2, -⟩ := hS
  have hj := (hσ j).1
  obtain ⟨m, hm⟩ := τ.surjective (σ j)
  have hk : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  show (D.tile i).angleAt j ∈ _
  rw [hj, ← hm]
  rcases hk with rfl | rfl | rfl
  · rw [h0]; simp
  · rw [h1]; simp
  · rw [h2]; simp

/-- **Multiplicities with the counts named, for any total.**  (`boundary_multiplicities_cards` is the case `t = π`.) -/
theorem cards_eq (D : Dissection N) {v : Plane} (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0) {t : ℝ}
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hsum : ∑ i, (D.tile i).localAngle v = t) :
    ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card : ℝ)) * α
      + ((({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card : ℝ)) * β
      + ((({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card : ℝ)) * γ
      + ((({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card : ℝ)) * Real.pi
      = t := by
  rw [sum_by_value ({α, β, γ, Real.pi, 0} : Finset ℝ) _ hvals] at hsum
  rw [show ({α, β, γ, Real.pi, 0} : Finset ℝ)
      = insert α (insert β (insert γ (insert Real.pi {0}))) from rfl] at hsum
  rw [Finset.sum_insert (by simp [hαβ, hαγ, hαπ, hα0]),
      Finset.sum_insert (by simp [hβγ, hβπ, hβ0]),
      Finset.sum_insert (by simp [hγπ, hγ0]),
      Finset.sum_insert (by simp [hπ0]), Finset.sum_singleton] at hsum
  push_cast at hsum ⊢
  linarith [hsum]

/-- Number of tiles presenting angle `θ` at `v`. -/
noncomputable def cnt (D : Dissection N) (v : Plane) (θ : ℝ) : ℕ :=
  ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)).card

/-- **Boundary figure on a real dissection.**  At a non-vertex point of the target boundary, the counts of tiles
presenting `α`, `β = 2π/3−α`, `π/3`, `π` are `(0,0,0,1)`, `(0,0,3,0)` or `(1,1,1,0)`. -/
theorem boundary_fan_real (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) {v : Plane} (hv : v ∈ frontier D.target.carrier)
    (hnv : v ∉ Set.range D.target.pts) :
    let n := fun θ => cnt D.toDissection v θ
    (n α = 0 ∧ n (2 * Real.pi / 3 - α) = 0 ∧ n (Real.pi / 3) = 0 ∧ n Real.pi = 1)
    ∨ (n α = 0 ∧ n (2 * Real.pi / 3 - α) = 0 ∧ n (Real.pi / 3) = 3 ∧ n Real.pi = 0)
    ∨ (n α = 1 ∧ n (2 * Real.pi / 3 - α) = 1 ∧ n (Real.pi / 3) = 1 ∧ n Real.pi = 0) := by
  intro n
  have hvals := localAngle_mem D.toDissection α (2 * Real.pi / 3 - α) (Real.pi / 3) hv hnv
    (fun i j => corner_mem D hS i j)
  have hs := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hv hnv
  have hc := cards_eq D.toDissection α _ _ (d_ab hirr) (d_ag hirr) (d_ap hirr) (d_a0 hirr)
    (d_bg hirr) (d_bp hirr) (d_b0 hirr) d_gp d_g0 d_p0 hvals hs
  have hc' : (cnt D.toDissection v α : ℝ) * α
      + (cnt D.toDissection v (2 * Real.pi / 3 - α) : ℝ) * (2 * Real.pi / 3 - α)
      + (cnt D.toDissection v (Real.pi / 3) : ℝ) * (Real.pi / 3)
      + (cnt D.toDissection v Real.pi : ℝ) * Real.pi = Real.pi := hc
  exact boundary_cases hirr _ _ _ _ hc'

/-- **Corner figure.**  At a target corner of angle `π/3` exactly one tile has a nonzero local angle, namely `π/3`. -/
theorem corner_fan_real (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (k : Fin 3) (hk : D.target.angleAt k = Real.pi / 3) :
    cnt D.toDissection (D.target.pts k) α = 0 ∧
    cnt D.toDissection (D.target.pts k) (2 * Real.pi / 3 - α) = 0 ∧
    cnt D.toDissection (D.target.pts k) (Real.pi / 3) = 1 ∧
    cnt D.toDissection (D.target.pts k) Real.pi = 0 := by
  have hs : ∑ i, (D.tile i).localAngle (D.target.pts k) = Real.pi / 3 := by
    rw [corner_angle_sum D.toDissection k]; exact hk
  have hpi := Real.pi_pos
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, 2 * Real.pi / 3 - α, Real.pi / 3, Real.pi, 0} : Finset ℝ) := by
    intro i
    have hle : (D.tile i).localAngle (D.target.pts k) ≤ Real.pi / 3 := by
      rw [← hs]
      exact Finset.single_le_sum (f := fun i => (D.tile i).localAngle (D.target.pts k))
        (fun i _ => Tri.localAngle_nonneg _ _) (Finset.mem_univ i)
    rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) (D.target.pts k) with
      ⟨j, _, hval⟩ | h2 | hpi' | h0
    · have := corner_mem D hS i j
      rw [hval]
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto
    · linarith
    · simp [hpi']
    · simp [h0]
  have hc := cards_eq D.toDissection α _ _ (d_ab hirr) (d_ag hirr) (d_ap hirr) (d_a0 hirr)
    (d_bg hirr) (d_bp hirr) (d_b0 hirr) d_gp d_g0 d_p0 hvals hs
  have hc' : (cnt D.toDissection (D.target.pts k) α : ℝ) * α
      + (cnt D.toDissection (D.target.pts k) (2 * Real.pi / 3 - α) : ℝ) * (2 * Real.pi / 3 - α)
      + (cnt D.toDissection (D.target.pts k) (Real.pi / 3) : ℝ) * (Real.pi / 3)
      + (cnt D.toDissection (D.target.pts k) Real.pi : ℝ) * Real.pi = Real.pi / 3 := hc
  exact (by
    have := corner_cases hirr _ _ _ _ hc'
    omega)

end real

/-! ## The concrete tile `T30` -/

section tile

open Erdos634.ChordWord Erdos634.Draft.G3CAng

theorem sa_pos : 0 < sa := by
  have h : Real.sqrt 21 < 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold sa; have := Real.sqrt_nonneg 21; linarith
theorem sb_pos : 0 < sb := by
  have h : Real.sqrt 21 < 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold sb; linarith
theorem sc_pos : 0 < sc := by unfold sc; norm_num

/-- **`T30` is a `π/3` tile.**  A triangle whose sides opposite the vertices `σ 0, σ 1, σ 2` are `a, b, c`
carries `SixtyData` (α = its angle at `σ 0`). -/
theorem t30_sixty_data (T : Tri) (σ : Equiv.Perm (Fin 3)) (o0 : T.oppLen (σ 0) = sa)
    (o1 : T.oppLen (σ 1) = sb) (o2 : T.oppLen (σ 2) = sc) :
    T.SixtyData (T.angleAt (σ 0)) sa sb sc := by
  have := sixty_data T σ 1 sa sb sc one_pos sa_pos sb_pos tile_relations.1
    (by rw [o0]; ring) (by rw [o1]; ring) (by rw [o2]; ring)
  simpa using this

/-- cos α = (3 − √21)/8. -/
theorem t30_cos (T : Tri) (σ : Equiv.Perm (Fin 3)) (o0 : T.oppLen (σ 0) = sa)
    (o1 : T.oppLen (σ 1) = sb) (o2 : T.oppLen (σ 2) = sc) :
    Real.cos (T.angleAt (σ 0)) = 3 / 8 - Real.sqrt 21 / 8 := by
  rw [cos_s0 T σ (by rw [o1]; exact sb_pos) (by rw [o2]; exact sc_pos), o0, o1, o2]
  have hs : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have hb : 0 < 2 * sb * sc := by have := sb_pos; have := sc_pos; positivity
  rw [div_eq_iff hb.ne']
  unfold sa sb sc
  linear_combination (-3) * hs

/-- **α/π is irrational for `T30`** (no new citation: `Row2.lemmaQ_sqfree17` + Mathlib's Niven integrality). -/
theorem t30_alpha_irr (T : Tri) (σ : Equiv.Perm (Fin 3)) (o0 : T.oppLen (σ 0) = sa)
    (o1 : T.oppLen (σ 1) = sb) (o2 : T.oppLen (σ 2) = sc) : Irr (T.angleAt (σ 0)) := by
  rintro ⟨r, hr⟩
  have hcos := t30_cos T σ o0 o1 o2
  have hs : Real.sqrt 21 ^ 2 = ((21 : ℕ) : ℝ) := by
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hs5 : Real.sqrt 21 < 5 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs4 : 4 < Real.sqrt 21 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hrange := Erdos634.Draft.FluxPaperWitness.cornerAngle_mem'
    (T.pts (σ 0 + 1)) (T.pts (σ 0)) (T.pts (σ 0 + 2))
  have hang : T.angleAt (σ 0) = cornerAngle (T.pts (σ 0 + 1)) (T.pts (σ 0)) (T.pts (σ 0 + 2)) := rfl
  have hQ : Erdos634.Geometry.Row2.QMu (Real.sqrt 21) (Real.cos (T.angleAt (σ 0))) :=
    ⟨3 / 8, -1 / 8, by rw [hcos]; push_cast; ring⟩
  have h0 : 0 < T.angleAt (σ 0) := by
    rcases hrange.1.lt_or_eq with h | h
    · rw [hang]; exact h
    · exfalso
      have : Real.cos (T.angleAt (σ 0)) = 1 := by rw [hang, ← h]; simp
      linarith
  have hπ : T.angleAt (σ 0) < Real.pi := by
    rcases hrange.2.lt_or_eq with h | h
    · rw [hang]; exact h
    · exfalso
      have : Real.cos (T.angleAt (σ 0)) = -1 := by rw [hang, h]; simp
      linarith
  have key := Erdos634.Geometry.Row2.lemmaQ_sqfree17 (p := 21) (by decide +kernel) (by norm_num) hs
    ⟨r, hr⟩ h0 hπ hQ
  have hirr := sqrt21_irrational
  rcases key with h | h | h
  · rw [h, Real.cos_pi_div_three] at hcos
    apply hirr; exact ⟨-1, by push_cast; linarith⟩
  · rw [h, Real.cos_pi_div_two] at hcos
    apply hirr; exact ⟨3, by push_cast; linarith⟩
  · rw [h, show Real.pi * (2 / 3) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three] at hcos
    apply hirr; exact ⟨7, by push_cast; linarith⟩

end tile

/-! ## A boundary non-vertex point (used by the witness) -/

theorem edge_mid (T : Tri) (k : Fin 3) :
    midpoint ℝ (T.pts k) (T.pts (k + 1)) ∈ frontier T.carrier ∧
    midpoint ℝ (T.pts k) (T.pts (k + 1)) ∉ Set.range T.pts := by
  refine ⟨Erdos634.SideWall.edge_subset_frontier T k (midpoint_mem_segment _ _), ?_⟩
  rintro ⟨j, hj⟩
  have hne : k ≠ k + 1 := by fin_cases k <;> decide
  have h1 : T.basis.coord k (midpoint ℝ (T.pts k) (T.pts (k + 1))) = 1 / 2 := by
    rw [AffineMap.map_midpoint]
    have e1 : T.basis.coord k (T.pts k) = 1 := T.basis.coord_apply_eq k
    have e2 : T.basis.coord k (T.pts (k + 1)) = 0 := T.basis.coord_apply_ne hne
    rw [e1, e2, midpoint_eq_smul_add]; norm_num
  rw [← hj] at h1
  by_cases hjk : j = k
  · subst hjk
    have e1 : T.basis.coord j (T.pts j) = 1 := T.basis.coord_apply_eq j
    rw [e1] at h1; norm_num at h1
  · have e2 : T.basis.coord k (T.pts j) = 0 := T.basis.coord_apply_ne (Ne.symm hjk)
    rw [e2] at h1; norm_num at h1

/-! ## WITNESS: the real 1440-tiling (equilateral side 240, tile (5,8,7)) -/

section witness

open Erdos634.Draft.G3CSixtyControl

/-- Every hypothesis of `corner_fan_real` holds on the real dissection `G3CSixtyControl.D`, at all three corners,
and the conclusion is then a nontrivial fact about it: each corner carries exactly one tile, a `π/3`. -/
theorem witness_corner (k : Fin 3) :
    cnt D.toDissection (D.target.pts k) α = 0 ∧
    cnt D.toDissection (D.target.pts k) (2 * Real.pi / 3 - α) = 0 ∧
    cnt D.toDissection (D.target.pts k) (Real.pi / 3) = 1 ∧
    cnt D.toDissection (D.target.pts k) Real.pi = 0 :=
  corner_fan_real D (hirr := α_irr) data k (t_angle k)

/-- And `boundary_fan_real` at the midpoint of a target side of the real dissection. -/
theorem witness_boundary :
    let v := midpoint ℝ (D.target.pts 0) (D.target.pts (0 + 1))
    let n := fun θ => cnt D.toDissection v θ
    (n α = 0 ∧ n (2 * Real.pi / 3 - α) = 0 ∧ n (Real.pi / 3) = 0 ∧ n Real.pi = 1)
    ∨ (n α = 0 ∧ n (2 * Real.pi / 3 - α) = 0 ∧ n (Real.pi / 3) = 3 ∧ n Real.pi = 0)
    ∨ (n α = 1 ∧ n (2 * Real.pi / 3 - α) = 1 ∧ n (Real.pi / 3) = 1 ∧ n Real.pi = 0) :=
  boundary_fan_real D (hirr := α_irr) data (edge_mid D.target 0).1 (edge_mid D.target 0).2

end witness

#print axioms witness_corner
#print axioms witness_boundary
#print axioms t30_alpha_irr
#print axioms t30_sixty_data

end Erdos634.Pi3Tile
