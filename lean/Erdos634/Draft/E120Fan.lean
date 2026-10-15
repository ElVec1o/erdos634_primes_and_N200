/-
Draft/E120Fan.lean -- the tile with an angle `2π/3`: its vertex figures on a real dissection.

Tile: angles `α`, `β = π/3 − α`, `γ = 2π/3` opposite the sides `a`, `b`, `c` (`Tri.TwoPiThreeData α a b c`), with
`α ∉ ℚπ`.  This is the `2π/3` counterpart of `Draft/T30LPi3Tile.lean` (namespace `Pi3Tile`), whose generic part
(`Irr`, `irr_split`, `cards_eq`, `cnt`) is reused.

* `fan_eq`: `x α + y β + z γ + s π = t π/3` gives `x = y` and `y + 2z + 3s = t`.
* `corner_cases` (`t = 1`): `(1, 1, 0; 0)`.  `boundary_cases` (`t = 3`): a straight angle, `(3, 3, 0)` or `(1, 1, 1)`.
* the distinctness lemmas `d_*`, and `corner_mem`: every corner angle of every tile is `α`, `β` or `γ`.
* `boundary_fan_real`, `corner_fan_real`: the figures at a point of the target boundary and at a target corner of
  angle `π/3`, as counts of tiles. not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.T30LPi3Tile
import Erdos634.Draft.FluxPaper

namespace Erdos634.TwoPi3Tile

open Erdos634.Geometry Erdos634.VertexFigureReal
open Erdos634.Pi3Tile (Irr irr_split cards_eq cnt)

/-- **The fan equation.** -/
theorem fan_eq {α : ℝ} (h : Irr α) (x y z s t : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * (Real.pi / 3 - α) + (z : ℝ) * (2 * Real.pi / 3)
      + (s : ℝ) * Real.pi = (t : ℝ) * (Real.pi / 3)) :
    x = y ∧ y + 2 * z + 3 * s = t := by
  have key := irr_split h (3 * ((x : ℤ) - y)) ((t : ℤ) - y - 2 * z - 3 * s)
    (by push_cast; linear_combination 3 * hsum)
  obtain ⟨h1, h2⟩ := key
  omega

/-- Boundary figure (angle sum `π`): one straight angle, `(α, α, α, β, β, β)` or `(α, β, γ)`. -/
theorem boundary_cases {α : ℝ} (h : Irr α) (x y z s : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * (Real.pi / 3 - α) + (z : ℝ) * (2 * Real.pi / 3)
      + (s : ℝ) * Real.pi = Real.pi) :
    (x = 0 ∧ y = 0 ∧ z = 0 ∧ s = 1) ∨ (x = 3 ∧ y = 3 ∧ z = 0 ∧ s = 0)
      ∨ (x = 1 ∧ y = 1 ∧ z = 1 ∧ s = 0) := by
  have := fan_eq h x y z s 3 (by push_cast; linarith)
  omega

/-- Corner of angle `π/3`: one `α` and one `β`. -/
theorem corner_cases {α : ℝ} (h : Irr α) (x y z s : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * (Real.pi / 3 - α) + (z : ℝ) * (2 * Real.pi / 3)
      + (s : ℝ) * Real.pi = Real.pi / 3) :
    x = 1 ∧ y = 1 ∧ z = 0 ∧ s = 0 := by
  have := fan_eq h x y z s 1 (by push_cast; linarith)
  omega

/-! ## Distinctness of the angle values, from irrationality -/

section distinct

variable {α : ℝ}

theorem d_ab (h : Irr α) : α ≠ Real.pi / 3 - α := fun e => h ⟨1 / 6, by push_cast; linarith⟩
theorem d_ag (h : Irr α) : α ≠ 2 * Real.pi / 3 := fun e => h ⟨2 / 3, by push_cast; linarith⟩
theorem d_ap (h : Irr α) : α ≠ Real.pi := fun e => h ⟨1, by push_cast; linarith⟩
theorem d_a0 (h : Irr α) : α ≠ 0 := fun e => h ⟨0, by push_cast; linarith⟩
theorem d_a2 (h : Irr α) : α ≠ 2 * Real.pi := fun e => h ⟨2, by push_cast; linarith⟩
theorem d_bg (h : Irr α) : Real.pi / 3 - α ≠ 2 * Real.pi / 3 := fun e => h ⟨-1 / 3, by push_cast; linarith⟩
theorem d_bp (h : Irr α) : Real.pi / 3 - α ≠ Real.pi := fun e => h ⟨-2 / 3, by push_cast; linarith⟩
theorem d_b0 (h : Irr α) : Real.pi / 3 - α ≠ 0 := fun e => h ⟨1 / 3, by push_cast; linarith⟩
theorem d_gp : 2 * Real.pi / 3 ≠ Real.pi := by have := Real.pi_pos; intro e; linarith
theorem d_g0 : 2 * Real.pi / 3 ≠ 0 := by have := Real.pi_pos; intro e; linarith
theorem d_p0 : Real.pi ≠ 0 := Real.pi_pos.ne'

theorem irr_swap (h : Irr α) : Irr (Real.pi / 3 - α) := by
  rintro ⟨r, hr⟩
  exact h ⟨1 / 3 - r, by push_cast; linarith⟩

end distinct

/-! ## Real dissections -/

section real

variable {N : ℕ}

/-- Every corner angle of every tile is `α`, `β` or `2π/3`. -/
theorem corner_mem (D : CongruentDissection N) {α a b c : ℝ} (hS : D.model.TwoPiThreeData α a b c)
    (i : Fin N) (j : Fin 3) :
    cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
      ∈ ({α, Real.pi / 3 - α, 2 * Real.pi / 3} : Finset ℝ) := by
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

/-- **Boundary figure on a real dissection.**  At a non-vertex point of the target boundary, the counts of tiles
presenting `α`, `β = π/3 − α`, `2π/3`, `π` are `(0,0,0,1)`, `(3,3,0,0)` or `(1,1,1,0)`. -/
theorem boundary_fan_real (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.TwoPiThreeData α a b c) {v : Plane} (hv : v ∈ frontier D.target.carrier)
    (hnv : v ∉ Set.range D.target.pts) :
    let n := fun θ => cnt D.toDissection v θ
    (n α = 0 ∧ n (Real.pi / 3 - α) = 0 ∧ n (2 * Real.pi / 3) = 0 ∧ n Real.pi = 1)
    ∨ (n α = 3 ∧ n (Real.pi / 3 - α) = 3 ∧ n (2 * Real.pi / 3) = 0 ∧ n Real.pi = 0)
    ∨ (n α = 1 ∧ n (Real.pi / 3 - α) = 1 ∧ n (2 * Real.pi / 3) = 1 ∧ n Real.pi = 0) := by
  intro n
  have hvals := localAngle_mem D.toDissection α (Real.pi / 3 - α) (2 * Real.pi / 3) hv hnv
    (fun i j => corner_mem D hS i j)
  have hs := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hv hnv
  have hc := cards_eq D.toDissection α _ _ (d_ab hirr) (d_ag hirr) (d_ap hirr) (d_a0 hirr)
    (d_bg hirr) (d_bp hirr) (d_b0 hirr) d_gp d_g0 d_p0 hvals hs
  have hc' : (cnt D.toDissection v α : ℝ) * α
      + (cnt D.toDissection v (Real.pi / 3 - α) : ℝ) * (Real.pi / 3 - α)
      + (cnt D.toDissection v (2 * Real.pi / 3) : ℝ) * (2 * Real.pi / 3)
      + (cnt D.toDissection v Real.pi : ℝ) * Real.pi = Real.pi := hc
  exact boundary_cases hirr _ _ _ _ hc'

/-- **Corner figure.**  At a target corner of angle `π/3` exactly two tiles have a nonzero local angle, one
presenting `α` and one presenting `π/3 − α`. -/
theorem corner_fan_real (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.TwoPiThreeData α a b c) (k : Fin 3) (hk : D.target.angleAt k = Real.pi / 3) :
    cnt D.toDissection (D.target.pts k) α = 1 ∧
    cnt D.toDissection (D.target.pts k) (Real.pi / 3 - α) = 1 ∧
    cnt D.toDissection (D.target.pts k) (2 * Real.pi / 3) = 0 ∧
    cnt D.toDissection (D.target.pts k) Real.pi = 0 := by
  have hs : ∑ i, (D.tile i).localAngle (D.target.pts k) = Real.pi / 3 := by
    rw [corner_angle_sum D.toDissection k]; exact hk
  have hpi := Real.pi_pos
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, Real.pi / 3 - α, 2 * Real.pi / 3, Real.pi, 0} : Finset ℝ) := by
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
      + (cnt D.toDissection (D.target.pts k) (Real.pi / 3 - α) : ℝ) * (Real.pi / 3 - α)
      + (cnt D.toDissection (D.target.pts k) (2 * Real.pi / 3) : ℝ) * (2 * Real.pi / 3)
      + (cnt D.toDissection (D.target.pts k) Real.pi : ℝ) * Real.pi = Real.pi / 3 := hc
  exact corner_cases hirr _ _ _ _ hc'

end real

end Erdos634.TwoPi3Tile

#print axioms Erdos634.TwoPi3Tile.boundary_fan_real
#print axioms Erdos634.TwoPi3Tile.corner_fan_real
