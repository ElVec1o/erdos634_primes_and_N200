/-
Draft/ZhangProps.lean — **Zhang's Theorem 4 and Propositions 8, 9, tile-uniform** (arXiv:2512.22696v4), summary module.

For every `2π/3` tile `(a, b, c)` (`c² = a² + ab + b²`, naturals) and every `t₀` with `t₀ ab ∈ a² + b² + ⟨a, b⟩`
(`Frob a b t₀`), and every `m ≥ 3 t₀`, the following are tile counts of the tile (each is an explicit
dissection of a triangle):
  * `a b m²`      equilateral triangle of side `m a b`            (`ZhangEqui.zhang_equi_m`, Thm 4),
  * `a (2a+b) m²` isosceles triangle `(m a c, m a c, m a (b+2a))`   (`ZhangIso.zhang_iso_m`, Prop 8),
  * `b (a+b) m²`  triangle `(m a b, m b c, m b (a+b))`              (`ZhangF1.zhang_f1_m`, Prop 9),
and the mirror images (`a ↔ b`) `b (2b+a) m²`, `a (a+b) m²`.
The mathematics is Zhang's; what is new is the formal, tile-uniform statement (one proof for all `(a,b,c)`).
Witnesses: `(3,5,7)`, `t₀ = 3`; `(7,8,13)`, `t₀ = 3`; both give `m ≥ 9`.

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.ZhangIso
import Erdos634.Draft.ZhangF1

open scoped Classical
set_option linter.unusedSectionVars false

namespace Erdos634.Draft.ZhangProps
open Erdos634.Draft.ZhangTrap Erdos634.Draft.ZhangEqui Erdos634.Draft.ZhangIso Erdos634.Draft.ZhangF1
open Erdos634.Draft.TileCountFamilies (TileCount)

theorem _root_.Erdos634.Draft.ZhangEqui.Frob.swap {a b t : ℕ} (h : Frob a b t) : Frob b a t := by
  obtain ⟨i, j, h⟩ := h
  exact ⟨j, i, by rw [mul_comm b a]; linarith⟩

theorem hc_swap {a b c : ℕ} (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) : c ^ 2 = b ^ 2 + b * a + a ^ 2 := by
  rw [hc]; ring

/-- the five Zhang families from one Frobenius witness. -/
theorem zhang_five (a b c t0 m : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (h0 : Frob a b t0) (hm : 3 * t0 ≤ m) :
    TileCount (a * b * m ^ 2) ∧ TileCount (a * (b + 2 * a) * m ^ 2) ∧ TileCount (b * (a + 2 * b) * m ^ 2) ∧
      TileCount (b * (a + b) * m ^ 2) ∧ TileCount (a * (b + a) * m ^ 2) := by
  have h0' := h0.swap
  have hc' := hc_swap hc
  refine ⟨zhang_equi_m a b c t0 m ha hb hc h0 hm, zhang_iso_m a b c t0 m ha hb hc h0 hm,
    zhang_iso_m b a c t0 m hb ha hc' h0' hm, zhang_f1_m a b c t0 m ha hb hc h0 hm, ?_⟩
  exact zhang_f1_m b a c t0 m hb ha hc' h0' hm

/-- (3,5,7), `m = 9`: the side-135 equilateral tiling by 1215 tiles, agreeing with `Draft.EqSemigroup.eqD_135`. -/
theorem zhang_357_m9 : ∃ (hL : 0 < 3 * 5 * (3 + 3 + 3)), ∃ D : Erdos634.Geometry.CongruentDissection (3 * 5 * (3 + 3 + 3) ^ 2),
    D.model = Mn 3 5 (by norm_num) (by norm_num) ∧ D.target = Erdos634.Draft.EqSemigroup.eqTri (3 * 5 * (3 + 3 + 3)) hL :=
  zhang_equi_dissection 3 5 7 3 3 3 (by norm_num) (by norm_num) (by norm_num) ⟨2, 1, by norm_num⟩
    ⟨2, 1, by norm_num⟩ ⟨2, 1, by norm_num⟩

example : TileCount 1215 := (zhang_five 3 5 7 3 9 (by norm_num) (by norm_num) (by norm_num) ⟨2, 1, by norm_num⟩ (by norm_num)).1
example : TileCount 4536 := (zhang_five 7 8 13 3 9 (by norm_num) (by norm_num) (by norm_num) ⟨1, 6, by norm_num⟩ (by norm_num)).1
/-- (7,8,13), `m = 9`: the isosceles `154 m²`, `184 m²` and F1 `120 m²`, `105 m²` families. -/
example : TileCount (154 * 9 ^ 2) ∧ TileCount (184 * 9 ^ 2) ∧ TileCount (120 * 9 ^ 2) ∧ TileCount (105 * 9 ^ 2) := by
  obtain ⟨-, h2, h3, h4, h5⟩ := zhang_five 7 8 13 3 9 (by norm_num) (by norm_num) (by norm_num) ⟨1, 6, by norm_num⟩ (by norm_num)
  exact ⟨by simpa using h2, by simpa using h3, by simpa using h4, by simpa using h5⟩

end Erdos634.Draft.ZhangProps

#print axioms Erdos634.Draft.ZhangProps.zhang_five
#print axioms Erdos634.Draft.ZhangProps.zhang_357_m9
