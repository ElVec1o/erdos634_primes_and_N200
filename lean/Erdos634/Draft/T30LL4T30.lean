import Mathlib.Tactic
import Erdos634.Draft.T30LL4Corner
import Erdos634.Draft.ChordWord

/-!
# `l3_corner` and `l4_corner` at the N = 60 tile `T30 = (9+√21, 9-√21, 12)`

All arithmetic inputs are discharged.  The word lemmas `x a+y b+z c = a → y = 0`, `= c → x+y+z = 1`, `= 2c → (x,y,z) = (0,0,2)` and `a ≠ b`, `a ≠ c`, `b ≠ c`, `b < a` are
`ChordWord.chord_a`, `chord_c`, `chord_2c` (irrational split) and `√21 ∈ (4,5)`.  `l4_T30`: no corner of type `(b,a)` (second tile on the longer-edge side has side edge `b`, on the shorter-edge side `a`).
`l3_T30`: the doubled corner `(a,b)` forces a `π/3` tile along the side past the doubled chord (conclusion of `l3_corner`).  Both are statements about dissections with model `T30` and `α ∉ ℚπ`.
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6 Erdos634.ChordWord

theorem sqrt21_gt4 : (4 : ℝ) < Real.sqrt 21 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
theorem sqrt21_lt5 : Real.sqrt 21 < 5 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem sb_lt_sa : sb < sa := by unfold sa sb; have := sqrt21_gt4; linarith
theorem sa_ne_sb : sa ≠ sb := sb_lt_sa.ne'
theorem sa_ne_sc : sa ≠ sc := by unfold sa sc; have := sqrt21_gt4; intro h; linarith
theorem sb_ne_sc : sb ≠ sc := by unfold sb sc; have := sqrt21_gt4; intro h; linarith

theorem word1_T30 : ∀ x y z : ℕ, (x : ℝ) * sa + y * sb + z * sc = sa → y = 0 :=
  fun x y z h => (chord_a x y z h).2.1
theorem wordc_T30 : ∀ x y z : ℕ, (x : ℝ) * sa + y * sb + z * sc = sc → x + y + z = 1 := by
  intro x y z h
  have := chord_c x y z h
  omega
theorem word2_T30 : ∀ x y z : ℕ, (x : ℝ) * sa + y * sb + z * sc = 2 * sc → x = 0 ∧ y = 0 ∧ z = 2 :=
  fun x y z h => chord_2c x y z h

/-- **L4 at `T30`.**  No corner of type `(b,a)`. -/
theorem l4_T30 {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α sa sb sc)
    (i : Fin N) (j : Fin 3) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hjv : (D.tile i).pts j = D.target.pts v) (hang : (D.tile i).angleAt j = Real.pi / 3)
    {p r : ℝ} (hp0 : 0 < p) (hr0 : 0 < r)
    (hP : (D.tile i).pts (j + 1) - D.target.pts v = p • (D.target.pts w - D.target.pts v))
    (hQ : (D.tile i).pts (j + 2) - D.target.pts v = r • (D.target.pts z - D.target.pts v))
    (hOP : dist (D.target.pts v) ((D.tile i).pts (j + 1)) = sa)
    (hOQ : dist (D.target.pts v) ((D.tile i).pts (j + 2)) = sb)
    (hK3 : SideTileLen D ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 1) - D.target.pts v) sb)
    (hK4 : SideTileLen D ((D.tile i).pts (j + 2)) ((D.tile i).pts (j + 2) - D.target.pts v) sa) :
    False :=
  l4_corner D hirr hS sa_ne_sc sb_ne_sc sa_ne_sb sb_lt_sa word1_T30 wordc_T30 i j v w z hvw hvz hwz hjv hang
    hp0 hr0 hP hQ hOP hOQ hK3 hK4

/-- **L3 at `T30`.**  The doubled corner `(a,b)`: the third edge on the side is not a `c`-edge (conclusion of `l3_corner`). -/
theorem l3_T30 {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α sa sb sc)
    (i : Fin N) (j : Fin 3) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hjv : (D.tile i).pts j = D.target.pts v) (hang : (D.tile i).angleAt j = Real.pi / 3)
    {p r : ℝ} (hp0 : 0 < p) (hr0 : 0 < r)
    (hP : (D.tile i).pts (j + 1) - D.target.pts v = p • (D.target.pts w - D.target.pts v))
    (hQ : (D.tile i).pts (j + 2) - D.target.pts v = r • (D.target.pts z - D.target.pts v))
    (hOP : dist (D.target.pts v) ((D.tile i).pts (j + 1)) = sa)
    (hOQ : dist (D.target.pts v) ((D.tile i).pts (j + 2)) = sb)
    (h2a : dist (D.target.pts v) (D.target.pts w) ≠ 2 * sa)
    (h2b : dist (D.target.pts v) (D.target.pts z) ≠ 2 * sb)
    (hK3 : SideTileLen D ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 1) - D.target.pts v) sa)
    (hK4 : SideTileLen D ((D.tile i).pts (j + 2)) ((D.tile i).pts (j + 2) - D.target.pts v) sb) :
    SideTile D ((D.tile i).pts (j + 1) + ((D.tile i).pts (j + 1) - D.target.pts v))
      ((D.tile i).pts (j + 1) - D.target.pts v) sa sb :=
  l3_corner D hirr hS sa_ne_sc sb_ne_sc sa_ne_sb word2_T30 i j v w z hvw hvz hwz hjv hang hp0 hr0 hP hQ hOP hOQ
    h2a h2b hK3 hK4

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.l4_T30
#print axioms Erdos634.C2Forward.l3_T30
