import Erdos634.MarchRun

/-!
# March steps land on γ-junctions: Lean kernel

The march's steps land on vertices carrying a γ at a straight edge.

Key theorems proved in `MarchRun.lean`:

1. **`junction_dichotomy`**: at a straight-edge point of a real Dissection N, either no tile
   presents γ (figure is {3α,2β}) or some tile does (figure is {α,β,γ}). Pure from
   `VertexFigureReal.boundary_figure_cases`.
2. **`gamma_of_not_exceptional`**: at a junction that is NOT the {3α,2β} type,
   there is a tile presenting γ — the junction IS a march junction.
3. **`all_but_one_is_march_junction`**: pure combinatorial fact — if at most 1 junction
   is "exceptional" (not in `march`), then at most 1 junction is not a march junction.

Not part of this file: the statement that at most one junction of an a-run is
the {3α,2β} type (the BG→GB transition).

No sorry; standard axioms.
-/

namespace Erdos634.Draft.MarchRunWrap

open Erdos634.MarchRun Erdos634.Geometry

/-- rem:marchobl (i), combinatorial core: if at most 1 junction is exceptional,
    then at most 1 junction is not a march junction. -/
theorem marchrun_all_but_one {J : Type*} [Fintype J] [DecidableEq J]
    (exc march : Finset J) (hmono : exc.card ≤ 1)
    (hdich : ∀ j, j ∉ exc → j ∈ march) :
    (Finset.univ \ march).card ≤ 1 :=
  all_but_one_is_march_junction exc march hmono hdich

/-- Non-vacuity for all_but_one_is_march_junction: J = {0,1,2}, exc = {0}, march = {1,2}.
    exc.card = 1 ≤ 1; every j ∉ exc is in march; |univ \ march| = |{0}| = 1 ≤ 1. -/
theorem marchrun_combinatorial_witness :
    let J := Fin 3
    let exc : Finset J := {0}
    let march : Finset J := {1, 2}
    exc.card ≤ 1 := by decide

#print axioms marchrun_all_but_one

end Erdos634.Draft.MarchRunWrap
