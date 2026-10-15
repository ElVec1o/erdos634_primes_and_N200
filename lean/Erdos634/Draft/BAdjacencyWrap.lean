import Erdos634.BAdjacency

/-!
# b-adjacency: wrapper

Re-exports, under `ba_` names, results of `BAdjacency`:
- `b_adjacency`: nonempty list with non-a ends, at most one c, at least one b → b at an end
- `ladder_room_kill`: 3f²+f < f³+f²+1 for f ≥ 3
- `no_full_phantom`: 3f² < f³+1 for f ≥ 3

No `sorry`; no axioms.
-/

namespace Erdos634.Draft.BAdjacencyWrap

open Erdos634.BAdjacency Letter

theorem ba_b_adjacency (M : List Letter) (hne : M ≠ [])
    (hhd : hd M ≠ Letter.a) (hlst : lst M ≠ Letter.a)
    (hc : cnt Letter.c M ≤ 1) (hb : 1 ≤ cnt Letter.b M) :
    hd M = Letter.b ∨ lst M = Letter.b :=
  b_adjacency M hne hhd hlst hc hb

theorem ba_ladder_room_kill (f : Nat) (h : 3 ≤ f) :
    3 * (f * f) + f < f * (f * f) + f * f + 1 :=
  ladder_room_kill f h

theorem ba_no_full_phantom (f : Nat) (h : 3 ≤ f) :
    3 * (f * f) < f * (f * f) + 1 :=
  no_full_phantom f h

-- Non-vacuity: ladder_room_kill at f=3: 30 < 37
example : 3 * (3 * 3) + 3 < 3 * (3 * 3) + 3 * 3 + 1 := ba_ladder_room_kill 3 (by omega)

#print axioms ba_b_adjacency
#print axioms ba_ladder_room_kill

end Erdos634.Draft.BAdjacencyWrap
