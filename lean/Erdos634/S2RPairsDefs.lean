import Erdos634.S2RTiling
import Erdos634.Z2Real

/-! S2RPairsDefs: separating-edge predicate for the N=322 certificate (split out of the Bridge so the
pair check can be chunked across modules; same definitions as R126TilingBridge). -/
namespace Erdos634.S2RTilingBridge
open Erdos634.Z2Real

def toZPt (p : S2RTiling.Pt) : ZPt := p

/-- Tile chunk `k` (blocks of 24 tiles). -/
def chunk (k : Nat) : List S2RTiling.Tri := (S2RTiling.tiles.drop (24 * k)).take 24

/-- The 6 candidate separating edges for a pair: each triangle's own 3 edges. -/
def edgeCands (A B : S2RTiling.Tri) : List (S2RTiling.Pt × S2RTiling.Pt) :=
  [S2RTiling.edgeOf A 0, S2RTiling.edgeOf A 1, S2RTiling.edgeOf A 2,
   S2RTiling.edgeOf B 0, S2RTiling.edgeOf B 1, S2RTiling.edgeOf B 2]

/-- The decidable side condition `sep_of_sepBy` needs for an edge `(P, Q)`, as a `Bool` — a direct
`decide` of the exact `Prop` `sep_of_sepBy` wants, so `sqCond_iff` is immediate. -/
def sqCond (pq : S2RTiling.Pt × S2RTiling.Pt) : Bool :=
  decide ((zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).1 ^ 2
             ≠ 2 * (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).2 ^ 2
         ∨ (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).1 ^ 2
             ≠ 2 * (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).2 ^ 2)

/-- Some candidate edge both separates `A` and `B` and satisfies the side condition. -/
def pairOK (A B : S2RTiling.Tri) : Bool :=
  (edgeCands A B).any (fun pq => S2RTiling.sepBy pq.1 pq.2 A B && sqCond pq)

end Erdos634.S2RTilingBridge
