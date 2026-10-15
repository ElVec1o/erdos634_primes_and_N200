import Erdos634.R126Tiling
import Erdos634.Z2Real

/-! R126C defs: shared definitions and slicing of `R126Tiling.tiles` for the chunked pair check. -/

namespace Erdos634.R126CBridge

open Erdos634.Z2Real

def toZPt (p : R126Tiling.Pt) : ZPt := p

/-- The 6 candidate separating edges for a pair: each triangle's own 3 edges. -/
def edgeCands (A B : R126Tiling.Tri) : List (R126Tiling.Pt × R126Tiling.Pt) :=
  [R126Tiling.edgeOf A 0, R126Tiling.edgeOf A 1, R126Tiling.edgeOf A 2,
   R126Tiling.edgeOf B 0, R126Tiling.edgeOf B 1, R126Tiling.edgeOf B 2]

/-- The decidable side condition `sep_of_sepBy` needs for an edge `(P, Q)`, as a `Bool` — a direct
`decide` of the exact `Prop` `sep_of_sepBy` wants, so `sqCond_iff` is immediate. -/
def sqCond (pq : R126Tiling.Pt × R126Tiling.Pt) : Bool :=
  decide ((zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).1 ^ 2
             ≠ 2 * (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).2 ^ 2
         ∨ (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).1 ^ 2
             ≠ 2 * (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).2 ^ 2)

/-- Some candidate edge both separates `A` and `B` and satisfies the side condition. -/
def pairOK (A B : R126Tiling.Tri) : Bool :=
  (edgeCands A B).any (fun pq => R126Tiling.sepBy pq.1 pq.2 A B && sqCond pq)

def slice0 : List R126Tiling.Tri := R126Tiling.tiles.take 21
def rest1 : List R126Tiling.Tri := R126Tiling.tiles.drop 21
def slice1 : List R126Tiling.Tri := rest1.take 21
def rest2 : List R126Tiling.Tri := rest1.drop 21
def slice2 : List R126Tiling.Tri := rest2.take 21
def rest3 : List R126Tiling.Tri := rest2.drop 21
def slice3 : List R126Tiling.Tri := rest3.take 21
def rest4 : List R126Tiling.Tri := rest3.drop 21
def slice4 : List R126Tiling.Tri := rest4.take 21
def rest5 : List R126Tiling.Tri := rest4.drop 21
def slice5 : List R126Tiling.Tri := rest5

theorem cover : ∀ A ∈ R126Tiling.tiles,
    A ∈ slice0 ∨ A ∈ slice1 ∨ A ∈ slice2 ∨ A ∈ slice3 ∨ A ∈ slice4 ∨ A ∈ slice5 := by
  intro A hA
  have e0 : slice0 ++ rest1 = R126Tiling.tiles := List.take_append_drop 21 _
  have e1 : slice1 ++ rest2 = rest1 := List.take_append_drop 21 _
  have e2 : slice2 ++ rest3 = rest2 := List.take_append_drop 21 _
  have e3 : slice3 ++ rest4 = rest3 := List.take_append_drop 21 _
  have e4 : slice4 ++ rest5 = rest4 := List.take_append_drop 21 _
  rw [← e0, List.mem_append] at hA
  rcases hA with h | h
  · exact Or.inl h
  rw [← e1, List.mem_append] at h
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  rw [← e2, List.mem_append] at h
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  rw [← e3, List.mem_append] at h
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  rw [← e4, List.mem_append] at h
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Erdos634.R126CBridge
