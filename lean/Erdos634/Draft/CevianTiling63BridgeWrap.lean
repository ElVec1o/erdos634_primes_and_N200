import Erdos634.CevianTiling63Bridge
namespace Erdos634.Draft.CevianTiling63BridgeWrap
open Erdos634.CevianTiling63Bridge Erdos634.Z15Real Erdos634.Geometry

theorem wrap_all_pieces_pos :
    ∀ t ∈ CevianTiling63.tiles,
      zpos (zcross (toZPt (CevianTiling63.t1 t)) (toZPt (CevianTiling63.t2 t))
        (toZPt (CevianTiling63.t3 t))) = true :=
  all_pieces_pos

theorem wrap_all_pairs_ok :
    ∀ A ∈ CevianTiling63.tiles, ∀ B ∈ CevianTiling63.tiles, A ≠ B → pairOK A B = true :=
  all_pairs_ok

theorem wrap_all_pieces_cong :
    ∀ t ∈ CevianTiling63.tiles, congOK' t = true :=
  all_pieces_cong

theorem wrap_pieces_interiors_disjoint {A B : CevianTiling63.Tri}
    (hA : A ∈ CevianTiling63.tiles) (hB : B ∈ CevianTiling63.tiles) (hne : A ≠ B) :
    Disjoint (interior (pieceTri hA).carrier) (interior (pieceTri hB).carrier) :=
  pieces_interiors_disjoint hA hB hne

example : True := trivial
#print axioms wrap_pieces_interiors_disjoint
end Erdos634.Draft.CevianTiling63BridgeWrap
