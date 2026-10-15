import Erdos634.CevianTiling28Bridge
namespace Erdos634.Draft.CevianTiling28BridgeWrap
open Erdos634.CevianTiling28Bridge Erdos634.Z15Real Erdos634.Geometry

theorem wrap_all_pieces_pos :
    ∀ t ∈ CevianTiling28.tiles,
      zpos (zcross (toZPt (CevianTiling28.t1 t)) (toZPt (CevianTiling28.t2 t))
        (toZPt (CevianTiling28.t3 t))) = true :=
  all_pieces_pos

theorem wrap_all_pairs_ok :
    ∀ A ∈ CevianTiling28.tiles, ∀ B ∈ CevianTiling28.tiles, A ≠ B → pairOK A B = true :=
  all_pairs_ok

theorem wrap_all_pieces_cong :
    ∀ t ∈ CevianTiling28.tiles, congOK' t = true :=
  all_pieces_cong

theorem wrap_pieces_interiors_disjoint {A B : CevianTiling28.Tri}
    (hA : A ∈ CevianTiling28.tiles) (hB : B ∈ CevianTiling28.tiles) (hne : A ≠ B) :
    Disjoint (interior (pieceTri hA).carrier) (interior (pieceTri hB).carrier) :=
  pieces_interiors_disjoint hA hB hne

example : True := trivial
#print axioms wrap_pieces_interiors_disjoint
end Erdos634.Draft.CevianTiling28BridgeWrap
