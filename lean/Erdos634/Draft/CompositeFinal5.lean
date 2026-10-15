-- Draft/CompositeFinal5.lean — N = 22 and N = 42: S2Closed discharged (CompositeS2Global); only `H1Right` remains.
import Erdos634.Draft.CompositeS2Global
import Erdos634.Draft.ChainCompositeR8b
import Erdos634.Draft.CompositeFinal3

namespace Erdos634.Draft.CompositeFinal5
open Erdos634.Geometry Erdos634.Draft.ChainComposite

theorem chain_22_H1only (gR : H1Right 22) (D : CongruentDissection 22) : False :=
  Erdos634.Draft.CompositeFinal3.chain_22_final gR
    Erdos634.Draft.CompositeS2Global.s2Closed_22 D

theorem chain_42_H1only (gR : H1Right 42) (D : CongruentDissection 42) : False :=
  Erdos634.Draft.R8Gen2.chain_42_R8 gR Erdos634.Draft.CompositeS2Global.s2Closed_42 D

#print axioms chain_22_H1only
#print axioms chain_42_H1only
end Erdos634.Draft.CompositeFinal5
