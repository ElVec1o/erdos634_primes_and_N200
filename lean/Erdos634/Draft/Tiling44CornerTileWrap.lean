import Erdos634.Tiling44CornerTile

namespace Erdos634.Draft.Tiling44CornerTileWrap

theorem wrap_corner_tile_edge_c :
    Tiling44.dist2 (Tiling44.t2 Tiling44.tiles[13]) (Tiling44.t3 Tiling44.tiles[13])
      = (1024, 0) :=
  _root_.corner_tile_edge_c

example : True := trivial
#print axioms wrap_corner_tile_edge_c

end Erdos634.Draft.Tiling44CornerTileWrap
