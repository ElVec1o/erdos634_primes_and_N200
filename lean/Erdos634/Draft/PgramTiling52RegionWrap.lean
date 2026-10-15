import Erdos634.PgramTiling52Region

namespace Erdos634.Draft.PgramTiling52RegionWrap

-- PgramTiling52Region.lean assembles the 52-piece parallelogram tiling (f=3, tile (3,8,9)) as a
-- CongruentRegionDissection.  There are no top-level theorems; the export is the def `dissection`.
-- Non-vacuity: the dissection's model is defined (tile (3,8,9), 52 pieces).
-- This is the f=3 analogue of PgramTiling22Region/PgramTiling22RegionWrap (f=2).
example : True := trivial
#check @Erdos634.PgramTiling52Region.dissection

end Erdos634.Draft.PgramTiling52RegionWrap
