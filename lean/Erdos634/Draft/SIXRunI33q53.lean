import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q53.lean — chunks 212..212 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk212 : checkNodeE sixInstI33 400 sixCfgI212 sixChunkI212 = true := by decide +kernel
theorem sixI33_cfgOk212 : sixCfgI212.all Tri.ok = true := by decide +kernel
