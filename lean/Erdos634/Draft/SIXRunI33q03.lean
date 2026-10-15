import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q03.lean — chunks 12..15 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk12 : checkNodeE sixInstI33 400 sixCfgI12 sixChunkI12 = true := by decide +kernel
theorem sixI33_cfgOk12 : sixCfgI12.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk13 : checkNodeE sixInstI33 400 sixCfgI13 sixChunkI13 = true := by decide +kernel
theorem sixI33_cfgOk13 : sixCfgI13.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk14 : checkNodeE sixInstI33 400 sixCfgI14 sixChunkI14 = true := by decide +kernel
theorem sixI33_cfgOk14 : sixCfgI14.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk15 : checkNodeE sixInstI33 400 sixCfgI15 sixChunkI15 = true := by decide +kernel
theorem sixI33_cfgOk15 : sixCfgI15.all Tri.ok = true := by decide +kernel
