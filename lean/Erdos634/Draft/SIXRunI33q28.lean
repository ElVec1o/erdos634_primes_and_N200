import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q28.lean — chunks 112..115 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk112 : checkNodeE sixInstI33 400 sixCfgI112 sixChunkI112 = true := by decide +kernel
theorem sixI33_cfgOk112 : sixCfgI112.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk113 : checkNodeE sixInstI33 400 sixCfgI113 sixChunkI113 = true := by decide +kernel
theorem sixI33_cfgOk113 : sixCfgI113.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk114 : checkNodeE sixInstI33 400 sixCfgI114 sixChunkI114 = true := by decide +kernel
theorem sixI33_cfgOk114 : sixCfgI114.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk115 : checkNodeE sixInstI33 400 sixCfgI115 sixChunkI115 = true := by decide +kernel
theorem sixI33_cfgOk115 : sixCfgI115.all Tri.ok = true := by decide +kernel
