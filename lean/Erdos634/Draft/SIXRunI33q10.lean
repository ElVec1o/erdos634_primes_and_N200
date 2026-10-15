import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q10.lean — chunks 40..43 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk40 : checkNodeE sixInstI33 400 sixCfgI40 sixChunkI40 = true := by decide +kernel
theorem sixI33_cfgOk40 : sixCfgI40.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk41 : checkNodeE sixInstI33 400 sixCfgI41 sixChunkI41 = true := by decide +kernel
theorem sixI33_cfgOk41 : sixCfgI41.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk42 : checkNodeE sixInstI33 400 sixCfgI42 sixChunkI42 = true := by decide +kernel
theorem sixI33_cfgOk42 : sixCfgI42.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk43 : checkNodeE sixInstI33 400 sixCfgI43 sixChunkI43 = true := by decide +kernel
theorem sixI33_cfgOk43 : sixCfgI43.all Tri.ok = true := by decide +kernel
