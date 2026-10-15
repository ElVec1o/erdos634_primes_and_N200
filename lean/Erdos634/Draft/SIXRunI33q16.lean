import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q16.lean — chunks 64..67 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk64 : checkNodeE sixInstI33 400 sixCfgI64 sixChunkI64 = true := by decide +kernel
theorem sixI33_cfgOk64 : sixCfgI64.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk65 : checkNodeE sixInstI33 400 sixCfgI65 sixChunkI65 = true := by decide +kernel
theorem sixI33_cfgOk65 : sixCfgI65.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk66 : checkNodeE sixInstI33 400 sixCfgI66 sixChunkI66 = true := by decide +kernel
theorem sixI33_cfgOk66 : sixCfgI66.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk67 : checkNodeE sixInstI33 400 sixCfgI67 sixChunkI67 = true := by decide +kernel
theorem sixI33_cfgOk67 : sixCfgI67.all Tri.ok = true := by decide +kernel
