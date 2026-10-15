import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q07.lean — chunks 28..31 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk28 : checkNodeE sixInstI33 400 sixCfgI28 sixChunkI28 = true := by decide +kernel
theorem sixI33_cfgOk28 : sixCfgI28.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk29 : checkNodeE sixInstI33 400 sixCfgI29 sixChunkI29 = true := by decide +kernel
theorem sixI33_cfgOk29 : sixCfgI29.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk30 : checkNodeE sixInstI33 400 sixCfgI30 sixChunkI30 = true := by decide +kernel
theorem sixI33_cfgOk30 : sixCfgI30.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk31 : checkNodeE sixInstI33 400 sixCfgI31 sixChunkI31 = true := by decide +kernel
theorem sixI33_cfgOk31 : sixCfgI31.all Tri.ok = true := by decide +kernel
