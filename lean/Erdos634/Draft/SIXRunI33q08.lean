import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q08.lean — chunks 32..35 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk32 : checkNodeE sixInstI33 400 sixCfgI32 sixChunkI32 = true := by decide +kernel
theorem sixI33_cfgOk32 : sixCfgI32.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk33 : checkNodeE sixInstI33 400 sixCfgI33 sixChunkI33 = true := by decide +kernel
theorem sixI33_cfgOk33 : sixCfgI33.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk34 : checkNodeE sixInstI33 400 sixCfgI34 sixChunkI34 = true := by decide +kernel
theorem sixI33_cfgOk34 : sixCfgI34.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk35 : checkNodeE sixInstI33 400 sixCfgI35 sixChunkI35 = true := by decide +kernel
theorem sixI33_cfgOk35 : sixCfgI35.all Tri.ok = true := by decide +kernel
