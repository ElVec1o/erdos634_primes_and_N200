import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q17.lean — chunks 68..71 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk68 : checkNodeE sixInstI33 400 sixCfgI68 sixChunkI68 = true := by decide +kernel
theorem sixI33_cfgOk68 : sixCfgI68.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk69 : checkNodeE sixInstI33 400 sixCfgI69 sixChunkI69 = true := by decide +kernel
theorem sixI33_cfgOk69 : sixCfgI69.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk70 : checkNodeE sixInstI33 400 sixCfgI70 sixChunkI70 = true := by decide +kernel
theorem sixI33_cfgOk70 : sixCfgI70.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk71 : checkNodeE sixInstI33 400 sixCfgI71 sixChunkI71 = true := by decide +kernel
theorem sixI33_cfgOk71 : sixCfgI71.all Tri.ok = true := by decide +kernel
