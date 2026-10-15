import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q14.lean — chunks 56..59 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk56 : checkNodeE sixInstI33 400 sixCfgI56 sixChunkI56 = true := by decide +kernel
theorem sixI33_cfgOk56 : sixCfgI56.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk57 : checkNodeE sixInstI33 400 sixCfgI57 sixChunkI57 = true := by decide +kernel
theorem sixI33_cfgOk57 : sixCfgI57.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk58 : checkNodeE sixInstI33 400 sixCfgI58 sixChunkI58 = true := by decide +kernel
theorem sixI33_cfgOk58 : sixCfgI58.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk59 : checkNodeE sixInstI33 400 sixCfgI59 sixChunkI59 = true := by decide +kernel
theorem sixI33_cfgOk59 : sixCfgI59.all Tri.ok = true := by decide +kernel
