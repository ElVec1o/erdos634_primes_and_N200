import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q35.lean — chunks 140..143 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk140 : checkNodeE sixInstI33 400 sixCfgI140 sixChunkI140 = true := by decide +kernel
theorem sixI33_cfgOk140 : sixCfgI140.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk141 : checkNodeE sixInstI33 400 sixCfgI141 sixChunkI141 = true := by decide +kernel
theorem sixI33_cfgOk141 : sixCfgI141.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk142 : checkNodeE sixInstI33 400 sixCfgI142 sixChunkI142 = true := by decide +kernel
theorem sixI33_cfgOk142 : sixCfgI142.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk143 : checkNodeE sixInstI33 400 sixCfgI143 sixChunkI143 = true := by decide +kernel
theorem sixI33_cfgOk143 : sixCfgI143.all Tri.ok = true := by decide +kernel
