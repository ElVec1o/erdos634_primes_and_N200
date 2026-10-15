import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q34.lean — chunks 136..139 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk136 : checkNodeE sixInstI33 400 sixCfgI136 sixChunkI136 = true := by decide +kernel
theorem sixI33_cfgOk136 : sixCfgI136.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk137 : checkNodeE sixInstI33 400 sixCfgI137 sixChunkI137 = true := by decide +kernel
theorem sixI33_cfgOk137 : sixCfgI137.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk138 : checkNodeE sixInstI33 400 sixCfgI138 sixChunkI138 = true := by decide +kernel
theorem sixI33_cfgOk138 : sixCfgI138.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk139 : checkNodeE sixInstI33 400 sixCfgI139 sixChunkI139 = true := by decide +kernel
theorem sixI33_cfgOk139 : sixCfgI139.all Tri.ok = true := by decide +kernel
