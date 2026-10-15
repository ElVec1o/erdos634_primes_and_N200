import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q11.lean — chunks 44..47 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk44 : checkNodeE sixInstI33 400 sixCfgI44 sixChunkI44 = true := by decide +kernel
theorem sixI33_cfgOk44 : sixCfgI44.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk45 : checkNodeE sixInstI33 400 sixCfgI45 sixChunkI45 = true := by decide +kernel
theorem sixI33_cfgOk45 : sixCfgI45.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk46 : checkNodeE sixInstI33 400 sixCfgI46 sixChunkI46 = true := by decide +kernel
theorem sixI33_cfgOk46 : sixCfgI46.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk47 : checkNodeE sixInstI33 400 sixCfgI47 sixChunkI47 = true := by decide +kernel
theorem sixI33_cfgOk47 : sixCfgI47.all Tri.ok = true := by decide +kernel
