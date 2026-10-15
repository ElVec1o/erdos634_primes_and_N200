import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q13.lean — chunks 52..55 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk52 : checkNodeE sixInstI33 400 sixCfgI52 sixChunkI52 = true := by decide +kernel
theorem sixI33_cfgOk52 : sixCfgI52.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk53 : checkNodeE sixInstI33 400 sixCfgI53 sixChunkI53 = true := by decide +kernel
theorem sixI33_cfgOk53 : sixCfgI53.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk54 : checkNodeE sixInstI33 400 sixCfgI54 sixChunkI54 = true := by decide +kernel
theorem sixI33_cfgOk54 : sixCfgI54.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk55 : checkNodeE sixInstI33 400 sixCfgI55 sixChunkI55 = true := by decide +kernel
theorem sixI33_cfgOk55 : sixCfgI55.all Tri.ok = true := by decide +kernel
