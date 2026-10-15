import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q52.lean — chunks 208..211 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk208 : checkNodeE sixInstI33 400 sixCfgI208 sixChunkI208 = true := by decide +kernel
theorem sixI33_cfgOk208 : sixCfgI208.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk209 : checkNodeE sixInstI33 400 sixCfgI209 sixChunkI209 = true := by decide +kernel
theorem sixI33_cfgOk209 : sixCfgI209.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk210 : checkNodeE sixInstI33 400 sixCfgI210 sixChunkI210 = true := by decide +kernel
theorem sixI33_cfgOk210 : sixCfgI210.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk211 : checkNodeE sixInstI33 400 sixCfgI211 sixChunkI211 = true := by decide +kernel
theorem sixI33_cfgOk211 : sixCfgI211.all Tri.ok = true := by decide +kernel
