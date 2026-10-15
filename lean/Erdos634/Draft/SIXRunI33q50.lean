import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q50.lean — chunks 200..203 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk200 : checkNodeE sixInstI33 400 sixCfgI200 sixChunkI200 = true := by decide +kernel
theorem sixI33_cfgOk200 : sixCfgI200.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk201 : checkNodeE sixInstI33 400 sixCfgI201 sixChunkI201 = true := by decide +kernel
theorem sixI33_cfgOk201 : sixCfgI201.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk202 : checkNodeE sixInstI33 400 sixCfgI202 sixChunkI202 = true := by decide +kernel
theorem sixI33_cfgOk202 : sixCfgI202.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk203 : checkNodeE sixInstI33 400 sixCfgI203 sixChunkI203 = true := by decide +kernel
theorem sixI33_cfgOk203 : sixCfgI203.all Tri.ok = true := by decide +kernel
