import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q00.lean — chunks 0..3 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk0 : checkNodeE sixInstI33 400 sixCfgI0 sixChunkI0 = true := by decide +kernel
theorem sixI33_cfgOk0 : sixCfgI0.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk1 : checkNodeE sixInstI33 400 sixCfgI1 sixChunkI1 = true := by decide +kernel
theorem sixI33_cfgOk1 : sixCfgI1.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk2 : checkNodeE sixInstI33 400 sixCfgI2 sixChunkI2 = true := by decide +kernel
theorem sixI33_cfgOk2 : sixCfgI2.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk3 : checkNodeE sixInstI33 400 sixCfgI3 sixChunkI3 = true := by decide +kernel
theorem sixI33_cfgOk3 : sixCfgI3.all Tri.ok = true := by decide +kernel
