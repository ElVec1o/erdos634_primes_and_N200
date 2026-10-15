import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q04.lean — chunks 16..19 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk16 : checkNodeE sixInstI33 400 sixCfgI16 sixChunkI16 = true := by decide +kernel
theorem sixI33_cfgOk16 : sixCfgI16.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk17 : checkNodeE sixInstI33 400 sixCfgI17 sixChunkI17 = true := by decide +kernel
theorem sixI33_cfgOk17 : sixCfgI17.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk18 : checkNodeE sixInstI33 400 sixCfgI18 sixChunkI18 = true := by decide +kernel
theorem sixI33_cfgOk18 : sixCfgI18.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk19 : checkNodeE sixInstI33 400 sixCfgI19 sixChunkI19 = true := by decide +kernel
theorem sixI33_cfgOk19 : sixCfgI19.all Tri.ok = true := by decide +kernel
