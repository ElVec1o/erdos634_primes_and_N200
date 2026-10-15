import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q31.lean — chunks 124..127 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk124 : checkNodeE sixInstI33 400 sixCfgI124 sixChunkI124 = true := by decide +kernel
theorem sixI33_cfgOk124 : sixCfgI124.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk125 : checkNodeE sixInstI33 400 sixCfgI125 sixChunkI125 = true := by decide +kernel
theorem sixI33_cfgOk125 : sixCfgI125.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk126 : checkNodeE sixInstI33 400 sixCfgI126 sixChunkI126 = true := by decide +kernel
theorem sixI33_cfgOk126 : sixCfgI126.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk127 : checkNodeE sixInstI33 400 sixCfgI127 sixChunkI127 = true := by decide +kernel
theorem sixI33_cfgOk127 : sixCfgI127.all Tri.ok = true := by decide +kernel
