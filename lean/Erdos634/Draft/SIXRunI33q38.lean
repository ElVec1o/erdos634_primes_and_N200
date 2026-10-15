import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q38.lean — chunks 152..155 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk152 : checkNodeE sixInstI33 400 sixCfgI152 sixChunkI152 = true := by decide +kernel
theorem sixI33_cfgOk152 : sixCfgI152.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk153 : checkNodeE sixInstI33 400 sixCfgI153 sixChunkI153 = true := by decide +kernel
theorem sixI33_cfgOk153 : sixCfgI153.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk154 : checkNodeE sixInstI33 400 sixCfgI154 sixChunkI154 = true := by decide +kernel
theorem sixI33_cfgOk154 : sixCfgI154.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk155 : checkNodeE sixInstI33 400 sixCfgI155 sixChunkI155 = true := by decide +kernel
theorem sixI33_cfgOk155 : sixCfgI155.all Tri.ok = true := by decide +kernel
