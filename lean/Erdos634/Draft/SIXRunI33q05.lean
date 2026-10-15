import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q05.lean — chunks 20..23 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk20 : checkNodeE sixInstI33 400 sixCfgI20 sixChunkI20 = true := by decide +kernel
theorem sixI33_cfgOk20 : sixCfgI20.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk21 : checkNodeE sixInstI33 400 sixCfgI21 sixChunkI21 = true := by decide +kernel
theorem sixI33_cfgOk21 : sixCfgI21.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk22 : checkNodeE sixInstI33 400 sixCfgI22 sixChunkI22 = true := by decide +kernel
theorem sixI33_cfgOk22 : sixCfgI22.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk23 : checkNodeE sixInstI33 400 sixCfgI23 sixChunkI23 = true := by decide +kernel
theorem sixI33_cfgOk23 : sixCfgI23.all Tri.ok = true := by decide +kernel
