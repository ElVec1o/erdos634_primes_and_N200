import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q21.lean — chunks 84..87 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk84 : checkNodeE sixInstI33 400 sixCfgI84 sixChunkI84 = true := by decide +kernel
theorem sixI33_cfgOk84 : sixCfgI84.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk85 : checkNodeE sixInstI33 400 sixCfgI85 sixChunkI85 = true := by decide +kernel
theorem sixI33_cfgOk85 : sixCfgI85.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk86 : checkNodeE sixInstI33 400 sixCfgI86 sixChunkI86 = true := by decide +kernel
theorem sixI33_cfgOk86 : sixCfgI86.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk87 : checkNodeE sixInstI33 400 sixCfgI87 sixChunkI87 = true := by decide +kernel
theorem sixI33_cfgOk87 : sixCfgI87.all Tri.ok = true := by decide +kernel
