import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q01.lean — chunks 4..7 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk4 : checkNodeE sixInstI33 400 sixCfgI4 sixChunkI4 = true := by decide +kernel
theorem sixI33_cfgOk4 : sixCfgI4.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk5 : checkNodeE sixInstI33 400 sixCfgI5 sixChunkI5 = true := by decide +kernel
theorem sixI33_cfgOk5 : sixCfgI5.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk6 : checkNodeE sixInstI33 400 sixCfgI6 sixChunkI6 = true := by decide +kernel
theorem sixI33_cfgOk6 : sixCfgI6.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk7 : checkNodeE sixInstI33 400 sixCfgI7 sixChunkI7 = true := by decide +kernel
theorem sixI33_cfgOk7 : sixCfgI7.all Tri.ok = true := by decide +kernel
