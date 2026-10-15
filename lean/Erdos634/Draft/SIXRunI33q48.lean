import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q48.lean — chunks 192..195 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk192 : checkNodeE sixInstI33 400 sixCfgI192 sixChunkI192 = true := by decide +kernel
theorem sixI33_cfgOk192 : sixCfgI192.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk193 : checkNodeE sixInstI33 400 sixCfgI193 sixChunkI193 = true := by decide +kernel
theorem sixI33_cfgOk193 : sixCfgI193.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk194 : checkNodeE sixInstI33 400 sixCfgI194 sixChunkI194 = true := by decide +kernel
theorem sixI33_cfgOk194 : sixCfgI194.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk195 : checkNodeE sixInstI33 400 sixCfgI195 sixChunkI195 = true := by decide +kernel
theorem sixI33_cfgOk195 : sixCfgI195.all Tri.ok = true := by decide +kernel
