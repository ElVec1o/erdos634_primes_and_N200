import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q06.lean — chunks 24..27 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk24 : checkNodeE sixInstI33 400 sixCfgI24 sixChunkI24 = true := by decide +kernel
theorem sixI33_cfgOk24 : sixCfgI24.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk25 : checkNodeE sixInstI33 400 sixCfgI25 sixChunkI25 = true := by decide +kernel
theorem sixI33_cfgOk25 : sixCfgI25.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk26 : checkNodeE sixInstI33 400 sixCfgI26 sixChunkI26 = true := by decide +kernel
theorem sixI33_cfgOk26 : sixCfgI26.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk27 : checkNodeE sixInstI33 400 sixCfgI27 sixChunkI27 = true := by decide +kernel
theorem sixI33_cfgOk27 : sixCfgI27.all Tri.ok = true := by decide +kernel
