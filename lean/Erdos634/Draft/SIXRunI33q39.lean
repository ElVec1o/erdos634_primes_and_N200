import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q39.lean — chunks 156..159 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk156 : checkNodeE sixInstI33 400 sixCfgI156 sixChunkI156 = true := by decide +kernel
theorem sixI33_cfgOk156 : sixCfgI156.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk157 : checkNodeE sixInstI33 400 sixCfgI157 sixChunkI157 = true := by decide +kernel
theorem sixI33_cfgOk157 : sixCfgI157.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk158 : checkNodeE sixInstI33 400 sixCfgI158 sixChunkI158 = true := by decide +kernel
theorem sixI33_cfgOk158 : sixCfgI158.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk159 : checkNodeE sixInstI33 400 sixCfgI159 sixChunkI159 = true := by decide +kernel
theorem sixI33_cfgOk159 : sixCfgI159.all Tri.ok = true := by decide +kernel
