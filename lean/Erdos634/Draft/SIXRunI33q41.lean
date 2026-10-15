import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q41.lean — chunks 164..167 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk164 : checkNodeE sixInstI33 400 sixCfgI164 sixChunkI164 = true := by decide +kernel
theorem sixI33_cfgOk164 : sixCfgI164.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk165 : checkNodeE sixInstI33 400 sixCfgI165 sixChunkI165 = true := by decide +kernel
theorem sixI33_cfgOk165 : sixCfgI165.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk166 : checkNodeE sixInstI33 400 sixCfgI166 sixChunkI166 = true := by decide +kernel
theorem sixI33_cfgOk166 : sixCfgI166.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk167 : checkNodeE sixInstI33 400 sixCfgI167 sixChunkI167 = true := by decide +kernel
theorem sixI33_cfgOk167 : sixCfgI167.all Tri.ok = true := by decide +kernel
