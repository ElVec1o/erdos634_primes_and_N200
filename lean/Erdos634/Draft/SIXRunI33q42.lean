import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q42.lean — chunks 168..171 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk168 : checkNodeE sixInstI33 400 sixCfgI168 sixChunkI168 = true := by decide +kernel
theorem sixI33_cfgOk168 : sixCfgI168.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk169 : checkNodeE sixInstI33 400 sixCfgI169 sixChunkI169 = true := by decide +kernel
theorem sixI33_cfgOk169 : sixCfgI169.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk170 : checkNodeE sixInstI33 400 sixCfgI170 sixChunkI170 = true := by decide +kernel
theorem sixI33_cfgOk170 : sixCfgI170.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk171 : checkNodeE sixInstI33 400 sixCfgI171 sixChunkI171 = true := by decide +kernel
theorem sixI33_cfgOk171 : sixCfgI171.all Tri.ok = true := by decide +kernel
