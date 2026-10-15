import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q15.lean — chunks 60..63 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk60 : checkNodeE sixInstI33 400 sixCfgI60 sixChunkI60 = true := by decide +kernel
theorem sixI33_cfgOk60 : sixCfgI60.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk61 : checkNodeE sixInstI33 400 sixCfgI61 sixChunkI61 = true := by decide +kernel
theorem sixI33_cfgOk61 : sixCfgI61.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk62 : checkNodeE sixInstI33 400 sixCfgI62 sixChunkI62 = true := by decide +kernel
theorem sixI33_cfgOk62 : sixCfgI62.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk63 : checkNodeE sixInstI33 400 sixCfgI63 sixChunkI63 = true := by decide +kernel
theorem sixI33_cfgOk63 : sixCfgI63.all Tri.ok = true := by decide +kernel
