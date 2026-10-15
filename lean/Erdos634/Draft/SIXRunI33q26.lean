import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q26.lean — chunks 104..107 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk104 : checkNodeE sixInstI33 400 sixCfgI104 sixChunkI104 = true := by decide +kernel
theorem sixI33_cfgOk104 : sixCfgI104.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk105 : checkNodeE sixInstI33 400 sixCfgI105 sixChunkI105 = true := by decide +kernel
theorem sixI33_cfgOk105 : sixCfgI105.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk106 : checkNodeE sixInstI33 400 sixCfgI106 sixChunkI106 = true := by decide +kernel
theorem sixI33_cfgOk106 : sixCfgI106.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk107 : checkNodeE sixInstI33 400 sixCfgI107 sixChunkI107 = true := by decide +kernel
theorem sixI33_cfgOk107 : sixCfgI107.all Tri.ok = true := by decide +kernel
