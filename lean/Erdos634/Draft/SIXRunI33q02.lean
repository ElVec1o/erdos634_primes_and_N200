import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q02.lean — chunks 8..11 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk8 : checkNodeE sixInstI33 400 sixCfgI8 sixChunkI8 = true := by decide +kernel
theorem sixI33_cfgOk8 : sixCfgI8.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk9 : checkNodeE sixInstI33 400 sixCfgI9 sixChunkI9 = true := by decide +kernel
theorem sixI33_cfgOk9 : sixCfgI9.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk10 : checkNodeE sixInstI33 400 sixCfgI10 sixChunkI10 = true := by decide +kernel
theorem sixI33_cfgOk10 : sixCfgI10.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk11 : checkNodeE sixInstI33 400 sixCfgI11 sixChunkI11 = true := by decide +kernel
theorem sixI33_cfgOk11 : sixCfgI11.all Tri.ok = true := by decide +kernel
