import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q36.lean — chunks 144..147 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk144 : checkNodeE sixInstI33 400 sixCfgI144 sixChunkI144 = true := by decide +kernel
theorem sixI33_cfgOk144 : sixCfgI144.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk145 : checkNodeE sixInstI33 400 sixCfgI145 sixChunkI145 = true := by decide +kernel
theorem sixI33_cfgOk145 : sixCfgI145.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk146 : checkNodeE sixInstI33 400 sixCfgI146 sixChunkI146 = true := by decide +kernel
theorem sixI33_cfgOk146 : sixCfgI146.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk147 : checkNodeE sixInstI33 400 sixCfgI147 sixChunkI147 = true := by decide +kernel
theorem sixI33_cfgOk147 : sixCfgI147.all Tri.ok = true := by decide +kernel
