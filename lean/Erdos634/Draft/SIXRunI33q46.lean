import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q46.lean — chunks 184..187 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk184 : checkNodeE sixInstI33 400 sixCfgI184 sixChunkI184 = true := by decide +kernel
theorem sixI33_cfgOk184 : sixCfgI184.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk185 : checkNodeE sixInstI33 400 sixCfgI185 sixChunkI185 = true := by decide +kernel
theorem sixI33_cfgOk185 : sixCfgI185.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk186 : checkNodeE sixInstI33 400 sixCfgI186 sixChunkI186 = true := by decide +kernel
theorem sixI33_cfgOk186 : sixCfgI186.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk187 : checkNodeE sixInstI33 400 sixCfgI187 sixChunkI187 = true := by decide +kernel
theorem sixI33_cfgOk187 : sixCfgI187.all Tri.ok = true := by decide +kernel
