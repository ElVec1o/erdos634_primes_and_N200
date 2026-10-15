import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q49.lean — chunks 196..199 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk196 : checkNodeE sixInstI33 400 sixCfgI196 sixChunkI196 = true := by decide +kernel
theorem sixI33_cfgOk196 : sixCfgI196.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk197 : checkNodeE sixInstI33 400 sixCfgI197 sixChunkI197 = true := by decide +kernel
theorem sixI33_cfgOk197 : sixCfgI197.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk198 : checkNodeE sixInstI33 400 sixCfgI198 sixChunkI198 = true := by decide +kernel
theorem sixI33_cfgOk198 : sixCfgI198.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk199 : checkNodeE sixInstI33 400 sixCfgI199 sixChunkI199 = true := by decide +kernel
theorem sixI33_cfgOk199 : sixCfgI199.all Tri.ok = true := by decide +kernel
