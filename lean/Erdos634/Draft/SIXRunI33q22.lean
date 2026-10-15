import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q22.lean — chunks 88..91 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk88 : checkNodeE sixInstI33 400 sixCfgI88 sixChunkI88 = true := by decide +kernel
theorem sixI33_cfgOk88 : sixCfgI88.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk89 : checkNodeE sixInstI33 400 sixCfgI89 sixChunkI89 = true := by decide +kernel
theorem sixI33_cfgOk89 : sixCfgI89.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk90 : checkNodeE sixInstI33 400 sixCfgI90 sixChunkI90 = true := by decide +kernel
theorem sixI33_cfgOk90 : sixCfgI90.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk91 : checkNodeE sixInstI33 400 sixCfgI91 sixChunkI91 = true := by decide +kernel
theorem sixI33_cfgOk91 : sixCfgI91.all Tri.ok = true := by decide +kernel
