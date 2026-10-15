import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q24.lean — chunks 96..99 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk96 : checkNodeE sixInstI33 400 sixCfgI96 sixChunkI96 = true := by decide +kernel
theorem sixI33_cfgOk96 : sixCfgI96.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk97 : checkNodeE sixInstI33 400 sixCfgI97 sixChunkI97 = true := by decide +kernel
theorem sixI33_cfgOk97 : sixCfgI97.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk98 : checkNodeE sixInstI33 400 sixCfgI98 sixChunkI98 = true := by decide +kernel
theorem sixI33_cfgOk98 : sixCfgI98.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk99 : checkNodeE sixInstI33 400 sixCfgI99 sixChunkI99 = true := by decide +kernel
theorem sixI33_cfgOk99 : sixCfgI99.all Tri.ok = true := by decide +kernel
