import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q25.lean — chunks 100..103 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk100 : checkNodeE sixInstI33 400 sixCfgI100 sixChunkI100 = true := by decide +kernel
theorem sixI33_cfgOk100 : sixCfgI100.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk101 : checkNodeE sixInstI33 400 sixCfgI101 sixChunkI101 = true := by decide +kernel
theorem sixI33_cfgOk101 : sixCfgI101.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk102 : checkNodeE sixInstI33 400 sixCfgI102 sixChunkI102 = true := by decide +kernel
theorem sixI33_cfgOk102 : sixCfgI102.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk103 : checkNodeE sixInstI33 400 sixCfgI103 sixChunkI103 = true := by decide +kernel
theorem sixI33_cfgOk103 : sixCfgI103.all Tri.ok = true := by decide +kernel
