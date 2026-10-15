import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q40.lean — chunks 160..163 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk160 : checkNodeE sixInstI33 400 sixCfgI160 sixChunkI160 = true := by decide +kernel
theorem sixI33_cfgOk160 : sixCfgI160.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk161 : checkNodeE sixInstI33 400 sixCfgI161 sixChunkI161 = true := by decide +kernel
theorem sixI33_cfgOk161 : sixCfgI161.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk162 : checkNodeE sixInstI33 400 sixCfgI162 sixChunkI162 = true := by decide +kernel
theorem sixI33_cfgOk162 : sixCfgI162.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk163 : checkNodeE sixInstI33 400 sixCfgI163 sixChunkI163 = true := by decide +kernel
theorem sixI33_cfgOk163 : sixCfgI163.all Tri.ok = true := by decide +kernel
