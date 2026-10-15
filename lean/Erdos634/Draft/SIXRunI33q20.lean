import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q20.lean — chunks 80..83 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk80 : checkNodeE sixInstI33 400 sixCfgI80 sixChunkI80 = true := by decide +kernel
theorem sixI33_cfgOk80 : sixCfgI80.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk81 : checkNodeE sixInstI33 400 sixCfgI81 sixChunkI81 = true := by decide +kernel
theorem sixI33_cfgOk81 : sixCfgI81.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk82 : checkNodeE sixInstI33 400 sixCfgI82 sixChunkI82 = true := by decide +kernel
theorem sixI33_cfgOk82 : sixCfgI82.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk83 : checkNodeE sixInstI33 400 sixCfgI83 sixChunkI83 = true := by decide +kernel
theorem sixI33_cfgOk83 : sixCfgI83.all Tri.ok = true := by decide +kernel
