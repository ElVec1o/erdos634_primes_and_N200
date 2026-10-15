import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q23.lean — chunks 92..95 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk92 : checkNodeE sixInstI33 400 sixCfgI92 sixChunkI92 = true := by decide +kernel
theorem sixI33_cfgOk92 : sixCfgI92.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk93 : checkNodeE sixInstI33 400 sixCfgI93 sixChunkI93 = true := by decide +kernel
theorem sixI33_cfgOk93 : sixCfgI93.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk94 : checkNodeE sixInstI33 400 sixCfgI94 sixChunkI94 = true := by decide +kernel
theorem sixI33_cfgOk94 : sixCfgI94.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk95 : checkNodeE sixInstI33 400 sixCfgI95 sixChunkI95 = true := by decide +kernel
theorem sixI33_cfgOk95 : sixCfgI95.all Tri.ok = true := by decide +kernel
