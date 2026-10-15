import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q19.lean — chunks 76..79 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk76 : checkNodeE sixInstI33 400 sixCfgI76 sixChunkI76 = true := by decide +kernel
theorem sixI33_cfgOk76 : sixCfgI76.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk77 : checkNodeE sixInstI33 400 sixCfgI77 sixChunkI77 = true := by decide +kernel
theorem sixI33_cfgOk77 : sixCfgI77.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk78 : checkNodeE sixInstI33 400 sixCfgI78 sixChunkI78 = true := by decide +kernel
theorem sixI33_cfgOk78 : sixCfgI78.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk79 : checkNodeE sixInstI33 400 sixCfgI79 sixChunkI79 = true := by decide +kernel
theorem sixI33_cfgOk79 : sixCfgI79.all Tri.ok = true := by decide +kernel
