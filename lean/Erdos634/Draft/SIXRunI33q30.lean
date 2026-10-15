import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q30.lean — chunks 120..123 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk120 : checkNodeE sixInstI33 400 sixCfgI120 sixChunkI120 = true := by decide +kernel
theorem sixI33_cfgOk120 : sixCfgI120.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk121 : checkNodeE sixInstI33 400 sixCfgI121 sixChunkI121 = true := by decide +kernel
theorem sixI33_cfgOk121 : sixCfgI121.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk122 : checkNodeE sixInstI33 400 sixCfgI122 sixChunkI122 = true := by decide +kernel
theorem sixI33_cfgOk122 : sixCfgI122.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk123 : checkNodeE sixInstI33 400 sixCfgI123 sixChunkI123 = true := by decide +kernel
theorem sixI33_cfgOk123 : sixCfgI123.all Tri.ok = true := by decide +kernel
