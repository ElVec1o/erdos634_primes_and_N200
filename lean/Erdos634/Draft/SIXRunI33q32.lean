import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q32.lean — chunks 128..131 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk128 : checkNodeE sixInstI33 400 sixCfgI128 sixChunkI128 = true := by decide +kernel
theorem sixI33_cfgOk128 : sixCfgI128.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk129 : checkNodeE sixInstI33 400 sixCfgI129 sixChunkI129 = true := by decide +kernel
theorem sixI33_cfgOk129 : sixCfgI129.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk130 : checkNodeE sixInstI33 400 sixCfgI130 sixChunkI130 = true := by decide +kernel
theorem sixI33_cfgOk130 : sixCfgI130.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk131 : checkNodeE sixInstI33 400 sixCfgI131 sixChunkI131 = true := by decide +kernel
theorem sixI33_cfgOk131 : sixCfgI131.all Tri.ok = true := by decide +kernel
