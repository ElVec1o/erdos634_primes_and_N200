import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q37.lean — chunks 148..151 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk148 : checkNodeE sixInstI33 400 sixCfgI148 sixChunkI148 = true := by decide +kernel
theorem sixI33_cfgOk148 : sixCfgI148.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk149 : checkNodeE sixInstI33 400 sixCfgI149 sixChunkI149 = true := by decide +kernel
theorem sixI33_cfgOk149 : sixCfgI149.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk150 : checkNodeE sixInstI33 400 sixCfgI150 sixChunkI150 = true := by decide +kernel
theorem sixI33_cfgOk150 : sixCfgI150.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk151 : checkNodeE sixInstI33 400 sixCfgI151 sixChunkI151 = true := by decide +kernel
theorem sixI33_cfgOk151 : sixCfgI151.all Tri.ok = true := by decide +kernel
