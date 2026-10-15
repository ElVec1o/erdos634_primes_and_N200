import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q51.lean — chunks 204..207 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk204 : checkNodeE sixInstI33 400 sixCfgI204 sixChunkI204 = true := by decide +kernel
theorem sixI33_cfgOk204 : sixCfgI204.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk205 : checkNodeE sixInstI33 400 sixCfgI205 sixChunkI205 = true := by decide +kernel
theorem sixI33_cfgOk205 : sixCfgI205.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk206 : checkNodeE sixInstI33 400 sixCfgI206 sixChunkI206 = true := by decide +kernel
theorem sixI33_cfgOk206 : sixCfgI206.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk207 : checkNodeE sixInstI33 400 sixCfgI207 sixChunkI207 = true := by decide +kernel
theorem sixI33_cfgOk207 : sixCfgI207.all Tri.ok = true := by decide +kernel
