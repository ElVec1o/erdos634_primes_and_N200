import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q12.lean — chunks 48..51 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk48 : checkNodeE sixInstI33 400 sixCfgI48 sixChunkI48 = true := by decide +kernel
theorem sixI33_cfgOk48 : sixCfgI48.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk49 : checkNodeE sixInstI33 400 sixCfgI49 sixChunkI49 = true := by decide +kernel
theorem sixI33_cfgOk49 : sixCfgI49.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk50 : checkNodeE sixInstI33 400 sixCfgI50 sixChunkI50 = true := by decide +kernel
theorem sixI33_cfgOk50 : sixCfgI50.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk51 : checkNodeE sixInstI33 400 sixCfgI51 sixChunkI51 = true := by decide +kernel
theorem sixI33_cfgOk51 : sixCfgI51.all Tri.ok = true := by decide +kernel
