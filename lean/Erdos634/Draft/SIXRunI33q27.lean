import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q27.lean — chunks 108..111 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk108 : checkNodeE sixInstI33 400 sixCfgI108 sixChunkI108 = true := by decide +kernel
theorem sixI33_cfgOk108 : sixCfgI108.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk109 : checkNodeE sixInstI33 400 sixCfgI109 sixChunkI109 = true := by decide +kernel
theorem sixI33_cfgOk109 : sixCfgI109.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk110 : checkNodeE sixInstI33 400 sixCfgI110 sixChunkI110 = true := by decide +kernel
theorem sixI33_cfgOk110 : sixCfgI110.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk111 : checkNodeE sixInstI33 400 sixCfgI111 sixChunkI111 = true := by decide +kernel
theorem sixI33_cfgOk111 : sixCfgI111.all Tri.ok = true := by decide +kernel
