import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q43.lean — chunks 172..175 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk172 : checkNodeE sixInstI33 400 sixCfgI172 sixChunkI172 = true := by decide +kernel
theorem sixI33_cfgOk172 : sixCfgI172.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk173 : checkNodeE sixInstI33 400 sixCfgI173 sixChunkI173 = true := by decide +kernel
theorem sixI33_cfgOk173 : sixCfgI173.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk174 : checkNodeE sixInstI33 400 sixCfgI174 sixChunkI174 = true := by decide +kernel
theorem sixI33_cfgOk174 : sixCfgI174.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk175 : checkNodeE sixInstI33 400 sixCfgI175 sixChunkI175 = true := by decide +kernel
theorem sixI33_cfgOk175 : sixCfgI175.all Tri.ok = true := by decide +kernel
