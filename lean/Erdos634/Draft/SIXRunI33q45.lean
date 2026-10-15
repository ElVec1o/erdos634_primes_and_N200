import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q45.lean — chunks 180..183 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk180 : checkNodeE sixInstI33 400 sixCfgI180 sixChunkI180 = true := by decide +kernel
theorem sixI33_cfgOk180 : sixCfgI180.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk181 : checkNodeE sixInstI33 400 sixCfgI181 sixChunkI181 = true := by decide +kernel
theorem sixI33_cfgOk181 : sixCfgI181.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk182 : checkNodeE sixInstI33 400 sixCfgI182 sixChunkI182 = true := by decide +kernel
theorem sixI33_cfgOk182 : sixCfgI182.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk183 : checkNodeE sixInstI33 400 sixCfgI183 sixChunkI183 = true := by decide +kernel
theorem sixI33_cfgOk183 : sixCfgI183.all Tri.ok = true := by decide +kernel
