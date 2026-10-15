import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q29.lean — chunks 116..119 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk116 : checkNodeE sixInstI33 400 sixCfgI116 sixChunkI116 = true := by decide +kernel
theorem sixI33_cfgOk116 : sixCfgI116.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk117 : checkNodeE sixInstI33 400 sixCfgI117 sixChunkI117 = true := by decide +kernel
theorem sixI33_cfgOk117 : sixCfgI117.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk118 : checkNodeE sixInstI33 400 sixCfgI118 sixChunkI118 = true := by decide +kernel
theorem sixI33_cfgOk118 : sixCfgI118.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk119 : checkNodeE sixInstI33 400 sixCfgI119 sixChunkI119 = true := by decide +kernel
theorem sixI33_cfgOk119 : sixCfgI119.all Tri.ok = true := by decide +kernel
