import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q18.lean — chunks 72..75 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk72 : checkNodeE sixInstI33 400 sixCfgI72 sixChunkI72 = true := by decide +kernel
theorem sixI33_cfgOk72 : sixCfgI72.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk73 : checkNodeE sixInstI33 400 sixCfgI73 sixChunkI73 = true := by decide +kernel
theorem sixI33_cfgOk73 : sixCfgI73.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk74 : checkNodeE sixInstI33 400 sixCfgI74 sixChunkI74 = true := by decide +kernel
theorem sixI33_cfgOk74 : sixCfgI74.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk75 : checkNodeE sixInstI33 400 sixCfgI75 sixChunkI75 = true := by decide +kernel
theorem sixI33_cfgOk75 : sixCfgI75.all Tri.ok = true := by decide +kernel
