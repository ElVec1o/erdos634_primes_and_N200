import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q09.lean — chunks 36..39 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk36 : checkNodeE sixInstI33 400 sixCfgI36 sixChunkI36 = true := by decide +kernel
theorem sixI33_cfgOk36 : sixCfgI36.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk37 : checkNodeE sixInstI33 400 sixCfgI37 sixChunkI37 = true := by decide +kernel
theorem sixI33_cfgOk37 : sixCfgI37.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk38 : checkNodeE sixInstI33 400 sixCfgI38 sixChunkI38 = true := by decide +kernel
theorem sixI33_cfgOk38 : sixCfgI38.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk39 : checkNodeE sixInstI33 400 sixCfgI39 sixChunkI39 = true := by decide +kernel
theorem sixI33_cfgOk39 : sixCfgI39.all Tri.ok = true := by decide +kernel
