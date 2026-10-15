import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q47.lean — chunks 188..191 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk188 : checkNodeE sixInstI33 400 sixCfgI188 sixChunkI188 = true := by decide +kernel
theorem sixI33_cfgOk188 : sixCfgI188.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk189 : checkNodeE sixInstI33 400 sixCfgI189 sixChunkI189 = true := by decide +kernel
theorem sixI33_cfgOk189 : sixCfgI189.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk190 : checkNodeE sixInstI33 400 sixCfgI190 sixChunkI190 = true := by decide +kernel
theorem sixI33_cfgOk190 : sixCfgI190.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk191 : checkNodeE sixInstI33 400 sixCfgI191 sixChunkI191 = true := by decide +kernel
theorem sixI33_cfgOk191 : sixCfgI191.all Tri.ok = true := by decide +kernel
