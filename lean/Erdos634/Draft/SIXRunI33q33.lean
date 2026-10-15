import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q33.lean — chunks 132..135 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk132 : checkNodeE sixInstI33 400 sixCfgI132 sixChunkI132 = true := by decide +kernel
theorem sixI33_cfgOk132 : sixCfgI132.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk133 : checkNodeE sixInstI33 400 sixCfgI133 sixChunkI133 = true := by decide +kernel
theorem sixI33_cfgOk133 : sixCfgI133.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk134 : checkNodeE sixInstI33 400 sixCfgI134 sixChunkI134 = true := by decide +kernel
theorem sixI33_cfgOk134 : sixCfgI134.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk135 : checkNodeE sixInstI33 400 sixCfgI135 sixChunkI135 = true := by decide +kernel
theorem sixI33_cfgOk135 : sixCfgI135.all Tri.ok = true := by decide +kernel
