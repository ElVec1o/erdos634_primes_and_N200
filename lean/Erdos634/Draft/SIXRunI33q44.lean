import Erdos634.Draft.SIXDataI33

-- Draft/SIXRunI33q44.lean — chunks 176..179 of the N=33 kernel checks (split of SIXRunI33).
set_option maxRecDepth 100000
open Refl

theorem sixI33_chunk176 : checkNodeE sixInstI33 400 sixCfgI176 sixChunkI176 = true := by decide +kernel
theorem sixI33_cfgOk176 : sixCfgI176.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk177 : checkNodeE sixInstI33 400 sixCfgI177 sixChunkI177 = true := by decide +kernel
theorem sixI33_cfgOk177 : sixCfgI177.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk178 : checkNodeE sixInstI33 400 sixCfgI178 sixChunkI178 = true := by decide +kernel
theorem sixI33_cfgOk178 : sixCfgI178.all Tri.ok = true := by decide +kernel
theorem sixI33_chunk179 : checkNodeE sixInstI33 400 sixCfgI179 sixChunkI179 = true := by decide +kernel
theorem sixI33_cfgOk179 : sixCfgI179.all Tri.ok = true := by decide +kernel
