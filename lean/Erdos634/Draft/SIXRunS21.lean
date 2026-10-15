import Erdos634.Draft.SIXDataS21

/-! Draft/SIXRunS21.lean.  Kernel checks (`decide +kernel`, no `native_decide`) of the
    `SIXDataS21` certificate (51 chunks + top tree). -/

set_option maxRecDepth 100000
open Refl

theorem sixS21_top : sixInstS21.checkAllR sixKnownS21 400 sixTreeS21 = true := by decide +kernel
theorem sixS21_ok : sixInstS21.ok = true := by decide +kernel
theorem sixS21_chunk0 : checkNodeE sixInstS21 400 sixCfgS0 sixChunkS0 = true := by decide +kernel
theorem sixS21_cfgOk0 : sixCfgS0.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk1 : checkNodeE sixInstS21 400 sixCfgS1 sixChunkS1 = true := by decide +kernel
theorem sixS21_cfgOk1 : sixCfgS1.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk2 : checkNodeE sixInstS21 400 sixCfgS2 sixChunkS2 = true := by decide +kernel
theorem sixS21_cfgOk2 : sixCfgS2.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk3 : checkNodeE sixInstS21 400 sixCfgS3 sixChunkS3 = true := by decide +kernel
theorem sixS21_cfgOk3 : sixCfgS3.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk4 : checkNodeE sixInstS21 400 sixCfgS4 sixChunkS4 = true := by decide +kernel
theorem sixS21_cfgOk4 : sixCfgS4.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk5 : checkNodeE sixInstS21 400 sixCfgS5 sixChunkS5 = true := by decide +kernel
theorem sixS21_cfgOk5 : sixCfgS5.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk6 : checkNodeE sixInstS21 400 sixCfgS6 sixChunkS6 = true := by decide +kernel
theorem sixS21_cfgOk6 : sixCfgS6.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk7 : checkNodeE sixInstS21 400 sixCfgS7 sixChunkS7 = true := by decide +kernel
theorem sixS21_cfgOk7 : sixCfgS7.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk8 : checkNodeE sixInstS21 400 sixCfgS8 sixChunkS8 = true := by decide +kernel
theorem sixS21_cfgOk8 : sixCfgS8.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk9 : checkNodeE sixInstS21 400 sixCfgS9 sixChunkS9 = true := by decide +kernel
theorem sixS21_cfgOk9 : sixCfgS9.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk10 : checkNodeE sixInstS21 400 sixCfgS10 sixChunkS10 = true := by decide +kernel
theorem sixS21_cfgOk10 : sixCfgS10.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk11 : checkNodeE sixInstS21 400 sixCfgS11 sixChunkS11 = true := by decide +kernel
theorem sixS21_cfgOk11 : sixCfgS11.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk12 : checkNodeE sixInstS21 400 sixCfgS12 sixChunkS12 = true := by decide +kernel
theorem sixS21_cfgOk12 : sixCfgS12.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk13 : checkNodeE sixInstS21 400 sixCfgS13 sixChunkS13 = true := by decide +kernel
theorem sixS21_cfgOk13 : sixCfgS13.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk14 : checkNodeE sixInstS21 400 sixCfgS14 sixChunkS14 = true := by decide +kernel
theorem sixS21_cfgOk14 : sixCfgS14.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk15 : checkNodeE sixInstS21 400 sixCfgS15 sixChunkS15 = true := by decide +kernel
theorem sixS21_cfgOk15 : sixCfgS15.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk16 : checkNodeE sixInstS21 400 sixCfgS16 sixChunkS16 = true := by decide +kernel
theorem sixS21_cfgOk16 : sixCfgS16.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk17 : checkNodeE sixInstS21 400 sixCfgS17 sixChunkS17 = true := by decide +kernel
theorem sixS21_cfgOk17 : sixCfgS17.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk18 : checkNodeE sixInstS21 400 sixCfgS18 sixChunkS18 = true := by decide +kernel
theorem sixS21_cfgOk18 : sixCfgS18.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk19 : checkNodeE sixInstS21 400 sixCfgS19 sixChunkS19 = true := by decide +kernel
theorem sixS21_cfgOk19 : sixCfgS19.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk20 : checkNodeE sixInstS21 400 sixCfgS20 sixChunkS20 = true := by decide +kernel
theorem sixS21_cfgOk20 : sixCfgS20.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk21 : checkNodeE sixInstS21 400 sixCfgS21 sixChunkS21 = true := by decide +kernel
theorem sixS21_cfgOk21 : sixCfgS21.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk22 : checkNodeE sixInstS21 400 sixCfgS22 sixChunkS22 = true := by decide +kernel
theorem sixS21_cfgOk22 : sixCfgS22.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk23 : checkNodeE sixInstS21 400 sixCfgS23 sixChunkS23 = true := by decide +kernel
theorem sixS21_cfgOk23 : sixCfgS23.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk24 : checkNodeE sixInstS21 400 sixCfgS24 sixChunkS24 = true := by decide +kernel
theorem sixS21_cfgOk24 : sixCfgS24.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk25 : checkNodeE sixInstS21 400 sixCfgS25 sixChunkS25 = true := by decide +kernel
theorem sixS21_cfgOk25 : sixCfgS25.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk26 : checkNodeE sixInstS21 400 sixCfgS26 sixChunkS26 = true := by decide +kernel
theorem sixS21_cfgOk26 : sixCfgS26.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk27 : checkNodeE sixInstS21 400 sixCfgS27 sixChunkS27 = true := by decide +kernel
theorem sixS21_cfgOk27 : sixCfgS27.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk28 : checkNodeE sixInstS21 400 sixCfgS28 sixChunkS28 = true := by decide +kernel
theorem sixS21_cfgOk28 : sixCfgS28.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk29 : checkNodeE sixInstS21 400 sixCfgS29 sixChunkS29 = true := by decide +kernel
theorem sixS21_cfgOk29 : sixCfgS29.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk30 : checkNodeE sixInstS21 400 sixCfgS30 sixChunkS30 = true := by decide +kernel
theorem sixS21_cfgOk30 : sixCfgS30.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk31 : checkNodeE sixInstS21 400 sixCfgS31 sixChunkS31 = true := by decide +kernel
theorem sixS21_cfgOk31 : sixCfgS31.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk32 : checkNodeE sixInstS21 400 sixCfgS32 sixChunkS32 = true := by decide +kernel
theorem sixS21_cfgOk32 : sixCfgS32.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk33 : checkNodeE sixInstS21 400 sixCfgS33 sixChunkS33 = true := by decide +kernel
theorem sixS21_cfgOk33 : sixCfgS33.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk34 : checkNodeE sixInstS21 400 sixCfgS34 sixChunkS34 = true := by decide +kernel
theorem sixS21_cfgOk34 : sixCfgS34.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk35 : checkNodeE sixInstS21 400 sixCfgS35 sixChunkS35 = true := by decide +kernel
theorem sixS21_cfgOk35 : sixCfgS35.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk36 : checkNodeE sixInstS21 400 sixCfgS36 sixChunkS36 = true := by decide +kernel
theorem sixS21_cfgOk36 : sixCfgS36.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk37 : checkNodeE sixInstS21 400 sixCfgS37 sixChunkS37 = true := by decide +kernel
theorem sixS21_cfgOk37 : sixCfgS37.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk38 : checkNodeE sixInstS21 400 sixCfgS38 sixChunkS38 = true := by decide +kernel
theorem sixS21_cfgOk38 : sixCfgS38.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk39 : checkNodeE sixInstS21 400 sixCfgS39 sixChunkS39 = true := by decide +kernel
theorem sixS21_cfgOk39 : sixCfgS39.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk40 : checkNodeE sixInstS21 400 sixCfgS40 sixChunkS40 = true := by decide +kernel
theorem sixS21_cfgOk40 : sixCfgS40.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk41 : checkNodeE sixInstS21 400 sixCfgS41 sixChunkS41 = true := by decide +kernel
theorem sixS21_cfgOk41 : sixCfgS41.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk42 : checkNodeE sixInstS21 400 sixCfgS42 sixChunkS42 = true := by decide +kernel
theorem sixS21_cfgOk42 : sixCfgS42.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk43 : checkNodeE sixInstS21 400 sixCfgS43 sixChunkS43 = true := by decide +kernel
theorem sixS21_cfgOk43 : sixCfgS43.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk44 : checkNodeE sixInstS21 400 sixCfgS44 sixChunkS44 = true := by decide +kernel
theorem sixS21_cfgOk44 : sixCfgS44.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk45 : checkNodeE sixInstS21 400 sixCfgS45 sixChunkS45 = true := by decide +kernel
theorem sixS21_cfgOk45 : sixCfgS45.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk46 : checkNodeE sixInstS21 400 sixCfgS46 sixChunkS46 = true := by decide +kernel
theorem sixS21_cfgOk46 : sixCfgS46.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk47 : checkNodeE sixInstS21 400 sixCfgS47 sixChunkS47 = true := by decide +kernel
theorem sixS21_cfgOk47 : sixCfgS47.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk48 : checkNodeE sixInstS21 400 sixCfgS48 sixChunkS48 = true := by decide +kernel
theorem sixS21_cfgOk48 : sixCfgS48.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk49 : checkNodeE sixInstS21 400 sixCfgS49 sixChunkS49 = true := by decide +kernel
theorem sixS21_cfgOk49 : sixCfgS49.all Tri.ok = true := by decide +kernel
theorem sixS21_chunk50 : checkNodeE sixInstS21 400 sixCfgS50 sixChunkS50 = true := by decide +kernel
theorem sixS21_cfgOk50 : sixCfgS50.all Tri.ok = true := by decide +kernel
