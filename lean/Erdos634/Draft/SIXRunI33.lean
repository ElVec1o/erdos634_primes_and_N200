import Erdos634.Draft.SIXDataI33
import Erdos634.Draft.SIXRunI33q00
import Erdos634.Draft.SIXRunI33q01
import Erdos634.Draft.SIXRunI33q02
import Erdos634.Draft.SIXRunI33q03
import Erdos634.Draft.SIXRunI33q04
import Erdos634.Draft.SIXRunI33q05
import Erdos634.Draft.SIXRunI33q06
import Erdos634.Draft.SIXRunI33q07
import Erdos634.Draft.SIXRunI33q08
import Erdos634.Draft.SIXRunI33q09
import Erdos634.Draft.SIXRunI33q10
import Erdos634.Draft.SIXRunI33q11
import Erdos634.Draft.SIXRunI33q12
import Erdos634.Draft.SIXRunI33q13
import Erdos634.Draft.SIXRunI33q14
import Erdos634.Draft.SIXRunI33q15
import Erdos634.Draft.SIXRunI33q16
import Erdos634.Draft.SIXRunI33q17
import Erdos634.Draft.SIXRunI33q18
import Erdos634.Draft.SIXRunI33q19
import Erdos634.Draft.SIXRunI33q20
import Erdos634.Draft.SIXRunI33q21
import Erdos634.Draft.SIXRunI33q22
import Erdos634.Draft.SIXRunI33q23
import Erdos634.Draft.SIXRunI33q24
import Erdos634.Draft.SIXRunI33q25
import Erdos634.Draft.SIXRunI33q26
import Erdos634.Draft.SIXRunI33q27
import Erdos634.Draft.SIXRunI33q28
import Erdos634.Draft.SIXRunI33q29
import Erdos634.Draft.SIXRunI33q30
import Erdos634.Draft.SIXRunI33q31
import Erdos634.Draft.SIXRunI33q32
import Erdos634.Draft.SIXRunI33q33
import Erdos634.Draft.SIXRunI33q34
import Erdos634.Draft.SIXRunI33q35
import Erdos634.Draft.SIXRunI33q36
import Erdos634.Draft.SIXRunI33q37
import Erdos634.Draft.SIXRunI33q38
import Erdos634.Draft.SIXRunI33q39
import Erdos634.Draft.SIXRunI33q40
import Erdos634.Draft.SIXRunI33q41
import Erdos634.Draft.SIXRunI33q42
import Erdos634.Draft.SIXRunI33q43
import Erdos634.Draft.SIXRunI33q44
import Erdos634.Draft.SIXRunI33q45
import Erdos634.Draft.SIXRunI33q46
import Erdos634.Draft.SIXRunI33q47
import Erdos634.Draft.SIXRunI33q48
import Erdos634.Draft.SIXRunI33q49
import Erdos634.Draft.SIXRunI33q50
import Erdos634.Draft.SIXRunI33q51
import Erdos634.Draft.SIXRunI33q52
import Erdos634.Draft.SIXRunI33q53

/-! Draft/SIXRunI33.lean.  Top-level kernel checks (`decide +kernel`) of the SIXDataI33 certificate; the 213 chunk checks live in SIXRunI33q00..q53 (split for memory). -/

set_option maxRecDepth 100000
open Refl

theorem sixI33_top : sixInstI33.checkAllR sixKnownI33 400 sixTreeI33 = true := by decide +kernel
theorem sixI33_ok : sixInstI33.ok = true := by decide +kernel
