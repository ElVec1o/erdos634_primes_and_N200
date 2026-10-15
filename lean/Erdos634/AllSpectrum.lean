/-
AllSpectrum.lean -- aggregate of the modules whose import closure contains a search certificate (`Refl.M*`): the
exclusions of individual composite values of `N` and the statements about the tile counts up to 200 that are
assembled from them.

Kept out of `Erdos634.All` for memory: together they loaded 9.5 GB of oleans in one `lean` process.  `All` does not
import this file and this file does not import `All`.  Build `Erdos634.All`, `Erdos634.AllSpectrum` and
`Erdos634.AllThreshold` one at a time (and the `AllCert*` aggregates for files that use the large certificates).
If this aggregate itself approaches 8.5 GB, split it by certificate family.
-/
import Erdos634.Draft.T30LPi3Close
import Erdos634.Refl.ME15Sound
import Erdos634.Refl.MS60Sound
import Erdos634.Refl.MS76Sound
import Erdos634.Refl.ME56Sound
import Erdos634.Refl.MC56Sound
import Erdos634.Refl.ME60Sound
import Erdos634.Draft.GapE120N
import Erdos634.Draft.N566076
import Erdos634.Draft.T30Cert
import Erdos634.Refl.MB70Sound
import Erdos634.Draft.N70
import Erdos634.Draft.SpectrumLe91
import Erdos634.Draft.SpectrumGap200
import Erdos634.Draft.N92
import Erdos634.Draft.Frontier34Wrap
import Erdos634.Draft.ChainIso
import Erdos634.Draft.N140
import Erdos634.Draft.Dichotomy23
import Erdos634.Draft.NotUniform104
import Erdos634.Draft.N172
import Erdos634.Draft.N124
import Erdos634.Draft.E2StripInstances
import Erdos634.Refl.MS1N188Sound
import Erdos634.Refl.MC188Sound
import Erdos634.Draft.N188
import Erdos634.Draft.Spectrum200b
import Erdos634.Draft.E60Cert
import Erdos634.Draft.Eq105
import Erdos634.Draft.E60Reduce
import Erdos634.Refl.MS135Sound
import Erdos634.Refl.MS132Sound
import Erdos634.Draft.E60N168
import Erdos634.Draft.E60N198
import Erdos634.Draft.N168
import Erdos634.Draft.N198
import Erdos634.Draft.Spectrum200c
import Erdos634.Draft.Spectrum200d
import Erdos634.Draft.E60Irr
import Erdos634.Draft.E60Parity
import Erdos634.Draft.E60Apps
import Erdos634.Refl.MS171Sound
import Erdos634.Refl.MG171Sound
import Erdos634.Draft.N171
import Erdos634.Draft.Spectrum200e
import Erdos634.Draft.E60N120
import Erdos634.Draft.ChainGapA
import Erdos634.Draft.N120Arith
import Erdos634.Refl.MF120Sound
import Erdos634.Draft.N120
import Erdos634.Draft.Spectrum200f
import Erdos634.Refl.MF105ASound
import Erdos634.Refl.MF105BSound
import Erdos634.Draft.N105
import Erdos634.Draft.Spectrum200g
import Erdos634.Refl.MG132Sound
import Erdos634.Refl.MG135Sound
import Erdos634.Draft.GPairs132
import Erdos634.Draft.TwoPrime
import Erdos634.Draft.Sqfree3Mod8Arith
import Erdos634.Draft.Sqfree3Mod8
import Erdos634.Draft.AllN3Cond
import Erdos634.Draft.AllN3Check1
import Erdos634.Draft.AllN3Check2
import Erdos634.Draft.AllN3Check3
import Erdos634.Draft.E120Irr
import Erdos634.Draft.E120Witness
import Erdos634.Draft.N135Red
import Erdos634.Draft.OpenReductions
import Erdos634.Draft.OpenReductionsNsq
import Erdos634.Draft.OpenReductions143
import Erdos634.Draft.Spectrum200Cond
import Erdos634.Refl.MG156Sound
import Erdos634.Draft.GPairs156
import Erdos634.Draft.N156G
import Erdos634.Refl.MS156Sound
import Erdos634.Draft.N156Red
import Erdos634.Draft.Spectrum200Cond2
import Erdos634.Draft.N143
import Erdos634.Draft.F2Row357
import Erdos634.Draft.Sqfree7Mod8
import Erdos634.Draft.Sqfree5Mod8
import Erdos634.Draft.QPExact
import Erdos634.Draft.Spectrum200Excl
