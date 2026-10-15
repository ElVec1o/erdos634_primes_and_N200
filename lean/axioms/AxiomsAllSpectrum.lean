/-
Axioms of the declarations of the Lean map table of the paper (and of the tilings with 330, 897 and 990
tiles) whose module lies in the import closure of `Erdos634.AllSpectrum`. After building `Erdos634.AllSpectrum`, run
from the directory `lean/`:
  lake env lean axioms/AxiomsAllSpectrum.lean
Every line of the output should read: depends on axioms: [propext, Classical.choice, Quot.sound].
-/
import Erdos634.Draft.E120Irr
import Erdos634.Draft.E60Irr
import Erdos634.Draft.N135Red
import Erdos634.Draft.N143
import Erdos634.Draft.QPExact
import Erdos634.Draft.Spectrum200Excl
import Erdos634.Draft.Spectrum200g
import Erdos634.Draft.Sqfree3Mod8
import Erdos634.Draft.Sqfree7Mod8
import Erdos634.Draft.TwoPrime

#print axioms Erdos634.Draft.Spectrum200g.tileCount_iff_le_200g
#print axioms Erdos634.Draft.Spectrum200g.tileCount_iff_le_131
#print axioms Erdos634.Draft.N143.tileCount_143
#print axioms Erdos634.Draft.Spectrum200Excl.tileCount_iff_le_200_of_excl
#print axioms Erdos634.Draft.E60Irr.sixty_commensurable
#print axioms Erdos634.Draft.E120Irr.twoPiThree_commensurable
#print axioms Erdos634.Draft.E60Irr.e60Pair_of_not_isSquare
#print axioms Erdos634.Draft.E120Irr.e120Pair_of_not_isSquare
#print axioms Erdos634.Draft.N143.dissection_143_unit
#print axioms Erdos634.Draft.N135.tileCount_135_iff
#print axioms Erdos634.Draft.TwoPrime.two_prime_tileCount_iff
#print axioms Erdos634.Draft.Sqfree3Mod8.not_tile_sqfree_3mod8
#print axioms Erdos634.Draft.Sqfree7Mod8.tile_sqfree_7mod8_form
#print axioms Erdos634.Draft.Sqfree7Mod8.sector_below_455
#print axioms Erdos634.Draft.QPExact.tile_sqfree_5mod8_explicit
#print axioms Erdos634.Draft.QPExact.sector5_below_517
