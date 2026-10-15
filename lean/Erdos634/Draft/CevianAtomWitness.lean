/-
Draft/CevianAtomWitness.lean -- the hypotheses of `CevianAtomFull.prop_cevianatom` are satisfiable.

The certified 48-tile atom `A_4` of the member `(1, 2)` (`NSQM.control_A4`: target sides `24, 24, 12`, tile `2, 3, 4`)
satisfies them at `(e, f, m) = (1, 2, 4)`, and the conclusion is a dissection of `Δ_4` (sides `44, 32, 32`) into
`64 + 48 + 64 = 176` copies of the tile.  This reproduces `CVCCevianCut.delta4_cevian_176` by the general-member
theorem; `176 = 2² · 44` is a known tile count, so this is a control and not a new value. not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.CevianAtomFull
import Erdos634.Draft.S5PinWitness
import Erdos634.Draft.CVCCevianCut

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.CevianAtomWitness

open Erdos634.Draft.WideColFull Erdos634.Draft.AddLawFull Erdos634.Draft.CevianAtomFull
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)
open Erdos634.Draft.FDCCevianAtom (hasSides_congr)

/-- **`Δ_4` of the member `(1, 2)` from the certified atom `A_4`.** -/
theorem cevian_instance :
    ∃ D : CongruentDissection 176,
      D.target = DTn 1 2 4 le_rfl (by norm_num) (by norm_num) ∧ D.model = MTn 1 2 le_rfl (by norm_num) := by
  obtain ⟨D, hT, hM, -⟩ := Erdos634.Draft.NSQM.control_A4
  obtain ⟨D', h1, h2⟩ := prop_cevianatom 1 2 4 le_rfl (by norm_num) (by norm_num) D
    (hasSides_congr hT (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num))
    (hasSides_congr hM (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num))
  obtain ⟨E, e1, e2⟩ := Erdos634.Draft.CVCCevianCut.exists_reindex
    (by rw [Erdos634.G3CAtomTilingBridge.tiles_length_eq_48] :
      2 * 4 * (2 * 4) + G3CAtomTiling.tiles.length + 2 * 4 * (2 * 4) = 176) D'
  exact ⟨E, e1.trans h1, e2.trans h2⟩

end Erdos634.Draft.CevianAtomWitness

#print axioms Erdos634.Draft.CevianAtomWitness.cevian_instance
