-- Draft/SporadicCounts.lean — the certified tilings as TileCount facts: 44, 63, 99, 176.
import Erdos634.Draft.TileCountFamilies
import Erdos634.Tiling44Bridge
import Erdos634.CevianTiling63Bridge
import Erdos634.CevianTiling28Bridge
import Erdos634.Tiling99Bridge
import Erdos634.Draft.Tiling77Bridge
import Erdos634.CollarCongruentM4

namespace Erdos634.Draft.SporadicCounts
open Erdos634.Draft.TileCountFamilies

theorem tc44 : TileCount 44 := by
  have h := Erdos634.Tiling44Bridge.dissection
  have hl : Tiling44.tiles.length = 44 := by decide
  rw [hl] at h; exact ⟨h⟩

theorem tc28 : TileCount 28 := by
  have h := Erdos634.CevianTiling28Bridge.dissection
  have hl : CevianTiling28.tiles.length = 28 := by decide
  rw [hl] at h; exact ⟨h⟩

theorem tc63 : TileCount 63 := by
  have h := Erdos634.CevianTiling63Bridge.dissection
  have hl : CevianTiling63.tiles.length = 63 := by decide
  rw [hl] at h; exact ⟨h⟩

theorem tc99 : TileCount 99 := by
  have h := Erdos634.Tiling99Bridge.dissection
  have hl : Tiling99.tiles.length = 99 := by decide
  rw [hl] at h; exact ⟨h⟩

theorem tc77 : TileCount 77 := by
  have h := Erdos634.Tiling77Bridge.dissection
  have hl : Tiling77.tiles.length = 77 := by decide
  rw [hl] at h; exact ⟨h⟩

theorem tc176 : TileCount 176 := ⟨delta4CongruentDissection⟩

end Erdos634.Draft.SporadicCounts
#print axioms Erdos634.Draft.SporadicCounts.tc44
#print axioms Erdos634.Draft.SporadicCounts.tc63
#print axioms Erdos634.Draft.SporadicCounts.tc176
#print axioms Erdos634.Draft.SporadicCounts.tc28
#print axioms Erdos634.Draft.SporadicCounts.tc77
