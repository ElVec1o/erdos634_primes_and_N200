import Erdos634.CevianTiling63
namespace Erdos634.Draft.CevianTiling63Wrap
open CevianTiling63

theorem wrap_congOK_tiles :
    ∀ t ∈ tiles, congOK t = true := by decide

theorem wrap_insideOK_tiles :
    ∀ t ∈ tiles, insideOK t = true := by decide

example : True := trivial
end Erdos634.Draft.CevianTiling63Wrap
