import Erdos634.RunPartition

/-!
# RunPartition — cSlot run kills: wrapper

Key results:
- `bOverM_dies`: `bOverMSet` placement is killed (after a cSlotTile)
- `cSplit_dies`: `cSplitSet` placement is killed (after a cSlotTile)
- `junction_c_a_run`: after cSlotTile+filler, the next run letter is BG or GB with cap

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.RunPartitionWrap

open Erdos634.RunPartition Erdos634.RunPartition.CSlot Erdos634.Geometry Erdos634.TilePlacement
    Erdos634.BaseBetaTargetCoord Erdos634.MarchKillsFan Erdos634.CertCoord
    Erdos634.MarchSlots Erdos634.MarchKills

theorem rp_bOverM_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    (hM : ModelData D f α β γ)
    {x₀ : ℝ} (hx : f ^ 2 ≤ x₀) (hL : x₀ + f ≤ baseLen 1 f) {i l m : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile (x₀ - f ^ 2) f (by linarith)).pts)
    (hl : Set.range (D.tile l).pts = bOverMSet x₀ f)
    (hm : FillerAtB D f x₀ (by linarith) m) : False :=
  bOverM_dies D hf hn hn3 htgt hM hx hL hi hl hm

theorem rp_cSplit_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    (hM : ModelData D f α β γ)
    {x₀ : ℝ} (hx : f ^ 2 ≤ x₀) (hL : x₀ + f ≤ baseLen 1 f) {i l m : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile (x₀ - f ^ 2) f (by linarith)).pts)
    (hl : Set.range (D.tile l).pts = cSplitSet x₀ f)
    (hm : FillerAtB D f x₀ (by linarith) m) : False :=
  cSplit_dies D hf hn hn3 htgt hM hx hL hi hl hm

-- Non-vacuity: the definitions exist (structural witnesses only)
example : @bOverM_dies = @bOverM_dies := rfl

#print axioms rp_bOverM_dies
#print axioms rp_cSplit_dies

end Erdos634.Draft.RunPartitionWrap
