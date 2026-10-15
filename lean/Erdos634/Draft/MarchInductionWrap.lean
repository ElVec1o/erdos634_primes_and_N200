import Erdos634.MarchInduction

/-!
# MarchInduction — march step + run rigidity induction: wrapper

Key results:
- `march_step`: one induction step of the march (MarchUpTo k → MarchUpTo (k+1))
- `run_rigid`: full run rigidity — all run letters are BG, all junctions have fillers

No sorry; standard axioms.
-/

namespace Erdos634.Draft.MarchInductionWrap

open Erdos634.MarchInduction Erdos634.Geometry Erdos634.TilePlacement
    Erdos634.BaseBetaTargetCoord Erdos634.MarchKillsFan Erdos634.CertCoord
    Erdos634.MarchKills

theorem mi_march_step {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    (hM : ModelData D f α β γ)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {t : ℝ} (ht : 0 < t) {k : ℕ} (hkL : t + (k + 2) * f ≤ baseLen 1 f)
    (hrun : ∃ (i : Fin N) (k' m : Fin 3), k' ≠ m ∧
      (D.tile i).pts k' = mkPt (t + (k + 1) * f) 0 ∧
      (D.tile i).pts m = mkPt (t + (k + 1) * f + f) 0)
    (hMk : MarchUpTo D f (by linarith) t k) : MarchUpTo D f (by linarith) t (k + 1) :=
  march_step D hf htgt hM hα hβpos hαβ hγdef hrel hirr ht hkL hrun hMk

theorem mi_run_rigid {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    (hM : ModelData D f α β γ)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {t : ℝ} (ht : 0 < t) {n : ℕ} (hnL : t + n * f ≤ baseLen 1 f)
    (hrun : LaysARun D f t n)
    (hbase : ∃ i, Set.range (D.tile i).pts = Set.range (aTileBG t f (by linarith)).pts) :
    ∀ k, k + 1 ≤ n → MarchUpTo D f (by linarith) t k :=
  run_rigid D hf htgt hM hα hβpos hαβ hγdef hrel hirr ht hnL hrun hbase

-- Non-vacuity: config_f3 exhibits angle data at f=3
example : ∃ α β γ : ℝ, (0 : ℝ) < α ∧ 0 < β := by
  exact ⟨modelAlpha 1 3, modelBeta 1 3, 2 * modelAlpha 1 3 + modelBeta 1 3,
    modelAlpha_pos (by norm_num : (1:ℝ) < 3),
    (modelBeta_mem (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) < 3)).1⟩

#print axioms mi_march_step
#print axioms mi_run_rigid

end Erdos634.Draft.MarchInductionWrap
