-- Draft/FluxPaperLemCancel.lean — `lem:cancel` as stated: for each `f ∈ {f_α, f_β}`,
-- Σ_tiles C_f(t) = Φ_f(∂ABC), for an arbitrary (not edge-to-edge) dissection.
-- This is the instance of the general `Dissection.flux_cancel` at the two weights `f_α`, `f_β`.
import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxCancel

open scoped Classical

namespace Erdos634.Geometry

theorem Paper.lem_cancel {N : ℕ} (D : Dissection N) (α : ℝ)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    (∑ i, (D.tile i).flux (fAlpha α hα).weight = D.target.flux (fAlpha α hα).weight) ∧
    (∑ i, (D.tile i).flux (fBeta α hα).weight = D.target.flux (fBeta α hα).weight) :=
  ⟨D.flux_cancel _ (fAlpha α hα).weight_odd, D.flux_cancel _ (fBeta α hα).weight_odd⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Paper.lem_cancel
