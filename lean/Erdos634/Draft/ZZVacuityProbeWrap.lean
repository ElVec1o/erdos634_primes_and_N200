import Erdos634.ZZVacuityProbe

namespace Erdos634.Draft.ZZVacuityProbeWrap
open Erdos634.VacuityProbe

theorem wrap_base_chain_consecutive_meet_vacuous {N : ℕ} (hN : 0 < N)
    (D : Erdos634.Geometry.Dissection N)
    (g : Erdos634.Geometry.Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Erdos634.Geometry.Plane →ₗ[ℝ] ℝ) :
    ∃ E : ℕ → Fin N × Fin 3, ∀ k, k + 1 < (Erdos634.BaseChain.wallList D g c).length →
      ∃ j ≤ k, Erdos634.OrientBridge.edgePos D dir (E (k + 1))
        ≤ Erdos634.ChainInstance.edgeEnd D dir (E j) :=
  base_chain_consecutive_meet_vacuous hN D g c dir

example : True := trivial
#check @wrap_base_chain_consecutive_meet_vacuous

end Erdos634.Draft.ZZVacuityProbeWrap
