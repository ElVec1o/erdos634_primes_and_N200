-- `S3Closed 21` holds with no hypothesis: the reduction `SIXS21Reduce.six21_scaled` plus the certified refutation tree of the
-- tile (2,3,4) in the isosceles (12,12,21) (`SIXBridgeS21.not_dissection_sides`), and `chain_21_final` with its residual discharged.
import Erdos634.Draft.SIXS21Reduce
import Erdos634.Draft.SIXBridgeS21
import Erdos634.Draft.CompositeFinal12

namespace Erdos634.Draft.SIXF21

open Erdos634.Geometry Erdos634.Draft.CompositeGen2

theorem s3Closed_21 : S3Closed 21 := by
  intro D α β a b c hα hrel hd t₀ t₁ ht h0 h1
  obtain ⟨σ, hm, h0', h1'⟩ := Rows11_13AnyLabel.transport D ht α h0 h1
  have hd' : (D.relabelTarget' σ).model.ThreeAlphaData α β a b c := hm ▸ hd
  obtain ⟨D', hT0, hT1, hT2, τ, m0, m1, m2⟩ :=
    SIX.six21_scaled rfl (D.relabelTarget' σ) hα hrel hd' h0' h1'
  exact Refl.SIXBridgeS21.not_dissection_sides D' 1 τ (by simpa using hT0) (by simpa using hT1)
    (by simpa using hT2) m0 m1 m2

/-- `21` is not a tile count: hypothesis-free. -/
theorem chain_21_final' (D : CongruentDissection 21) : False :=
  Erdos634.Draft.CompositeFinal12.chain_21_final s3Closed_21 D

end Erdos634.Draft.SIXF21

#print axioms Erdos634.Draft.SIXF21.chain_21_final'
