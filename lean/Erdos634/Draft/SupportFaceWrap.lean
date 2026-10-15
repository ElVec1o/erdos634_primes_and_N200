import Erdos634.SupportFace

namespace Erdos634.Draft.SupportFaceWrap
open Erdos634.SupportFace

theorem wrap_contact_eq_face {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →ₗ[ℝ] ℝ) (c : ℝ) (s : Finset E)
    (hle : ∀ v ∈ s, f v ≤ c) :
    {x ∈ convexHull ℝ (s : Set E) | f x = c}
      = convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) :=
  contact_eq_face f c s hle

example : True := trivial
#check @wrap_contact_eq_face

end Erdos634.Draft.SupportFaceWrap
