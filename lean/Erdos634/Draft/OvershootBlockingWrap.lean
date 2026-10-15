import Erdos634.OvershootBlocking

namespace Erdos634.Draft.OvershootBlockingWrap
open Erdos634.Geometry Erdos634.CertCoord Erdos634.RouteOne
open Erdos634.OvershootBlocking

theorem wrap_escape_flank_advance_of_deviation {N : ℕ} (D : CongruentDissection N)
    (Ed : EscapeData D.toDissection) (f : ℝ) (hf : 2 ≤ f)
    (hmodel : ({dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
                dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) = {f, f ^ 2 - 1, f ^ 2})
    (E : Plane) (hEy : (E - Ed.V) 1 = 0) (hEx : (E - Ed.V) 0 = f)
    (k : Fin N) (hki : k ≠ Ed.i)
    (hdev : ∀ r : ℝ, 0 < r → ∃ q : Plane, q ∈ (D.tile k).carrier ∧ dist q E < r ∧
      0 < (q - E) 1) :
    ∃ (c : Fin 3) (o : Fin 3), (o = 1 ∨ o = 2) ∧
      (D.tile Ed.i).pts c = Ed.V ∧ (D.tile Ed.i).pts (c + o) = Ed.V + f • mkPt 1 0 :=
  escape_flank_advance_of_deviation D Ed f hf hmodel E hEy hEx k hki hdev

example : True := trivial
#print axioms wrap_escape_flank_advance_of_deviation

end Erdos634.Draft.OvershootBlockingWrap
