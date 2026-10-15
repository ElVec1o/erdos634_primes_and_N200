import Erdos634.MidTriangle

namespace Erdos634.Draft.MidTriangleWrap

open Erdos634.MidTriangle

theorem wrap_corner_decomp_alphabeta (p q r : Int)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h1 : q + r = 1) (h2 : 2*p - 3*q + r = -1) :
    p = 1 ∧ q = 1 ∧ r = 0 :=
  corner_decomp_alphabeta p q r hp hq hr h1 h2

theorem wrap_corner_decomp_apex (p q r : Int)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h1 : q + r = 0) (h2 : 2*p - 3*q + r = 2) :
    p = 1 ∧ q = 0 ∧ r = 0 :=
  corner_decomp_apex p q r hp hq hr h1 h2

theorem wrap_base_walk_forced_12 (P Q R : Int)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (h : 2*P + 3*Q + 4*R = 3) :
    P = 0 ∧ Q = 1 ∧ R = 0 :=
  base_walk_forced_12 P Q R hP hQ hR h

theorem wrap_base_walk_forced_23 (P Q R : Int)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (h : 6*P + 5*Q + 9*R = 10) :
    P = 0 ∧ Q = 2 ∧ R = 0 :=
  base_walk_forced_23 P Q R hP hQ hR h

theorem wrap_base_walk_forced_56 (P Q R : Int)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (h : 30*P + 11*Q + 36*R = 55) :
    P = 0 ∧ Q = 5 ∧ R = 0 :=
  base_walk_forced_56 P Q R hP hQ hR h

theorem wrap_base_walk_forced_47 (P Q R : Int)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (h : 28*P + 33*Q + 49*R = 132) :
    P = 0 ∧ Q = 4 ∧ R = 0 :=
  base_walk_forced_47 P Q R hP hQ hR h

example : wrap_corner_decomp_alphabeta 1 1 0 (by omega) (by omega) (by omega) (by omega) (by omega)
    = ⟨rfl, rfl, rfl⟩ := rfl

#print axioms wrap_base_walk_forced_47

end Erdos634.Draft.MidTriangleWrap
