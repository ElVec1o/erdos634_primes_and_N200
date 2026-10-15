import Erdos634.LambdaFactor
namespace Erdos634.Draft.LambdaFactorWrap
open Erdos634.LambdaFactor

variable {R : Type*} [CommRing R]

theorem wrap_P_factor (I e f lam : R) (hI : I ^ 2 = -1) :
    I * e * f * lam ^ 3 - (f ^ 2 - e ^ 2) * lam ^ 2 + f ^ 2
      = I * G I e f lam * (e * lam + I * f) :=
  P_factor I e f lam hI

theorem wrap_Q_factor (I e f lam : R) (hI : I ^ 2 = -1) :
    f ^ 2 * lam ^ 3 - (f ^ 2 - e ^ 2) * lam - I * e * f
      = G I e f lam * (f * lam + I * e) :=
  Q_factor I e f lam hI

theorem wrap_b_in_ideal (I e f lam : R) :
    f * (e * lam + I * f) - e * (f * lam + I * e) = I * (f ^ 2 - e ^ 2) :=
  b_in_ideal I e f lam

theorem wrap_ideal_membership_is_automatic (I e f m lam : R)
    (hroot : e * lam + I * f = 0) (hsq : lam ^ 2 = -1) :
    H I e f m lam = -(m * I * (f ^ 2 - e ^ 2)) :=
  ideal_membership_is_automatic I e f m lam hroot hsq

theorem wrap_metric_class_never_fires (e f m : ℤ) (he : 1 ≤ e) (hef : e < f) (hm : 1 ≤ m) :
    11 * ((3 * f - 2 * e) * (f + e)) ≤ 6 * (m * f * (3 * f ^ 2 - e ^ 2)) :=
  metric_class_never_fires e f m he hef hm

example : True := trivial
#print axioms wrap_metric_class_never_fires
end Erdos634.Draft.LambdaFactorWrap
