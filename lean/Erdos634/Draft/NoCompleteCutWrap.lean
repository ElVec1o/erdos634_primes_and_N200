import Erdos634.NoCompleteCut

namespace Erdos634.Draft.NoCompleteCutWrap

open Erdos634.NoCompleteCut

theorem ncc_coprime_N_f {e f : ℤ} (hcop : IsCoprime e f) :
    IsCoprime (3 * f ^ 2 - e ^ 2) f :=
  coprime_N_f hcop

theorem ncc_base_to_leg_cut_impossible {e f AQ : ℤ} (hcop : IsCoprime e f)
    (hAQ : 0 < AQ) (hlt : AQ < f ^ 3) (hf : 0 < f)
    (hdvd : f ^ 3 ∣ (3 * f ^ 2 - e ^ 2) * AQ) : False :=
  base_to_leg_cut_impossible hcop hAQ hlt hf hdvd

theorem ncc_apex_cut_impossible {e f P : ℤ} (hcop : IsCoprime e f)
    (hP : 0 < P) (hlt : P < f ^ 6) (hf : 0 < f)
    (hdvd : f ^ 6 ∣ (3 * f ^ 2 - e ^ 2) * P) : False :=
  apex_cut_impossible hcop hP hlt hf hdvd

theorem ncc_controls_escape :
    (2:ℤ) ^ 2 ∣ 2 ^ 2 * 11 ∧ (3:ℤ) ^ 2 ∣ 3 ^ 2 * 11 ∧ (4:ℤ) ^ 2 ∣ 4 ^ 2 * 11 :=
  controls_escape

example : ncc_controls_escape = controls_escape := rfl

#print axioms ncc_base_to_leg_cut_impossible
#print axioms ncc_apex_cut_impossible

end Erdos634.Draft.NoCompleteCutWrap
