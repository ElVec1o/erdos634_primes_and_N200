import Erdos634.N1GapSubGolden
namespace Erdos634.Draft.N1GapSubGoldenWrap
open Erdos634.N1GapSubGolden Erdos634.N1Gap
variable {e f a b c : ℕ}

theorem wrap_SubGolden_b_lt_a (S : SubGolden e f a b c) : b < a :=
  S.b_lt_a

theorem wrap_SubGolden_a_lt_c (S : SubGolden e f a b c) : a < c :=
  S.a_lt_c

theorem wrap_not_member (S : SubGolden e f a b c) : ¬ Member e f a b c :=
  not_member S

theorem wrap_floor_b_div_a (S : SubGolden e f a b c) : b / a = 0 :=
  floor_b_div_a S

theorem wrap_card_adm_subGolden (S : SubGolden e f a b c) :
    card_adm_subGolden S = card_adm_subGolden S := rfl

theorem wrap_epred_subGolden (f : ℕ) (hf : 3 ≤ f) :
    SubGolden (f - 1) f (f * f - f) (2 * f - 1) (f * f) :=
  epred_subGolden f hf

theorem wrap_epred_prime_mod_twelve (f : ℕ) (hf : 2 ≤ f) (hp : Nat.Prime (2 * f * f + 2 * f - 1))
    (hgt : 3 < 2 * f * f + 2 * f - 1) : (2 * f * f + 2 * f - 1) % 12 = 11 :=
  epred_prime_mod_twelve f hf hp hgt

theorem wrap_witness_23 : SubGolden 2 3 6 5 9 := witness_23

theorem wrap_witness_83 : SubGolden 5 6 30 11 36 := witness_83

example : True := trivial
#print axioms wrap_epred_prime_mod_twelve
end Erdos634.Draft.N1GapSubGoldenWrap
