import Erdos634.BaseBetaWalks

/-!
# Walk equation arithmetic kernels: wrapper

`BaseBetaWalks.*` provides the Diophantine walk-equation lemmas used throughout
the base-β analysis.

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseBetaWalksWrap

open Erdos634.BaseBetaWalks

theorem bbw_exists_of_dvd_sub (f x y : ℕ) (hy : y < f) (hd : (f : ℤ) ∣ (x : ℤ) - (y : ℤ)) :
    ∃ j : ℕ, x = y + f * j :=
  exists_of_dvd_sub f x y hy hd

theorem bbw_base_walk_param (e f P Q R B : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2)
    (h : P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B)) :
    ∃ j : ℕ, ∃ p : ℤ, Q = e + f * j ∧ (P : ℤ) = j * e + f * p ∧
      p * e + j * f + R = 2 * e ∧ P * e + j * B + R * f = 2 * (e * f) :=
  base_walk_param e f P Q R B he hef hcop hB h

theorem bbw_side_walk_param (e f P Q R B : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2)
    (h : P * (e * f) + Q * B + R * f ^ 2 = f ^ 3) :
    ∃ q : ℕ, ∃ p : ℤ, Q = f * q ∧ (P : ℤ) = q * e + f * p ∧ p * e + q * f + R = f ∧
      P * e + q * B + R * f = f ^ 2 :=
  side_walk_param e f P Q R B he hef hcop hB h

theorem bbw_base_trichotomy (e f P Q R B : ℕ) (he : 1 ≤ e) (h2e : 2 * e < f)
    (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2)
    (h : P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B)) :
    (P = 0 ∧ Q = e ∧ R = 2 * e) ∨ (P = f ∧ Q = e ∧ R = e) ∨ (P = 2 * f ∧ Q = e ∧ R = 0) :=
  base_trichotomy e f P Q R B he h2e hcop hB h

theorem bbw_side_dichotomy (e f P Q R B : ℕ) (he : 1 ≤ e) (h2e : 2 * e < f)
    (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2)
    (h : P * (e * f) + Q * B + R * f ^ 2 = f ^ 3) :
    (P = e ∧ Q = f ∧ R = 0) ∨ (∃ u : ℕ, Q = 0 ∧ P = f * u ∧ u * e + R = f) :=
  side_dichotomy e f P Q R B he h2e hcop hB h

theorem bbw_base_trichotomy_cfree (e f P Q R B : ℕ) (he : 1 ≤ e) (h2e : 2 * e < f)
    (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2) (hR : 1 ≤ R)
    (h : P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B)) :
    (P = 0 ∧ Q = e ∧ R = 2 * e) ∨ (P = f ∧ Q = e ∧ R = e) :=
  base_trichotomy_cfree e f P Q R B he h2e hcop hB hR h

theorem bbw_side_no_b (e f P Q R B : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hB : B + e ^ 2 = f ^ 2) (hR : 1 ≤ R) (h : P * (e * f) + Q * B + R * f ^ 2 = f ^ 3) :
    Q = 0 ∧ ∃ u : ℕ, P = f * u ∧ u * e + R = f :=
  side_no_b e f P Q R B he hef hcop hB hR h

theorem bbw_apex_leftover_nonrepresentable (e f na nb nc B : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2) :
    na * (e * f) + nb * B + nc * f ^ 2 ≠ e ^ 2 :=
  apex_leftover_nonrepresentable e f na nb nc B he hef hcop hB

theorem bbw_pierced_corner_types (x y z : ℕ) (h1 : y + z = 1) (h2 : 2 * x + z = 3 * y + 3) :
    (x = 3 ∧ y = 1 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 1) :=
  pierced_corner_types x y z h1 h2

theorem bbw_pre_pierce_dichotomy (e f ℓ B : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hB : B + e ^ 2 = f ^ 2) (hmem : ℓ = e * f ∨ ℓ = B ∨ ℓ = f ^ 2) (hle : ℓ ≤ e ^ 2) :
    ℓ = B ∧ f ^ 2 ≤ 2 * e ^ 2 :=
  pre_pierce_dichotomy e f ℓ B he hef hB hmem hle

theorem bbw_edge_ab_unsplittable (e f na nb nc B : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2) (hn : 2 ≤ na + nb + nc) :
    na * (e * f) + nb * B + nc * f ^ 2 ≠ e * f ∧ na * (e * f) + nb * B + nc * f ^ 2 ≠ B :=
  edge_ab_unsplittable e f na nb nc B he hef hcop hB hn

theorem bbw_far_near_disjoint (e f k na nb nc B : ℕ) (hcop : Nat.Coprime e f) (hef : e < f)
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ f) (hB : B + e ^ 2 = f ^ 2) (hnc : 1 ≤ nc) :
    k * B ≠ na * (e * f) + nb * B + nc * f ^ 2 :=
  far_near_disjoint e f k na nb nc B hcop hef hk1 hk2 hB hnc

theorem bbw_b_not_dvd_fsq (e f B : ℕ) (hcop : Nat.Coprime e f) (hef : e < f) (he : 2 ≤ e)
    (hB : B + e ^ 2 = f ^ 2) : ¬ B ∣ f ^ 2 :=
  b_not_dvd_fsq e f B hcop hef he hB

theorem bbw_far_is_bpow (e f na nb nc B : ℕ) (hcop : Nat.Coprime e f) (hef : e < f) (he : 2 ≤ e)
    (hB : B + e ^ 2 = f ^ 2) (hb1 : 1 ≤ nb)
    (h : f * B = na * (e * f) + nb * B + nc * f ^ 2) :
    na = 0 ∧ nb = f ∧ nc = 0 :=
  far_is_bpow e f na nb nc B hcop hef he hB hb1 h

theorem bbw_kb_unique_rep (e f k na nb nc B : ℕ) (hcop : Nat.Coprime e f) (hef : e < f)
    (he : 2 ≤ e) (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ f) (hB : B + e ^ 2 = f ^ 2)
    (h : k * B = na * (e * f) + nb * B + nc * f ^ 2) :
    na = 0 ∧ nb = k ∧ nc = 0 :=
  kb_unique_rep e f k na nb nc B hcop hef he hk1 hk2 hB h

theorem bbw_b_run_figure_is_111 (x y z : ℕ) (hpi : y + z = 2 ∧ 2 * x + z = 3 * y)
    (hgamma : 1 ≤ z) : x = 1 ∧ y = 1 ∧ z = 1 :=
  b_run_figure_is_111 x y z hpi hgamma

theorem bbw_halfpi_minus_alpha_unique (x y z : ℕ) (h1 : y + z = 1)
    (h2 : 2 * x + z + 1 = 3 * y) : x = 1 ∧ y = 1 ∧ z = 0 :=
  halfpi_minus_alpha_unique x y z h1 h2

/-- Non-vacuity: exists_of_dvd_sub at f=5, x=7, y=2. -/
theorem bbw_witness : ∃ j : ℕ, (7:ℕ) = 2 + 5 * j := ⟨1, by norm_num⟩

#print axioms bbw_base_trichotomy
#print axioms bbw_far_is_bpow
#print axioms bbw_kb_unique_rep

end Erdos634.Draft.BaseBetaWalksWrap
