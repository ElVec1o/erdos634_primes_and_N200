import Erdos634.SideNoB

/-!
# SideNoB — equal-side no-b-edge theorems: wrapper

`SideNoB.*` arithmetic kernels.

Key theorems (all ℕ arithmetic):

1. **`side_no_b_uncond`**: unconditional Q=0 on the equal side given gcd(e,f)=1, e<f, γ-trap.
2. **`side_quantized`**: f ∣ x from x·e + z·f = f² (coprimality).
3. **`side_no_b_e_one`**: at e=1, f≥2 the equal-side walk forces Q=0.

Pure ℕ arithmetic: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.SideNoBWrap

open Erdos634.SideNoB

/-- Equal side carries no b-edge: unconditional at e<f. -/
theorem sidenoB_uncond {e f b P Q R : ℕ} (hco : Nat.Coprime e f) (hef : e < f)
    (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) : Q = 0 :=
  side_no_b_uncond hco hef hb hwalk hgamma

/-- Quantization: x·e + z·f = f² forces f ∣ x. -/
theorem sidenoB_quantized {e f x z : ℕ} (hf : 1 ≤ f) (hco : Nat.Coprime e f)
    (h : x * e + z * f = f * f) : f ∣ x :=
  side_quantized hf hco h

/-- At e=1, f≥2: equal-side walk Q=0. -/
theorem sidenoB_e_one {f b P Q R : ℕ} (hf : 2 ≤ f)
    (hb : b + 1 = f * f)
    (hwalk : P * (1 * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) : Q = 0 :=
  side_no_b_e_one hf hb hwalk hgamma

/-- Non-vacuity: e=1, f=2 satisfies coprimality and e<f. -/
theorem sidenoB_witness : Nat.Coprime 1 2 ∧ (1:ℕ) < 2 := by norm_num [Nat.Coprime]

#print axioms sidenoB_uncond
#print axioms sidenoB_quantized

end Erdos634.Draft.SideNoBWrap
