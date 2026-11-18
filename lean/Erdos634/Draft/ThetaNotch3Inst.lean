-- Draft/ThetaNotch3Inst.lean -- decidable instantiation lemma of the notch seed (rho >= 1, n <= n1), instances and controls.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
* `NP3cond`: a decidable conjunction (the hypotheses of `NP3`); `thetaTiled_of_cond` : `NP3cond ... -> forall t >= M + j f, ThetaTiled e f (f f - e e) t`.
* Instances (all `by decide`): `(3,4)` at `t = 14` with `n = 3 < n1 = 4` (ONE mirrored strip), `(4,5)` at `t = 18` (`n = 4`, `n1 = 6`, two strips),
  `(5,6)` at `t = 28` (`n = 5`, `n1 = 8`, three strips), and the strip-free rows of `ThetaNotch2Inst` through `NP3` with `n = n1`.
* `TileCount 1372, 1792, 2916, 8624`.
* controls: `NP3cond` is witnessed (the instances); at `(2,3)` no `NP3cond` has `M + j f <= 6` (consistent with `not_thetaTiled_2_3_t4`, `_t3`).
CREDIT: Paliy (annulus / band steps on a seed), Beeson (48 seed), Laczkovich, Zhang.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch3Main
import Erdos634.Draft.ThetaUnitUp

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled thetaTiled_upset)
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- the hypotheses of `NP3`, as a decidable proposition (`g = f - e`, `b = f f - e e`) -/
def NP3cond (e f M n n1 j s rho : ℕ) : Prop :=
  1 ≤ e ∧ e < f ∧ 1 ≤ n ∧ n ≤ n1 ∧ e ≤ (f - e) * n ∧ e * M = f * n1 + rho ∧ 1 ≤ rho ∧ rho < f ∧ 1 ≤ j ∧ j * f < s ∧
    s < M + j * f ∧ e * n ≤ j * (f * f - e * e) ∧ e * n + s * f ≤ (M + j * f) * f ∧ e + (f - e) * (j * f) ≤ (f - e) * s

instance (e f M n n1 j s rho : ℕ) : Decidable (NP3cond e f M n n1 j s rho) := by unfold NP3cond; infer_instance

def mkNP3 (e f M n n1 j s rho : ℕ) (h : NP3cond e f M n n1 j s rho) : NP3 where
  e := e
  f := f
  g := f - e
  b := f * f - e * e
  M := M
  n := n
  n1 := n1
  j := j
  s := s
  rho := rho
  he := h.1
  hg := by have := h.2.1; omega
  hfg := by have := h.2.1; omega
  hb := by
    have := h.2.1
    have : e * e ≤ f * f := Nat.mul_self_le_mul_self (by omega)
    omega
  hn := h.2.2.1
  hnn := h.2.2.2.1
  hgn := h.2.2.2.2.1
  hrho := h.2.2.2.2.2.1
  hr1 := h.2.2.2.2.2.2.1
  hrf := h.2.2.2.2.2.2.2.1
  hj := h.2.2.2.2.2.2.2.2.1
  hks := h.2.2.2.2.2.2.2.2.2.1
  hst := h.2.2.2.2.2.2.2.2.2.2.1
  hB := h.2.2.2.2.2.2.2.2.2.2.2.1
  hC := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  hD := h.2.2.2.2.2.2.2.2.2.2.2.2.2

namespace NP3
theorem hnM (P : NP3) : P.n ≤ P.M := by
  have h := P.hrho
  have h1 : P.e < P.f := P.hef
  have h2 := P.hn
  have h3 := P.hnn
  by_contra hc; push_neg at hc
  nlinarith [Nat.mul_le_mul_left P.e hc.le, Nat.mul_le_mul_right P.n h1.le, Nat.mul_le_mul_left P.f h3]

/-- the up-set of the seed: `theta_t` for every `t >= M + j f` -/
theorem thetaTiled_up (P : NP3) : ∀ t, P.M + P.j * P.f ≤ t → ThetaTiled P.e P.f P.b t := by
  intro t ht
  have hg : P.e ≤ (P.f - P.e) * (P.M + P.j * P.f) := by
    have h1 : P.f - P.e = P.g := by have := P.hfg; omega
    rw [h1]
    exact le_trans P.hgn (Nat.mul_le_mul_left _ (le_trans P.hnM (Nat.le_add_right _ _)))
  exact thetaTiled_upset P.e P.f P.b _ P.he P.hef P.hb hg (thetaTiled_notch3 P) t ht
end NP3

/-- **Decidable instantiation**: `NP3cond` gives `theta_t(e,f)` for all `t >= M + j f`. -/
theorem thetaTiled_of_cond (e f M n n1 j s rho : ℕ) (h : NP3cond e f M n n1 j s rho) :
    ∀ t, M + j * f ≤ t → ThetaTiled e f (f * f - e * e) t := by
  have := NP3.thetaTiled_up (mkNP3 e f M n n1 j s rho h)
  exact this

/-! ### instances: rows with strips -/

/-- `theta_14(3,4)`: `(j,M,n,n1,s,rho) = (2,6,3,4,11,2)` -- ONE strip (`n < n1`); 1372 tiles of `(12,7,16)`. -/
theorem thetaTiled_3_4_14 : ThetaTiled 3 4 7 14 := thetaTiled_of_cond 3 4 6 3 4 2 11 2 (by decide) 14 (by norm_num)
/-- `theta_18(4,5)`: `(2,8,4,6,14,2)` -- two strips; 2916 tiles of `(20,9,25)`. -/
theorem thetaTiled_4_5_18 : ThetaTiled 4 5 9 18 := thetaTiled_of_cond 4 5 8 4 6 2 14 2 (by decide) 18 (by norm_num)
/-- `theta_28(5,6)`: `(3,10,5,8,23,2)` -- three strips; 8624 tiles of `(30,11,36)`. -/
theorem thetaTiled_5_6_28 : ThetaTiled 5 6 11 28 := thetaTiled_of_cond 5 6 10 5 8 3 23 2 (by decide) 28 (by norm_num)
/-- the strip-free instance of `ThetaNotch2Inst` through `NP3` (`n = n1`) -/
theorem thetaTiled_2_3_via_np3 : ThetaTiled 2 3 5 7 := thetaTiled_of_cond 2 3 4 2 2 1 5 2 (by decide) 7 (by norm_num)

theorem tileCount_1372 : TileCount 1372 := by obtain ⟨D, -, -⟩ := thetaTiled_3_4_14; exact ⟨D⟩
theorem tileCount_1792 : TileCount 1792 := by
  obtain ⟨D, -, -⟩ := thetaTiled_of_cond 3 4 6 3 4 2 11 2 (by decide) 16 (by norm_num); exact ⟨D⟩
theorem tileCount_2916 : TileCount 2916 := by obtain ⟨D, -, -⟩ := thetaTiled_4_5_18; exact ⟨D⟩
theorem tileCount_8624 : TileCount 8624 := by obtain ⟨D, -, -⟩ := thetaTiled_5_6_28; exact ⟨D⟩

/-! ### controls -/

/-- **Witness**: `NP3cond` holds at the four rows above (and the strip counts are `n1 - n = 1, 2, 3, 0`). -/
theorem np3_witnesses :
    NP3cond 3 4 6 3 4 2 11 2 ∧ NP3cond 4 5 8 4 6 2 14 2 ∧ NP3cond 5 6 10 5 8 3 23 2 ∧ NP3cond 2 3 4 2 2 1 5 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **Negative control (hypothesis boundary)**: at `(e,f) = (2,3)` no `NP3cond` has `M + j f <= 6`. -/
theorem np3_boundary_2_3 (M n n1 j s rho : ℕ) (h : NP3cond 2 3 M n n1 j s rho) : 7 ≤ M + j * 3 := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  omega

/-- consistency with the proved NO `ThetaUnitUp.not_thetaTiled_2_3_t4` (and `_t3`): no `NP3cond` at `(2,3)` has `t = 3, 4`. -/
theorem np3_consistent_2_3 (M n n1 j s rho : ℕ) (h : NP3cond 2 3 M n n1 j s rho) : M + j * 3 ≠ 4 ∧ M + j * 3 ≠ 3 := by
  have := np3_boundary_2_3 M n n1 j s rho h; omega

end

end Erdos634.Draft.ThetaNotch
