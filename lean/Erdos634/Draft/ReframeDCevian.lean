/-
Draft/ReframeDCevian.lean  In `AllThreshold`.

The geometric hypotheses of `ReframeD.reframe_d` discharged for the horizontal cevian of `T_M(1,f)`.

The cevian `AQ` of `DeltaTri f hf M` is the segment from the apex `A = Φ_f (ptA f M) = Φ_f (0, B₀ M)` to `Q = Φ_f (ptQ f M) =
Φ_f (A₀ M, B₀ M)` (points of `SignedDecompE1`); in the skew frame it is the horizontal segment `y = B₀ M`, so its unit direction
is `u = Φ_f (1, 0) = g₁` and the line is `{skewY = B₀ M}` (`ReframeCWedge.skewY`).  Proved here, for a congruent dissection
`D` with `D.target = DeltaTri f hf M _`:

    cevU_norm        -- `‖u‖ = 1`
    foot_eq          -- `Φ_f (ptQ f M) = A + L • u`, `L = M f (f²−1)` (the foot of the cevian is at distance `L`)
    cev_hint         -- `hint`: the open cevian `(A, A + L u)` is interior to the target
    cev_out0         -- `hout0`: the line leaves the target before `A`
    cev_outL         -- `houtL`: the line leaves the target after the foot `Q`
    reframe_d_cevian -- `ReframeD.reframe_d` for this line with `hφ, hX, hu, hu1, hint, hout0, houtL` proved; the hypotheses
                     --   left are exactly `hℓ, hℓL` (a length `0 < ℓ ≤ L`), `hseed` and `hbc`

Hypotheses left in `reframe_d_cevian`: `hseed` (the ray starts with a tile edge `[A, A + ℓ u]` of either side: not derived) and
`hbc` (the hypothesis of (d): at the first common junction, one side lays only edges `b`, the other only edges `c`).
In the seed tiling of `T_3(1,3)` (the 234-tile tiling of `Draft.N234`, checked by a program outside Lean)
this cevian has the word `c^8` on one side against `b^9` on the other, the first common junction at `72 = b c = L`, so `hseed`
and `hbc` hold there with `M = f = 3` (and the conclusion is `x₀ = 72`, `f ≤ M` with equality); for the other cevian of that
tiling and for the cevians of the `f = 4` file they do not.  There is no Lean witness: the conclusion `f ≤ M` is the content of
(d) and the theorem is an implication whose hypotheses (`hseed`, `hbc`) hold for some dissections and fail for others.
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.ReframeD
import Erdos634.Draft.ReframeCWedge

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord Set

namespace Erdos634.Draft.ReframeDCevian
open Erdos634.Draft.WFrameF
open Erdos634.Draft.WtoDeltaF (DS DeltaTri carrier_DeltaTri)
open Erdos634.Draft.ReframeCWedge (skewY skewY_Phi)
open Erdos634.Draft.TraceCovering (Straddled)
open Erdos634.Draft.ReframeD (AllLen)
open Erdos634.Draft.SignedDecompE1 (dist_Phi_eq ptA ptQ sdU sdV)
open Erdos634.Draft.WBrickF (PhiL)

/-- the apex of `T_M(1,f)` in the plane: `Φ_F (0, B₀ M)` -/
noncomputable def apexPt (F M : ℝ) : Plane := Phi F (0, (2 * F ^ 2 - 1) * M)

/-- the unit direction of the cevian `AQ`: `Φ_F (1, 0)` -/
noncomputable def cevU (F : ℝ) : Plane := Phi F (1, 0)

theorem apexPt_eq (F M : ℝ) : apexPt F M = Phi F (ptA F M) := rfl

theorem Phi_inj {F : ℝ} (hF : 1 < F) : Function.Injective (Phi F) :=
  Function.LeftInverse.injective (Psi_Phi hF)

theorem cevU_norm {F : ℝ} (hF : 1 < F) : ‖cevU F‖ = 1 := by
  have h0 : Phi F (0, 0) = 0 := by simp [Phi]
  have h := dist_Phi_eq F hF (1, 0) (0, 0) 1 zero_le_one (by norm_num)
  rw [h0, dist_zero_right] at h
  exact h

/-- the point at parameter `x` on the ray from the apex -/
theorem line_pt (F x v : ℝ) : Phi F (0, v) + x • Phi F (1, 0) = Phi F (x, v) := by
  simp only [Phi]
  module

theorem apex_add (F M x : ℝ) : apexPt F M + x • cevU F = Phi F (x, (2 * F ^ 2 - 1) * M) :=
  line_pt F x _

/-- **The foot of the cevian is at distance `L = M f (f²−1)` from the apex along the ray.** -/
theorem foot_eq (F M : ℝ) : Phi F (ptQ F M) = apexPt F M + (M * F * (F ^ 2 - 1)) • cevU F := by
  rw [apex_add]
  show Phi F (F * (F ^ 2 - 1) * M, (2 * F ^ 2 - 1) * M) = Phi F (M * F * (F ^ 2 - 1), (2 * F ^ 2 - 1) * M)
  congr 2
  ring

theorem mem_interior_DS {u v w : ℝ} {p : ℝ × ℝ} (h1 : p.1 < u) (h2 : u * v < v * p.1 + u * p.2)
    (h3 : u * (p.2 - v) < (w - v) * p.1) : p ∈ interior (DS u v w) := by
  refine mem_interior.mpr ⟨{q : ℝ × ℝ | q.1 < u ∧ u * v < v * q.1 + u * q.2 ∧ u * (q.2 - v) < (w - v) * q.1},
    ?_, ?_, ⟨h1, h2, h3⟩⟩
  · rintro q ⟨a, b, c⟩
    exact ⟨a.le, b.le, c.le⟩
  · exact (isOpen_lt (by fun_prop) (by fun_prop)).and
      ((isOpen_lt (by fun_prop) (by fun_prop)).and (isOpen_lt (by fun_prop) (by fun_prop)))

section target

variable (f M : ℕ) (hf : 2 ≤ f) (hM : 1 ≤ M) {N : ℕ} (D : CongruentDissection N)
  (hT : D.target = DeltaTri f hf M (by omega))

include hM hT

/-- **`hint`: the open cevian is interior to the target.** -/
theorem cev_hint : ∀ x ∈ Ioo 0 ((M : ℝ) * f * ((f : ℝ) ^ 2 - 1)),
    apexPt (f : ℝ) (M : ℝ) + x • cevU (f : ℝ) ∈ interior D.target.carrier := by
  have hFR := Erdos634.Draft.WPgramF.hF f hf
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hFp : (0 : ℝ) < f := by linarith
  have hF2 : (1 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  intro x hx
  rw [hT, carrier_DeltaTri f hf M (by omega), interior_image hFR, apex_add]
  refine ⟨(x, (2 * (f : ℝ) ^ 2 - 1) * (M : ℝ)), ?_, rfl⟩
  have hv : 0 < (2 * (f : ℝ) ^ 2 - 1) * (M : ℝ) := mul_pos (by linarith) hMR
  have hfm : 0 < (f : ℝ) ^ 2 * M := mul_pos (by linarith) hMR
  have hu0 : 0 < (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (M : ℝ) := mul_pos (mul_pos hFp (by linarith)) hMR
  refine mem_interior_DS ?_ ?_ ?_
  · show x < (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (M : ℝ)
    nlinarith [hx.2]
  · show (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (M : ℝ) * ((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ))
      < (2 * (f : ℝ) ^ 2 - 1) * (M : ℝ) * x
        + (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (M : ℝ) * ((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ))
    nlinarith [mul_pos hv hx.1]
  · show (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (M : ℝ) * ((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ)
        - (2 * (f : ℝ) ^ 2 - 1) * (M : ℝ))
      < ((3 * (f : ℝ) ^ 2 - 1) * (M : ℝ) - (2 * (f : ℝ) ^ 2 - 1) * (M : ℝ)) * x
    nlinarith [mul_pos hfm hx.1]

/-- **`hout0`: the line leaves the target before the apex.** -/
theorem cev_out0 : ∀ t : ℝ, t < 0 → apexPt (f : ℝ) (M : ℝ) + t • cevU (f : ℝ) ∉ D.target.carrier := by
  have hFR := Erdos634.Draft.WPgramF.hF f hf
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hF2 : (1 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  intro t ht hmem
  rw [hT, carrier_DeltaTri f hf M (by omega), apex_add] at hmem
  obtain ⟨p, hp, hpe⟩ := hmem
  have hp' := Phi_inj hFR hpe
  subst hp'
  obtain ⟨_, h2, _⟩ := hp
  have hv : 0 < (2 * (f : ℝ) ^ 2 - 1) * (M : ℝ) := mul_pos (by linarith) hMR
  have : (2 * (f : ℝ) ^ 2 - 1) * (M : ℝ) * t < 0 := mul_neg_of_pos_of_neg hv ht
  have hu0 : (0 : ℝ) < (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (M : ℝ) :=
    mul_pos (mul_pos (by linarith) (by linarith)) hMR
  change (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (M : ℝ) * ((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ))
    ≤ (2 * (f : ℝ) ^ 2 - 1) * (M : ℝ) * t
      + (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (M : ℝ) * ((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ)) at h2
  linarith

/-- **`houtL`: the line leaves the target after the foot of the cevian.** -/
theorem cev_outL : ∀ t : ℝ, (M : ℝ) * f * ((f : ℝ) ^ 2 - 1) < t →
    apexPt (f : ℝ) (M : ℝ) + t • cevU (f : ℝ) ∉ D.target.carrier := by
  have hFR := Erdos634.Draft.WPgramF.hF f hf
  intro t ht hmem
  rw [hT, carrier_DeltaTri f hf M (by omega), apex_add] at hmem
  obtain ⟨p, hp, hpe⟩ := hmem
  have hp' := Phi_inj hFR hpe
  subst hp'
  obtain ⟨h1, _, _⟩ := hp
  change t ≤ (f : ℝ) * ((f : ℝ) ^ 2 - 1) * (M : ℝ) at h1
  nlinarith [ht, h1]

end target

/-! ## `reframe_d` for the cevian -/

/-- **`prop:reframe` (d), for the horizontal cevian of `T_M(1,f)`.**  Let `D` be a congruent dissection with target
`DeltaTri f hf M _`.  On the cevian from the apex `A = Φ_f (ptA f M)` to the foot `Φ_f (ptQ f M)` (the line `{skewY = B₀ M}`),
let `0 < ℓ ≤ L = M f (f²−1)`, let the ray start with a tile edge `[A, A + ℓ u]` of either side (`hseed`), and suppose that at the
first common junction one side lays only edges `b = f²−1` and the other only edges `c = f²` (`hbc`).  Then that junction is at
the distance `b c` from `A`, and `M ≥ f`.

The geometric hypotheses of `ReframeD.reframe_d` (`φ ≠ 0`, `φ A = c`, `φ u = 0`, `‖u‖ = 1`, `hint`, `hout0`, `houtL`) are proved
here; `hseed` and `hbc` are the hypotheses of the paper's (d) and are left (see the header: they hold in the seed tiling of
`T_3(1,3)` on the cevian to `Q`, and fail on other cevians). -/
theorem reframe_d_cevian (f M : ℕ) (hf : 2 ≤ f) (hM : 1 ≤ M) {N : ℕ} (D : CongruentDissection N)
    (hT : D.target = DeltaTri f hf M (by omega))
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓL : ℓ ≤ (M : ℝ) * f * ((f : ℝ) ^ 2 - 1))
    (hseed : ∃ e ∈ D.toDissection.lineChain (skewY (f : ℝ)) ((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ)) ∪
        D.toDissection.lineChain (-skewY (f : ℝ)) (-((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ))),
      (D.tile e.1).edge e.2 =
        segment ℝ (apexPt (f : ℝ) (M : ℝ)) (apexPt (f : ℝ) (M : ℝ) + ℓ • cevU (f : ℝ)))
    (hbc : ∀ x₀ : ℝ, ℓ ≤ x₀ → x₀ ≤ (M : ℝ) * f * ((f : ℝ) ^ 2 - 1) →
      ¬ Straddled D.toDissection (skewY (f : ℝ)) ((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ))
        (apexPt (f : ℝ) (M : ℝ) + x₀ • cevU (f : ℝ)) →
      ¬ Straddled D.toDissection (-skewY (f : ℝ)) (-((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ)))
        (apexPt (f : ℝ) (M : ℝ) + x₀ • cevU (f : ℝ)) →
      (∀ y ∈ Ioo 0 x₀,
        Straddled D.toDissection (skewY (f : ℝ)) ((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ))
          (apexPt (f : ℝ) (M : ℝ) + y • cevU (f : ℝ)) ∨
        Straddled D.toDissection (-skewY (f : ℝ)) (-((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ)))
          (apexPt (f : ℝ) (M : ℝ) + y • cevU (f : ℝ))) →
      (AllLen D.toDissection (skewY (f : ℝ)) ((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ)) (apexPt (f : ℝ) (M : ℝ))
          (cevU (f : ℝ)) x₀ ((f : ℝ) ^ 2 - 1) ∧
        AllLen D.toDissection (-skewY (f : ℝ)) (-((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ))) (apexPt (f : ℝ) (M : ℝ))
          (cevU (f : ℝ)) x₀ ((f : ℝ) ^ 2)) ∨
      (AllLen D.toDissection (skewY (f : ℝ)) ((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ)) (apexPt (f : ℝ) (M : ℝ))
          (cevU (f : ℝ)) x₀ ((f : ℝ) ^ 2) ∧
        AllLen D.toDissection (-skewY (f : ℝ)) (-((2 * (f : ℝ) ^ 2 - 1) * (M : ℝ))) (apexPt (f : ℝ) (M : ℝ))
          (cevU (f : ℝ)) x₀ ((f : ℝ) ^ 2 - 1))) :
    ∃ x₀ : ℝ, x₀ = ((f : ℝ) ^ 2 - 1) * (f : ℝ) ^ 2 ∧ ℓ ≤ x₀ ∧
      x₀ ≤ (M : ℝ) * f * ((f : ℝ) ^ 2 - 1) ∧ f ≤ M := by
  have hFR := Erdos634.Draft.WPgramF.hF f hf
  have hFp : (0 : ℝ) < f := by linarith
  have hφ : skewY (f : ℝ) ≠ 0 := by
    intro h
    have h1 := skewY_Phi hFR (0, 1)
    rw [h] at h1
    simp at h1
  have hX : skewY (f : ℝ) (apexPt (f : ℝ) (M : ℝ)) = (2 * (f : ℝ) ^ 2 - 1) * (M : ℝ) :=
    skewY_Phi hFR _
  have hu : skewY (f : ℝ) (cevU (f : ℝ)) = 0 := skewY_Phi hFR (1, 0)
  exact Erdos634.Draft.ReframeD.reframe_d (D := D.toDissection) f M hf hφ hX hu (cevU_norm hFR) hℓ hℓL
    (cev_hint f M hf hM D hT) (cev_out0 f M hf hM D hT) (cev_outL f M hf hM D hT) hseed hbc

end Erdos634.Draft.ReframeDCevian

#print axioms Erdos634.Draft.ReframeDCevian.cevU_norm
#print axioms Erdos634.Draft.ReframeDCevian.foot_eq
#print axioms Erdos634.Draft.ReframeDCevian.cev_hint
#print axioms Erdos634.Draft.ReframeDCevian.cev_out0
#print axioms Erdos634.Draft.ReframeDCevian.cev_outL
#print axioms Erdos634.Draft.ReframeDCevian.reframe_d_cevian
