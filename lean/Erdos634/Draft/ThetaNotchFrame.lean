-- Draft/ThetaNotchFrame.lean -- the APEX-UNIT FRAME of the notch seed: coordinates, half-plane facts, SSS helper.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
In the apex frame of `theta_t` (`theta_t = {x,y >= 0, x+y <= t}`, legs along the axes, one unit = `f b` real length along a leg,
`e b` along the base direction `(1,-1)`), the point `(x,y)` is the point `cH (x,y) = (f b (s-x-y), e b x)` of the skew frame
`Phi_phi`, `phi = f/e` (the frame of the `ThetaUnit` pieces at the base vertex `(0,s)`: `X'` along the leg towards the apex,
`Y'` along the base).  `ax, ay` read the apex coordinates back from a skew point.  Half-plane facts about regions are stated as
`al * ax p + be * ay p <= ga`; two regions with opposite facts have disjoint interiors (`disj_of_facts`).
The real squared length of an apex vector `(dx,dy)` is `b^2 (f^2 (dx^2+dy^2) + (2f^2-e^2) dx dy)` (`dist2_cH`).

CREDIT: Paliy (annulus/band steps on a seed), Beeson (48 seed), Laczkovich, Zhang, Beeson-Rosu (skew frame).
INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchBase
import Erdos634.Draft.Collar23A

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

def cH (E F s : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (F * (F ^ 2 - E ^ 2) * (s - q.1 - q.2), E * (F ^ 2 - E ^ 2) * q.1)
def cHv (E F : ℝ) (w : ℝ × ℝ) : ℝ × ℝ := (F * (F ^ 2 - E ^ 2) * (-w.1 - w.2), E * (F ^ 2 - E ^ 2) * w.1)
def ax (E F : ℝ) (p : ℝ × ℝ) : ℝ := p.2 / (E * (F ^ 2 - E ^ 2))
def ay (E F s : ℝ) (p : ℝ × ℝ) : ℝ := s - p.2 / (E * (F ^ 2 - E ^ 2)) - p.1 / (F * (F ^ 2 - E ^ 2))

section frame
variable {E F : ℝ} (s : ℝ) (hE : 0 < E) (hEF : E < F)
include hE hEF

theorem frame_pos : 0 < F ∧ 0 < F ^ 2 - E ^ 2 := ⟨by linarith, by nlinarith⟩

theorem cH_add (q w : ℝ × ℝ) : cH E F s (q + w) = cH E F s q + cHv E F w := by
  ext <;> simp only [cH, cHv, Prod.fst_add, Prod.snd_add] <;> ring

theorem cH_comb (a b c : ℝ × ℝ) (α β : ℝ) :
    cH E F s (a + α • (b - a) + β • (c - a)) = cH E F s a + α • (cH E F s b - cH E F s a) + β • (cH E F s c - cH E F s a) := by
  ext <;> simp only [cH, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem cH_par (a v1 v2 : ℝ × ℝ) (α β : ℝ) :
    cH E F s (a + α • v1 + β • v2) = cH E F s a + α • cHv E F v1 + β • cHv E F v2 := by
  ext <;> simp only [cH, cHv, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem cH_sub (a b : ℝ × ℝ) : cH E F s b - cH E F s a = cHv E F (b - a) := by
  ext <;> simp only [cH, cHv, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem ax_cH (q : ℝ × ℝ) : ax E F (cH E F s q) = q.1 := by
  obtain ⟨hF, hb⟩ := frame_pos hE hEF
  simp only [ax, cH]; field_simp

theorem ay_cH (q : ℝ × ℝ) : ay E F s (cH E F s q) = q.2 := by
  obtain ⟨hF, hb⟩ := frame_pos hE hEF
  simp only [ay, cH]; field_simp; ring

theorem cH_ax_ay (p : ℝ × ℝ) : cH E F s (ax E F p, ay E F s p) = p := by
  obtain ⟨hF, hb⟩ := frame_pos hE hEF
  ext <;> simp only [cH, ax, ay] <;> field_simp <;> ring

/-- a fact about apex coordinates on a `Preg` region, from its four corners (apex points) -/
theorem preg_apex_le (a V1 V2 : ℝ × ℝ) (σ al be ga : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1)
    (c1 : al * (a.1 + σ * (V1.1 - a.1)) + be * (a.2 + σ * (V1.2 - a.2)) ≤ ga)
    (c2 : al * (a.1 + σ * (V2.1 - a.1)) + be * (a.2 + σ * (V2.2 - a.2)) ≤ ga)
    (c3 : al * V1.1 + be * V1.2 ≤ ga) (c4 : al * V2.1 + be * V2.2 ≤ ga) :
    ∀ p ∈ Preg (cH E F s a) (cH E F s V1) (cH E F s V2) σ, al * ax E F p + be * ay E F s p ≤ ga := by
  rintro p ⟨α, β, hα, hβ, hs0, hs1, rfl⟩
  rw [← cH_comb s hE hEF, ax_cH s hE hEF, ay_cH s hE hEF]
  exact preg_le a V1 V2 σ al be ga h0 h1 c1 c2 c3 c4 _ ⟨α, β, hα, hβ, hs0, hs1, rfl⟩

theorem par_apex_le (a w1 w2 : ℝ × ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (al be ga : ℝ)
    (c00 : al * a.1 + be * a.2 ≤ ga)
    (c10 : al * (a + p • w1).1 + be * (a + p • w1).2 ≤ ga)
    (c01 : al * (a + q • w2).1 + be * (a + q • w2).2 ≤ ga)
    (c11 : al * (a + p • w1 + q • w2).1 + be * (a + p • w1 + q • w2).2 ≤ ga) :
    ∀ x ∈ Par (cH E F s a) (cHv E F w1) (cHv E F w2) p q, al * ax E F x + be * ay E F s x ≤ ga := by
  rintro x ⟨α, β, hα, hα', hβ, hβ', rfl⟩
  have : cH E F s a + α • cHv E F w1 + β • cHv E F w2 = cH E F s (a + α • w1 + β • w2) := (cH_par s hE hEF a w1 w2 α β).symm
  rw [this, ax_cH s hE hEF, ay_cH s hE hEF]
  exact Par_le a w1 w2 p q hp hq al be ga c00 c10 c01 c11 _ ⟨α, β, hα, hα', hβ, hβ', rfl⟩

end frame

/-- two sets with opposite half-plane facts (in apex coordinates) have disjoint interiors -/
theorem disj_of_facts {E F : ℝ} (s : ℝ) (hE : 0 < E) (hEF : E < F) {S1 S2 : Set (ℝ × ℝ)} (al be ga : ℝ)
    (hnd : al ≠ 0 ∨ be ≠ 0)
    (h1 : ∀ p ∈ S1, al * ax E F p + be * ay E F s p ≤ ga)
    (h2 : ∀ p ∈ S2, (-al) * ax E F p + (-be) * ay E F s p ≤ -ga) :
    Disjoint (interior S1) (interior S2) := by
  obtain ⟨hF, hb⟩ := frame_pos hE hEF
  have hEB : 0 < E * (F ^ 2 - E ^ 2) := mul_pos hE hb
  have hFB : 0 < F * (F ^ 2 - E ^ 2) := mul_pos hF hb
  have key : ∀ p : ℝ × ℝ, al * ax E F p + be * ay E F s p =
      (-be / (F * (F ^ 2 - E ^ 2))) * p.1 + ((al - be) / (E * (F ^ 2 - E ^ 2))) * p.2 + be * s := by
    intro p; simp only [ax, ay]; field_simp; ring
  refine Erdos634.Draft.Collar23.interior_disj_lin (S := S2) (T := S1) (-be / (F * (F ^ 2 - E ^ 2))) ((al - be) / (E * (F ^ 2 - E ^ 2))) (ga - be * s) ?_ ?_ ?_
    |>.symm
  · rcases hnd with h | h
    · have : (al - be) / (E * (F ^ 2 - E ^ 2)) ≠ 0 ∨ -be / (F * (F ^ 2 - E ^ 2)) ≠ 0 := by
        by_contra hc; push_neg at hc
        obtain ⟨c1, c2⟩ := hc
        have : be = 0 := by
          have := div_eq_zero_iff.mp c2; rcases this with h' | h'
          · linarith
          · exact absurd h' hFB.ne'
        have h3 := div_eq_zero_iff.mp c1; rcases h3 with h' | h'
        · exact h (by linarith)
        · exact absurd h' hEB.ne'
      rcases this with h' | h' <;> positivity
    · have h' : -be / (F * (F ^ 2 - E ^ 2)) ≠ 0 := div_ne_zero (neg_ne_zero.mpr h) hFB.ne'
      positivity
  · intro p hp
    have := h2 p hp
    have h3 := key p
    linarith [this]
  · intro p hp
    have := h1 p hp
    rw [key] at this
    linarith

/-- squared real distance of two apex points -/
theorem dist2_cH {E F : ℝ} (s : ℝ) (hE : 0 < E) (hEF : E < F) {φ : ℝ} (hφ : 1 < φ) (hφE : φ = F / E) (p q : ℝ × ℝ) :
    dist (Phi φ (cH E F s p)) (Phi φ (cH E F s q)) ^ 2 =
      (F ^ 2 - E ^ 2) ^ 2 * (F ^ 2 * ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) + (2 * F ^ 2 - E ^ 2) * ((p.1 - q.1) * (p.2 - q.2))) := by
  obtain ⟨hF, hb⟩ := frame_pos hE hEF
  rw [sq_Phi hφ]
  subst hφE
  simp only [cH]
  field_simp
  ring

end

end Erdos634.Draft.ThetaNotch
