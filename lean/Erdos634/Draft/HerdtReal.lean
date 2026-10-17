/-
Draft/HerdtReal.lean — the real-parameter theorem `herdtReal` of the Herdt 11-piece family: pieces (Draft.HerdtReal0),
tilings (Draft.HerdtTile), count identity, `pack_exists`.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.HerdtReal0

open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Rect RTiling.cast)

namespace Erdos634.Draft.HerdtFamily
open Erdos634.Draft.LaczFamily Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G
open Erdos634.Draft.S2L (pack_exists)

theorem herdtReal {x y mh yh qh lh : ℝ} (h : HP x y mh yh qh lh)
    (kr ko kl kg kc kb kp k1 l1 k2 l2 k3 l3 k4 l4 : ℕ)
    (er : (kr : ℝ) = x * y * Df x y mh yh qh lh)
    (eo : (ko : ℝ) = x ^ 2 * Df x y mh yh qh lh)
    (el : (kl : ℝ) = bq x y * Df x y mh yh qh lh)
    (eg : (kg : ℝ) = tauf x y mh yh qh lh * x * bq x y)
    (ec : (kc : ℝ) = tauf x y mh yh qh lh * x ^ 3)
    (eb : (kb : ℝ) = tauf x y mh yh qh lh * x ^ 2 * y)
    (ep : (kp : ℝ) = tauf x y mh yh qh lh * y * bq x y)
    (hk1 : x * y * ((k1 : ℝ) + 1) = Vp x y * yh)
    (hl1 : bq x y * ((l1 : ℝ) + 1) = x * y * bq x y * Df x y mh yh qh lh)
    (hk2 : bq x y * ((k2 : ℝ) + 1) = Vp x y * mh)
    (hl2 : x * y * ((l2 : ℝ) + 1) = x * y * bq x y * Df x y mh yh qh lh)
    (hk3 : bq x y * ((k3 : ℝ) + 1) = x ^ 2 * y * bq x y * tauf x y mh yh qh lh)
    (hl3 : x * y * ((l3 : ℝ) + 1) = x * Vp x y * lh)
    (hk4 : x * y * ((k4 : ℝ) + 1) = x ^ 2 * y * bq x y * tauf x y mh yh qh lh)
    (hl4 : bq x y * ((l4 : ℝ) + 1) = x * Vp x y * qh) :
    ∃ D : CongruentDissection (kr * kr + ko * ko + kl * kl + kg * kg + kc * kc + kb * kb + kp * kp
        + 2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1) + 2 * (k3 + 1) * (l3 + 1) + 2 * (k4 + 1) * (l4 + 1)),
      D.model = Mod h.lp ∧ D.target = tgt h := by
  have hx := h.lp.hx
  have hy := h.lp.hy
  have hb : 0 < bq x y := h.lp.hb
  have hD : 0 < Df x y mh yh qh lh := by
    unfold Df; have := h.hm; have := h.hy'; have := h.hq; have := h.hl; positivity
  have hT : 0 < tauf x y mh yh qh lh := by
    unfold tauf; have := h.hm; have := h.hy'; have := h.hq; have := h.hl; positivity
  have posk : ∀ (k : ℕ) (e : ℝ), (k : ℝ) = e → 0 < e → 0 < k := by
    intro k e hk he
    have : (0 : ℝ) < k := by rw [hk]; exact he
    exact_mod_cast this
  have p0 := posk kr _ er (by positivity)
  have p1 := posk ko _ eo (by positivity)
  have p2 := posk kl _ el (by positivity)
  have p3 := posk kg _ eg (by positivity)
  have p4 := posk kc _ ec (by positivity)
  have p5 := posk kb _ eb (by positivity)
  have p6 := posk kp _ ep (by positivity)
  have R : ∀ a : Fin 11, RTiling (Sset h a) (Mod h.lp) (cntS kr ko kl kg kc kb kp k1 l1 k2 l2 k3 l3 k4 l4 a) :=
    fun a => match a with
    | ⟨0, _⟩ => R_red h kr p0 er
    | ⟨1, _⟩ => R_ora h ko p1 eo
    | ⟨2, _⟩ => R_lgr h kl p2 el
    | ⟨3, _⟩ => R_gre h kg p3 eg
    | ⟨4, _⟩ => R_cya h kc p4 ec
    | ⟨5, _⟩ => R_lbg h kb p5 eb
    | ⟨6, _⟩ => R_pbg h kp p6 ep
    | ⟨7, _⟩ => R_yel h k1 l1 hk1 hl1
    | ⟨8, _⟩ => R_mar h k2 l2 hk2 hl2
    | ⟨9, _⟩ => R_llw h k3 l3 hk3 hl3
    | ⟨10, _⟩ => R_plw h k4 l4 hk4 hl4
    | ⟨k + 11, hk⟩ => absurd hk (by omega)
  have hsum : ∑ a, cntS kr ko kl kg kc kb kp k1 l1 k2 l2 k3 l3 k4 l4 a
      = kr * kr + ko * ko + kl * kl + kg * kg + kc * kc + kb * kb + kp * kp
        + 2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1) + 2 * (k3 + 1) * (l3 + 1) + 2 * (k4 + 1) * (l4 + 1) := by
    simp [Fin.sum_univ_succ, cntS]
    ring
  -- the brick counts
  have hxyb : x * y * bq x y ≠ 0 := by positivity
  have c1 : ((k1 : ℝ) + 1) * ((l1 : ℝ) + 1) = Vp x y * yh * Df x y mh yh qh lh := by
    apply mul_left_cancel₀ hxyb
    calc x * y * bq x y * (((k1 : ℝ) + 1) * ((l1 : ℝ) + 1))
        = (x * y * ((k1 : ℝ) + 1)) * (bq x y * ((l1 : ℝ) + 1)) := by ring
      _ = (Vp x y * yh) * (x * y * bq x y * Df x y mh yh qh lh) := by rw [hk1, hl1]
      _ = x * y * bq x y * (Vp x y * yh * Df x y mh yh qh lh) := by ring
  have c2 : ((k2 : ℝ) + 1) * ((l2 : ℝ) + 1) = Vp x y * mh * Df x y mh yh qh lh := by
    apply mul_left_cancel₀ hxyb
    calc x * y * bq x y * (((k2 : ℝ) + 1) * ((l2 : ℝ) + 1))
        = (bq x y * ((k2 : ℝ) + 1)) * (x * y * ((l2 : ℝ) + 1)) := by ring
      _ = (Vp x y * mh) * (x * y * bq x y * Df x y mh yh qh lh) := by rw [hk2, hl2]
      _ = x * y * bq x y * (Vp x y * mh * Df x y mh yh qh lh) := by ring
  have c3 : ((k3 : ℝ) + 1) * ((l3 : ℝ) + 1) = x ^ 2 * tauf x y mh yh qh lh * Vp x y * lh := by
    apply mul_left_cancel₀ hxyb
    calc x * y * bq x y * (((k3 : ℝ) + 1) * ((l3 : ℝ) + 1))
        = (bq x y * ((k3 : ℝ) + 1)) * (x * y * ((l3 : ℝ) + 1)) := by ring
      _ = (x ^ 2 * y * bq x y * tauf x y mh yh qh lh) * (x * Vp x y * lh) := by rw [hk3, hl3]
      _ = x * y * bq x y * (x ^ 2 * tauf x y mh yh qh lh * Vp x y * lh) := by ring
  have c4 : ((k4 : ℝ) + 1) * ((l4 : ℝ) + 1) = x ^ 2 * tauf x y mh yh qh lh * Vp x y * qh := by
    apply mul_left_cancel₀ hxyb
    calc x * y * bq x y * (((k4 : ℝ) + 1) * ((l4 : ℝ) + 1))
        = (x * y * ((k4 : ℝ) + 1)) * (bq x y * ((l4 : ℝ) + 1)) := by ring
      _ = (x ^ 2 * y * bq x y * tauf x y mh yh qh lh) * (x * Vp x y * qh) := by rw [hk4, hl4]
      _ = x * y * bq x y * (x ^ 2 * tauf x y mh yh qh lh * Vp x y * qh) := by ring
  have key := pack_exists (M := Mod h.lp) (T := tgt h) (Sset h)
    (cntS kr ko kl kg kc kb kp k1 l1 k2 l2 k3 l3 k4 l4) R (hS_all h) (hsub_all h)
    (hvol_all h _ (by
      rw [hsum]
      push_cast
      have d1 : 2 * ((k1 : ℝ) + 1) * ((l1 : ℝ) + 1) = 2 * (Vp x y * yh * Df x y mh yh qh lh) := by rw [mul_assoc, c1]
      have d2 : 2 * ((k2 : ℝ) + 1) * ((l2 : ℝ) + 1) = 2 * (Vp x y * mh * Df x y mh yh qh lh) := by rw [mul_assoc, c2]
      have d3 : 2 * ((k3 : ℝ) + 1) * ((l3 : ℝ) + 1) = 2 * (x ^ 2 * tauf x y mh yh qh lh * Vp x y * lh) := by rw [mul_assoc, c3]
      have d4 : 2 * ((k4 : ℝ) + 1) * ((l4 : ℝ) + 1) = 2 * (x ^ 2 * tauf x y mh yh qh lh * Vp x y * qh) := by rw [mul_assoc, c4]
      rw [d1, d2, d3, d4, er, eo, el, eg, ec, eb, ep]
      simp only [Df, tauf, gg, bq, Vp]
      ring))
  rw [hsum] at key
  exact key

end Erdos634.Draft.HerdtFamily
