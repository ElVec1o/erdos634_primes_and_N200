/-
Draft/HerdtFamily.lean — **the Herdt 11-piece family for the `γ = 2α` branch** (Lead 1 of private/ROOM/DISCOVERY/leads6.md).
Tile `(a, b, c) = (u², v² - u², uv)`, `γ = 2α`, `u < v < 2u`, `b = v² - u²`.  The macro-dissection of the isosceles triangle with
base angles `α` into seven triangles similar to the tile and four parallelograms of `b × c` bricks is the template of
B. Herdt's 1125-tiling by `(4, 5, 6)` (Beeson, "Tilings of an isosceles triangle", Fig. 23, instance `(u, v) = (2, 3)` only);
its uniformization in `(u, v)` is ours (DISCOVERY room, 2026-10-17; real-parameter theorem `Draft.HerdtReal.herdtReal`).

* `herdt_family`: for positive integers `τ, D, a1, n1, a2, n2` with
  `b a1 + uv n1 + D u⁴ = τ v b²` and `b a2 + v n2 + τ u⁴ = D v b`, the number `b (v (D + τ v))²` is a tile count.
  (`g = v (D + τ v)` is the scale of the target: legs `v b g`, `u b g`.)  The hypotheses force `(v²-u²)³ v² > u⁸` (`τ·Vp = …`).
* `herdt_uniform`: whenever `(v²-u²)³ v² > u⁸` (and `u < v < 2u`), `b (g₀ s)²` is a tile count for every `s ≥ 1`, with the explicit
  `g₀ = 2 v (Vp + (u⁴ + buv)(u⁴ + b v²))`, `Vp = b³v² - u⁸`.
* instances: `(3,5)`, `g = 35`, `N = 19600`; `(4,7)`, `g = 63`, `N = 130977`.
UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.HerdtReal

open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.HerdtFamily
open Erdos634.Draft.LaczFamily
open Erdos634.Draft.TileCountFamilies (TileCount tileCount_scale)

theorem herdt_family (u v b τ D a1 n1 a2 n2 : ℕ) (hu : 0 < u) (huv : u < v) (hv2 : v < 2 * u)
    (hτ : 0 < τ) (hD : 0 < D) (ha1 : 0 < a1) (hn1 : 0 < n1) (ha2 : 0 < a2) (hn2 : 0 < n2)
    (hb : b + u ^ 2 = v ^ 2)
    (hE1 : b * a1 + u * v * n1 + D * u ^ 4 = τ * v * b ^ 2)
    (hE2 : b * a2 + v * n2 + τ * u ^ 4 = D * v * b) :
    TileCount (b * (v * (D + τ * v)) ^ 2) := by
  have hv : 0 < v := by omega
  have hbpos : 0 < b := by
    have : u ^ 2 < v ^ 2 := Nat.pow_lt_pow_left huv (by norm_num)
    omega
  -- reals
  have hbR : (b : ℝ) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
    have : ((b + u ^ 2 : ℕ) : ℝ) = ((v ^ 2 : ℕ) : ℝ) := by rw [hb]
    push_cast at this; linarith
  have hE1R : (b : ℝ) * a1 + u * v * n1 + D * (u : ℝ) ^ 4 = τ * v * (b : ℝ) ^ 2 := by exact_mod_cast hE1
  have hE2R : (b : ℝ) * a2 + v * n2 + τ * (u : ℝ) ^ 4 = D * v * b := by exact_mod_cast hE2
  have hxR : (0 : ℝ) < u := by exact_mod_cast hu
  have hyR : (0 : ℝ) < v := by exact_mod_cast hv
  have hxyR : (u : ℝ) < v := by exact_mod_cast huv
  have hy2R : (v : ℝ) < 2 * u := by exact_mod_cast hv2
  have hbRpos : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hτR : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hbq : bq (u : ℝ) v = b := by unfold bq; linarith
  have hVpdef : Vp (u : ℝ) v = (b : ℝ) ^ 3 * (v : ℝ) ^ 2 - (u : ℝ) ^ 8 := by unfold Vp; rw [hbq]
  have hpos1 : (0 : ℝ) < (b : ℝ) * a1 + u * v * n1 := by positivity
  have hpos2 : (0 : ℝ) < (b : ℝ) * a2 + v * n2 := by positivity
  have hVp : 0 < Vp (u : ℝ) v := by
    have e : (τ : ℝ) * Vp (u : ℝ) v = v * b * ((b : ℝ) * a1 + u * v * n1) + (u : ℝ) ^ 4 * ((b : ℝ) * a2 + v * n2) := by
      rw [hVpdef]; linear_combination (-((v : ℝ) * b)) * hE1R + (-((u : ℝ) ^ 4)) * hE2R
    have : 0 < (τ : ℝ) * Vp (u : ℝ) v := by rw [e]; positivity
    exact (mul_pos_iff_of_pos_left hτR).mp this
  have hLP : LP (u : ℝ) v 1 := LP.mk' hxR hyR one_pos hxyR hy2R hVp
  -- the four positive parameters
  obtain ⟨mh, hmh⟩ : ∃ mh : ℝ, mh * Vp (u : ℝ) v = b * a1 := ⟨b * a1 / Vp (u : ℝ) v, by field_simp⟩
  obtain ⟨yh, hyh⟩ : ∃ yh : ℝ, yh * Vp (u : ℝ) v = u * v * n1 := ⟨u * v * n1 / Vp (u : ℝ) v, by field_simp⟩
  obtain ⟨qh, hqh⟩ : ∃ qh : ℝ, qh * Vp (u : ℝ) v = b * a2 := ⟨b * a2 / Vp (u : ℝ) v, by field_simp⟩
  obtain ⟨lh, hlh⟩ : ∃ lh : ℝ, lh * Vp (u : ℝ) v = v * n2 := ⟨v * n2 / Vp (u : ℝ) v, by field_simp⟩
  have pm : 0 < mh := by
    have : 0 < mh * Vp (u : ℝ) v := by rw [hmh]; positivity
    exact (mul_pos_iff_of_pos_right hVp).mp this
  have py : 0 < yh := by
    have : 0 < yh * Vp (u : ℝ) v := by rw [hyh]; positivity
    exact (mul_pos_iff_of_pos_right hVp).mp this
  have pq : 0 < qh := by
    have : 0 < qh * Vp (u : ℝ) v := by rw [hqh]; positivity
    exact (mul_pos_iff_of_pos_right hVp).mp this
  have pl : 0 < lh := by
    have : 0 < lh * Vp (u : ℝ) v := by rw [hlh]; positivity
    exact (mul_pos_iff_of_pos_right hVp).mp this
  have hHP : HP (u : ℝ) v mh yh qh lh := HP.mk' hLP pm py pq pl
  have eD : Df (u : ℝ) v mh yh qh lh = D := by
    apply mul_right_cancel₀ hVp.ne'
    unfold Df
    rw [hbq]
    linear_combination ((u : ℝ) ^ 4) * hmh + ((u : ℝ) ^ 4) * hyh + ((v : ℝ) * (b : ℝ) ^ 2) * hqh
      + ((v : ℝ) * (b : ℝ) ^ 2) * hlh + ((u : ℝ) ^ 4) * hE1R + ((v : ℝ) * (b : ℝ) ^ 2) * hE2R
      - (D : ℝ) * hVpdef
  have eT : tauf (u : ℝ) v mh yh qh lh = τ := by
    apply mul_right_cancel₀ hVp.ne'
    unfold tauf
    rw [hbq]
    linear_combination ((v : ℝ) * b) * hmh + ((v : ℝ) * b) * hyh + ((u : ℝ) ^ 4) * hqh
      + ((u : ℝ) ^ 4) * hlh + ((v : ℝ) * b) * hE1R + ((u : ℝ) ^ 4) * hE2R - (τ : ℝ) * hVpdef
  -- integral side counts
  have succ_ex : ∀ m : ℕ, 0 < m → ∃ k, m = k + 1 := fun m hm => ⟨m - 1, by omega⟩
  obtain ⟨k1, hk1⟩ := succ_ex n1 hn1
  obtain ⟨k2, hk2⟩ := succ_ex a1 ha1
  obtain ⟨l3, hl3⟩ := succ_ex n2 hn2
  obtain ⟨l1, hl1⟩ := succ_ex (u * v * D) (by positivity)
  obtain ⟨l2, hl2⟩ := succ_ex (b * D) (by positivity)
  obtain ⟨k3, hk3⟩ := succ_ex (u ^ 2 * v * τ) (by positivity)
  obtain ⟨k4, hk4⟩ := succ_ex (u * b * τ) (by positivity)
  obtain ⟨l4, hl4⟩ := succ_ex (u * a2) (by positivity)
  have c1 : (n1 : ℝ) = (k1 : ℝ) + 1 := by exact_mod_cast hk1
  have c2 : (a1 : ℝ) = (k2 : ℝ) + 1 := by exact_mod_cast hk2
  have c3 : (n2 : ℝ) = (l3 : ℝ) + 1 := by exact_mod_cast hl3
  have d1 : (u : ℝ) * v * D = (l1 : ℝ) + 1 := by exact_mod_cast hl1
  have d2 : (b : ℝ) * D = (l2 : ℝ) + 1 := by exact_mod_cast hl2
  have d3 : (u : ℝ) ^ 2 * v * τ = (k3 : ℝ) + 1 := by exact_mod_cast hk3
  have d4 : (u : ℝ) * b * τ = (k4 : ℝ) + 1 := by exact_mod_cast hk4
  have d5 : (u : ℝ) * a2 = (l4 : ℝ) + 1 := by exact_mod_cast hl4
  have key := herdtReal hHP (u * v * D) (u ^ 2 * D) (b * D) (τ * u * b) (τ * u ^ 3) (τ * u ^ 2 * v) (τ * v * b)
    k1 l1 k2 l2 k3 l3 k4 l4
    (by push_cast; rw [eD])
    (by push_cast; rw [eD])
    (by push_cast; rw [eD, hbq])
    (by push_cast; rw [eT, hbq] <;> ring)
    (by push_cast; rw [eT] <;> ring)
    (by push_cast; rw [eT] <;> ring)
    (by push_cast; rw [eT, hbq] <;> ring)
    (by rw [← c1]; linear_combination (-1 : ℝ) * hyh)
    (by rw [← d1, hbq, eD]; ring)
    (by rw [← c2, hbq]; linear_combination (-1 : ℝ) * hmh)
    (by rw [← d2, hbq, eD]; ring)
    (by rw [← d3, hbq, eT]; ring)
    (by rw [← c3]; linear_combination (-(u : ℝ)) * hlh)
    (by rw [← d4, hbq, eT]; ring)
    (by rw [← d5, hbq]; linear_combination (-(u : ℝ)) * hqh)
  obtain ⟨Dis, -, -⟩ := key
  have hbZ : (b : ℤ) = (v : ℤ) ^ 2 - (u : ℤ) ^ 2 := by
    have : ((b + u ^ 2 : ℕ) : ℤ) = ((v ^ 2 : ℕ) : ℤ) := by rw [hb]
    push_cast at this; linarith
  have hE1Z : (b : ℤ) * a1 + u * v * n1 + D * (u : ℤ) ^ 4 = τ * v * (b : ℤ) ^ 2 := by exact_mod_cast hE1
  have hE2Z : (b : ℤ) * a2 + v * n2 + τ * (u : ℤ) ^ 4 = D * v * b := by exact_mod_cast hE2
  have hN : (u * v * D) * (u * v * D) + (u ^ 2 * D) * (u ^ 2 * D) + (b * D) * (b * D) + (τ * u * b) * (τ * u * b)
      + (τ * u ^ 3) * (τ * u ^ 3) + (τ * u ^ 2 * v) * (τ * u ^ 2 * v) + (τ * v * b) * (τ * v * b)
      + 2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1) + 2 * (k3 + 1) * (l3 + 1) + 2 * (k4 + 1) * (l4 + 1)
      = b * (v * (D + τ * v)) ^ 2 := by
    rw [← hk1, ← hl1, ← hk2, ← hl2, ← hk3, ← hl3, ← hk4, ← hl4]
    have : (((u * v * D) * (u * v * D) + (u ^ 2 * D) * (u ^ 2 * D) + (b * D) * (b * D) + (τ * u * b) * (τ * u * b)
      + (τ * u ^ 3) * (τ * u ^ 3) + (τ * u ^ 2 * v) * (τ * u ^ 2 * v) + (τ * v * b) * (τ * v * b)
      + 2 * n1 * (u * v * D) + 2 * a1 * (b * D) + 2 * (u ^ 2 * v * τ) * n2 + 2 * (u * b * τ) * (u * a2) : ℕ) : ℤ)
      = ((b * (v * (D + τ * v)) ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [hbZ] at hE1Z hE2Z ⊢
      linear_combination (2 * (D : ℤ)) * hE1Z + (2 * (τ : ℤ) * (u : ℤ) ^ 2) * hE2Z
    exact_mod_cast this
  rw [hN] at Dis
  exact ⟨Dis⟩

/-- **Uniform form.**  Whenever `u < v < 2u` and `(v²-u²)³ v² > u⁸`, for every `s ≥ 1`
`b (s g₀)²` is a tile count, `b = v²-u²`, `g₀ = 2 v (Vp + (u⁴ + b u v)(u⁴ + b v²))`, `Vp = b³v² - u⁸`. -/
theorem herdt_uniform (u v : ℕ) (hu : 0 < u) (huv : u < v) (hv2 : v < 2 * u)
    (hV : u ^ 8 < (v ^ 2 - u ^ 2) ^ 3 * v ^ 2) (s : ℕ) (hs : 0 < s) :
    TileCount ((v ^ 2 - u ^ 2) * (s * (2 * v * (((v ^ 2 - u ^ 2) ^ 3 * v ^ 2 - u ^ 8)
      + (u ^ 4 + (v ^ 2 - u ^ 2) * u * v) * (u ^ 4 + (v ^ 2 - u ^ 2) * v ^ 2)))) ^ 2) := by
  have hu2 : u ^ 2 < v ^ 2 := Nat.pow_lt_pow_left huv (by norm_num)
  obtain ⟨b, hb⟩ : ∃ b, b = v ^ 2 - u ^ 2 := ⟨_, rfl⟩
  have hbu : b + u ^ 2 = v ^ 2 := by rw [hb]; omega
  obtain ⟨Vn, hVn, hVn0⟩ : ∃ Vn, b ^ 3 * v ^ 2 = u ^ 8 + Vn ∧ 0 < Vn :=
    ⟨b ^ 3 * v ^ 2 - u ^ 8, by rw [hb]; omega, by rw [hb]; omega⟩
  have hbpos : 0 < b := by rw [hb]; omega
  have hv : 0 < v := by omega
  rw [← hb]
  have hVn' : b ^ 3 * v ^ 2 - u ^ 8 = Vn := by omega
  rw [hVn']
  have hVnZ : (b : ℤ) ^ 3 * (v : ℤ) ^ 2 = (u : ℤ) ^ 8 + Vn := by exact_mod_cast hVn
  have := herdt_family u v b (s * (2 * b * v * (u ^ 4 + b * u * v)))
    (s * (2 * Vn + 2 * u ^ 4 * (u ^ 4 + b * u * v))) (s * (u * v * Vn)) (s * (b * Vn)) (s * (v * Vn)) (s * (b * Vn))
    hu huv hv2 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hbu
    (by
      have : ((b * (s * (u * v * Vn)) + u * v * (s * (b * Vn)) + (s * (2 * Vn + 2 * u ^ 4 * (u ^ 4 + b * u * v))) * u ^ 4 : ℕ) : ℤ)
          = ((s * (2 * b * v * (u ^ 4 + b * u * v)) * v * b ^ 2 : ℕ) : ℤ) := by
        push_cast
        linear_combination (-2 * (s : ℤ) * ((u : ℤ) ^ 4 + b * u * v)) * hVnZ
      exact_mod_cast this)
    (by ring)
  convert this using 2
  ring

/-! ### instances -/
/-- `(u,v) = (3,5)`, tile `(9,16,15)`, `g = 35`, `N = 16 · 35² = 19600`: the first tiling of the `γ = 2α` branch with `u ≥ 3`
below `10⁶` tiles (macro-dissection exact; tile-level verified in the DISCOVERY room). -/
theorem tileCount_19600 : TileCount 19600 := by
  have := herdt_family 3 5 16 1 2 8 66 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- `(u,v) = (4,7)`, tile `(16,33,28)`, `g = 63`, `N = 33 · 63² = 130977`. -/
theorem tileCount_130977 : TileCount 130977 := by
  have := herdt_family 4 7 33 1 2 11 241 2 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- the control: Herdt's own instance `(u,v) = (2,3)`, tile `(4,5,6)`, `g = 15`, `N = 5 · 15² = 1125`. -/
theorem tileCount_1125 : TileCount 1125 := by
  have := herdt_family 2 3 5 1 2 5 3 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

end Erdos634.Draft.HerdtFamily

#print axioms Erdos634.Draft.HerdtFamily.herdtReal
#print axioms Erdos634.Draft.HerdtFamily.herdt_family
#print axioms Erdos634.Draft.HerdtFamily.herdt_uniform
#print axioms Erdos634.Draft.HerdtFamily.tileCount_19600
#print axioms Erdos634.Draft.HerdtFamily.tileCount_130977
#print axioms Erdos634.Draft.HerdtFamily.tileCount_1125
