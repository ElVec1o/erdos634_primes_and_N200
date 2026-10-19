/-
Credit: D. Paliy (2026-10-03 to 10-08, W/beta caps, exact boundary-adjacency and thick-member observations; public repository github.com/DenisUkranian/erdos-634-tilings), M. Beeson and G. Rosu.
Draft/SplusThickGeom.lean -- written 19 October 2026.  UNAUDITED.  Not in `All`; in `AllSplusThick`.

**The geometry of the case `a > b` of `M°(e+1)`, in lattice coordinates** (pure lemmas over the reals; part 1 of the new argument of S+).
Notation: `p(ξ, η) = lpG e f 1 0 ξ η`, `a = e f`, `b = f² − e²`, `c = f²`, `K = 2f² − e²`, `s₀ = K / b`.
The line `S` of the new argument is the line through `Q = p(0, 1)` and `R = p(−1, s₀)` (the `a`-edge of the mirror tile `T`).
* `gA_lpG`: the form of the side `A'A` of the corner `2α` on the lattice: `t e √(4f²−e²) f² (K ξ + b η)`.
* `Fs`, `Fs_lp`: a functional constant on `S`, `Fs = b GHG − f² FXG`; `Fs p(ξ, η) = −f² h (b η + f² ξ)`.
* `Wst`: the lattice point `p(−b/a, 1 + f²/a)` on `S`, at the distance `b` from `Q` and `c` from `Z_1 = p(e/f, 1)`.

Credit: Beeson-Rosu (framework), the E2R6 room, Chisel, the S+ audit.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGMo

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SplusThick

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

/-! ## 1. The form of the side `A'A` on the lattice -/

/-- `g_A (p(ξ, η)) = t e √(4f² − e²) f² (K ξ + b η)` for the apex `t (K² − 2f⁴, e K √(4f²−e²))` -/
theorem gA_lpG (e f t ξ η : ℝ) (he : 0 < e) (hef : e < f) :
    gA (t * ((2 * f ^ 2 - e ^ 2) ^ 2 - 2 * f ^ 4)) (t * (e * (2 * f ^ 2 - e ^ 2) * rtG e f))
        (lpG e f 1 0 ξ η)
      = t * e * rtG e f * f ^ 2 * ((2 * f ^ 2 - e ^ 2) * ξ + (f ^ 2 - e ^ 2) * η) := by
  have hf : f ≠ 0 := by have := he.trans hef; exact this.ne'
  unfold lpG
  rw [gA_mk]
  unfold uuG hhG
  field_simp
  ring

/-! ## 2. A functional constant on `S` -/

/-- the functional `b GHG − f² FXG`: constant on the lines of direction `(−1, f²/b)` of the lattice -/
noncomputable def Fs (e f : ℝ) : Plane →ₗ[ℝ] ℝ := (f ^ 2 - e ^ 2) • GHG f - f ^ 2 • FXG e f 1

theorem Fs_lp (e f ξ η : ℝ) :
    Fs e f (lpG e f 1 0 ξ η) = -(f ^ 2 * hhG e f) * ((f ^ 2 - e ^ 2) * η + f ^ 2 * ξ) := by
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  unfold Fs
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, GHG_lp, FXG_lp hε]
  unfold lvG
  simp only [smul_eq_mul]
  ring

theorem Fs_ne (e f : ℝ) (he : 0 < e) (hef : e < f) : Fs e f ≠ 0 := by
  intro h
  have h1 := Fs_lp e f 0 1
  rw [h] at h1
  simp only [LinearMap.zero_apply] at h1
  have hf : 0 < f := he.trans hef
  have := nhG_pos he hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have h2 : 0 < (f ^ 2 * hhG e f) * ((f ^ 2 - e ^ 2) * 1 + f ^ 2 * 0) := by positivity
  linarith


/-! ## 3. The point `W* = p(−b/a, 1 + f²/a)` -/

/-- `W*` is at the distance `b` from `Q = p(0,1)` -/
theorem dist_Wst_Q (e f : ℝ) (he : 0 < e) (hef : e < f) :
    dist (lpG e f 1 0 (-((f ^ 2 - e ^ 2) / (e * f))) (1 + f ^ 2 / (e * f))) (lpG e f 1 0 0 1)
      = f ^ 2 - e ^ 2 := by
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hf : 0 < f := he.trans hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  refine dist_lpG he hef hε hb.le ?_
  unfold QfG
  field_simp
  ring

/-- `W*` is at the distance `c` from `Z_1 = p(e/f, 1)` -/
theorem dist_Wst_Z (e f : ℝ) (he : 0 < e) (hef : e < f) :
    dist (lpG e f 1 0 (-((f ^ 2 - e ^ 2) / (e * f))) (1 + f ^ 2 / (e * f))) (lpG e f 1 0 (e / f) 1)
      = f ^ 2 := by
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hf : 0 < f := he.trans hef
  refine dist_lpG he hef hε (by positivity) ?_
  unfold QfG
  field_simp
  ring

theorem Fs_Wst (e f : ℝ) (he : 0 < e) (hef : e < f) :
    Fs e f (lpG e f 1 0 (-((f ^ 2 - e ^ 2) / (e * f))) (1 + f ^ 2 / (e * f)))
      = -(f ^ 2 * hhG e f) * ((f ^ 2 - e ^ 2) * 1 + f ^ 2 * 0) := by
  have hf : 0 < f := he.trans hef
  rw [Fs_lp]
  congr 1
  field_simp
  ring

theorem Fs_Z (e f : ℝ) (he : 0 < e) (hef : e < f) :
    Fs e f (lpG e f 1 0 (e / f) 1) < -(f ^ 2 * hhG e f) * ((f ^ 2 - e ^ 2) * 1 + f ^ 2 * 0) := by
  have hf : 0 < f := he.trans hef
  rw [Fs_lp]
  have h := nhG_pos he hef
  have : 0 < (f ^ 2 * hhG e f) * (f ^ 2 * (e / f)) := by positivity
  nlinarith


/-! ## 4. The clamps of `S = [Q, R]` -/

section clamps

variable {N : ℕ} {D : CongruentDissection N}

/-- **the left end of `S` is clamped by `X_0 = U(0,0)`** (the backward ray from `Q` along `S` is interior to `X_0`): with `δ > 0`,
`δ s₀ < 1`, `s₀ > 2`, the open segment from `P' = p(δ, 1 − δ (s₀ − 1))` to `Q = p(0, 1)` is interior to `X_0`. -/
theorem left_clamp_S {e f s₀ δ : ℝ} {tX : Fin N}
    (hX : HasV D tX (lpG e f 1 0 0 0) (lpG e f 1 0 1 0) (lpG e f 1 0 0 1))
    (hs : 2 < s₀) (hδ : 0 < δ) (hδs : δ * s₀ < 1) :
    openSegment ℝ (lpG e f 1 0 δ (1 - δ * (s₀ - 1))) (lpG e f 1 0 0 1)
      ⊆ interior (D.tile tX).carrier := by
  intro y hy
  rw [openSegment_eq_image_lineMap] at hy
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
  rw [lineMap_lpG]
  have hk0 : 0 < δ * (1 - τ) := mul_pos hδ (by linarith)
  have hkd : δ * (1 - τ) < δ := by nlinarith
  have e' : lpG e f 1 0 (δ + τ * (0 - δ)) ((1 - δ * (s₀ - 1)) + τ * (1 - (1 - δ * (s₀ - 1))))
      = (δ * (1 - τ) * (s₀ - 2)) • lpG e f 1 0 0 0 + (δ * (1 - τ)) • lpG e f 1 0 1 0
        + (1 - (s₀ - 1) * (δ * (1 - τ))) • lpG e f 1 0 0 1 := by
    unfold lpG
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
  rw [e']
  refine hasV_bary hX (mul_pos hk0 (by linarith)) hk0 ?_ (by ring)
  nlinarith

/-- **beyond `R` the line `S` leaves Δ** (`g_A` is `t e √ f² (K ξ + b η)`, which is `0` at `R = p(−1, s₀)`, `s₀ b = K`, and decreases along `S`) -/
theorem right_out_S {e f s₀ δ : ℝ} {α β γ L ax ay : ℝ} {e' f' : ℕ}
    (S : SetupG D e' f' α β γ L ax ay) (he : 0 < e) (hef : e < f)
    (hs : s₀ * (f ^ 2 - e ^ 2) = 2 * f ^ 2 - e ^ 2) (hδ : 0 < δ)
    (hA2 : ∃ t : ℝ, 0 < t ∧ ax = t * ((2 * f ^ 2 - e ^ 2) ^ 2 - 2 * f ^ 4) ∧
      ay = t * (e * (2 * f ^ 2 - e ^ 2) * rtG e f)) :
    ∀ y ∈ openSegment ℝ (lpG e f 1 0 (-1 - δ) (s₀ + δ * (s₀ - 1))) (lpG e f 1 0 (-1) s₀),
      y ∉ D.target.carrier := by
  intro y hy hmem
  obtain ⟨t, ht, hax, hay⟩ := hA2
  rw [openSegment_eq_image_lineMap] at hy
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
  rw [lineMap_lpG] at hmem
  have hg := (S.mem hmem).2.1
  rw [hax, hay, gA_lpG e f t _ _ he hef] at hg
  have hf : 0 < f := he.trans hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hr := rtG_pos he hef
  have hval : (2 * f ^ 2 - e ^ 2) * (-1 - δ + τ * (-1 - (-1 - δ))) +
      (f ^ 2 - e ^ 2) * (s₀ + δ * (s₀ - 1) + τ * (s₀ - (s₀ + δ * (s₀ - 1))))
      = -(δ * (1 - τ)) * (f ^ 2 - e ^ 2) := by
    linear_combination (1 + δ * (1 - τ)) * hs
  have hk : 0 < δ * (1 - τ) := mul_pos hδ (by linarith)
  rw [hval] at hg
  have : 0 < t * e * rtG e f * f ^ 2 := by positivity
  nlinarith [mul_pos this (mul_pos hk hb)]

end clamps


/-! ## 5. The case `a^f` of `M°(e+1)` when `b < a` -/

section main

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ}

local notation "ee" => (e : ℝ)
local notation "ff" => (f : ℝ)

/-- a natural-number representation of `j a` from a real one (the analogue of `SideRunGRow.rep_nat_c`) -/
theorem rep_nat_a {e f j x y z : ℕ} (hef : e < f)
    (h : (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2
      = (j : ℝ) * ((e : ℝ) * f)) :
    x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = j * (e * f) := by
  have hle : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  have h' : ((x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 : ℕ) : ℝ) = ((j * (e * f) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle]
    linarith [h]
  exact_mod_cast h'

set_option maxHeartbeats 1600000 in
/-- **THE CASE `a^f` OF `M°(e+1)` FOR `b < a`** (the new argument of S+): the first tile `Y` above `Λ` has its `b`-edge `[Q, W]` along the `a`-edge `S = [Q, R]` of the mirror tile `T`
(`W = p(−b/a, 1 + f²/a)` inside `S` since `b < a`); by (P) (`run_partition`) the tile edges on the `Y` side of `S` sum to `a`; they are `a`, `b` or `c`; Lemma `Aa` with `j = 1` leaves a single
edge `a`; but `Y` contributes an edge `b ≠ a`. (Conclusion `False`.) -/
theorem aF_false_thick (S : SetupG D e f α β γ L ax ay)
    (W : StepCtxO D e f α β γ L ax ay 0 (e + 1) 0)
    (hba : ff ^ 2 - ee ^ 2 < ee * ff)
    (hA2 : ∃ t : ℝ, 0 < t ∧ ax = t * ((2 * ff ^ 2 - ee ^ 2) ^ 2 - 2 * ff ^ 4) ∧
      ay = t * (ee * (2 * ff ^ 2 - ee ^ 2) * rtG ee ff))
    (hall : RowLenAll D ee ff 0 0 e (ee * ff)) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hb := S.b_pos
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hq : e + 0 + 1 = e + 1 := rfl
  have h0 := a_all_A2 W (q := e) hq rfl hall (f - 1) 0 (by have := S.hef; omega)
  obtain ⟨tY, Wp, hY, hlt, hle, dQ, dZ⟩ := h0
  have hQeq : Zp ee ff 0 0 0 = lpG ee ff 1 0 0 1 := lpG_congr (by simp) (by simp)
  have hZeq : Zp ee ff 0 0 (0 + 1) = lpG ee ff 1 0 (ee / ff) 1 := lpG_congr (by simp) (by simp)
  rw [hQeq, hZeq] at hY
  rw [hQeq] at dQ
  rw [hZeq] at dZ
  -- the mirror tile and `X_0`
  obtain ⟨tT, hT⟩ := W.hM
  have hs := mirK_mul S
  have hs2 : 2 < mirK ee ff := mirK_gt_two S
  have hT' : HasV D tT (lpG ee ff 1 0 0 0) (lpG ee ff 1 0 0 1) (lpG ee ff 1 0 (-1) (mirK ee ff)) :=
    HasV.congr hT (lpG_congr rfl (by simp)) (lpG_congr rfl (by simp)) (lpG_congr rfl (by simp [mirK]))
  obtain ⟨tX, hX⟩ := W.hK2.1 0 0 le_rfl (by omega)
  have hX' : HasV D tX (lpG ee ff 1 0 0 0) (lpG ee ff 1 0 1 0) (lpG ee ff 1 0 0 1) :=
    HasV.congr hX (lpG_congr (by simp) (by simp)) (lpG_congr (by simp) (by simp))
      (lpG_congr (by simp) (by simp))
  -- notation
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ = mirK ee ff := ⟨_, rfl⟩
  rw [← hs₀] at hs hs2 hT'
  have hbs : ff ^ 2 - ee ^ 2 ≠ 0 := hb.ne'
  have hr1 : (ff ^ 2 - ee ^ 2) * (s₀ - 1) = ff ^ 2 := by linear_combination hs
  have hQ0 := Fs_lp ee ff 0 1
  -- `Wp = W*`
  have hWeq : Wp = lpG ee ff 1 0 (-((ff ^ 2 - ee ^ 2) / (ee * ff))) (1 + ff ^ 2 / (ee * ff)) := by
    have hZQ : lpG ee ff 1 0 (ee / ff) 1 - lpG ee ff 1 0 0 1 = mkPt (ee * ff) 0 := by
      unfold lpG
      apply plane_ext <;> simp only [PiLp.sub_apply, mkPt_zero, mkPt_one] <;> field_simp <;> ring
    refine third_unique_F (GHG ff) (P := lpG ee ff 1 0 0 1) (Q := lpG ee ff 1 0 (ee / ff) 1)
      (c := GHG ff (lpG ee ff 1 0 0 1)) (κ := -(ee / ff)) ?_ ?_ rfl ?_ ?_ ?_ ?_
    · have := div_pos he0 hf0; linarith
    · intro y
      rw [hZQ, GHG_apply]
      simp only [cross, mkPt_zero, mkPt_one]
      field_simp
      ring
    · rw [dQ, dist_Wst_Q ee ff he0 hef]
    · rw [dZ, dist_Wst_Z ee ff he0 hef]
    · rw [GHG_lp]
      have := hlt
      simpa using this
    · rw [GHG_lp, GHG_lp]
      have h := nhG_pos he0 hef
      have : 0 < ff ^ 2 / (ee * ff) := by positivity
      nlinarith [mul_pos h this]
  -- the points of `S`
  have hdQR : dist (lpG ee ff 1 0 (-1) s₀) (lpG ee ff 1 0 0 1) = ee * ff := by
    have := dist_mirrorQ he0 hef hε (x := 0) 0 s₀ hs
    simpa using this
  have hQR : lpG ee ff 1 0 0 1 ≠ lpG ee ff 1 0 (-1) s₀ := lpG_ne_xi he0 hef hε (by norm_num)
  have hτ0 : 0 < (ff ^ 2 - ee ^ 2) / (ee * ff) := by positivity
  have hτ1 : (ff ^ 2 - ee ^ 2) / (ee * ff) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hWS : Wp ∈ segment ℝ (lpG ee ff 1 0 0 1) (lpG ee ff 1 0 (-1) s₀) := by
    rw [hWeq]
    have h := lp_mem_segG (e := ee) (f := ff) (ε := 1) (x := 0) (ξ := 0) (η := 1) (ξ' := -1) (η' := s₀)
      hτ0.le hτ1
    have e1 : (0 : ℝ) + (ff ^ 2 - ee ^ 2) / (ee * ff) * (-1 - 0) = -((ff ^ 2 - ee ^ 2) / (ee * ff)) := by ring
    have e2 : (1 : ℝ) + (ff ^ 2 - ee ^ 2) / (ee * ff) * (s₀ - 1) = 1 + ff ^ 2 / (ee * ff) := by
      field_simp
      linear_combination hr1
    rw [e1, e2] at h
    exact h
  -- the functional
  have hFs : Fs ee ff ≠ 0 := Fs_ne ee ff he0 hef
  have hc0 : Fs ee ff (lpG ee ff 1 0 0 1) = -(ff ^ 2 * hhG ee ff) * ((ff ^ 2 - ee ^ 2) * 1 + ff ^ 2 * 0) :=
    Fs_lp ee ff 0 1
  have hcR : Fs ee ff (lpG ee ff 1 0 (-1) s₀) = Fs ee ff (lpG ee ff 1 0 0 1) := by
    rw [Fs_lp, hc0]; congr 1; linear_combination hs
  -- the clamp parameter
  obtain ⟨δ, hδ0, hδs⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * s₀ < 1 :=
    ⟨1 / (2 * s₀), by positivity, by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith⟩
  have hP'F : Fs ee ff (lpG ee ff 1 0 δ (1 - δ * (s₀ - 1))) = Fs ee ff (lpG ee ff 1 0 0 1) := by
    rw [Fs_lp, hc0]; congr 1; linear_combination (-δ) * hr1
  have hQ'F : Fs ee ff (lpG ee ff 1 0 (-1 - δ) (s₀ + δ * (s₀ - 1))) = Fs ee ff (lpG ee ff 1 0 0 1) := by
    rw [Fs_lp, hc0]; congr 1; linear_combination hs + δ * hr1
  have hP'mem : lpG ee ff 1 0 0 1 ∈ openSegment ℝ (lpG ee ff 1 0 δ (1 - δ * (s₀ - 1)))
      (lpG ee ff 1 0 (-1) s₀) := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨δ / (1 + δ), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith
    · rw [lineMap_lpG]
      refine lpG_congr ?_ ?_
      · field_simp; ring
      · field_simp; ring
  have hQ'mem : lpG ee ff 1 0 (-1) s₀ ∈ openSegment ℝ (lpG ee ff 1 0 0 1)
      (lpG ee ff 1 0 (-1 - δ) (s₀ + δ * (s₀ - 1))) := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨1 / (1 + δ), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith
    · rw [lineMap_lpG]
      refine lpG_congr ?_ ?_
      · field_simp; ring
      · field_simp; ring
  -- membership and positivity
  obtain ⟨t, ht, hax, hay'⟩ := hA2
  have hQm : lpG ee ff 1 0 0 1 = mkPt (ff ^ 2 - uuG ee ff) (hhG ee ff) := by
    unfold lpG; exact mkPt_congr (by ring) (by ring)
  have hZm : lpG ee ff 1 0 (ee / ff) 1 = mkPt (ff ^ 2 - uuG ee ff + ee * ff) (hhG ee ff) := by
    unfold lpG; exact mkPt_congr (by field_simp; ring) (by ring)
  have hQmem : lpG ee ff 1 0 0 1 ∈ D.target.carrier := hT'.mem₂
  have hRmem : lpG ee ff 1 0 (-1) s₀ ∈ D.target.carrier := hT'.mem₃
  have hh := hhG_pos he0 hef
  have hy1 : 0 < (lpG ee ff 1 0 0 1) 1 := by rw [hQm, mkPt_one]; exact hh
  have hgA : 0 < gA ax ay (lpG ee ff 1 0 0 1) := by
    rw [hax, hay', gA_lpG ee ff t _ _ he0 hef]
    have h1 : 0 < t * ee * rtG ee ff * ff ^ 2 := by
      have := rtG_pos he0 hef
      positivity
    have h2 : t * ee * rtG ee ff * ff ^ 2 * ((2 * ff ^ 2 - ee ^ 2) * 0 + (ff ^ 2 - ee ^ 2) * 1)
        = t * ee * rtG ee ff * ff ^ 2 * (ff ^ 2 - ee ^ 2) := by ring
    rw [h2]; exact mul_pos h1 hb
  have hgB : 0 < gB L ax ay (lpG ee ff 1 0 0 1) := by
    rw [hQm]
    refine S.gB_pos_of_right (t := ee * ff) (by positivity) ?_
    rw [← hZm]; exact hY.mem₂
  have hint := S.interior_seg hQmem hRmem (Or.inl hy1) (Or.inl hgA) (Or.inl hgB)
  have hwall : ∀ y ∈ openSegment ℝ (lpG ee ff 1 0 0 1) (lpG ee ff 1 0 (-1) s₀),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hT'
    refine seg_wall D.toDissection (t := tT) hmj ?_
    rw [hm, hj]
    exact openSegment_subset_segment ℝ _ _ hy
  have hS := CSlot.segment_subset_level (Fs ee ff) (Fs ee ff (lpG ee ff 1 0 0 1)) (u := lpG ee ff 1 0 0 1)
    (v := lpG ee ff 1 0 (-1) s₀) rfl hcR
  have hLeft : ∀ ed ∈ D.lineChain (Fs ee ff) (Fs ee ff (lpG ee ff 1 0 0 1)),
      ¬ Straddles ((D.tile ed.1).edge ed.2) (lpG ee ff 1 0 δ (1 - δ * (s₀ - 1))) (lpG ee ff 1 0 0 1)
        (lpG ee ff 1 0 (-1) s₀) :=
    fun ed _ => not_straddles_of_interior D.toDissection (j := tX) (left_clamp_S hX' hs2 hδ0 hδs)
      ed.1 ed.2
  have hRight : ∀ ed ∈ D.lineChain (Fs ee ff) (Fs ee ff (lpG ee ff 1 0 0 1)),
      ¬ Straddles ((D.tile ed.1).edge ed.2) (lpG ee ff 1 0 (-1 - δ) (s₀ + δ * (s₀ - 1)))
        (lpG ee ff 1 0 (-1) s₀) (lpG ee ff 1 0 0 1) :=
    fun ed _ => not_straddles_of_outside D.toDissection
      (right_out_S S he0 hef hs hδ0 ⟨t, ht, hax, hay'⟩) ed.1 ed.2
  have hpart := run_partition D.toDissection (Fs ee ff) hFs _ hQR hP'F hQ'F hP'mem hQ'mem hS hint hwall
    hLeft hRight
  rw [dist_comm, hdQR] at hpart
  -- the edge of `Y` along `S`
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hY
  have hcov := fin3_cover k m j hkm hkj hmj
  have hFW : Fs ee ff Wp = Fs ee ff (lpG ee ff 1 0 0 1) := by
    rw [hWeq, Fs_Wst ee ff he0 hef, hc0]
  have hFZ : Fs ee ff (lpG ee ff 1 0 (ee / ff) 1) < Fs ee ff (lpG ee ff 1 0 0 1) := by
    rw [hc0]; exact Fs_Z ee ff he0 hef
  have hYle : ∀ i, Fs ee ff ((D.tile tY).pts i) ≤ Fs ee ff (lpG ee ff 1 0 0 1) := by
    intro i
    rcases hcov i with h | h | h
    · rw [h, hk]
    · rw [h, hm]; exact hFZ.le
    · rw [h, hj, hFW]
  obtain ⟨i0, hi0⟩ := tile_edge_of_pair (D.tile tY) hkj
  have hed : (tY, i0) ∈ D.lineChain (Fs ee ff) (Fs ee ff (lpG ee ff 1 0 0 1)) := by
    refine Dissection.mem_lineChain.mpr ⟨?_, ?_, hYle⟩
    · show Fs ee ff ((D.tile tY).pts i0) = _
      rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, hk]
      · rw [h1, hj, hFW]
    · show Fs ee ff ((D.tile tY).pts (i0 + 1)) = _
      rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, hj, hFW]
      · rw [h2, hk]
  have hQS : lpG ee ff 1 0 0 1 ∈ segment ℝ (lpG ee ff 1 0 0 1) (lpG ee ff 1 0 (-1) s₀) :=
    left_mem_segment ℝ _ _
  have hsub : (D.tile tY).edge i0 ⊆ segment ℝ (lpG ee ff 1 0 0 1) (lpG ee ff 1 0 (-1) s₀) := by
    show segment ℝ ((D.tile tY).pts i0) ((D.tile tY).pts (i0 + 1)) ⊆ _
    rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hk, hj]; exact (convex_segment _ _).segment_subset hQS hWS
    · rw [h1, h2, hk, hj]; exact (convex_segment _ _).segment_subset hWS hQS
  have hlenY : dist ((D.tile tY).pts i0) ((D.tile tY).pts (i0 + 1)) = ff ^ 2 - ee ^ 2 := by
    rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hk, hj, dist_comm]; exact dQ
    · rw [h1, h2, hk, hj]; exact dQ
  -- the counting
  obtain ⟨Sf, hSf⟩ : ∃ Sf : Finset (Fin N × Fin 3), Sf = (D.lineChain (Fs ee ff) (Fs ee ff (lpG ee ff 1 0 0 1))).filter
      (fun ed => (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG ee ff 1 0 0 1) (lpG ee ff 1 0 (-1) s₀)) :=
    ⟨_, rfl⟩
  have hpart' : ∑ ed ∈ Sf, dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = ee * ff := by
    rw [hSf]; exact hpart
  have hlen : ∀ ed ∈ Sf, dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = ee * ff ∨
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = ff ^ 2 - ee ^ 2 ∨
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = ff ^ 2 :=
    fun ed _ => edge_length_casesG D S.hM ed.1 ed.2
  have hac : ee * ff ≠ ff ^ 2 := by
    intro h
    nlinarith [mul_pos hf0 (sub_pos.mpr hef)]
  have hcnt := sum_counts Sf (fun ed => dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1))) hac hlen
  have heq := hpart'.symm.trans hcnt
  have hnat := rep_nat_a S.hef (j := 1) (x := (Sf.filter (fun ed => dist ((D.tile ed.1).pts ed.2)
      ((D.tile ed.1).pts (ed.2 + 1)) = ee * ff)).card)
    (y := (Sf.filter (fun ed => ¬ dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = ee * ff ∧
      ¬ dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = ff ^ 2)).card)
    (z := (Sf.filter (fun ed => dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = ff ^ 2)).card)
    (by rw [Nat.cast_one, one_mul]; exact heq.symm)
  obtain ⟨-, hy0, -⟩ := SideRunGArith.Aa S.he S.hef S.hco (j := 1) le_rfl
    (by have := S.hf2; omega) hnat
  have hmem : (tY, i0) ∈ Sf.filter (fun ed => ¬ dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = ee * ff ∧
      ¬ dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = ff ^ 2) := by
    rw [Finset.mem_filter, hSf, Finset.mem_filter]
    refine ⟨⟨hed, hsub⟩, ?_, ?_⟩ <;> rw [hlenY]
    · intro h; linarith
    · intro h; have := pow_pos he0 2; linarith
  rw [Finset.card_eq_zero.mp hy0] at hmem
  simp at hmem

end main

end Erdos634.Draft.SplusThick

#print axioms Erdos634.Draft.SplusThick.gA_lpG
#print axioms Erdos634.Draft.SplusThick.dist_Wst_Q
#print axioms Erdos634.Draft.SplusThick.dist_Wst_Z
#print axioms Erdos634.Draft.SplusThick.left_clamp_S
#print axioms Erdos634.Draft.SplusThick.right_out_S
#print axioms Erdos634.Draft.SplusThick.aF_false_thick
