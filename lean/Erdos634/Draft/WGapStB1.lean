/-
Draft/WGapStB1.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.3).
Not imported by any aggregate.  STATION port of `WGapB1` (lattice origin `x`, absolute levels, floor `J0`); see WGapStInv1.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapB1
import Erdos634.Draft.WGapWL2

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapSt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set Erdos634.Draft.WGapStmt

variable {N : ℕ} {D : CongruentDissection N}

open Erdos634.Draft.WGapStmt hiding sj BotClamp Inv Unfl Flip utm_cast nearOK_inv level_known inv_hint_wall level_data ha_succ hDp_succ unfl_utm inv_step top_pt top_clamp hthird_of_inv ub ClampB FlipAt Bst bst_self ub_norm ub_ne clampB_outside clampB_tile

/-- the downward `b`-step along `l'_c` at `p'(c,js)` -/
noncomputable def ub (e f : ℕ) (x : ℝ) (c js : ℕ) : Plane :=
  mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) - mpG (e : ℝ) f 1 x (c : ℝ) ((js : ℝ) + 1)

/-- the far-side clamp of `X0 = p'(c,js)` along `l'_c` -/
def ClampB (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (c js : ℕ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ ed ∈ D.lineChain (crossL (ub e f x c js)) (cross (ub e f x c js) (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ))),
    ¬ Straddles ((D.tile ed.1).edge ed.2) (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) + ub e f x c js)
      (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ)) (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) - t • ub e f x c js)

/-- the far-side `c`-edge tile at `X0 = p'(c,js)` (the flipped tile) -/
def FlipAt (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (c js : ℕ) : Prop :=
  ∃ τ, HasV D τ (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ)) (mpG (e : ℝ) f 1 x ((c : ℝ) + nuG (e : ℝ) f) (js : ℝ))
    (mpG (e : ℝ) f 1 x (c : ℝ) ((js : ℝ) + 1 / nuG (e : ℝ) f))

/-- **The structure (b) of the station invariant**: for `c + J0 < j` there is `js ≥ J0` (the row of `X0 = p'(c,js)`) with `c + js + 1 <= j`, a far-side
`c`-edge tile at `X0`, clamped (wall or the `b`-edge of `U'(c, js-1)`), and the near-side tiles `D'(c-1, i')` for `js <= i' <= j-1-c`. -/
def Bst (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (J0 : ℕ) (j c : ℕ) : Prop :=
  c + J0 < j → ∃ js : ℕ, J0 ≤ js ∧ c + js + 1 ≤ j ∧ FlipAt D e f x c js ∧ ClampB D e f x c js ∧
    ∀ i' : ℕ, js ≤ i' → c + i' + 1 ≤ j → DTM D (e : ℝ) f 1 x ((c - 1 : ℕ) : ℝ) (i' : ℝ)

theorem bst_self (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (J0 j c : ℕ) (h : j ≤ c + J0) : Bst D e f x J0 j c :=
  fun h' => absurd h' (by omega)

section b1

variable {e f : ℕ} {α β γ L ax ay : ℝ} {x : ℝ} {J0 : ℕ}

theorem ub_norm (S : SetupG D e f α β γ L ax ay) (c js : ℕ) : ‖ub e f x c js‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  unfold ub
  rw [← dist_eq_norm]
  exact dist_mp_v S.e0 S.hef' (by norm_num) _ _

theorem ub_ne (S : SetupG D e f α β γ L ax ay) (c js : ℕ) : ub e f x c js ≠ 0 := by
  intro h
  have := ub_norm (x := x) S c js
  rw [h, norm_zero] at this
  have hb := S.b_pos
  linarith

/-- **[SIDE-2] at a station**: the clamp of `X0 = p'(c,J0)` along `l'_c` from the wall tile (`EdgeCover` at `q'(c,J0)`, `Wall Lemma`) -/
theorem clampB_wall (S : SetupG D e f α β γ L ax ay) (c : ℕ)
    (hW : EdgeCover D (mpG (e : ℝ) f 1 x (c : ℝ) (J0 : ℝ)) (mpG (e : ℝ) f 1 x 1 (J0 : ℝ) - mpG (e : ℝ) f 1 x 0 (J0 : ℝ))) :
    ClampB D e f x c J0 := by
  intro t ht ed _
  obtain ⟨φ, -, -, hpush⟩ := hW
  have hκ := kapG_pos S.e0 S.hef'
  have hcr : 0 < cross (mpG (e : ℝ) f 1 x 1 (J0 : ℝ) - mpG (e : ℝ) f 1 x 0 (J0 : ℝ)) (ub e f x c J0) := by
    unfold ub
    rw [cross_mpG S.e0 S.hef']
    nlinarith
  obtain ⟨ε₀, hε₀, hp⟩ := hpush _ hcr
  refine not_straddles_short D.toDissection (j := φ) hε₀ ht ?_ ?_ ed.1 ed.2
  · simp
  · intro ε h0 h1
    have := hp ε h0 h1
    simpa using this

set_option maxHeartbeats 1000000 in
/-- the clamp of `X0 = p'(c,js)` (`js >= 1`) from the far-side tile `U'(c, js-1)` (its `b`-edge is the extension below `X0`) -/
theorem clampB_tile (S : SetupG D e f α β γ L ax ay) {c js : ℕ} (hjs : 1 ≤ js)
    (hU : UTM D (e : ℝ) f 1 x (c : ℝ) (((js - 1 : ℕ)) : ℝ)) : ClampB D e f x c js := by
  intro t ht ed hed
  obtain ⟨j₁, hj⟩ := hU
  have hcast : (((js - 1 : ℕ)) : ℝ) = (js : ℝ) - 1 := by rw [Nat.cast_sub hjs]; simp
  rw [hcast] at hj
  obtain ⟨O, E1, E2, hm⟩ := mpG_affine_x S.e0 S.hef' x
  set X₀ := mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) with hX₀
  set u := ub e f x c js with hu
  have hP' : mpG (e : ℝ) f 1 x (c : ℝ) ((js : ℝ) - 1) = X₀ + u := by
    rw [hX₀, hu]; unfold ub; simp only [hm]
    ext x; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  have hC : mpG (e : ℝ) f 1 x (c : ℝ) ((js : ℝ) - 1 + 1) = X₀ := by rw [hX₀]; exact mpG_congr' rfl (by ring)
  have hj' : HasV D j₁ (X₀ + u) X₀ (mpG (e : ℝ) f 1 x ((c : ℝ) + 1) ((js : ℝ) - 1)) := by
    have := hj.rot.rot.swap
    exact hasV_congr this hP'.symm.symm hC rfl
  obtain ⟨k₁, hk₁⟩ := hasV_edge_eq hj'
  have hu0 : u ≠ 0 := ub_ne S c js
  set F := crossL u with hF
  set cc := cross u X₀ with hcc
  have hFX : F X₀ = cc := crossL_apply _ _
  have hFu : F u = 0 := by rw [hF, crossL_apply]; simp [cross]; ring
  have hFl : ∀ s : ℝ, F (X₀ + s • u) = cc := by
    intro s; rw [map_add, map_smul, hFu, hFX]; simp
  have hFP' : F (X₀ + u) = cc := by simpa using hFl 1
  have hFQ : F (X₀ - t • u) = cc := by
    have := hFl (-t); simpa [sub_eq_add_neg] using this
  have hcrossB : cross u (mpG (e : ℝ) f 1 x ((c : ℝ) + 1) ((js : ℝ) - 1) - X₀) < 0 := by
    rw [hu, hX₀]; unfold ub
    rw [cross_mpG S.e0 S.hef']
    have := kapG_pos S.e0 S.hef'
    nlinarith
  have hFB : F (mpG (e : ℝ) f 1 x ((c : ℝ) + 1) ((js : ℝ) - 1)) ≤ cc := by
    have h1 : F (mpG (e : ℝ) f 1 x ((c : ℝ) + 1) ((js : ℝ) - 1)) =
        cross u (mpG (e : ℝ) f 1 x ((c : ℝ) + 1) ((js : ℝ) - 1) - X₀) + cc := by
      rw [hF, crossL_apply, hcc, ← cross_add_right]; congr 1; abel
    linarith
  have hle₁ : ∀ y ∈ (D.tile j₁).carrier, F y ≤ cc :=
    Tri.carrier_subset_halfplane (D.tile j₁) F cc (hj'.all (P := fun z => F z ≤ cc) (le_of_eq hFP') (le_of_eq hFX) hFB)
  have hE₁ : ∀ y ∈ (D.tile j₁).edge k₁, F y = cc := by
    intro y hy
    rw [hk₁] at hy
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    rw [map_add, map_smul, map_smul, hFP', hFX]
    simp only [smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  have hPQ : X₀ ≠ X₀ - t • u := by
    intro h
    have : t • u = 0 := by
      have := congrArg (fun z => X₀ - z) h
      simpa using this.symm
    rcases smul_eq_zero.mp this with h0 | h0
    · exact ht.ne' h0
    · exact hu0 h0
  have hP'mem : X₀ ∈ openSegment ℝ (X₀ + u) (X₀ - t • u) := by
    refine ⟨t / (1 + t), 1 / (1 + t), by positivity, by positivity, by field_simp; ring, ?_⟩
    ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    ring
  by_cases hee : ed = (j₁, k₁)
  · rintro ⟨-, z, hzE, hzQ⟩
    rw [hee] at hzE
    rw [hk₁] at hzE
    obtain ⟨a, b, ha, hb, hab, hz1⟩ := hzE
    obtain ⟨c', d, hc', hd, hcd, hz2⟩ := hzQ
    have hb' : b = 1 - a := by linarith
    have hc'' : c' = 1 - d := by linarith
    subst hb' hc''
    have hz : (a + d * t) • u = 0 := by
      have e := hz1.trans hz2.symm
      ext x
      have := congrArg (fun z => z x) e
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, PiLp.zero_apply] at this ⊢
      nlinarith [this]
    rcases smul_eq_zero.mp hz with h0 | h0
    · nlinarith [mul_pos hd ht]
    · exact hu0 h0
  · exact not_straddles_of_sameside_edge D.toDissection F (Erdos634.Geometry.crossL_ne_zero hu0) cc hPQ hFX hFQ hFP' hP'mem hle₁ hE₁
      (by rw [hk₁]) hed hee


end b1

end Erdos634.Draft.WGapSt
