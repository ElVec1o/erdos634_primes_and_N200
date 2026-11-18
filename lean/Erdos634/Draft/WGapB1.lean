/-
Draft/WGapB1.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 invariant (b), [SIDE-2]).
Not imported by any aggregate.  Module P-D1: the structure (b) of the invariant and the clamp of the far-side `c`-edge's start `X0 = p'(c, js)` along the line `l'_c`:
* `ub e f c js = p'(c,js) - p'(c,js+1)` (the DOWNWARD b-step; tiles on `{crossL ub <= level}` are the FAR (left of `l'_c`) tiles), `ClampB`: no far-side chain edge straddles `X0` (extension below it, run above it, any length),
* `clampB_outside` ([SIDE-2], `js = 0`: the extension below `p'(c,0)` has `eta < 0`, outside the target by `mp_out`),
* `clampB_tile` (`js >= 1`: the far-side tile `U'(c, js-1)` has its b-edge `[p'(c,js-1), X0]` on the extension, `not_straddles_of_sameside_edge`),
* `Bst`: (b) of the invariant for `c < j`, with `FlipAt c js` the far-side `c`-edge tile at `X0`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapCase1a

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

variable {N : ℕ} {D : CongruentDissection N}

/-- the downward `b`-step along `l'_c` at `p'(c,js)` -/
noncomputable def ub (e f c js : ℕ) : Plane :=
  mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) - mpG (e : ℝ) f 1 0 (c : ℝ) ((js : ℝ) + 1)

/-- the far-side clamp of `X0 = p'(c,js)` along `l'_c`: no far-side chain edge straddles `X0` (extension below, run above of any length) -/
def ClampB (D : CongruentDissection N) (e f c js : ℕ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ ed ∈ D.lineChain (crossL (ub e f c js)) (cross (ub e f c js) (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ))),
    ¬ Straddles ((D.tile ed.1).edge ed.2) (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) + ub e f c js)
      (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ)) (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) - t • ub e f c js)

/-- the far-side `c`-edge tile at `X0 = p'(c,js)` (the flipped tile) -/
def FlipAt (D : CongruentDissection N) (e f c js : ℕ) : Prop :=
  ∃ τ, HasV D τ (mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ)) (mpG (e : ℝ) f 1 0 ((c : ℝ) + nuG (e : ℝ) f) (js : ℝ))
    (mpG (e : ℝ) f 1 0 (c : ℝ) ((js : ℝ) + 1 / nuG (e : ℝ) f))

/-- **The structure (b) of the invariant** (PROOF P5, I_j (b)): for `c < j` there is `js` with `c + js <= j - 1`, a far-side `c`-edge tile at `X0 = p'(c,js)`
clamped for the far side (SIDE-2 or the b-edge of `U'(c, js-1)`), and the near-side tiles `D'(c-1, i')` for `js <= i' <= j-1-c`. -/
def Bst (D : CongruentDissection N) (e f : ℕ) (j c : ℕ) : Prop :=
  c < j → ∃ js : ℕ, c + js + 1 ≤ j ∧ FlipAt D e f c js ∧ ClampB D e f c js ∧
    ∀ i' : ℕ, js ≤ i' → c + i' + 1 ≤ j → DTM D (e : ℝ) f 1 0 ((c - 1 : ℕ) : ℝ) (i' : ℝ)

theorem bst_self (D : CongruentDissection N) (e f j : ℕ) : Bst D e f j j := fun h => absurd h (lt_irrefl _)

section b1

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem ub_norm (S : SetupG D e f α β γ L ax ay) (c js : ℕ) : ‖ub e f c js‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  unfold ub
  rw [← dist_eq_norm]
  exact dist_mp_v S.e0 S.hef' (by norm_num) _ _

theorem ub_ne (S : SetupG D e f α β γ L ax ay) (c js : ℕ) : ub e f c js ≠ 0 := by
  intro h
  have := ub_norm S c js
  rw [h, norm_zero] at this
  have hb := S.b_pos
  linarith

/-- **[SIDE-2]** the clamp of `p'(c,0)` along `l'_c` (the extension below it is outside the target) -/
theorem clampB_outside (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (c : ℕ) : ClampB D e f c 0 := by
  intro t ht ed _
  refine not_straddles_of_outside D.toDissection ?_ ed.1 ed.2
  intro y hy
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  obtain ⟨O, E1, E2, hm⟩ := mpG_affine S.e0 S.hef'
  have hy : a • (mpG (e : ℝ) f 1 0 (c : ℝ) ((0 : ℕ) : ℝ) + ub e f c 0) + b • mpG (e : ℝ) f 1 0 (c : ℝ) ((0 : ℕ) : ℝ) =
      mpG (e : ℝ) f 1 0 (c : ℝ) (-a) := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    unfold ub
    simp only [hm]
    push_cast
    ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  rw [hy]
  exact mp_out S h2 (by linarith)

theorem hasV_edge_eq {t : Fin N} {A B C : Plane} (h : HasV D t A B C) :
    ∃ k : Fin 3, (D.tile t).edge k = segment ℝ A B := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  rcases fin3_adj k m hkm with h' | h'
  · refine ⟨k, ?_⟩
    simp only [Tri.edge]; rw [← h', hk, hm]
  · refine ⟨m, ?_⟩
    simp only [Tri.edge]; rw [← h', hk, hm, segment_symm]

set_option maxHeartbeats 1000000 in
/-- the clamp of `X0 = p'(c,js)` (`js >= 1`) from the far-side tile `U'(c, js-1)` (its `b`-edge is the extension below `X0`) -/
theorem clampB_tile (S : SetupG D e f α β γ L ax ay) {c js : ℕ} (hjs : 1 ≤ js)
    (hU : UTM D (e : ℝ) f 1 0 (c : ℝ) (((js - 1 : ℕ)) : ℝ)) : ClampB D e f c js := by
  intro t ht ed hed
  obtain ⟨j₁, hj⟩ := hU
  have hcast : (((js - 1 : ℕ)) : ℝ) = (js : ℝ) - 1 := by rw [Nat.cast_sub hjs]; simp
  rw [hcast] at hj
  obtain ⟨O, E1, E2, hm⟩ := mpG_affine S.e0 S.hef'
  set X₀ := mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) with hX₀
  set u := ub e f c js with hu
  have hP' : mpG (e : ℝ) f 1 0 (c : ℝ) ((js : ℝ) - 1) = X₀ + u := by
    rw [hX₀, hu]; unfold ub; simp only [hm]
    ext x; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  have hC : mpG (e : ℝ) f 1 0 (c : ℝ) ((js : ℝ) - 1 + 1) = X₀ := by rw [hX₀]; exact mpG_congr' rfl (by ring)
  have hj' : HasV D j₁ (X₀ + u) X₀ (mpG (e : ℝ) f 1 0 ((c : ℝ) + 1) ((js : ℝ) - 1)) := by
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
  have hcrossB : cross u (mpG (e : ℝ) f 1 0 ((c : ℝ) + 1) ((js : ℝ) - 1) - X₀) < 0 := by
    rw [hu, hX₀]; unfold ub
    rw [cross_mpG S.e0 S.hef']
    have := kapG_pos S.e0 S.hef'
    nlinarith
  have hFB : F (mpG (e : ℝ) f 1 0 ((c : ℝ) + 1) ((js : ℝ) - 1)) ≤ cc := by
    have h1 : F (mpG (e : ℝ) f 1 0 ((c : ℝ) + 1) ((js : ℝ) - 1)) =
        cross u (mpG (e : ℝ) f 1 0 ((c : ℝ) + 1) ((js : ℝ) - 1) - X₀) + cc := by
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
  · exact not_straddles_of_sameside_edge D.toDissection F (crossL_ne_zero hu0) cc hPQ hFX hFQ hFP' hP'mem hle₁ hE₁
      (by rw [hk₁]) hed hee

end b1

end Erdos634.Draft.WGapStmt
