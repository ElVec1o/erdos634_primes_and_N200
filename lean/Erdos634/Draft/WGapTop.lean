/-
Draft/WGapTop.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 "Top clamp", (U3-c)).
Not imported by any aggregate.  Module P-E4:
* `not_straddles_short` (the VARIANT of `not_straddles_of_interior` needed by the top clamp, Case 1 and the end of Case 3): if a SHORT initial piece of the extension `(P', P)` is
  interior to a tile, then no tile edge on the line straddles `P`.  (Straddles needs the edge to meet BOTH `(P', P)` and `(P, Q)`; the edge is convex, so it contains a short piece of the
  extension near `P`, which is interior to the tile.)  Setting: `Q = P - rho (P' - P)`, `rho > 0` (the three clamps of the chord have this shape).
* `top_clamp`: the clamp at `X0 = p(0,j)` for the far side (the hX of `chord_all`), from the tile `U(0,j-1)` (direction `e(gamma+pi)` is interior to it, `sMir > 2`).
* `hthird_of_inv`: (U3-c) at level `j <= J` from `Inv j c` via `chord_all`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapInv3

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

theorem not_straddles_short (D : Dissection N) {P' P Q : Plane} {j : Fin N} {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hQ : Q = P - ρ • (P' - P))
    (hj : ∀ ε : ℝ, 0 < ε → ε < δ → P + ε • (P' - P) ∈ interior (D.tile j).carrier) (i : Fin N) (k : Fin 3) :
    ¬ Straddles ((D.tile i).edge k) P' P Q := by
  rintro ⟨⟨y, hyE, hyP⟩, ⟨z, hzE, hzQ⟩⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hyP
  obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hzQ
  have hb' : b = 1 - a := by linarith
  have hc' : c = 1 - d := by linarith
  subst hb' hc' hQ
  set v := P' - P with hv
  have hy : a • P' + (1 - a) • P = P + a • v := by
    rw [hv]; ext x; simp; ring
  have hz : (1 - d) • P + d • (P - ρ • v) = P - (d * ρ) • v := by
    ext x; simp; ring
  rw [hy] at hyE
  rw [hz] at hzE
  set ε := min a δ / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; have := lt_min ha hδ; linarith
  have hεa : ε < a := by rw [hε]; have := min_le_left a δ; linarith [lt_min ha hδ]
  have hεδ : ε < δ := by rw [hε]; have := min_le_right a δ; linarith [lt_min ha hδ]
  have hdρ : 0 < d * ρ := mul_pos hd hρ
  set θ := (a - ε) / (a + d * ρ) with hθ
  have hden : 0 < a + d * ρ := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hden.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hden]; linarith
  have hconv : Convex ℝ ((D.tile i).edge k) := by
    unfold Geometry.Tri.edge; exact convex_segment _ _
  have hw : (1 - θ) • (P + a • v) + θ • (P - (d * ρ) • v) ∈ (D.tile i).edge k :=
    hconv hyE hzE (by linarith) hθ0 (by ring)
  have hweq : (1 - θ) • (P + a • v) + θ • (P - (d * ρ) • v) = P + ε • v := by
    have h1 : (1 - θ) * a - θ * (d * ρ) = ε := by
      rw [hθ]; field_simp; ring
    ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    have := congrArg (fun r => r * v x) h1
    simp only at this
    nlinarith [this]
  rw [hweq] at hw
  exact D.edge_point_not_interior hw j (hj ε hε0 hεδ)

theorem sMir_gt_two {e f : ℝ} (he : 0 < e) (hef : e < f) : 2 < sMir e f := by
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have h := sMir_mul he hef
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_le_mul_of_nonneg_right hcon hb.le]

/-- the point `X0 - eps s_j` as a point of the cone of `U(0,j-1)` at `p(0,j)` -/
theorem top_pt {e f : ℝ} (he : 0 < e) (hef : e < f) (j ε : ℝ) :
    mpG e f 1 0 0 j + ε • ((mpG e f 1 0 0 j + (-1 : ℝ) • (mpG e f 1 0 1 (j - 1) - mpG e f 1 0 0 j)) - mpG e f 1 0 0 j) =
      lpG e f 1 0 0 (j - 1 + 1) + ε • ((sMir e f - 2) • (lpG e f 1 0 0 (j - 1) - lpG e f 1 0 0 (j - 1 + 1)) +
        (1 : ℝ) • (lpG e f 1 0 (0 + 1) (j - 1) - lpG e f 1 0 0 (j - 1 + 1))) := by
  rw [mpG_eq_zero he hef, mpG_eq he hef]
  unfold lpG
  ext x
  fin_cases x <;> simp <;> ring

section top

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem top_clamp (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    {j n : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) (hn : 1 ≤ n) :
    ∀ ed ∈ D.lineChain (crossL (sj e f j)) (cross (sj e f j) (mpG (e : ℝ) f 1 0 0 (j : ℝ))),
      ¬ Straddles ((D.tile ed.1).edge ed.2)
        (mpG (e : ℝ) f 1 0 0 (j : ℝ) + (-1 : ℝ) • sj e f j) (mpG (e : ℝ) f 1 0 0 (j : ℝ))
        (mpG (e : ℝ) f 1 0 0 (j : ℝ) + (n : ℝ) • sj e f j) := by
  intro ed _
  have hcast : (((j - 1 : ℕ)) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj1]; simp
  obtain ⟨t, ht⟩ := hU (j - 1) (by omega)
  rw [hcast] at ht
  have hs2 := sMir_gt_two S.e0 S.hef'
  obtain ⟨ε₀, hε₀, hpush⟩ := hasV_push ht.rot.rot (θ1 := sMir (e : ℝ) f - 2) (θ2 := 1) (by linarith) one_pos
  refine not_straddles_short D.toDissection (j := t) hε₀ (ρ := (n : ℝ)) (by exact_mod_cast hn) ?_ ?_ ed.1 ed.2
  · unfold sj; ext x; simp; ring
  · intro ε h0 h1
    have h := hpush ε h0 h1
    unfold sj
    rw [top_pt S.e0 S.hef' (j : ℝ) ε]
    exact h

set_option maxHeartbeats 1000000 in
/-- **(U3-c) at level `j <= J`** from the invariant: a far-side tile over every a-step of the chord -/
theorem hthird_of_inv (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ f - 1)
    (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) {Bst : ℕ → ℕ → Prop} {j c : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J)
    (I : Inv D e f Bst j c) :
    ∀ i : ℕ, i < c → ∃ (τ : Fin N) (W : Plane),
        HasV D τ (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - i)) (mpG (e : ℝ) f 1 0 ((i : ℝ) + 1) ((j : ℝ) - i - 1)) W ∧
        cross (mpG (e : ℝ) f 1 0 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (j : ℝ)) (W - mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - i)) < 0 := by
  have hn : c ≤ f - 1 := by have := I.cj; omega
  have hnorm : ‖sj e f j‖ = (e : ℝ) * f := by
    unfold sj; exact mirror_step_norm S.e0 S.hef' 0 (j : ℝ)
  have hef : (0 : ℝ) < (e : ℝ) * f := S.a_pos
  have hs0 : sj e f j ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; linarith
  obtain ⟨hint, hwall⟩ := inv_hint_wall S hU hT hj1 hjJ I
  have hint' : openSegment ℝ (mpG (e : ℝ) f 1 0 0 (j : ℝ)) (mpG (e : ℝ) f 1 0 0 (j : ℝ) + (c : ℝ) • sj e f j) ⊆ interior D.target.carrier := hint
  have hwall' : ∀ y ∈ openSegment ℝ (mpG (e : ℝ) f 1 0 0 (j : ℝ)) (mpG (e : ℝ) f 1 0 0 (j : ℝ) + (c : ℝ) • sj e f j),
      ∀ i, y ∉ interior (D.tile i).carrier := hwall
  have key := chord_all S (crossL (sj e f j)) (crossL_ne_zero hs0) (cross (sj e f j) (mpG (e : ℝ) f 1 0 0 (j : ℝ))) hs0 hnorm
    (crossL_apply _ _) (by rw [crossL_apply]; simp [cross]; ring) I.c1 hn hint' hwall'
    (top_clamp S hU hj1 hjJ I.c1) I.clamp
  intro i hi
  obtain ⟨τ, W, hV, hW⟩ := key i hi
  have h1 : mpG (e : ℝ) f 1 0 0 (j : ℝ) + (i : ℝ) • sj e f j = mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - i) := by
    unfold sj; exact step_pt S.e0 S.hef' 0 (j : ℝ) (i : ℝ)
  have h2 : mpG (e : ℝ) f 1 0 0 (j : ℝ) + ((i : ℝ) + 1) • sj e f j =
      mpG (e : ℝ) f 1 0 ((i : ℝ) + 1) ((j : ℝ) - i - 1) := by
    unfold sj
    exact (step_pt S.e0 S.hef' 0 (j : ℝ) ((i : ℝ) + 1)).trans (mpG_congr' rfl (by ring))
  refine ⟨τ, W, ?_, ?_⟩
  · rw [h1, h2] at hV; exact hV
  · show cross (sj e f j) (W - mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - i)) < 0
    have e1 : cross (sj e f j) (W - (mpG (e : ℝ) f 1 0 0 (j : ℝ) + (i : ℝ) • sj e f j)) =
        crossL (sj e f j) W - cross (sj e f j) (mpG (e : ℝ) f 1 0 0 (j : ℝ)) := by
      rw [crossL_apply]; simp [cross]; ring
    rw [← h1, e1]; linarith

end top

end Erdos634.Draft.WGapStmt
