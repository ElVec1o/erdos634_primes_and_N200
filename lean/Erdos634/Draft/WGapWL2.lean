/-
Draft/WGapWL2.lean -- written 15 November 2026 (session 6).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.2, Wall Lemma).
Not imported by any aggregate.  Module WL2: `wl_cover` (abstract: the straddling edge gives `EdgeCover D (P0 + q d) d`), `mpG_affine_x` (the mirror lattice at an arbitrary origin `x` is affine),
and the Wall Lemma `wl_mirror` = S1 (`wl_stmt`) of WGapStmt_Scratch20261115.lean, textually the scratch statement.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapWL1

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

/-- the mirror lattice at an arbitrary origin is an affine image of `Z^2` -/
theorem mpG_affine_x {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) :
    ∃ O E1 E2 : Plane, ∀ ξ η : ℝ, mpG e f 1 x ξ η = O + ξ • E1 + η • E2 := by
  refine ⟨mpG e f 1 x 0 0, mpG e f 1 x 1 0 - mpG e f 1 x 0 0, mpG e f 1 x 0 1 - mpG e f 1 x 0 0, ?_⟩
  intro ξ η
  simp only [mpG_eq he hef]
  unfold lpG
  ext i
  fin_cases i <;> simp <;> ring

section wl2

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem wl_cover (S : SetupG D e f α β γ L ax ay) {q : ℕ} (hq1 : 1 ≤ q) (hqf : q ≤ f - 1)
    (P0 d : Plane) (ν : ℝ) (hdn : ‖d‖ = (f : ℝ) ^ 2) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hνb : (f : ℝ) ^ 2 * ν = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (E : Fin N) (A0 : Plane) (hE : HasV D E P0 (P0 + d) A0) (hA0 : cross d (A0 - P0) < 0)
    (Fo : Fin N) (R : Plane) (hFo : HasV D Fo P0 (P0 + ν • d) R) (hR : 0 < cross d (R - P0))
    (hT : ∀ t : ℕ, t < q → ∃ (T : Fin N) (A : Plane),
      HasV D T (P0 + (t : ℝ) • d) (P0 + ((t : ℝ) + 1) • d) A ∧ cross d (A - (P0 + (t : ℝ) • d)) < 0) :
    EdgeCover D (P0 + (q : ℝ) • d) d := by
  obtain ⟨ed, hed, hs⟩ := wl_straddle S hq1 hqf P0 d ν hdn hν0 hν1 hνb E A0 hE hA0 Fo R hFo hR hT
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hf2 := S.c_pos
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at hdn; simp at hdn; linarith
  have hF : crossL (-d) ≠ 0 := crossL_ne_zero (neg_ne_zero.mpr hd0)
  have hFl : ∀ s : ℝ, crossL (-d) (P0 + s • d) = crossL (-d) P0 := by
    intro s
    simp only [crossL_apply, cross, PiLp.neg_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hPQ : P0 + (q : ℝ) • d ≠ P0 := by
    intro h
    have : (q : ℝ) • d = 0 := by simpa using h
    rcases smul_eq_zero.mp this with h0 | h0
    · exact hqpos.ne' h0
    · exact hd0 h0
  have hP' : P0 + (q : ℝ) • d ∈ openSegment ℝ (P0 + ((q : ℝ) + 1) • d) P0 := by
    have := pt_openSeg P0 d (a := 0) (b := (q : ℝ) + 1) (t := (q : ℝ)) hqpos (by linarith)
    rw [openSegment_symm]
    simpa using this
  obtain ⟨hmem, hang, hpush⟩ := straddle_data D.toDissection (crossL (-d)) hF (crossL (-d) P0)
    (P := P0 + (q : ℝ) • d) (Q := P0) (P' := P0 + ((q : ℝ) + 1) • d) hPQ (hFl _) rfl (hFl _) hP' hed hs
  refine ⟨ed.1, hmem, hang, fun w hw => ?_⟩
  have hFw : crossL (-d) w < 0 := by
    simp only [crossL_apply, cross, PiLp.neg_apply]
    simp only [cross] at hw
    linarith
  exact hpush w hFw

/-- **S1, the Wall Lemma** (PROOF 6.2), textually the scratch statement `wl_stmt` -/
theorem wl_mirror (S : SetupG D e f α β γ L ax ay) (c₀ J q : ℕ)
    (hq1 : 1 ≤ q) (hqf : q ≤ f - 1)
    (hSt1 : UTM D (e : ℝ) (f : ℝ) 1 ((c₀ : ℝ) * (f : ℝ) ^ 2) 0 (J : ℝ))
    (hSt2 : St2 D (e : ℝ) (f : ℝ) ((c₀ : ℝ) * (f : ℝ) ^ 2) (J : ℝ))
    (hU : ∀ t : ℕ, t < q → UTM D (e : ℝ) (f : ℝ) 1 ((c₀ : ℝ) * (f : ℝ) ^ 2) (t : ℝ) (J : ℝ)) :
    EdgeCover D (mpG (e : ℝ) (f : ℝ) 1 ((c₀ : ℝ) * (f : ℝ) ^ 2) (q : ℝ) (J : ℝ))
      (mpG (e : ℝ) (f : ℝ) 1 ((c₀ : ℝ) * (f : ℝ) ^ 2) 1 (J : ℝ) - mpG (e : ℝ) (f : ℝ) 1 ((c₀ : ℝ) * (f : ℝ) ^ 2) 0 (J : ℝ)) := by
  have he0 := S.e0
  have he0 := S.e0
  have hef := S.hef'
  have hκ := kapG_pos he0 hef
  have hν0 := nuG_pos he0 hef
  have hν1 := nuG_lt_one he0 hef
  have hνb := nuG_spec he0 hef
  set x : ℝ := (c₀ : ℝ) * (f : ℝ) ^ 2 with hx
  obtain ⟨O, E1, E2, hm⟩ := mpG_affine_x he0 hef x
  set P0 : Plane := mpG (e : ℝ) (f : ℝ) 1 x 0 (J : ℝ) with hP0
  set d : Plane := mpG (e : ℝ) (f : ℝ) 1 x 1 (J : ℝ) - P0 with hd
  have hpt : ∀ ξ : ℝ, mpG (e : ℝ) (f : ℝ) 1 x ξ (J : ℝ) = P0 + ξ • d := by
    intro ξ
    rw [hd, hP0]
    simp only [hm]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  have hdn : ‖d‖ = (f : ℝ) ^ 2 := by
    have := dist_mp_u (x := x) he0 hef (by norm_num : (1 : ℝ) ^ 2 = 1) 0 (J : ℝ)
    rw [zero_add, dist_comm, dist_eq_norm] at this
    exact this
  have hcr : ∀ ξ : ℝ, cross d (mpG (e : ℝ) (f : ℝ) 1 x ξ ((J : ℝ) + 1) - mpG (e : ℝ) (f : ℝ) 1 x ξ (J : ℝ)) =
      -(kapG (e : ℝ) (f : ℝ)) := by
    intro ξ
    rw [hd, hP0, cross_mpG he0 hef]
    ring
  obtain ⟨E, hE⟩ := hSt1
  obtain ⟨Fo, W, R, hFo, hWeq, hRpos⟩ := hSt2
  have hE' : HasV D E P0 (P0 + d) (mpG (e : ℝ) (f : ℝ) 1 x 0 ((J : ℝ) + 1)) :=
    hasV_congr hE rfl (by rw [zero_add, hd]; abel) rfl
  have hA0 : cross d (mpG (e : ℝ) (f : ℝ) 1 x 0 ((J : ℝ) + 1) - P0) < 0 := by
    have := hcr 0
    rw [hP0]; rw [this]; linarith
  have key := wl_cover S hq1 hqf P0 d (nuG (e : ℝ) (f : ℝ)) hdn hν0 hν1 hνb E _ hE' hA0 Fo R
    (hasV_congr hFo rfl hWeq rfl) hRpos ?_
  · rw [hpt (q : ℝ)]; exact key
  · intro t ht
    obtain ⟨T, hT⟩ := hU t ht
    refine ⟨T, mpG (e : ℝ) (f : ℝ) 1 x (t : ℝ) ((J : ℝ) + 1), hasV_congr hT (hpt _) (hpt _) rfl, ?_⟩
    rw [← hpt (t : ℝ), hcr (t : ℝ)]
    linarith

end wl2

#print axioms wl_mirror

end Erdos634.Draft.WGapStmt
