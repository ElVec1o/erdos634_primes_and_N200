import Mathlib.Tactic
import Erdos634.Draft.ThmDPGoodRow
import Erdos634.Draft.ThmDSector4
import Erdos634.Draft.ThmDRowVertex

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (4): `PGood` at a frontier non-vertex (the corner start)  
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem PGood_of_frontier (C : CtxBaseT D u v α β γ L ax ay ε x) {η : ℝ} (hη : 0 < η)
    (hPf : lpT (u : ℝ) (v : ℝ) ε x 0 η ∈ frontier D.target.carrier)
    (hPnv : lpT (u : ℝ) (v : ℝ) ε x 0 η ∉ Set.range D.target.pts)
    (hside : (ε = 1 ∧ gA ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 η) = 0) ∨
      (ε = -1 ∧ gB L ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 η) = 0))
    (hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 η) (lpT (u : ℝ) (v : ℝ) ε x η 0) ⊆
      interior D.target.carrier) :
    PGood D (u : ℝ) (v : ℝ) ε x α η := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hβpos : 0 < β := by
    have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
    have e : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
    rw [e] at h; exact h
  have h3α : 3 * α < Real.pi := by have := S.hβ; linarith
  refine ⟨D.target.isCompact.isClosed.frontier_subset hPf, ?_, ?_, ?_, ?_⟩
  · intro tW tE hne _ _ a a' hW hE
    exact pinfan_ang D S.hirr S.hM.hα' (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α hPf hPnv
      tW tE hne a a' hW hE
  · exact ⟨Finset.univ, Erdos634.PinPlumbing.pin_angle_sum D.toDissection hPf hPnv, fun τ _ _ => Finset.mem_univ τ⟩
  · refine ⟨1, one_pos, fun Q i k => ?_⟩
    have hout : ∀ y ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x (-1) η) (lpT (u : ℝ) (v : ℝ) ε x 0 η),
        y ∉ D.target.carrier := by
      intro y hy
      rw [openSegment_eq_image_lineMap] at hy
      obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
      rw [lineMap_lpT]
      have := west_outside S C.hε hside (δ := 1 - τ) (by linarith)
      rwa [show lpT (u : ℝ) (v : ℝ) ε x (-1 + τ * (0 - -1)) (η + τ * (η - η))
        = lpT (u : ℝ) (v : ℝ) ε x (0 - (1 - τ)) η from lpT_congr (by ring) (by ring)]
    exact not_straddles_of_outside D.toDissection hout i k
  · have hηR : η ≠ 0 := hη.ne'
    have hPQ : lpT (u : ℝ) (v : ℝ) ε x η 0 ≠ lpT (u : ℝ) (v : ℝ) ε x 0 η :=
      (lpT_ne_eta hu huv hv2 hηR).symm
    set P := lpT (u : ℝ) (v : ℝ) ε x 0 η with hPdef
    set Q := lpT (u : ℝ) (v : ℝ) ε x η 0 with hQdef
    have hGP : GST (u : ℝ) (v : ℝ) ε P = GST (u : ℝ) (v : ℝ) ε Q := by
      rw [hPdef, hQdef, GST_lp hε, GST_lp hε]; congr 1; congr 1; ring
    refine ⟨AffineMap.lineMap Q P (2 : ℝ), ?_, ?_, ?_⟩
    · rw [lineMap_lin, hGP]; ring
    · rw [openSegment_eq_image_lineMap]
      refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    · intro i k
      have hout := out_beyond_frontier D.target.convex hPQ (by rw [openSegment_symm]; exact hint) hPf.2
      exact not_straddles_of_outside D.toDissection
        (fun y hy => hout y (by rw [openSegment_symm]; exact hy)) i k

#print axioms PGood_of_frontier
end Erdos634.Draft.ThmDRun
