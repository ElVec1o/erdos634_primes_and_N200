/-
Draft/InstLbl.lean -- instance statements from certificates whose target is labelled in another vertex order.

`IsoInst.isoinst_of_cert`, `Geometry.s3inst_of_cert`, `NSQRW.s4inst_of_cert` expect the certificate's target with its
sides in a fixed order (`01, 12, 02` = base, leg, leg for the isosceles ones).  The search that produced some of the
refutation trees ends only when the isosceles target stands on a leg, so those certificates have the
order (leg, base, leg); the S4 certificate of `184` has the order `(S' e (2f²−e²), S' f (f²−e²), S' f³)`.  This file
restates the three lemmas for those orders.  `cert_apply` is the common step: a certificate applies to every
dissection whose target and model have the certificate's side lengths under some relabelling of the vertices.

No sorry, no native_decide.
-/
import Erdos634.Draft.IsoInst
import Erdos634.Draft.RWInst
import Erdos634.Draft.S3Inst

open scoped Classical

namespace Erdos634.Draft.InstLbl

open Erdos634.Geometry Erdos634.Geometry.GapE120Dis Erdos634.Draft.IsoInst Erdos634.Draft.NSQRW

/-- **A certificate applies under any relabelling**: if the target and the model of `D` have the side lengths of
`TGT` and `MODEL` after relabelling the vertices by `ρ` and `μ`, the certificate refutes `D`. -/
theorem cert_apply (TGT MODEL : Erdos634.Geometry.Tri)
    (hno : ∀ {N : ℕ} (D : CongruentDissection N), D.target.Congruent TGT → D.model.Congruent MODEL → False)
    {N : ℕ} (D : CongruentDissection N) (ρ μ : Equiv.Perm (Fin 3))
    (t01 : dist (D.target.pts (ρ 0)) (D.target.pts (ρ 1)) = dist (TGT.pts 0) (TGT.pts 1))
    (t12 : dist (D.target.pts (ρ 1)) (D.target.pts (ρ 2)) = dist (TGT.pts 1) (TGT.pts 2))
    (t02 : dist (D.target.pts (ρ 0)) (D.target.pts (ρ 2)) = dist (TGT.pts 0) (TGT.pts 2))
    (m01 : dist (D.model.pts (μ 0)) (D.model.pts (μ 1)) = dist (MODEL.pts 0) (MODEL.pts 1))
    (m12 : dist (D.model.pts (μ 1)) (D.model.pts (μ 2)) = dist (MODEL.pts 1) (MODEL.pts 2))
    (m02 : dist (D.model.pts (μ 0)) (D.model.pts (μ 2)) = dist (MODEL.pts 0) (MODEL.pts 2)) : False := by
  have hTc : D.target.Congruent TGT :=
    (D.target.congruent_relabel ρ).trans (Tri.congruent_of_dist (D.target.relabel ρ) TGT
      (by simp only [Tri.relabel_pts]; exact t01)
      (by simp only [Tri.relabel_pts]; exact t12)
      (by simp only [Tri.relabel_pts]; exact t02))
  have hMc : D.model.Congruent MODEL :=
    (D.model.congruent_relabel μ).trans (Tri.congruent_of_dist (D.model.relabel μ) MODEL
      (by simp only [Tri.relabel_pts]; exact m01)
      (by simp only [Tri.relabel_pts]; exact m12)
      (by simp only [Tri.relabel_pts]; exact m02))
  exact hno D hTc hMc

theorem rs0 : (finRotate 3).symm (0 : Fin 3) = 2 := by decide
theorem rs1 : (finRotate 3).symm (1 : Fin 3) = 0 := by decide
theorem rs2 : (finRotate 3).symm (2 : Fin 3) = 1 := by decide

/-- an Iso instance from a certificate whose target is labelled (leg `k c₀`, base `k (a₀+2b₀)`, leg) in the vertex
order `01, 12, 02`; `MODEL` has sides `(a₀, b₀, c₀)` in that order -/
theorem isoinst_of_cert_lbl (a₀ b₀ c₀ k : ℤ) (TGT MODEL : Erdos634.Geometry.Tri)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = (k : ℝ) * c₀ ∧
      dist (TGT.pts 1) (TGT.pts 2) = (k : ℝ) * ((a₀ : ℝ) + 2 * b₀) ∧ dist (TGT.pts 0) (TGT.pts 2) = (k : ℝ) * c₀)
    (hM : dist (MODEL.pts 0) (MODEL.pts 1) = (a₀ : ℝ) ∧
      dist (MODEL.pts 1) (MODEL.pts 2) = (b₀ : ℝ) ∧ dist (MODEL.pts 0) (MODEL.pts 2) = (c₀ : ℝ))
    (hno : ∀ {N : ℕ} (D : CongruentDissection N), D.target.Congruent TGT → D.model.Congruent MODEL → False) :
    IsoInst a₀ b₀ c₀ k := by
  intro N D ⟨τ, t0, t1, t2⟩ ⟨σ, m0, m1, m2⟩
  obtain ⟨g1, g2, g3⟩ := hT
  obtain ⟨k1, k2, k3⟩ := hM
  obtain ⟨u1, u2, u3⟩ := sides_of_perm D.target τ
  rw [t0] at u1; rw [t1] at u2; rw [t2] at u3
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  rw [m0] at s1; rw [m1] at s2; rw [m2] at s3
  refine cert_apply TGT MODEL hno D ((finRotate 3).symm.trans τ) ((finRotate 3).trans σ) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Equiv.trans_apply, Equiv.trans_apply, rs0, rs1, g1, dist_comm]; exact u2
  · rw [Equiv.trans_apply, Equiv.trans_apply, rs1, rs2, g2]; exact u3
  · rw [Equiv.trans_apply, Equiv.trans_apply, rs0, rs2, g3, dist_comm]; exact u1
  · rw [Equiv.trans_apply, Equiv.trans_apply, fr0, fr1, k1]; exact s1
  · rw [Equiv.trans_apply, Equiv.trans_apply, fr1, fr2, k2, dist_comm]; exact s2
  · rw [Equiv.trans_apply, Equiv.trans_apply, fr0, fr2, k3, dist_comm]; exact s3

/-- an S3 instance from a certificate whose target is labelled (leg, base, leg) in the vertex order `01, 12, 02`;
`MODEL` has sides `(e f, f²−e², f²)` in that order -/
theorem s3inst_of_cert_lbl (m e f : ℕ) (TGT MODEL : Erdos634.Geometry.Tri)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = (m : ℝ) * (f : ℝ) ^ 2 * ((f : ℝ) + e) ∧
      dist (TGT.pts 1) (TGT.pts 2) = (m : ℝ) * ((f : ℝ) + e) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      dist (TGT.pts 0) (TGT.pts 2) = (m : ℝ) * (f : ℝ) ^ 2 * ((f : ℝ) + e))
    (hM : dist (MODEL.pts 0) (MODEL.pts 1) = (e : ℝ) * f ∧
      dist (MODEL.pts 1) (MODEL.pts 2) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist (MODEL.pts 0) (MODEL.pts 2) = (f : ℝ) ^ 2)
    (hno : ∀ {N : ℕ} (D : CongruentDissection N), D.target.Congruent TGT → D.model.Congruent MODEL → False) :
    S3Inst m e f := by
  intro N D h0 h1 h2 ⟨σ, m0, m1, m2⟩
  obtain ⟨g1, g2, g3⟩ := hT
  obtain ⟨k1, k2, k3⟩ := hM
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  rw [m0] at s1; rw [m1] at s2; rw [m2] at s3
  refine cert_apply TGT MODEL hno D (finRotate 3).symm ((finRotate 3).trans σ) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [rs0, rs1, g1, ← h1]; rfl
  · rw [rs1, rs2, g2, ← h2]; rfl
  · rw [rs0, rs2, g3, ← h0, dist_comm]; rfl
  · rw [Equiv.trans_apply, Equiv.trans_apply, fr0, fr1, k1]; exact s1
  · rw [Equiv.trans_apply, Equiv.trans_apply, fr1, fr2, k2, dist_comm]; exact s2
  · rw [Equiv.trans_apply, Equiv.trans_apply, fr0, fr2, k3, dist_comm]; exact s3

/-- an S4 instance from a certificate whose target has sides `(S' e (2f²−e²), S' f (f²−e²), S' f³)` in the vertex
order `01, 12, 02`; `MODEL` has sides `(e f, f²−e², f²)` in that order -/
theorem s4inst_of_cert_lbl (S' e f : ℤ) (TGT MODEL : Erdos634.Geometry.Tri)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = (S' : ℝ) * e * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      dist (TGT.pts 1) (TGT.pts 2) = (S' : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      dist (TGT.pts 0) (TGT.pts 2) = (S' : ℝ) * (f : ℝ) ^ 3)
    (hM : dist (MODEL.pts 0) (MODEL.pts 1) = (e : ℝ) * f ∧
      dist (MODEL.pts 1) (MODEL.pts 2) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist (MODEL.pts 0) (MODEL.pts 2) = (f : ℝ) ^ 2)
    (hno : ∀ {N : ℕ} (D : CongruentDissection N), D.target.Congruent TGT → D.model.Congruent MODEL → False) :
    S4Inst S' e f := by
  intro N D h0 h1 h2 ⟨σ, m0, m1, m2⟩
  obtain ⟨g1, g2, g3⟩ := hT
  obtain ⟨k1, k2, k3⟩ := hM
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  rw [m0] at s1; rw [m1] at s2; rw [m2] at s3
  refine cert_apply TGT MODEL hno D (finRotate 3) ((finRotate 3).trans σ) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fr0, fr1, g1, ← h0]; rfl
  · rw [fr1, fr2, g2, ← h1]; rfl
  · rw [fr0, fr2, g3, ← h2, dist_comm]; rfl
  · rw [Equiv.trans_apply, Equiv.trans_apply, fr0, fr1, k1]; exact s1
  · rw [Equiv.trans_apply, Equiv.trans_apply, fr1, fr2, k2, dist_comm]; exact s2
  · rw [Equiv.trans_apply, Equiv.trans_apply, fr0, fr2, k3, dist_comm]; exact s3

end Erdos634.Draft.InstLbl

#print axioms Erdos634.Draft.InstLbl.isoinst_of_cert_lbl
#print axioms Erdos634.Draft.InstLbl.s3inst_of_cert_lbl
#print axioms Erdos634.Draft.InstLbl.s4inst_of_cert_lbl
