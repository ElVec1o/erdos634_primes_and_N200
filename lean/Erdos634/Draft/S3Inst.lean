/-
Draft/S3Inst.lean -- the S3 leaf `S3Closed N` (base-α isosceles target `(α, α, α+2β)`) from its finitely many instances.

`CompositeS3Refined.Row11.excluded_isoQRef` proves `S3Closed N` when the reduced Row-11 equation
`N d = m² (2e+d)(e²+4ed+2d²)` has no solution (`IsoQRef N`).  Here each solution `(e, d, m)` is carried as a leaf
`S3Inst m e f` (`f = e + d`): "no dissection of the isosceles triangle with legs `m f² (f+e)` and base
`m (f+e)(2f²−e²)` by the tile `(e f, f²−e², f²)`".  The proof is `excluded_isoQRef` verbatim up to the reduced equation;
the instance is then applied after scaling by `f²/c` (legs from the flux relation, base from `Row11.sides`).
`s3inst_of_cert` discharges an instance from a search certificate by SSS.

Composite-N leaves; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.CompositeS3Refined
import Erdos634.Draft.GapE120Dis

open scoped Classical

namespace Erdos634.Geometry

open Rows11_13AnyLabel

/-- **The S3 instance `(m, e, f)`**: no dissection (any number of tiles) of the isosceles triangle with legs
`m f² (f+e)` and base `m (f+e)(2f² − e²)` by the tile with sides `(e f, f² − e², f²)`. -/
def S3Inst (m e f : ℕ) : Prop :=
  ∀ {N : ℕ} (D : CongruentDissection N),
    D.target.oppLen 0 = (m : ℝ) * (f : ℝ) ^ 2 * ((f : ℝ) + e) →
    D.target.oppLen 1 = (m : ℝ) * (f : ℝ) ^ 2 * ((f : ℝ) + e) →
    D.target.oppLen 2 = (m : ℝ) * ((f : ℝ) + e) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) →
    (∃ σ : Equiv.Perm (Fin 3), D.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ D.model.oppLen (σ 2) = (f : ℝ) ^ 2) → False

open Erdos634.Geometry.GapE120Dis in
/-- an S3 instance from a certificate: `TGT` has sides (base, leg, leg) and `MODEL` sides `(e f, f²−e², f²)`,
both in the vertex order `01, 12, 02` -/
theorem s3inst_of_cert (m e f : ℕ) (TGT MODEL : Tri)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = (m : ℝ) * ((f : ℝ) + e) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      dist (TGT.pts 1) (TGT.pts 2) = (m : ℝ) * (f : ℝ) ^ 2 * ((f : ℝ) + e) ∧
      dist (TGT.pts 0) (TGT.pts 2) = (m : ℝ) * (f : ℝ) ^ 2 * ((f : ℝ) + e))
    (hM : dist (MODEL.pts 0) (MODEL.pts 1) = (e : ℝ) * f ∧
      dist (MODEL.pts 1) (MODEL.pts 2) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist (MODEL.pts 0) (MODEL.pts 2) = (f : ℝ) ^ 2)
    (hno : ∀ {N : ℕ} (D : CongruentDissection N), D.target.Congruent TGT → D.model.Congruent MODEL → False) :
    S3Inst m e f := by
  intro N D h0 h1 h2 ⟨σ, m0, m1, m2⟩
  obtain ⟨g1, g2, g3⟩ := hT
  obtain ⟨k1, k2, k3⟩ := hM
  have hTc : D.target.Congruent TGT := by
    refine Tri.congruent_of_dist _ _ ?_ ?_ ?_
    · rw [g1, ← h2]; rfl
    · rw [g2, ← h0]; rfl
    · rw [g3, ← h1, dist_comm]; rfl
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  rw [m0] at s1; rw [m1] at s2; rw [m2] at s3
  have hMc : D.model.Congruent MODEL := by
    set τ : Equiv.Perm (Fin 3) := (finRotate 3).trans σ with hτ
    have h0' : τ 0 = σ 1 := by simp [hτ, fr0]
    have h1' : τ 1 = σ 2 := by simp [hτ, fr1]
    have h2' : τ 2 = σ 0 := by simp [hτ, fr2]
    have hc := Tri.congruent_of_dist (D.model.relabel τ) MODEL
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h0', h1', s1, k1])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h1', h2', dist_comm, s2, k2])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h0', h2', dist_comm, s3, k3])
    exact (D.model.congruent_relabel τ).trans hc
  exact hno D hTc hMc

theorem excluded_s3_oriented {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α) (hP1 : D.target.angleAt 1 = α)
    (hinst : ∀ e d m : ℕ, 1 ≤ e → 1 ≤ d → Nat.Coprime e (e + d) →
      N * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) → S3Inst m e (e + d)) : False := by
  obtain ⟨s, M, hs0, hs1, hc, ha, hb, hM1, hleg, harea⟩ := Row11.area D hα hrel h hP0 hP1
  obtain ⟨r, hr⟩ := Row11.rational D hα hrel h hP0 hP1
  have hsr : s = r := by
    have : c * (s - r) = 0 := by rw [ha] at hr; linear_combination hr
    linarith [(mul_eq_zero.mp this).resolve_left hc.ne']
  -- `s = e/f` in lowest terms, `f = e + d`, `e, d ≥ 1`
  have hr0 : 0 < r := by exact_mod_cast (hsr ▸ hs0 : (0 : ℝ) < r)
  obtain ⟨e, he⟩ : ∃ e : ℕ, r.num = e := ⟨r.num.toNat, (Int.toNat_of_nonneg (Rat.num_pos.mpr hr0).le).symm⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ, f = r.den := ⟨_, rfl⟩
  have hf0 : 0 < f := hfdef ▸ r.den_pos
  have hcop : Nat.Coprime e f := by
    have := r.reduced; rw [he, ← hfdef] at this; simpa using this
  have hsef : s = (e : ℝ) / f := by
    rw [hsr, ← Rat.num_div_den r, he, ← hfdef]
    push_cast <;> ring
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf0
  have he1 : 1 ≤ e := by
    have : (0 : ℝ) < e := by
      have h1 := hs0; rw [hsef] at h1
      have h2 := mul_pos h1 hfR
      rwa [div_mul_cancel₀ _ hfR.ne'] at h2
    exact_mod_cast this
  have hef : e < f := by
    have : (e : ℝ) < f := by
      have := hs1; rw [hsef, div_lt_one hfR] at this; exact this
    exact_mod_cast this
  obtain ⟨d, hd⟩ : ∃ d, f = e + d := ⟨f - e, by omega⟩
  have hd1 : 1 ≤ d := by omega
  -- `M` natural
  obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le (by linarith : (0 : ℤ) ≤ M)
  push_cast at hleg harea
  have hfd : (f : ℝ) = e + d := by rw [hd]; push_cast; ring
  -- the tiling equation over ℕ: `N·d·(3e+2d)² = m'²·(2e+d)·(e²+4ed+2d²)`
  have hNeq : N * d * (3 * e + 2 * d) ^ 2 = m' ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
    have hf' : (f : ℝ) ≠ 0 := hfR.ne'
    have key : (N : ℝ) * d * (3 * e + 2 * d) ^ 2 - (m' : ℝ) ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))
        = (f : ℝ) ^ 3 * ((N : ℝ) * (1 - s) * (2 + s) ^ 2 - (m' : ℝ) ^ 2 * (1 + s) * (2 - s ^ 2)) := by
      rw [hsef, hfd]
      have hed : (e : ℝ) + d ≠ 0 := by rw [← hfd]; exact hf'
      field_simp <;> ring
    rw [harea, sub_self, mul_zero, sub_eq_zero] at key
    exact_mod_cast key
  -- the leg word gives `X'·(2f+e) = m'·f²·(f+e)`
  obtain ⟨na, nb, nc, hw⟩ := D.side_word_threeAlpha h 0
  set X' : ℕ := na * (e * (e + d)) + nb * (d * (2 * e + d)) + nc * (e + d) ^ 2 with hX'def
  have hXeq : X' * (2 * (e + d) + e) = m' * ((e + d + e) * (e + d) ^ 2) := by
    have hf' : (f : ℝ) ≠ 0 := hfR.ne'
    have hX'R : (X' : ℝ) * c = D.target.oppLen 0 * (f : ℝ) ^ 2 := by
      rw [hw, ha, hb, hsef, hfd, hX'def]
      have hed : (e : ℝ) + d ≠ 0 := by rw [← hfd]; exact hf'
      push_cast
      field_simp <;> ring
    have hlegf : D.target.oppLen 0 * (2 * f + e) = m' * c * (f + e) := by
      have := hleg
      rw [hsef] at this
      field_simp at this
      linear_combination this
    have hc' : c ≠ 0 := hc.ne'
    have : c * ((X' : ℝ) * (2 * (e + d) + e) - m' * ((e + d + e) * (e + d) ^ 2)) = 0 := by
      rw [hfd] at hlegf hX'R
      linear_combination (2 * ((e : ℝ) + d) + e) * hX'R + ((e : ℝ) + d) ^ 2 * hlegf
    have h2 := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc')
    exact_mod_cast h2
  -- `(2f+e) ∣ M`
  have hcop' : Nat.Coprime e (e + d) := by rw [← hd]; exact hcop
  obtain ⟨m, hm⟩ := Erdos634.IsoAlpha.isoalpha_X_forces e (e + d) m' X' hcop' hXeq
  -- the reduced equation `N·d = m²·(2e+d)·(e²+4ed+2d²)`
  have hred : N * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
    rw [hm] at hNeq
    have h3 : 0 < (3 * e + 2 * d) ^ 2 := by positivity
    have e2 : 2 * (e + d) + e = 3 * e + 2 * d := by ring
    rw [e2] at hNeq
    have : (3 * e + 2 * d) ^ 2 * (N * d) = (3 * e + 2 * d) ^ 2 * (m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))) := by
      calc (3 * e + 2 * d) ^ 2 * (N * d) = N * d * (3 * e + 2 * d) ^ 2 := by ring
        _ = ((3 * e + 2 * d) * m) ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := hNeq
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_left h3 this
  -- the instance: scale by `f²/c`
  have hI : S3Inst m e (e + d) := hinst e d m he1 hd1 hcop' hred
  rw [← hd] at hI
  have hP2 : D.target.angleAt 2 = α + 2 * β := by
    have := D.target.angleAt_sum; rw [hP0, hP1] at this; linarith
  obtain ⟨s', -, -, -, -, ha', -, hY, hX1⟩ := Row11.sides D hrel h hP0 hP1 hP2
  have hss : s' = s := by
    have : c * (s' - s) = 0 := by rw [ha] at ha'; linear_combination -ha'
    linarith [(mul_eq_zero.mp this).resolve_left hc.ne']
  rw [hss] at hY
  have hmR : (m' : ℝ) = (2 * ((e : ℝ) + d) + e) * m := by exact_mod_cast hm
  have h2s : (0 : ℝ) < 2 + s := by linarith
  have hX : D.target.oppLen 0 = (m : ℝ) * c * (f + e) := by
    have key : D.target.oppLen 0 * (2 + s) = (m : ℝ) * c * (f + e) * (2 + s) := by
      rw [hleg, hmR, hsef, ← hfd]; first | (field_simp; ring) | field_simp
    exact mul_right_cancel₀ h2s.ne' key
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := h
  set sc : ℝ := (f : ℝ) ^ 2 / c with hsc
  have hscpos : 0 < sc := div_pos (by positivity) hc
  set Ds := Erdos634.Realizable.scaleDissection (D.model.pts 0) sc hscpos.ne' D with hDs
  have htd : ∀ i j : Fin 3, dist (Ds.target.pts i) (Ds.target.pts j) = sc * dist (D.target.pts i) (D.target.pts j) := by
    intro i j
    rw [hDs, Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.homothetyEquiv_dist, abs_of_pos hscpos]
  have hmd : ∀ i j : Fin 3, dist (Ds.model.pts i) (Ds.model.pts j) = sc * dist (D.model.pts i) (D.model.pts j) := by
    intro i j
    rw [hDs, Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.homothetyEquiv_dist, abs_of_pos hscpos]
  have hto : ∀ k : Fin 3, Ds.target.oppLen k = sc * D.target.oppLen k := fun k => by
    unfold Tri.oppLen; exact htd _ _
  have hmo : ∀ k : Fin 3, Ds.model.oppLen k = sc * D.model.oppLen k := fun k => by
    unfold Tri.oppLen; exact hmd _ _
  refine hI Ds ?_ ?_ ?_ ⟨σm, ?_, ?_, ?_⟩
  · rw [hto, hX, hsc]; first | (field_simp; ring) | field_simp
  · rw [hto, hX1, hX, hsc]; first | (field_simp; ring) | field_simp
  · rw [hto, hY, hX, hsef, hsc]; first | (field_simp; ring) | field_simp
  · rw [hmo, ham, ha, hsef, hsc]; first | (field_simp; ring) | field_simp
  · rw [hmo, hbm, hb, hsef, hsc]; first | (field_simp; ring) | field_simp
  · rw [hmo, hcm, hsc]; first | (field_simp; ring) | field_simp

/-- **`S3Closed N` from the instances.** -/
theorem s3Closed_of_inst (N : ℕ)
    (hinst : ∀ e d m : ℕ, 1 ≤ e → 1 ≤ d → Nat.Coprime e (e + d) →
      N * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) → S3Inst m e (e + d)) :
    Erdos634.Draft.CompositeGen2.S3Closed N := by
  intro D α β a b c hα hrel hdata t₀ t₁ ht hP0 hP1
  obtain ⟨σ, hm, h0, h1⟩ := transport D ht α hP0 hP1
  exact excluded_s3_oriented (D.relabelTarget' σ) hα hrel (hm ▸ hdata) h0 h1 hinst

end Erdos634.Geometry

#print axioms Erdos634.Geometry.s3Closed_of_inst
