-- No sorry, no native_decide.
-- Cheap controls for the Case A lemmas on REAL edge-to-edge dissections with rational angles:
--  (a) `Equilateral3` (N = 3, the first PRIME-N witness): model (30,30,120) = ![1,1,4]·π/6, n = 6:
--      lemma1_full (tile-corner and target-corner lattice conjuncts), lemmaK (abstract), lemmaV (ℓ = 5), lemmaV_prime (3 ∣ 6).
--  (b) ladders of `PiFour.dissection` (N = 2k²; model transferred: `E.model = PiFour.dissection.model`):
--      lemmaV with POSITIVE valuation (N = 18, ℓ = 3: v₃ = 2; N = 50, ℓ = 5: v₅ = 2), lemma1_full, lemmaK (abstract).
import Erdos634.Draft.Equilateral3
import Erdos634.Draft.G3RCCommon
import Erdos634.Draft.A1FieldClause
import Erdos634.Draft.CaseALemmaVDissection
import Erdos634.Draft.CaseALemmaVWitness
import Erdos634.Draft.CaseALemmaHPiFour
import Erdos634.Draft.RWEast
import Erdos634.Ladder

namespace Erdos634.Draft.G3RCSmallControls

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.G3RCAngles
  Erdos634.Draft.G3RCCommon Erdos634.KConj Erdos634.CertCoord

/-! ## (a) Equilateral3 -/

def T3 : LT := ((0, 0), (6, 0), (3, 1))
theorem hpos3 : 0 < cross T3.1 T3.2.1 T3.2.2 := by decide

theorem model3_angles (D : CongruentDissection 3) (h : det3 0 0 6 0 3 (Real.sqrt 3) ≠ 0)
    (hm : D.model = mkTri 0 0 6 0 3 (Real.sqrt 3) h) (k : Fin 3) :
    D.model.angleAt k = (![1, 1, 4] : Fin 3 → ℕ) k * Real.pi / (6 : ℕ) := by
  have hpts : ∀ k, D.model.pts k = (triOf T3 hpos3).pts k := by
    intro k
    rw [hm, triOf_pts]
    fin_cases k <;> simp [mkTri_pts, toPt, rx, ry, vtx, T3]
  have hang : ∀ j, D.model.angleAt j = (triOf T3 hpos3).angleAt j := by
    intro j; unfold Tri.angleAt; rw [hpts, hpts, hpts]
  have s := s3pos; have s2 := s3sq'
  have a0 : (triOf T3 hpos3).angleAt 0 = Real.pi / 6 := by
    have k0 : oppSq T3 0 = 12 := by decide
    have k1 : oppSq T3 (0 + 1) = 12 := by decide
    have k2 : oppSq T3 (0 + 2) = 36 := by decide
    have oA := oppLen_sq T3 hpos3 0; have oB := oppLen_sq T3 hpos3 (0 + 1); have oC := oppLen_sq T3 hpos3 (0 + 2)
    rw [k0] at oA; rw [k1] at oB; rw [k2] at oC
    refine ang_val _ 0 _ _ _ (12 * Real.sqrt 3) _ (by simpa using oA) (by simpa using oB) (by simpa using oC)
      (by norm_num) (by norm_num) (by positivity) (by nlinarith) (by positivity) (by linarith [Real.pi_pos]) ?_
    rw [Real.cos_pi_div_six]; field_simp; nlinarith
  have a1 : (triOf T3 hpos3).angleAt 1 = Real.pi / 6 := by
    have k0 : oppSq T3 1 = 12 := by decide
    have k1 : oppSq T3 (1 + 1) = 36 := by decide
    have k2 : oppSq T3 (1 + 2) = 12 := by decide
    have oA := oppLen_sq T3 hpos3 1; have oB := oppLen_sq T3 hpos3 (1 + 1); have oC := oppLen_sq T3 hpos3 (1 + 2)
    rw [k0] at oA; rw [k1] at oB; rw [k2] at oC
    refine ang_val _ 1 _ _ _ (12 * Real.sqrt 3) _ (by simpa using oA) (by simpa using oB) (by simpa using oC)
      (by norm_num) (by norm_num) (by positivity) (by nlinarith) (by positivity) (by linarith [Real.pi_pos]) ?_
    rw [Real.cos_pi_div_six]; field_simp; nlinarith
  have hs := (triOf T3 hpos3).angleAt_sum
  rw [hang]
  fin_cases k
  · simp [a0]
  · simp [a1]
  · simp; linarith

theorem equil3_model_angles : ∃ D : CongruentDissection 3,
    ∀ k, D.model.angleAt k = (![1, 1, 4] : Fin 3 → ℕ) k * Real.pi / (6 : ℕ) := by
  obtain ⟨D, h, hm⟩ := Erdos634.Draft.Equilateral3.exists_dissection_3_model
  exact ⟨D, model3_angles D h hm⟩

/-- `lemma1_full` on the real `CongruentDissection 3` (prime N = 3): corners in the lattice `Lpaper 6 ![1,1,4] ⊂ Kf 6`. -/
theorem equil3_lemma1_full : ∃ D : CongruentDissection 3,
    (∀ i k, A1Field.zc D ((D.tile i).pts k) ∈ A1Field.Lpaper 6 ![1, 1, 4]) ∧
    (∀ k, A1Field.zc D (D.target.pts k) ∈ A1Field.Lpaper 6 ![1, 1, 4]) ∧
    (∀ x ∈ A1Field.Lpaper 6 ![1, 1, 4], x ∈ CaseA.LemmaV.Kf 6) := by
  obtain ⟨D, ha⟩ := equil3_model_angles
  have := Erdos634.Geometry.A1Field.lemma1_full D (n := 6) (by norm_num) ![1, 1, 4] ha
  exact ⟨D, this.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2⟩

/-- `lemmaK` on it (abstract: `fig` not evaluated here). -/
theorem equil3_lemmaK : ∃ (D : CongruentDissection 3) (idx : Fin 3 → Equiv.Perm (Fin 3)),
    (∀ j, D.target.angleAt j = (Erdos634.LemmaKStar.uu ![1, 1, 4] (fig D idx) j : ℕ) * Real.pi / (6 : ℕ)) ∧
    ∀ k : ℤ, Int.gcd k 6 = 1 → Erdos634.LemmaKStar.K1 6 ![1, 1, 4] (fig D idx) k ∧
      Erdos634.LemmaKStar.K2 6 ![1, 1, 4] (fig D idx) k := by
  obtain ⟨D, ha⟩ := equil3_model_angles
  obtain ⟨idx, hidx⟩ := exists_idx D (n := 6) ![1, 1, 4] ha
  exact ⟨D, idx, lemmaK D (n := 6) (by norm_num) ![1, 1, 4] ha idx hidx⟩

/-- `lemmaV_prime` on a real dissection with PRIME N = 3: `3 ∣ 6` (the prime-form divisibility claim, genuinely tested). -/
theorem equil3_lemmaV_prime : (3 : ℕ) ∣ 6 := by
  obtain ⟨D, ha⟩ := equil3_model_angles
  exact Erdos634.Geometry.CaseA.LemmaV.lemmaV_prime D (n := 6) (by norm_num) ![1, 1, 4] ha
    (by norm_num) (by norm_num)

theorem equil3_lemmaV : Even (padicValNat 5 3) := by
  obtain ⟨D, ha⟩ := equil3_model_angles
  exact Erdos634.Geometry.CaseA.LemmaV.lemmaV D (n := 6) (by norm_num) ![1, 1, 4] ha (ℓ := 5)
    Nat.prime_five (by norm_num)

/-- discrimination: `![1,1,3]` (angle sum ≠ 6) is refuted for the model. -/
theorem equil3_discriminates : ¬ ∃ D : CongruentDissection 3,
    ∀ k, D.model.angleAt k = (![1, 1, 3] : Fin 3 → ℕ) k * Real.pi / (6 : ℕ) := by
  rintro ⟨D, h⟩
  have hs := D.model.angleAt_sum
  have := h 0; have := h 1; have := h 2
  simp [Fin.sum_univ_three] at *
  linarith [Real.pi_pos]

/-! ## (b) ladders of `PiFour.dissection` -/

open Erdos634.Draft.CaseALemmaHPiFour in
theorem ladder_pi4 (k : ℕ) (hk : 0 < k) :
    ∃ E : CongruentDissection (k * k * 2), E.model = dissection.model := by
  obtain ⟨hind, heta⟩ := Erdos634.Draft.RWEast.tri_eta dissection.target
  obtain ⟨E, -, hE⟩ := Erdos634.Ladder.ladder _ _ _ hind dissection heta k hk
  exact ⟨E, hE⟩

open Erdos634.Draft.CaseALemmaHPiFour in
theorem ladder_pi4_lemmas (k : ℕ) (hk : 0 < k) : ∃ E : CongruentDissection (k * k * 2),
    (∀ i j, A1Field.zc E ((E.tile i).pts j) ∈ A1Field.Lpaper 4 ![1, 2, 1]) ∧
    (∀ j, A1Field.zc E (E.target.pts j) ∈ A1Field.Lpaper 4 ![1, 2, 1]) ∧
    (∃ idx : Fin (k * k * 2) → Equiv.Perm (Fin 3),
      (∀ j, E.target.angleAt j = (Erdos634.LemmaKStar.uu ![1, 2, 1] (fig E idx) j : ℕ) * Real.pi / (4 : ℕ)) ∧
      ∀ u : ℤ, Int.gcd u 4 = 1 → Erdos634.LemmaKStar.K1 4 ![1, 2, 1] (fig E idx) u ∧
        Erdos634.LemmaKStar.K2 4 ![1, 2, 1] (fig E idx) u) ∧
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ 8 → Even (padicValNat ℓ (k * k * 2)) := by
  obtain ⟨E, hE⟩ := ladder_pi4 k hk
  have ha : ∀ i, E.model.angleAt i = (![1, 2, 1] : Fin 3 → ℕ) i * Real.pi / (4 : ℕ) := by
    intro i; rw [hE]; exact Erdos634.Draft.CaseALemmaVWitness.model_angles i
  have h1 := Erdos634.Geometry.A1Field.lemma1_full E (n := 4) (by norm_num) ![1, 2, 1] ha
  obtain ⟨idx, hidx⟩ := exists_idx E (n := 4) ![1, 2, 1] ha
  exact ⟨E, h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.1, ⟨idx, lemmaK E (n := 4) (by norm_num) ![1, 2, 1] ha idx hidx⟩,
    fun ℓ hℓ h8 => Erdos634.Geometry.CaseA.LemmaV.lemmaV E (n := 4) (by norm_num) ![1, 2, 1] ha hℓ
      (by simpa using h8)⟩

/-- N = 18, ℓ = 3: positive valuation `v₃(18) = 2`, even, on a real dissection (ladder k = 3 of the N = 2 tiling). -/
theorem ladder18_lemmaV : ∃ E : CongruentDissection 18, Even (padicValNat 3 18) ∧ padicValNat 3 18 = 2 := by
  obtain ⟨E, -, -, -, h⟩ := ladder_pi4_lemmas 3 (by norm_num)
  have hv : padicValNat 3 18 = 2 := by
    have : (18 : ℕ) = 3 ^ 2 * 2 := by norm_num
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  exact ⟨E, h 3 Nat.prime_three (by norm_num), hv⟩

end Erdos634.Draft.G3RCSmallControls

#print axioms Erdos634.Draft.G3RCSmallControls.equil3_lemma1_full
#print axioms Erdos634.Draft.G3RCSmallControls.equil3_lemmaK
#print axioms Erdos634.Draft.G3RCSmallControls.equil3_lemmaV_prime
#print axioms Erdos634.Draft.G3RCSmallControls.equil3_lemmaV
#print axioms Erdos634.Draft.G3RCSmallControls.equil3_discriminates
#print axioms Erdos634.Draft.G3RCSmallControls.ladder_pi4_lemmas
#print axioms Erdos634.Draft.G3RCSmallControls.ladder18_lemmaV
