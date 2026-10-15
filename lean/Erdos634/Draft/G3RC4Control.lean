-- No sorry, no native_decide.
-- CONTROL C4 on a REAL non-edge-to-edge tiling with rational angles: the 30-60-90 triangle (legs √3, 3) tiled by twelve 30-60-90 tiles.
-- (T-junction incidences: 5; both chiralities used).  Premise data: model angles (π/6, π/3, π/2) = ![1,2,3]·π/6, n = 6;
-- target angles (3,1,2)·π/6.  Instantiates and APPLIES lemma1_full, lemmaK (fig evaluated), lemmaV (ℓ = 5), star.
import Erdos634.Draft.G3RC4Tiling
import Erdos634.Draft.G3RCCommon
import Erdos634.Draft.A1FieldClause
import Erdos634.Draft.CaseALemmaHExc2
import Erdos634.Draft.CaseALemmaH
import Erdos634.Draft.CaseALemmaVDissection

namespace Erdos634.Draft.G3RC4Control

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.G3RCAngles
  Erdos634.Draft.G3RCCommon Erdos634.Draft.G3RC4Tiling Erdos634.KConj

noncomputable abbrev D : CongruentDissection cert.leaves.length := cd cert cert_ok

theorem hT : 0 < cross cert.target.1 cert.target.2.1 cert.target.2.2 := by decide
theorem hgood : ∀ t ∈ cert.leaves, goodT t := by decide +kernel
theorem hgM : goodT cert.model := by decide +kernel
theorem hmid : ∀ k, midx cert.model k = k := by decide +kernel

theorem ha (k : Fin 3) :
    D.model.angleAt k = (![1, 2, 3] : Fin 3 → ℕ) k * Real.pi / (6 : ℕ) :=
  model_angles cert cert_ok hgM hmid k

theorem e_tgt : D.target = triOf cert.target hT := cd_target cert cert_ok

theorem hm0 : D.model.angleAt 0 = Real.pi / 6 := by
  have := ha 0; simp at this; linarith
theorem hmp : D.model.angleAt 1 = Real.pi / 3 := by
  have := ha 1; simp at this; linarith
theorem hmq : D.model.angleAt 2 = Real.pi / 2 := by
  have := ha 2; simp at this; linarith

theorem hti0 : D.target.angleAt 0 = Real.pi / 2 := by
  have s := s3pos; have s2 := s3sq'
  have k0 : oppSq cert.target 0 = 192 := by decide
  have k1 : oppSq cert.target (0 + 1) = 48 := by decide
  have k2 : oppSq cert.target (0 + 2) = 144 := by decide
  have oA := oppLen_sq cert.target hT 0
  have oB := oppLen_sq cert.target hT (0 + 1)
  have oC := oppLen_sq cert.target hT (0 + 2)
  rw [k0] at oA; rw [k1] at oB; rw [k2] at oC
  rw [e_tgt]
  refine ang_val (triOf cert.target hT) 0 _ _ _ (48 * Real.sqrt 3) _ (by simpa using oA) (by simpa using oB)
    (by simpa using oC) (by norm_num) (by norm_num) (by positivity) (by nlinarith) (by positivity)
    (by linarith [Real.pi_pos]) ?_
  rw [Real.cos_pi_div_two]; norm_num

theorem hti1 : D.target.angleAt 1 = Real.pi / 6 := by
  have s := s3pos; have s2 := s3sq'
  have k0 : oppSq cert.target 1 = 48 := by decide
  have k1 : oppSq cert.target (1 + 1) = 144 := by decide
  have k2 : oppSq cert.target (1 + 2) = 192 := by decide
  have oA := oppLen_sq cert.target hT 1
  have oB := oppLen_sq cert.target hT (1 + 1)
  have oC := oppLen_sq cert.target hT (1 + 2)
  rw [k0] at oA; rw [k1] at oB; rw [k2] at oC
  rw [e_tgt]
  refine ang_val (triOf cert.target hT) 1 _ _ _ (96 * Real.sqrt 3) _ (by simpa using oA) (by simpa using oB)
    (by simpa using oC) (by norm_num) (by norm_num) (by positivity) (by nlinarith) (by positivity)
    (by linarith [Real.pi_pos]) ?_
  rw [Real.cos_pi_div_six]; field_simp; nlinarith

theorem hti2 : D.target.angleAt 2 = Real.pi / 3 := by
  have := D.target.angleAt_sum; rw [hti0, hti1] at this; linarith

theorem target_angle (j : Fin 3) :
    D.target.angleAt j = (![3, 1, 2] : Fin 3 → ℕ) j * Real.pi / (6 : ℕ) := by
  fin_cases j
  · simp [hti0]; linarith
  · simp [hti1]
  · simp [hti2]; linarith

theorem c4_lemma1_full :
    0 < A1Field.circD D.model ∧
    (∀ k, D.model.oppLen k = A1Field.circD D.model * Real.sin (((![1, 2, 3] : Fin 3 → ℕ) k : ℝ) * Real.pi / (6 : ℕ))) ∧
    A1Field.zc D (D.target.pts 0) = 0 ∧
    A1Field.zc D (D.target.pts 1) = ((dist (D.target.pts 1) (D.target.pts 0) / A1Field.circD D.model : ℝ) : ℂ) ∧
    0 < dist (D.target.pts 1) (D.target.pts 0) / A1Field.circD D.model ∧
    (∀ i k, (D.tile i).pts k - D.target.pts 0 ∈ A1Pos.Lform D 6) ∧
    (∀ i k, A1Field.zc D ((D.tile i).pts k) ∈ A1Field.Lpaper 6 ![1, 2, 3]) ∧
    (∀ k, A1Field.zc D (D.target.pts k) ∈ A1Field.Lpaper 6 ![1, 2, 3]) ∧
    (∀ x ∈ A1Field.Lpaper 6 ![1, 2, 3], x ∈ CaseA.LemmaV.Kf 6) :=
  Erdos634.Geometry.A1Field.lemma1_full D (n := 6) (by norm_num) ![1, 2, 3] ha

def tab : Fin 3 → Fin 3 → ℕ := ![![0, 0, 1], ![1, 0, 0], ![2, 0, 0]]

theorem latFig_tab : ∀ j l, latFig cert j l = tab j l := by decide +kernel

theorem c4_lemmaK :
    ∃ idx : Fin cert.leaves.length → Equiv.Perm (Fin 3),
      (∀ i v, (D.tile i).angleAt v = (![1, 2, 3] : Fin 3 → ℕ) (idx i v) * Real.pi / (6 : ℕ)) ∧
      fig D idx = tab ∧
      (∀ j, D.target.angleAt j = (Erdos634.LemmaKStar.uu ![1, 2, 3] tab j : ℕ) * Real.pi / (6 : ℕ)) ∧
      ∀ k : ℤ, Int.gcd k 6 = 1 → Erdos634.LemmaKStar.K1 6 ![1, 2, 3] tab k ∧
        Erdos634.LemmaKStar.K2 6 ![1, 2, 3] tab k := by
  obtain ⟨idx, hidx⟩ := exists_idx D (n := 6) ![1, 2, 3] ha
  have hf : fig D idx = tab := by
    funext j l; rw [fig_eq cert cert_ok hgood idx hidx, latFig_tab]
  have := lemmaK D (n := 6) (by norm_num) ![1, 2, 3] ha idx hidx
  rw [hf] at this
  exact ⟨idx, hidx, hf, this⟩

/-- the corner-figure table reproduces the independently computed target angles -/
theorem uu_tab : ∀ j, Erdos634.LemmaKStar.uu ![1, 2, 3] tab j = (![3, 1, 2] : Fin 3 → ℕ) j := by decide

-- lemmaH is NOT applicable to C4 (target angles (3,1,2) have no two equal acute angles).

theorem c4_lemmaV : Even (padicValNat 5 12) := by
  have := Erdos634.Geometry.CaseA.LemmaV.lemmaV D (n := 6) (by norm_num) ![1, 2, 3] ha (ℓ := 5)
    Nat.prime_five (by norm_num)
  rwa [show cert.leaves.length = 12 from cert_len] at this

/-- the premise-free sine identity `star` on C4 (N = 12): side word `c` of target side 0 has
`c₀·sin(π/6) + c₁·sin(π/3) + c₂·sin(π/2) = 2√3` (X² = 12). -/
theorem c4_star : ∃ c : Fin 3 → ℕ, (c 0 : ℝ) * (1 / 2) + c 1 * (Real.sqrt 3 / 2) + c 2 * 1 = 2 * Real.sqrt 3 := by
  obtain ⟨c, hc⟩ := Erdos634.Geometry.CaseA.LemmaV.star D
  refine ⟨c, ?_⟩
  have hN : ((cert.leaves.length : ℕ) : ℝ) = 12 := by rw [cert_len]; norm_num
  simp only [Fin.sum_univ_three] at hc
  rw [hN, hm0, hmp, hmq, hti0, hti1, hti2] at hc
  simp only [Real.sin_pi_div_six, Real.sin_pi_div_three, Real.sin_pi_div_two] at hc
  have s := s3pos; have s2 := s3sq'
  set X : ℝ := (c 0 : ℝ) * (1 / 2) + c 1 * (Real.sqrt 3 / 2) + c 2 * 1 with hX
  have hX0 : 0 ≤ X := by positivity
  have hX2 : X ^ 2 = 12 := by
    have : X ^ 2 * (Real.sqrt 3 / 4) = 3 * Real.sqrt 3 := by rw [hX]; nlinarith
    nlinarith
  nlinarith [sq_nonneg (X - 2 * Real.sqrt 3), sq_nonneg (X + 2 * Real.sqrt 3)]

theorem tjunction1 : ∃ (i j : Fin cert.leaves.length) (v m : Fin 3),
    (D.tile i).pts v ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)) :=
  ⟨⟨4, by decide⟩, ⟨2, by decide⟩, 1, 2, tjunction cert cert_ok _ _ _ _ (by decide +kernel) (by decide +kernel)⟩

theorem tjunction2 : ∃ (i j : Fin cert.leaves.length) (v m : Fin 3),
    (D.tile i).pts v ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)) :=
  ⟨⟨9, by decide⟩, ⟨4, by decide⟩, 1, 2, tjunction cert cert_ok _ _ _ _ (by decide +kernel) (by decide +kernel)⟩

theorem ha_discriminates : ¬ ∀ k, D.model.angleAt k = (![1, 2, 2] : Fin 3 → ℕ) k * Real.pi / (6 : ℕ) := by
  intro h
  have h2 := h 2; have h3 := ha 2
  rw [h3] at h2; simp at h2 <;> linarith [Real.pi_pos]

/-- negative controls: the kernel rejects perturbed certificates -/
def certBadTarget : Cert := { cert with target := (cert.target.1, cert.target.2.1, (cert.target.2.2.1, cert.target.2.2.2 + 1)) }
def certBadModel : Cert := { cert with model := ((0,2),(-2,0),(0,1)) }
def certDrop : Cert := { cert with clusters := [Bsp.leaf cert.leaves.head!] }

theorem badTarget_rejected : certBadTarget.ok = false := by decide +kernel
theorem badModel_rejected : certBadModel.ok = false := by decide +kernel
theorem drop_rejected : certDrop.ok = false := by decide +kernel

end Erdos634.Draft.G3RC4Control

#print axioms Erdos634.Draft.G3RC4Control.c4_lemma1_full
#print axioms Erdos634.Draft.G3RC4Control.c4_lemmaK
#print axioms Erdos634.Draft.G3RC4Control.uu_tab
#print axioms Erdos634.Draft.G3RC4Control.c4_lemmaV
#print axioms Erdos634.Draft.G3RC4Control.c4_star
#print axioms Erdos634.Draft.G3RC4Control.tjunction1
#print axioms Erdos634.Draft.G3RC4Control.tjunction2
#print axioms Erdos634.Draft.G3RC4Control.ha_discriminates
#print axioms Erdos634.Draft.G3RC4Control.badTarget_rejected
#print axioms Erdos634.Draft.G3RC4Control.badModel_rejected
#print axioms Erdos634.Draft.G3RC4Control.drop_rejected
