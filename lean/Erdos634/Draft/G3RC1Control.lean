-- No sorry, no native_decide.
-- CONTROL C1 on a REAL non-edge-to-edge tiling with rational angles: the equilateral triangle (real side 2) tiled
-- by eight 30-60-90 tiles (4 T-junction incidences, reflections used).  Instantiates the premises of
-- `lemma1_full`, `lemmaK` (with `fig` evaluated), `lemmaH` (θ = π/3), `lemmaV` (ℓ = 5) and APPLIES them.
-- Premise data: model angles (π/6, π/3, π/2) = ![1,2,3]·π/6, n = 6; target angles (2,2,2)·π/6.
import Erdos634.Draft.G3RC1Tiling
import Erdos634.Draft.G3RCCommon
import Erdos634.Draft.A1FieldClause
import Erdos634.Draft.CaseALemmaHExc2
import Erdos634.Draft.CaseALemmaH
import Erdos634.Draft.CaseALemmaVDissection

namespace Erdos634.Draft.G3RC1Control

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.G3RCAngles
  Erdos634.Draft.G3RCCommon Erdos634.Draft.G3RC1Tiling Erdos634.KConj

/-- the real dissection -/
noncomputable abbrev D : CongruentDissection cert.leaves.length := cd cert cert_ok

theorem hT : 0 < cross cert.target.1 cert.target.2.1 cert.target.2.2 := by decide
theorem hgood : ∀ t ∈ cert.leaves, goodT t := by decide +kernel
theorem hgM : goodT cert.model := by decide +kernel
theorem hmid : ∀ k, midx cert.model k = k := by decide +kernel

theorem ha (k : Fin 3) :
    D.model.angleAt k = (![1, 2, 3] : Fin 3 → ℕ) k * Real.pi / (6 : ℕ) :=
  model_angles cert cert_ok hgM hmid k

theorem target_angle (j : Fin 3) :
    D.target.angleAt j = (![2, 2, 2] : Fin 3 → ℕ) j * Real.pi / (6 : ℕ) := by
  have key : ∀ k, oppSq cert.target k = 64 := by decide
  have oA := oppLen_sq cert.target hT j
  have oB := oppLen_sq cert.target hT (j + 1)
  have oC := oppLen_sq cert.target hT (j + 2)
  rw [key] at oA oB oC
  have := ang_val (triOf cert.target hT) j _ _ _ 64 (Real.pi / 3) (by simpa using oA) (by simpa using oB)
    (by simpa using oC) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by rw [Real.cos_pi_div_three]; norm_num)
  have e : D.target = triOf cert.target hT := cd_target cert cert_ok
  rw [e, this]; fin_cases j <;> simp <;> ring

/-- (1) `lemma1_full` on the real dissection (all 9 conjuncts). -/
theorem c1_lemma1_full :
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

/-- (2) `lemmaK`: any corner labelling gives corner figures with the stated table; K1 ∧ K2 hold at the units. -/
def tab : Fin 3 → Fin 3 → ℕ := ![![0, 1, 0], ![0, 1, 0], ![2, 0, 0]]

theorem latFig_tab : ∀ j l, latFig cert j l = tab j l := by decide +kernel

theorem c1_lemmaK :
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

/-- the corner-figure table reproduces the independently computed target angles (2,2,2)·π/6 -/
theorem uu_tab : ∀ j, Erdos634.LemmaKStar.uu ![1, 2, 3] tab j = (![2, 2, 2] : Fin 3 → ℕ) j := by decide

/-- (3) `lemmaH` with θ = π/3: acute model angle at vertex 1, right angle at vertex 2, target angle θ at vertices 0, 1. -/
theorem hmp : D.model.angleAt 1 = Real.pi / 3 := by
  have := ha 1; simp at this; linarith
theorem hmq : D.model.angleAt 2 = Real.pi / 2 := by
  have := ha 2; simp at this; linarith
theorem hti (j : Fin 3) : D.target.angleAt j = Real.pi / 3 := by
  have := target_angle j; fin_cases j <;> simp at this ⊢ <;> linarith

theorem c1_lemmaH : ¬ ((cert.leaves.length).Prime ∧ 5 ≤ cert.leaves.length) :=
  Erdos634.Geometry.CaseA.LemmaH.lemmaH D ⟨1 / 3, by push_cast; ring⟩ (by positivity)
    (by linarith [Real.pi_pos]) (p := 1) (q := 2) (by decide) hmp hmq (i := 0) (j := 1) (by decide)
    (hti 0) (hti 1)

theorem c1_count_eq : ∃ r x y : ℕ, ((cert.leaves.length : ℕ) : ℝ) =
    2 * ((r : ℝ) + x * Real.sin (Real.pi / 3) + y * Real.cos (Real.pi / 3)) ^ 2 :=
  Erdos634.Geometry.CaseA.LemmaH.count_eq D (by positivity) (by linarith [Real.pi_pos])
    (p := 1) (q := 2) (by decide) hmp hmq (i := 0) (j := 1) (by decide) (hti 0) (hti 1)

/-- (4) `lemmaV` with ℓ = 5 (v₅(8) = 0: low information) and the premise-free sine identity `star`. -/
theorem c1_lemmaV : Even (padicValNat 5 8) := by
  have := Erdos634.Geometry.CaseA.LemmaV.lemmaV D (n := 6) (by norm_num) ![1, 2, 3] ha (ℓ := 5)
    Nat.prime_five (by norm_num)
  rwa [show cert.leaves.length = 8 from cert_len] at this

theorem hm0 : D.model.angleAt 0 = Real.pi / 6 := by
  have := ha 0; simp at this; linarith

/-- the premise-free sine identity `star`, evaluated on C1: the side word `c` of target side 0 satisfies
`c₀·sin(π/6) + c₁·sin(π/3) + c₂·sin(π/2) = 2` (N sin A₀ sin A₁ sin A₂ sin B₀ = X² sin B₁ sin B₂ with N = 8). -/
theorem c1_star : ∃ c : Fin 3 → ℕ, (c 0 : ℝ) * (1 / 2) + c 1 * (Real.sqrt 3 / 2) + c 2 * 1 = 2 := by
  obtain ⟨c, hc⟩ := Erdos634.Geometry.CaseA.LemmaV.star D
  refine ⟨c, ?_⟩
  have hN : ((cert.leaves.length : ℕ) : ℝ) = 8 := by rw [cert_len]; norm_num
  simp only [Fin.sum_univ_three] at hc
  rw [hN, hm0, hmp, hmq, hti 0, hti 1, hti 2] at hc
  simp only [Real.sin_pi_div_six, Real.sin_pi_div_three, Real.sin_pi_div_two] at hc
  have s := s3pos; have s2 := s3sq'
  set X : ℝ := (c 0 : ℝ) * (1 / 2) + c 1 * (Real.sqrt 3 / 2) + c 2 * 1 with hX
  have hX0 : 0 ≤ X := by positivity
  have hX2 : X ^ 2 = 4 := by
    have : X ^ 2 * (3 / 4) = 3 := by rw [hX]; push_cast at hc; nlinarith
    nlinarith
  nlinarith

/-- (5) the tiling is genuinely not edge-to-edge: two explicit T-junction incidences (vertex of one tile in the open edge of another). -/
theorem tjunction1 : ∃ (i j : Fin cert.leaves.length) (v m : Fin 3),
    (D.tile i).pts v ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)) :=
  ⟨⟨2, by decide⟩, ⟨6, by decide⟩, 2, 2, tjunction cert cert_ok _ _ _ _ (by decide +kernel) (by decide +kernel)⟩

theorem tjunction2 : ∃ (i j : Fin cert.leaves.length) (v m : Fin 3),
    (D.tile i).pts v ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)) :=
  ⟨⟨4, by decide⟩, ⟨3, by decide⟩, 2, 2, tjunction cert cert_ok _ _ _ _ (by decide +kernel) (by decide +kernel)⟩

/-- (6) premise discrimination: a wrong angle vector is refuted. -/
theorem ha_discriminates : ¬ ∀ k, D.model.angleAt k = (![1, 2, 2] : Fin 3 → ℕ) k * Real.pi / (6 : ℕ) := by
  intro h
  have h2 := h 2; have h3 := ha 2
  rw [h3] at h2; simp at h2 <;> linarith [Real.pi_pos]

/-- (7) negative controls: the kernel rejects perturbed certificates. -/
def clBad : Bsp := Bsp.split (4,0) (2,2) (.split (2,0) (2,2) (.leaf ((0,0),(2,0),(2,3))) (.leaf ((2,0),(4,0),(2,2)))) (.split (4,0) (5,1) (.split (6,2) (2,2) (.split (5,1) (2,2) (.leaf ((2,2),(4,0),(5,1))) (.leaf ((2,2),(5,1),(6,2)))) (.split (4,2) (4,4) (.leaf ((4,4),(2,2),(4,2))) (.leaf ((4,4),(4,2),(6,2))))) (.split (6,0) (6,2) (.leaf ((4,0),(6,0),(6,2))) (.leaf ((6,0),(8,0),(6,2)))))

def certBad : Cert := { target := ((0,0),(8,0),(4,4)), model := ((0,2),(-2,0),(0,0)), clusters := [clBad], seps := [] }
def certBadModel : Cert := { cert with model := ((0,2),(-2,0),(0,1)) }
def certDrop : Cert := { cert with clusters := [Bsp.split (4,0) (2,2) (.leaf ((0,0),(2,0),(2,2))) (.leaf ((2,0),(4,0),(2,2)))] }

theorem bad_rejected : certBad.ok = false := by decide +kernel
theorem badModel_rejected : certBadModel.ok = false := by decide +kernel
theorem drop_rejected : certDrop.ok = false := by decide +kernel
theorem good_accepted : cert.ok = true := cert_ok

end Erdos634.Draft.G3RC1Control

#print axioms Erdos634.Draft.G3RC1Control.c1_lemma1_full
#print axioms Erdos634.Draft.G3RC1Control.c1_lemmaK
#print axioms Erdos634.Draft.G3RC1Control.uu_tab
#print axioms Erdos634.Draft.G3RC1Control.c1_lemmaH
#print axioms Erdos634.Draft.G3RC1Control.c1_count_eq
#print axioms Erdos634.Draft.G3RC1Control.c1_lemmaV
#print axioms Erdos634.Draft.G3RC1Control.c1_star
#print axioms Erdos634.Draft.G3RC1Control.tjunction1
#print axioms Erdos634.Draft.G3RC1Control.tjunction2
#print axioms Erdos634.Draft.G3RC1Control.ha_discriminates
#print axioms Erdos634.Draft.G3RC1Control.bad_rejected
#print axioms Erdos634.Draft.G3RC1Control.badModel_rejected
#print axioms Erdos634.Draft.G3RC1Control.drop_rejected
