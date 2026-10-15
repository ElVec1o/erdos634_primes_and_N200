-- Draft/CaseALemmaK1Witness.lean: joint witness and counterexample for
-- Draft/CaseALemmaK1.lean `lemmaK_K1` (Case A, Lemma K, K1 half).
-- Witness: the real `CongruentDissection 2` of CaseALemmaHPiFour (isosceles right triangle cut by
-- its altitude): model angles (1,2,1)·π/4, target angles (1,1,2)·π/4, corner figures
-- f = ((1,0,0),(1,0,0),(1,0,1)) (the apex carries both tiles' π/4 corners).  Every hypothesis of
-- `lemmaK_K1` discharged; conclusion K1 at every unit k.
-- Counterexample: K1 is not vacuous: for tile (1,1,3)π/5 on target (1,2,2)π/5, K1 fails at k = 2,
-- so by `lemmaK_K1` no CongruentDissection has those angles.
import Erdos634.Draft.CaseALemmaK1
import Erdos634.Draft.CaseALemmaVWitness

namespace Erdos634.Draft.CaseALemmaK1Witness

open Erdos634.Geometry Erdos634.Draft.CaseALemmaHPiFour Erdos634.Geometry.CaseA.LemmaK1
  Erdos634.LemmaKStar

def fW : Fin 3 → Fin 3 → ℕ := ![![1, 0, 0], ![1, 0, 0], ![1, 0, 1]]

theorem target_angles (j : Fin 3) :
    dissection.target.angleAt j = (uu ![1, 2, 1] fW j : ℕ) * Real.pi / (4 : ℕ) := by
  have h0 := target_angleAt0; have h1 := target_angleAt1
  have hs := dissection.target.angleAt_sum
  fin_cases j <;> simp [uu, fW, Fin.sum_univ_three] <;> linarith

theorem lemmaK_K1_witness {k : ℤ} (hk : Int.gcd k 4 = 1) : K1 4 ![1, 2, 1] fW k :=
  lemmaK_K1 dissection (n := 4) (by norm_num) ![1, 2, 1]
    Erdos634.Draft.CaseALemmaVWitness.model_angles fW target_angles hk

def fBad : Fin 3 → Fin 3 → ℕ := ![![1, 0, 0], ![2, 0, 0], ![2, 0, 0]]

theorem K1_teeth : ¬ K1 5 ![1, 1, 3] fBad 2 := by
  unfold K1 sT sABC xv yv uu fBad
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

theorem no_dissection_11_3_on_1_2_2 {N : ℕ} (D : CongruentDissection N)
    (ha : ∀ i, D.model.angleAt i = (![1, 1, 3] : Fin 3 → ℕ) i * Real.pi / (5 : ℕ))
    (hf : ∀ j, D.target.angleAt j = (uu ![1, 1, 3] fBad j : ℕ) * Real.pi / (5 : ℕ)) : False :=
  K1_teeth (lemmaK_K1 D (n := 5) (by norm_num) _ ha fBad hf (k := 2) (by decide))

end Erdos634.Draft.CaseALemmaK1Witness

#print axioms Erdos634.Draft.CaseALemmaK1Witness.lemmaK_K1_witness
#print axioms Erdos634.Draft.CaseALemmaK1Witness.K1_teeth
#print axioms Erdos634.Draft.CaseALemmaK1Witness.no_dissection_11_3_on_1_2_2
