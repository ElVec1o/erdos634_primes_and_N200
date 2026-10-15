-- No sorry, no native_decide.
-- Theorem H (`TheoremHCongruent.theorem_H_congruent`, via `L3MReal.theorem_H_real`) has conclusion `False`, so its
-- hypotheses cannot all be satisfied by a real dissection: such a dissection would be a counterexample.  This file
-- therefore gives a split control at the smallest member (e, f) = (2, 5) (tile (10,21,25), target legs 125, base 142,
-- m = 1 count N = 3 f^2 - e^2 = 71): a real `CongruentDissection` (N = 1, the one-tile dissection) that meets the
-- model-congruence hypothesis `hmod` and the arithmetic hypotheses, while the target-congruence hypothesis `htgt` is
-- refuted by an explicit side-length computation (the base 142 is not a side of the tile).  Each half is satisfiable;
-- only the conjunction is excluded by Theorem H.
import Erdos634.Draft.TheoremHCongruent

open scoped Classical

namespace Erdos634.Draft.G3HThmH

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord Erdos634.Draft.ModelWitnessE

theorem h1 : (0 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
theorem h2 : ((2 : ℕ) : ℝ) < ((5 : ℕ) : ℝ) := by norm_num

/-- The real one-tile dissection of the tile (10,21,25): `hmod` of `theorem_H_congruent` holds (reflexivity). -/
theorem hmod_witness :
    (single (tileTri ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2)).model.Congruent
      (tileTri ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2) := Tri.Congruent.refl _

/-- `htgt` FAILS for that dissection: its target (the tile) has no side of length 142 = base of `baseBetaTarget 2 5`. -/
theorem htgt_fails :
    ¬ (single (tileTri ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2)).target.Congruent
      (baseBetaTarget ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2) := by
  intro h
  have hm := h.sideMultiset_eq
  have hb := baseBetaTarget_dist_base h1 h2
  obtain ⟨s0, s1, s2⟩ := Erdos634.Draft.TheoremHCongruent.tileTri_sides h1 h2
  simp only [sideOpp, Erdos634.E1NormalForm.fin3_two_add_one, Erdos634.E1NormalForm.fin3_two_add_two,
    Erdos634.E1NormalForm.fin3_one_add_one, Erdos634.E1NormalForm.fin3_one_add_two,
    zero_add] at s0 s1 s2
  have hmem : dist ((baseBetaTarget ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 0)
      ((baseBetaTarget ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 1) ∈
      ({dist ((baseBetaTarget ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 0)
          ((baseBetaTarget ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 1),
        dist ((baseBetaTarget ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 2)
          ((baseBetaTarget ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 0),
        dist ((baseBetaTarget ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 1)
          ((baseBetaTarget ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 2)} : Multiset ℝ) := by simp
  rw [← hm] at hmem
  change _ ∈ ({dist ((tileTri ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 0)
        ((tileTri ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 1),
      dist ((tileTri ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 2)
        ((tileTri ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 0),
      dist ((tileTri ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 1)
        ((tileTri ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2).pts 2)} : Multiset ℝ) at hmem
  rw [hb, s0, s1, s2] at hmem
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
  norm_num at hmem

/-- The arithmetic hypotheses of `theorem_H_congruent` at (2, 5) hold. -/
theorem arith_25 : Nat.Coprime 2 5 ∧ 2 ≤ 2 ∧ 2 + 2 ≤ 5 := ⟨by decide, le_rfl, by norm_num⟩

/-- Split control, packaged: a real dissection with `hmod`, and `htgt` refuted for it; so the only way to meet the
whole premise set is a dissection that Theorem H proves does not exist. -/
theorem split_control :
    ∃ D : CongruentDissection 1,
      D.model.Congruent (tileTri ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2) ∧
      ¬ D.target.Congruent (baseBetaTarget ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2) :=
  ⟨_, hmod_witness, htgt_fails⟩

/-- The literal theorem applied with a hypothetical joint witness yields `False`: here, re-stated, so the
unsatisfiability is the theorem's content. -/
theorem no_joint_witness_25 :
    ¬ ∃ (N : ℕ) (D : CongruentDissection N),
      D.target.Congruent (baseBetaTarget ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2) ∧
      D.model.Congruent (tileTri ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) h1 h2) := by
  rintro ⟨N, D, ht, hm⟩
  exact Erdos634.Draft.TheoremHCongruent.theorem_H_congruent D (by decide) le_rfl (by norm_num) h1 h2 ht hm

end Erdos634.Draft.G3HThmH
#print axioms Erdos634.Draft.G3HThmH.hmod_witness
#print axioms Erdos634.Draft.G3HThmH.htgt_fails
#print axioms Erdos634.Draft.G3HThmH.split_control
#print axioms Erdos634.Draft.G3HThmH.no_joint_witness_25
