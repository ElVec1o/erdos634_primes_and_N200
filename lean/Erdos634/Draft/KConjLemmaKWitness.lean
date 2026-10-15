-- Draft/KConjLemmaKWitness.lean — example for `lemmaK` in Draft/KConjLemmaK.lean:
-- K2 has teeth BEYOND K1.
--   Tile (1,1,3)π/5; corner figures f = ((0,1,0),(0,1,0),(0,3,0)) (target (1,1,3)π/5, its obtuse
--   corner filled by three π/5 corners).  K1 holds at every unit k (s_T = s_ABC = 1,1,2,2 at
--   k = 1,2,3,4), but K2 fails at k = 2 (f₃·x′ = 6/5 ≠ 1/5 = x′_{u₃}).  Hence, by `lemmaK`, no
--   CongruentDissection with model angles (1,1,3)π/5 has these corner figures, for any corner
--   labelling — a non-existence consequence that K1 alone (`lemmaK_K1`) cannot give.
-- (The joint witness for `lemmaK` itself is `KConj.lemmaK_witness`, on the real HPiFour dissection.)
-- Imported directly by All.lean.  No (e, f) is evaluated.
import Erdos634.Draft.KConjLemmaK

namespace Erdos634.KConj.Witness

open Erdos634.Geometry Erdos634.LemmaKStar Erdos634.KConj

def fBad2 : Fin 3 → Fin 3 → ℕ := ![![0, 1, 0], ![0, 1, 0], ![0, 3, 0]]

theorem K1_holds : ∀ k ∈ ({1, 2, 3, 4} : Finset ℤ), K1 5 ![1, 1, 3] fBad2 k := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
  · unfold K1 sT sABC xv yv uu fBad2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    try norm_num [Int.fract]

theorem K2_teeth : ¬ K2 5 ![1, 1, 3] fBad2 2 := by
  intro h
  have h2 := h 2
  unfold xp xpu sT xv yv uu fBad2 at h2
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h2
  norm_num [Int.fract] at h2

theorem no_dissection_fig {N : ℕ} (D : CongruentDissection N)
    (ha : ∀ i, D.model.angleAt i = (![1, 1, 3] : Fin 3 → ℕ) i * Real.pi / (5 : ℕ))
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i v, (D.tile i).angleAt v = (![1, 1, 3] : Fin 3 → ℕ) (idx i v) * Real.pi / (5 : ℕ)) :
    fig D idx ≠ fBad2 := by
  intro h
  have := ((lemmaK D (n := 5) (by norm_num) _ ha idx hidx).2 2 (by decide)).2
  rw [h] at this
  exact K2_teeth this

end Erdos634.KConj.Witness

#print axioms Erdos634.KConj.Witness.K1_holds
#print axioms Erdos634.KConj.Witness.K2_teeth
#print axioms Erdos634.KConj.Witness.no_dissection_fig
