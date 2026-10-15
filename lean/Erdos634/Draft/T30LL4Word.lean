import Mathlib.Tactic
import Erdos634.Draft.T30LL4Chain

/-!
# From a chain-sum with a `b`-edge to a word with `y ≥ 1`

`word_of_sum_with`: on a `CongruentDissection` with `SixtyData` model (`a, b, c` pairwise distinct), if a finite set `S` of tile edges has total length `L` and contains an edge of length `b`,
then `x a + y b + z c = L` for naturals `x, y, z` with `1 ≤ y` (counts of the edges of length `a`, `b`, `c`).  Every edge length is one of `a, b, c` (`edge_length_trichotomy`, `sideLen_mem`).
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.Pi3F6 Erdos634.EdgeWordConversion

theorem word_of_sum_with {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hS : D.model.SixtyData α a b c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (S : Finset (Fin N × Fin 3)) (L : ℝ) (hL : 0 ≤ L)
    (hsum : ∑ e ∈ S, ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal L)
    (e0 : Fin N × Fin 3) (he0 : e0 ∈ S)
    (hb : dist ((D.tile e0.1).pts e0.2) ((D.tile e0.1).pts (e0.2 + 1)) = b) :
    ∃ x y z : ℕ, 1 ≤ y ∧ (x : ℝ) * a + y * b + z * c = L := by
  classical
  set len : Fin N × Fin 3 → ℝ := fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) with hlen
  have hreal : ∑ e ∈ S, len e = L := by
    have := congrArg ENNReal.toReal hsum
    rwa [ENNReal.toReal_sum (fun e _ => ENNReal.ofReal_ne_top),
      Finset.sum_congr rfl (fun e _ => ENNReal.toReal_ofReal dist_nonneg),
      ENNReal.toReal_ofReal hL] at this
  have hmem : ∀ e, len e = a ∨ len e = b ∨ len e = c := by
    intro e
    rcases edge_length_trichotomy D e.1 e.2 with h | h | h <;> rw [hlen] <;> simp only <;> rw [h] <;>
      exact sideLen_mem D hS _
  have s1 := Finset.sum_filter_add_sum_filter_not S (fun e => len e = a) (len)
  have s2 := Finset.sum_filter_add_sum_filter_not (S.filter (fun e => ¬ len e = a)) (fun e => len e = b) (len)
  have hA : ∑ e ∈ S.filter (fun e => len e = a), len e = ((S.filter (fun e => len e = a)).card : ℝ) * a := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2), Finset.sum_const, nsmul_eq_mul]
  have hB : ∑ e ∈ (S.filter (fun e => ¬ len e = a)).filter (fun e => len e = b), len e
      = (((S.filter (fun e => ¬ len e = a)).filter (fun e => len e = b)).card : ℝ) * b := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2), Finset.sum_const, nsmul_eq_mul]
  have hC : ∑ e ∈ (S.filter (fun e => ¬ len e = a)).filter (fun e => ¬ len e = b), len e
      = (((S.filter (fun e => ¬ len e = a)).filter (fun e => ¬ len e = b)).card : ℝ) * c := by
    rw [Finset.sum_congr (g := fun _ => c) rfl (fun e he => by
      obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
      obtain ⟨he3, he4⟩ := Finset.mem_filter.mp he1
      rcases hmem e with h | h | h
      · exact absurd h he4
      · exact absurd h he2
      · exact h), Finset.sum_const, nsmul_eq_mul]
  refine ⟨(S.filter (fun e => len e = a)).card,
    ((S.filter (fun e => ¬ len e = a)).filter (fun e => len e = b)).card,
    ((S.filter (fun e => ¬ len e = a)).filter (fun e => ¬ len e = b)).card, ?_, ?_⟩
  · apply Finset.card_pos.mpr
    exact ⟨e0, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he0, by
      show ¬ len e0 = a
      rw [hlen]; simp only; rw [hb]; exact fun h => hab h.symm⟩, hb⟩⟩
  · rw [← hreal, ← s1, ← s2, hA, hB, hC]; ring

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.word_of_sum_with
