import Erdos634.ChordFinsetReachLemma
namespace Erdos634.Draft.ChordFinsetReachLemmaWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_reach_of_le_all {N : ℕ} {P bound' : Plane} {R S : Fin N → Plane} {L' : List (Fin N)}
    {g' : ℕ → Plane}
    (hg'0 : g' 0 = bound')
    (hg'match : ∀ i (h : i < L'.length),
      g' (2 * i + 1) = R (L'.get ⟨i, h⟩) ∧ g' (2 * i + 2) = S (L'.get ⟨i, h⟩))
    (hgo : ∀ k ∈ L', Wbtw ℝ P (R k) (S k))
    (hle' : ∀ k ∈ L', Wbtw ℝ P bound' (R k)) :
    ∀ i, i ≤ 2 * L'.length → Wbtw ℝ P bound' (g' i) :=
  reach_of_le_all hg'0 hg'match hgo hle'

example : True := trivial
#print axioms reach_of_le_all
end Erdos634.Draft.ChordFinsetReachLemmaWrap
