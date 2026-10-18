import Erdos634.Draft.ThmCPair

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D', module 2: the decidable condition on a G-leaf pair  

`thmDChk M M'` : with `g = Gd/2`, `u = (M'-M)/Gd`, `d = 2M/Gd`: `2 ≤ g ∧ (g - 1) d < u`.
(`g = 1` is the coprime pair, closed by `gPair_of_coprime`; the audit G2 requires `g ≥ 2` in the statement.)
-/

namespace Erdos634.Draft.ThmD

open Erdos634.Draft.ThmC

def thmDChk (M M' : ℕ) : Prop :=
  2 ≤ Gd M M' / 2 ∧ (Gd M M' / 2 - 1) * (2 * M / Gd M M') < (M' - M) / Gd M M'

instance (M M' : ℕ) : Decidable (thmDChk M M') := by unfold thmDChk; infer_instance

theorem thmDChk_param {M M' : ℕ} (hM : 0 < M) (hlt : 3 * M < M') (hpar : M % 2 = M' % 2)
    (h : thmDChk M M') :
    ∃ g u d : ℕ, 2 ≤ g ∧ 0 < d ∧ d < u ∧ Nat.Coprime u (u + d) ∧ M = g * d ∧ M' = g * (u + (u + d)) ∧
      (g - 1) * d < u := by
  obtain ⟨g, u, d, hg, hu, hd, hgp, hdp, hdu, hc, hM1, hM2⟩ := pair_param hM hlt hpar
  refine ⟨g, u, d, ?_, hdp, hdu, hc, hM1, hM2, ?_⟩
  · subst hg; exact h.1
  · subst hg hu hd; exact h.2

/-- witnesses: `(M,M') = (2,14)`: `g=2,u=3,d=1`; `(g-1)d = 1 < 3`. New relative to `thmCChk`: `(6,24)`-type pairs
with `g = ⌈u/d⌉`: `(u,d,g) = (3,2,2)`: `M = 4`, `M' = 2·8 = 16`: `thmDChk 4 16`, not `thmCChk 4 16` (`⌊2·5/3⌋·2 = 6 ≥ 3`). -/
example : thmDChk 2 14 := by decide
example : thmDChk 4 16 := by decide
example : ¬ thmCChk 4 16 := by decide
/-- negative controls: `(6,24)` is `(u,d,g) = (3,2,3)`, `(g-1)d = 4 ≥ 3`; `g = 1` pairs are excluded. -/
example : ¬ thmDChk 6 24 := by decide
example : ¬ thmDChk 1 9 := by decide

end Erdos634.Draft.ThmD

#print axioms Erdos634.Draft.ThmD.thmDChk_param
