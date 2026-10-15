import Mathlib.Tactic
import Erdos634.Draft.GLIFinal
import Erdos634.Draft.GLCWit

/-!
# Witnesses and counterexample checks on the real `N = 1125` dissection (`k = 2`, tile `(4,5,6)·16`)

`G3GControl.D` is a certified `CongruentDissection 1125`, model `TwoAlphaData α 64 80 96` (`= 16·(k², 2k+1, k(k+1))`, `k = 2`, `s = 16`), target isosceles with base angles
`α` at vertices `0`, `1` and legs `2400 = 16·150`, base `3600`.  It satisfies every hypothesis of `leafG_of_dissection` EXCEPT the two that define the leaf-G family:
`3 ≤ k` (here `k = 2`) and the leaf-scale leg `s·2k(2k+1) = 320` (here `2400`); `ctl_hX` records that the leg hypothesis really fails.
The interface lemmas used by the proof are instantiated on `D`:
* `wit_V`: chains of a real side exist and `sideOf_V` applies;
* `wit_sum`: the chain sum equals the side length (`150 = 2400/16` at `k = 2`);
* `wit_corner`: `corner_both` (corner tile, `K` coupling, `C2`) at the corner `0`, with the `k = 2` word lemma;
* `wit_apex`: `apex_pair` for the two legs.
Not witnessed (no real dissection with `k ≥ 3` is available): `leafG_core` / `leafG_of_dissection` themselves (the conclusion is `False`), and
`corner_G2_core` (needs the `(c,c)` chain configuration, which is a property of the chosen chains).
Counterexample checks: `ctl_apex_base` (the apex lemma's hypothesis `angleAt r = π − 2α` fails at a base corner), `ctl_hX`.
-/

namespace Erdos634.GLI

open Erdos634.Geometry Erdos634.Draft.G3GControl Erdos634.GLG

theorem t_ang2 : D.target.angleAt 2 = Real.pi - 2 * α := by
  have hsum := D.target.angleAt_sum
  rw [t_ang0, t_ang1] at hsum; linarith

theorem dist12_1125 : dist (D.target.pts 1) (D.target.pts 2) = 2400 := t_opp0
theorem dist20_1125 : dist (D.target.pts 2) (D.target.pts 0) = 2400 := t_opp1

theorem wit_V : ∃ (w : Wall D.toDissection) (E : ℕ → Fin _ × Fin 3) (n : ℕ), IsChain w E n ∧
    (sideOf D α 64 80 w.dir E n).V := by
  obtain ⟨w, -, -⟩ := exists_wall D.toDissection 0 1 (by decide)
  obtain ⟨E, n, C⟩ := w.exists_chain D.toDissection.pos
  exact ⟨w, E, n, C, sideOf_V D α_irr data C⟩

theorem wit_sum : ∃ (w : Wall D.toDissection) (E : ℕ → Fin _ × Fin 3) (n : ℕ), IsChain w E n ∧
    w.a = D.target.pts 1 ∧ w.b = D.target.pts 2 ∧
    ∑ m ∈ Finset.range n, lenK 2 ((sideOf D α 64 80 w.dir E n).ty m) = 150 := by
  obtain ⟨w, hwa, hwb⟩ := exists_wall D.toDissection 1 2 (by decide)
  obtain ⟨E, n, C⟩ := w.exists_chain D.toDissection.pos
  refine ⟨w, E, n, C, hwa, hwb, ?_⟩
  exact sum_lenK_nat D 2 (s := 16) (by norm_num) α_irr data (by norm_num) (by norm_num) (by norm_num)
    C 150 (by rw [hwa, hwb, dist12_1125]; norm_num)

theorem wit_corner : ∃ (wa wb : Wall D.toDissection) (Ea Eb : ℕ → Fin _ × Fin 3) (na nb : ℕ)
    (Ca : IsChain wa Ea na) (Cb : IsChain wb Eb nb), ∃ (i : Fin _) (j : Fin 3) (Pa Pb : Plane),
      (D.tile i).pts j = D.target.pts 0 ∧ (D.tile i).angleAt j = α ∧ SideAt D α wa Ea na i j Pa ∧
      SideAt D α wb Eb nb i j Pb ∧
      ((tyE D.toDissection 64 80 (Ea 0) = TT.b ∧ tyE D.toDissection 64 80 (Eb 0) = TT.c) ∨
       (tyE D.toDissection 64 80 (Ea 0) = TT.c ∧ tyE D.toDissection 64 80 (Eb 0) = TT.b)) := by
  obtain ⟨wa, hwaa, hwab⟩ := exists_wall D.toDissection 0 1 (by decide)
  obtain ⟨wb, hwba, hwbb⟩ := exists_wall D.toDissection 0 2 (by decide)
  obtain ⟨Ea, na, Ca⟩ := wa.exists_chain D.toDissection.pos
  obtain ⟨Eb, nb, Cb⟩ := wb.exists_chain D.toDissection.pos
  refine ⟨wa, wb, Ea, Eb, na, nb, Ca, Cb, ?_⟩
  have h01 : dist (D.target.pts 0) (D.target.pts (0 + 1)) = 3600 := GLC.dist01
  have h02 : dist (D.target.pts 0) (D.target.pts (0 + 2)) = 2400 := GLC.dist02
  obtain ⟨i, j, Pa, Pb, hij, hjα, SA, SB, ty, -⟩ := corner_both D α_irr data (by norm_num) (by norm_num)
    GLC.hword_1125 0 t_ang0 (by rw [h01]; norm_num) (by rw [h01]; norm_num) (by rw [h02]; norm_num)
    (by rw [h02]; norm_num) Ca Cb hwaa hwab hwba hwbb
  exact ⟨i, j, Pa, Pb, hij, hjα, SA, SB, ty⟩

theorem wit_apex : ∃ (wA wB : Wall D.toDissection) (EA EB : ℕ → Fin _ × Fin 3) (nA nB : ℕ),
    IsChain wA EA nA ∧ IsChain wB EB nB ∧
    ((eAng D.toDissection wA.dir (EA (nA - 1)) = α ∧
        eAng D.toDissection wB.dir (EB (nB - 1)) = Real.pi - 3 * α) ∨
     (eAng D.toDissection wA.dir (EA (nA - 1)) = Real.pi - 3 * α ∧
        eAng D.toDissection wB.dir (EB (nB - 1)) = α)) := by
  obtain ⟨wA, hAa, hAb⟩ := exists_wall D.toDissection 0 2 (by decide)
  obtain ⟨wB, hBa, hBb⟩ := exists_wall D.toDissection 1 2 (by decide)
  obtain ⟨EA, nA, CA⟩ := wA.exists_chain D.toDissection.pos
  obtain ⟨EB, nB, CB⟩ := wB.exists_chain D.toDissection.pos
  exact ⟨wA, wB, EA, EB, nA, nB, CA, CB,
    apex_pair D α_irr data (p := 0) (q := 1) (r := 2) (by decide) (by decide) (by decide) t_ang2
      CA CB hAa hAb hBa hBb⟩

/-- The apex hypothesis `angleAt r = π − 2α` fails at a base corner (it is not vacuous). -/
theorem ctl_apex_base : ¬ (D.target.angleAt 0 = Real.pi - 2 * α) := by
  intro e
  rw [t_ang0] at e
  exact α_irr ⟨1 / 3, by push_cast; linarith⟩

/-- The leaf-scale leg hypothesis of `leafG_of_dissection` is a real constraint: `D` (`k = 2`) does not satisfy it. -/
theorem ctl_hX : ¬ (dist (D.target.pts 1) (D.target.pts 2) = 16 * ((2 * 2 * (2 * 2 + 1) : ℕ) : ℝ)) := by
  rw [dist12_1125]; norm_num

end Erdos634.GLI

#print axioms Erdos634.GLI.wit_V
#print axioms Erdos634.GLI.wit_sum
#print axioms Erdos634.GLI.wit_corner
#print axioms Erdos634.GLI.wit_apex
#print axioms Erdos634.GLI.ctl_apex_base
