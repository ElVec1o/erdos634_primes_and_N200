import Mathlib
import Erdos634.Draft.BeesonMap31b

/-!
# Beeson map, batch 31c: Theorem 37 (Beeson-Rosu), `j = 1`, on a real `CongruentDissection`, UNCONDITIONAL (the two named hypotheses of BeesonRosu37d2 are derived)

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Theorem 37, Lemmas 23, 30, 34, 35, 36), Beeson (1206.2229v4), Laczkovich, Zhang, Paliy.
Formalization debt, not progress on the /goal outcomes.

* `apex_count`: in a `SetupG` frame whose corner `Q' = (0,0)` has angle `2 alpha` or `3 alpha` (`corner_A_angle`), no four distinct tiles have a vertex at `Q'`
  (`corner_counts`: every such tile has `a >= 1`, the sum of the `a` is at most `3`).
* `thm37_j1`: for a real `CongruentDissection D0` of the isosceles-beta triangle `(k^3, k^3, m (3k^2 - m^2))` with a tile congruent to `(km, k^2 - m^2, k^2)`, `0 < m < k`, `gcd = 1`:
  `False`.  Printed Theorem 37 with `j = 1` (the leg `AB` is chosen as the one whose first tile has no mirror beside it, `not_both_mirror`; `hCorner` from 31a).
-/

open scoped Classical
set_option linter.unusedVariables false

namespace Erdos634.BeesonMap31c

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.SideRunG Erdos634.Draft.SideRunGA
  Erdos634.Draft.SideRun Erdos634.Draft.W2E1 Erdos634.BaseBetaTargetCoord Erdos634.TilePlacement Erdos634.Geometry.Dissection
  Erdos634.BeesonRosu37b1 Erdos634.BeesonRosu37c2 Erdos634.BeesonRosu37d1 Erdos634.BeesonRosu37d2
  Erdos634.BeesonMap31a Erdos634.BeesonMap31b

variable {N : ℕ}

theorem apex_count {e f : ℕ} {α β γ L ax ay : ℝ} {D : CongruentDissection N}
    (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay) :
    ∀ a b c d : Fin N, (∃ k, (D.tile a).pts k = CertCoord.mkPt 0 0) → (∃ k, (D.tile b).pts k = CertCoord.mkPt 0 0) →
      (∃ k, (D.tile c).pts k = CertCoord.mkPt 0 0) → (∃ k, (D.tile d).pts k = CertCoord.mkPt 0 0) →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False := by
  obtain ⟨n, hn, hloc⟩ := corner_A_angle S Co
  have h0 : D.target.pts 0 = CertCoord.mkPt 0 0 := by rw [S.tgt, Tg_pts0]
  obtain ⟨a, b, hlocab, hb0, hb1, hg2, hsa, hsb⟩ :=
    corner_counts S 0 (A := n) (B := 0) (by rw [h0, hloc]; simp)
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ :=
    Erdos634.MarchKillsFan.distinct_of_pos_ne S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel
  have hge : ∀ i, (∃ k, (D.tile i).pts k = CertCoord.mkPt 0 0) → 1 ≤ a i := by
    rintro i ⟨k, hk⟩
    have hk' : (D.tile i).pts k = D.target.pts 0 := hk.trans h0.symm
    have hpos : 0 < (D.tile i).localAngle (D.target.pts 0) := by
      rw [← hk', Tri.localAngle_vertex]
      exact Erdos634.MarchFlank.cornerAngle_pos (D.tile i) k
    have hbi : b i = 0 := by
      have : b i ≤ ∑ m, b m := Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    by_contra hlt
    have hai : a i = 0 := by omega
    have hli := hlocab i
    rw [hai, hbi] at hli
    simp at hli
    rw [hli] at hpos
    exact lt_irrefl _ hpos
  intro x y z w hx hy hz hw hxy hxz hxw hyz hyw hzw
  have h4 : a x + a y + a z + a w ≤ ∑ m, a m := by
    have hsub : ({x, y, z, w} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset (f := a) hsub
    rw [Finset.sum_insert (by simp [hxy, hxz, hxw]), Finset.sum_insert (by simp [hyz, hyw]),
      Finset.sum_pair hzw] at this
    omega
  have := hge x hx
  have := hge y hy
  have := hge z hz
  have := hge w hw
  omega

/-- **Theorem 37 (Beeson-Rosu), `j = 1`, on a real `CongruentDissection`**: there is no dissection of the isosceles-beta triangle with sides `(k^3, k^3, m (3k^2 - m^2))`
into tiles congruent to `(km, k^2 - m^2, k^2)`, `0 < m < k`, `gcd (m, k) = 1`. -/
theorem thm37_j1 (k m : ℕ) (hm : 1 ≤ m) (hmk : m < k) (hco : Nat.Coprime m k) (D₀ : CongruentDissection N)
    (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = (k : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = (k : ℝ) ^ 3)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2))
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2)) : False := by
  set τ' : Equiv.Perm (Fin 3) := (Equiv.swap (0 : Fin 3) 1).trans τ with hτ'
  have e0 : τ' 0 = τ 1 := by simp [hτ', Equiv.swap_apply_left]
  have e1 : τ' 1 = τ 0 := by simp [hτ', Equiv.swap_apply_right]
  have e2 : τ' 2 = τ 2 := by
    simp [hτ', Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
  have h1' : dist (D₀.target.pts (τ' 1)) (D₀.target.pts (τ' 2)) = (k : ℝ) ^ 3 := by
    rw [e1, e2, dist_comm]; exact h2
  have h2' : dist (D₀.target.pts (τ' 2)) (D₀.target.pts (τ' 0)) = (k : ℝ) ^ 3 := by
    rw [e0, e2, dist_comm]; exact h1
  have h3' : dist (D₀.target.pts (τ' 0)) (D₀.target.pts (τ' 1)) = (m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2) := by
    rw [e0, e1, dist_comm]; exact h3
  by_cases hN : ∀ i₀ T : Fin N, LaysBaseOn D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) i₀ Ty.C1 0 →
      ¬ MirrorBeside D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) i₀ T
  · exact thm37_j1_of_nomirror k m hm hmk hco D₀ τ h1 h2 h3 hMod hN
  by_cases hN' : ∀ i₀ T : Fin N, LaysBaseOn D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ' 2)) (D₀.target.pts (τ' 0)) i₀ Ty.C1 0 →
      ¬ MirrorBeside D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ' 2)) i₀ T
  · exact thm37_j1_of_nomirror k m hm hmk hco D₀ τ' h1' h2' h3' hMod hN'
  -- both legs have a mirror beside the first tile: impossible
  have hM1 : ∃ i₀ T : Fin N, LaysBaseOn D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) i₀ Ty.C1 0 ∧
      MirrorBeside D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) i₀ T := by
    by_contra hcon
    exact hN (fun i₀ T hl hm' => hcon ⟨i₀, T, hl, hm'⟩)
  have hM2 : ∃ i₀ T : Fin N, LaysBaseOn D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ' 2)) (D₀.target.pts (τ' 0)) i₀ Ty.C1 0 ∧
      MirrorBeside D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ' 2)) i₀ T := by
    by_contra hcon
    exact hN' (fun i₀ T hl hm' => hcon ⟨i₀, T, hl, hm'⟩)
  obtain ⟨i₁, T₁, hL1, hMi1⟩ := hM1
  obtain ⟨i₂, T₂, hL2, hMi2⟩ := hM2
  rw [e2, e0] at hL2
  rw [e2] at hMi2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmkR : (m : ℝ) < k := by exact_mod_cast hmk
  have T : TileOK (m : ℝ) (k : ℝ) := tileOK_of_nat hm hmk hco
  obtain ⟨cA, cB, cC⟩ := Erdos634.BeesonRosu37c1.corners_of_dists D₀.target hmR hmkR τ h1 h2 h3
  have hApex : cornerAngle (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = 3 * modelAlpha (m : ℝ) (k : ℝ) := by
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cC
  have hBeta : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = modelBeta (m : ℝ) (k : ℝ) := by
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cA
  have f0 : (finRotate 3).symm.trans τ 2 = τ 1 := rfl
  have f1 : (finRotate 3).symm.trans τ 0 = τ 2 := rfl
  have f2 : (finRotate 3).symm.trans τ 1 = τ 0 := rfl
  obtain ⟨D, g, L, ax, ay, hL, hdist, hD, hP, hB, S, Co, -⟩ :=
    setup_of_corners m k hm hmk hco D₀ hMod ((finRotate 3).symm.trans τ)
      (Or.inr (by rw [f0, f1, f2]; exact hApex)) (Or.inl (by rw [f0, f1, f2]; exact hBeta))
  replace hP : g (D₀.target.pts (τ 2)) = CertCoord.mkPt 0 0 := hP
  have hcount : ∀ a b c d : Fin N, (∃ k', (D₀.tile a).pts k' = D₀.target.pts (τ 2)) →
      (∃ k', (D₀.tile b).pts k' = D₀.target.pts (τ 2)) → (∃ k', (D₀.tile c).pts k' = D₀.target.pts (τ 2)) →
      (∃ k', (D₀.tile d).pts k' = D₀.target.pts (τ 2)) →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False := by
    intro a b c d ha hb hc hd
    have tr : ∀ i, (∃ k', (D₀.tile i).pts k' = D₀.target.pts (τ 2)) → ∃ k', (D.tile i).pts k' = CertCoord.mkPt 0 0 := by
      rintro i ⟨k', hk'⟩
      exact ⟨k', by rw [hD, hk', hP]⟩
    exact apex_count S Co a b c d (tr a ha) (tr b hb) (tr c hc) (tr d hd)
  have hkpos : (0 : ℝ) < k := hmR.trans hmkR
  have hd0 : 0 < dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) := by rw [h2]; positivity
  have hd1 : 0 < dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) := by rw [dist_comm, h1]; positivity
  have hang : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) = 3 * modelAlpha (m : ℝ) (k : ℝ) := cC
  exact not_both_mirror T hd0 hd1 hang hL1 hMi1 hL2 hMi2 hcount

end Erdos634.BeesonMap31c

#print axioms Erdos634.BeesonMap31c.apex_count
#print axioms Erdos634.BeesonMap31c.thm37_j1
