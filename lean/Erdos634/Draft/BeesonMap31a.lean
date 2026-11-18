import Mathlib
import Erdos634.Draft.BeesonRosu37d2

/-!
# Beeson map, batch 31a: Theorem 37 (Beeson-Rosu), the corner-tile claim `hCorner` DERIVED

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Theorem 37, last paragraph: "the tile at `A` has its `beta` angle at `A`, so its `a` edge
must lie on `AB` or `AC`"), Beeson (1206.2229v4, Lemmas 23, 34), Laczkovich, Zhang, Paliy.  Formalization debt, not progress on the /goal outcomes.

BeesonRosu37d2 proved `thm37_j1_of_corner` from two NAMED hypotheses, `hNoM` and `hCorner`.  This file DERIVES `hCorner`:

* `corner_tile_facts`: at a corner `V` of the target whose local angle is `beta` (SetupG frame), exactly one tile of the dissection has a vertex at `V`
  (`corner_counts`: sum of the `alpha`-counts `0`, of the `beta`-counts `1`), and its local angle at `V` is `beta`.
* `corner_sL`: a tile laying a base of type `t` on a side ending at such a corner `V` (`V` its end vertex) has `sL t = b` (opposite side to the `beta` vertex; `HasV.anglesG`).
* `thm37_j1_of_nomirror`: Theorem 37 for `j = 1` on a real `CongruentDissection` with ONE named hypothesis `hNoM` (no mirror tile beside the first leg tile).
-/

open scoped Classical
set_option linter.unusedVariables false

namespace Erdos634.BeesonMap31a

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.SideRunG Erdos634.Draft.SideRunGA
  Erdos634.Draft.SideRun Erdos634.Draft.W2E1 Erdos634.BaseBetaTargetCoord Erdos634.TilePlacement Erdos634.Geometry.Dissection
  Erdos634.BeesonRosu37b1 Erdos634.BeesonRosu37c2 Erdos634.BeesonRosu37d1 Erdos634.BeesonRosu37d2

variable {N : ℕ}

/-- **Exactly one tile at a `beta` corner, showing `beta`.** -/
theorem corner_tile_facts {e f : ℕ} {α β γ L ax ay : ℝ} {D : CongruentDissection N}
    (S : SetupG D e f α β γ L ax ay) (hB : D.target.localAngle (D.target.pts 1) = β) :
    (∀ i k, (D.tile i).pts k = D.target.pts 1 → (D.tile i).localAngle (D.target.pts 1) = β) ∧
    (∀ i i' k k', (D.tile i).pts k = D.target.pts 1 → (D.tile i').pts k' = D.target.pts 1 → i = i') := by
  obtain ⟨a, b, hloc, hb0, hb1, hg2, hsa, hsb⟩ :=
    corner_counts S 1 (A := 0) (B := 1) (by simpa using hB)
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ :=
    Erdos634.MarchKillsFan.distinct_of_pos_ne S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel
  have hkey : ∀ i k, (D.tile i).pts k = D.target.pts 1 → b i = 1 ∧ (D.tile i).localAngle (D.target.pts 1) = β := by
    intro i k hk
    have hmem := congruentDissection_localAngle_mem D α β γ S.hM.hα' S.hM.hβ' S.hM.hγ' 1 i
    have hpos : 0 < (D.tile i).localAngle (D.target.pts 1) := by
      rw [← hk, Tri.localAngle_vertex]
      exact Erdos634.MarchFlank.cornerAngle_pos (D.tile i) k
    have hai : a i = 0 := by
      have : a i ≤ ∑ m, a m := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hbi : b i ≤ 1 := by
      have : b i ≤ ∑ m, b m := Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hli := hloc i
    rw [hai] at hli
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h
    · exfalso
      rw [h] at hli
      interval_cases hbv : b i
      · simp at hli; exact hα0 hli
      · simp at hli; exact hαβ hli
    · have h1 := hb1 i h
      exact ⟨by omega, h⟩
    · have := hg2 i (Or.inl h); omega
    · have := hg2 i (Or.inr h); omega
    · rw [h] at hpos; exact absurd hpos (lt_irrefl _)
  refine ⟨fun i k hk => (hkey i k hk).2, fun i i' k k' hk hk' => ?_⟩
  by_contra hne
  have h1 := (hkey i k hk).1
  have h2 := (hkey i' k' hk').1
  have hsub : ({i, i'} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
  have := Finset.sum_le_sum_of_subset (f := b) hsub
  rw [Finset.sum_pair hne] at this
  omega

/-- **A tile whose vertex `m` is at the `beta` corner has the opposite side `b`**: if a tile of `D₀` (transported to `D` by `g`) has the vertices `k, m, j`
with `m` at the corner `V` (`g V = D.target.pts 1`) and `dist j k = sL t`, then `sL t = f² - e²`. -/
theorem corner_sL {e f : ℕ} {α β γ L ax ay : ℝ} {D₀ D : CongruentDissection N} {g : Plane ≃ᵢ Plane}
    (S : SetupG D e f α β γ L ax ay) (hD : ∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m))
    (hB : D.target.localAngle (D.target.pts 1) = β) {V : Plane} (hV : g V = D.target.pts 1)
    {t : Ty} {i : Fin N} {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j)
    (hm : (D₀.tile i).pts m = V)
    (hsL : dist ((D₀.tile i).pts j) ((D₀.tile i).pts k) = t.sLG (e : ℝ) (f : ℝ)) :
    t.sLG (e : ℝ) (f : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ :=
    Erdos634.MarchKillsFan.distinct_of_pos_ne S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel
  have hv : (D.tile i).pts m = D.target.pts 1 := by rw [hD, hm, hV]
  have hloc := (corner_tile_facts S hB).1 i m hv
  have hHas : HasV D i (D.target.pts 1) ((D.tile i).pts k) ((D.tile i).pts j) :=
    ⟨m, k, j, hkm.symm, hmj, hkj, hv, rfl, rfl⟩
  obtain ⟨hA, hBb, hC⟩ := hHas.anglesG S.tile S.hM
  have hd : dist ((D.tile i).pts k) ((D.tile i).pts j) = t.sLG (e : ℝ) (f : ℝ) := by
    rw [hD, hD, g.dist_eq, dist_comm]; exact hsL
  have hcases : t.sLG (e : ℝ) (f : ℝ) = (f : ℝ) ^ 2 ∨ t.sLG (e : ℝ) (f : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨
      t.sLG (e : ℝ) (f : ℝ) = (e : ℝ) * f := by
    cases t <;> simp [Ty.sLG]
  rcases hcases with h | h | h
  · exfalso
    have := hC (hd.trans h)
    rw [hloc] at this
    exact hβγ this
  · exact h
  · exfalso
    have := hA (hd.trans h)
    rw [hloc] at this
    exact hαβ this.symm

/-- **Theorem 37 (Beeson-Rosu), `j = 1`, on a real `CongruentDissection`, with the single named hypothesis `hNoM`**: `hCorner` of `thm37_j1_of_corner` is derived. -/
theorem thm37_j1_of_nomirror (k m : ℕ) (hm : 1 ≤ m) (hmk : m < k) (hco : Nat.Coprime m k) (D₀ : CongruentDissection N)
    (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = (k : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = (k : ℝ) ^ 3)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2))
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2))
    (hNoM : ∀ i₀ T : Fin N, LaysBaseOn D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) i₀ Ty.C1 0 →
      ¬ MirrorBeside D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) i₀ T) : False := by
  have e1 : ((Equiv.swap (0 : Fin 3) 1).trans τ) 1 = τ 0 := by simp [Equiv.swap_apply_right]
  obtain ⟨D, g, ax, ay, hD, hP, hB, S, Co⟩ := setup_TG_pinned m k hm hmk hco one_pos D₀ ((Equiv.swap (0 : Fin 3) 1).trans τ)
    (by rw [one_mul, dist_comm]; exact h2) (by rw [one_mul, dist_comm]; exact h1) (by rw [one_mul, dist_comm]; exact h3) hMod
  obtain ⟨t, ht, hax, hay⟩ := Co.hB
  have hcorner := S.corner_right_beta ht hax hay
  have hloc : D.target.localAngle (D.target.pts 1) = modelBeta (m : ℝ) (k : ℝ) := by
    rw [Tri.localAngle_vertex]
    exact hcorner
  have hV : g (D₀.target.pts (τ 0)) = D.target.pts 1 := by
    rw [← e1, hB, S.tgt, Tg_pts1]
  refine thm37_j1_of_corner k m hm hmk hco D₀ τ h1 h2 h3 hMod hNoM ?_
  intro c₁ c₂ X₁ X₂ tile₁ tile₂ ty₁ ty₂ hb hl
  have hd₁ : 0 < dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 0)) :=
    dist_pos.mpr (fun h => absurd (τ.injective (D₀.target.indep.injective h)) (by decide))
  have hd₂ : 0 < dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) :=
    dist_pos.mpr (fun h => absurd (τ.injective (D₀.target.indep.injective h)) (by decide))
  have T : TileOK (m : ℝ) (k : ℝ) := tileOK_of_nat hm hmk hco
  obtain ⟨k₁, m₁, j₁, hkm₁, hkj₁, hmj₁, hk₁, hX₁, hm₁, hjk₁, hjm₁, -⟩ := last_tile T.he T.hef hd₁ hb
  obtain ⟨k₂, m₂, j₂, hkm₂, hkj₂, hmj₂, hk₂, hX₂, hm₂, hjk₂, hjm₂, -⟩ := last_tile T.he T.hef hd₂ hl
  have hv₁ : (D.tile (tile₁ (c₁ - 1))).pts m₁ = D.target.pts 1 := by rw [hD, hm₁, hV]
  have hv₂ : (D.tile (tile₂ (c₂ - 1))).pts m₂ = D.target.pts 1 := by rw [hD, hm₂, hV]
  refine ⟨(corner_tile_facts S hloc).2 _ _ _ _ hv₁ hv₂, ?_, ?_⟩
  · exact corner_sL S hD hloc hV hkm₁ hkj₁ hmj₁ hm₁ hjk₁
  · exact corner_sL S hD hloc hV hkm₂ hkj₂ hmj₂ hm₂ hjk₂

end Erdos634.BeesonMap31a

#print axioms Erdos634.BeesonMap31a.corner_tile_facts
#print axioms Erdos634.BeesonMap31a.corner_sL
#print axioms Erdos634.BeesonMap31a.thm37_j1_of_nomirror
