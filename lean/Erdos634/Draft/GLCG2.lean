import Mathlib.Tactic
import Erdos634.Draft.GLCWire
import Erdos634.Draft.A1CornerLattice

/-!
# `corner_G2`: G2 at a real `α`-corner

`corner_G2`: at a target corner of angle `α` of a dissection by the `γ = 2α` tile (hypotheses of `GLCG1.corner_G1`, plus the word lemmas for `a`, `2a`, `c` and `b < c`), there is a corner tile `T = tile i` (vertex `j` at
the corner `O`) such that for each orientation `(m1, m2)` of its other two vertices with `|O pts m1| = c` (the side `s` carries the `c`-edge), `|O pts m2| = b`, `2·pts m1 − O` and `2·pts m2 − O` not target vertices
(`s` and `s'` longer than `2c`, `2b`): if the second tile `K` on `s` (`α` at `pts m1`, an edge along the side of length `c`) is a `(c,c)` configuration, then NO tile has a vertex `Q₁ = 2·pts m1 − O` of angle `γ` with an edge along
the forward ray of `s`.  This is (G2): "the third tile on `s` does not start with `γ`" (the third edge on `s` is not an `a`-edge and not a `b`-edge with its `γ`-end at `Q₁`, since the `a`-edge ends are `(β,γ)` and the
`b`-edge ends `(α,γ)`).  Cases: `K_P` has a `b`-edge (`T3 = T + (Y−O)`, chord `P₂Q₁` of length `2a`, `GLCCase1`) or a `c`-edge (`GLCCase2`).
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.C2Forward Erdos634.Pi3F6 Erdos634.Pi3Tile Erdos634.EdgeWordConversion

variable {N : ℕ}

theorem refl_third_eq (D : CongruentDissection N) (i : Fin N) (j : Fin 3) {P Q X0 : Plane}
    (hcar1 : (D.tile i).carrier = convexHull ℝ {P, Q, X0})
    (hP : (D.tile i).pts (j + 1) = P) (hQ : (D.tile i).pts (j + 2) = Q) : X0 = (D.tile i).pts j := by
  have hext := Erdos634.Geometry.A1Pos.target_vertex_extreme (D.tile i) j
  rw [hcar1] at hext
  have := extremePoints_convexHull_subset hext
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  rcases this with h1 | h1 | h1
  · exact absurd (h1.trans hP.symm) (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j))
  · exact absurd (h1.trans hQ.symm) (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j))
  · exact h1.symm

set_option maxHeartbeats 3200000 in
theorem corner_G2 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hb0 : 0 < b) (hbc' : b < c)
    (hsides : ∀ i : Fin 3, sideLen D i = a ∨ sideLen D i = b ∨ sideLen D i = c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1)
    (hword1 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x = 1 ∧ y = 0 ∧ z = 0)
    (hword2 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = 2 * a → x = 2 ∧ y = 0 ∧ z = 0)
    (hwordc : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x = 0 ∧ y = 0 ∧ z = 1)
    (k0 : Fin 3) (hk : D.target.angleAt k0 = α)
    (hA1 : dist (D.target.pts k0) (D.target.pts (k0 + 1)) ≠ b)
    (hA2 : dist (D.target.pts k0) (D.target.pts (k0 + 1)) ≠ c)
    (hB1 : dist (D.target.pts k0) (D.target.pts (k0 + 2)) ≠ b)
    (hB2 : dist (D.target.pts k0) (D.target.pts (k0 + 2)) ≠ c) :
    ∃ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts k0 ∧ (D.tile i).angleAt j = α ∧
      ∀ (m1 m2 : Fin 3), ((m1 = j + 1 ∧ m2 = j + 2) ∨ (m1 = j + 2 ∧ m2 = j + 1)) →
        dist (D.target.pts k0) ((D.tile i).pts m1) = c → dist (D.target.pts k0) ((D.tile i).pts m2) = b →
        (∀ v' : Fin 3, D.target.pts v' ≠ (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0)) →
        (∀ v' : Fin 3, D.target.pts v' ≠ (D.tile i).pts m2 + ((D.tile i).pts m2 - D.target.pts k0)) →
        ∀ (K : Fin N) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts m1 → (D.tile K).angleAt l = α →
          ((SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0) ((D.tile K).pts (l + 1) - (D.tile i).pts m1) ∧
              dist ((D.tile i).pts m1) ((D.tile K).pts (l + 1)) = c) ∨
            (SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0) ((D.tile K).pts (l + 2) - (D.tile i).pts m1) ∧
              dist ((D.tile i).pts m1) ((D.tile K).pts (l + 2)) = c)) →
          (¬ ∃ (U : Fin N) (l' : Fin 3), (D.tile U).pts l' = (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0) ∧
            (D.tile U).angleAt l' = 2 * α ∧
            (SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0)
                ((D.tile U).pts (l' + 1) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0))) ∨
             SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0)
                ((D.tile U).pts (l' + 2) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0))))) ∧
          ∃ (K' : Fin N) (l'' : Fin 3), (D.tile K').pts l'' = (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0) ∧
            (D.tile K').angleAt l'' = α ∧
            (SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0)
                ((D.tile K').pts (l'' + 1) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0))) ∨
             SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0)
                ((D.tile K').pts (l'' + 2) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0)))) := by
  obtain ⟨i, j, hj, hang, hcase, hlen, j', hj', X0, hcar1, hcar2, ⟨KP1, lP1, hKP1pt, hKP1ang, hKP1ray⟩,
    ⟨KQ1, lQ1, hKQ1pt, hKQ1ang, hKQ1ray⟩⟩ := corner_G1 D hα hS hab hac hword k0 hk hA1 hA2 hB1 hB2
  have hX0 : X0 = (D.tile i).pts j := refl_third_eq D i j hcar1 rfl rfl
  rw [hX0, hj] at hcar2
  refine ⟨i, j, hj, hang, ?_⟩
  intro m1 m2 hm hOX hOY hQ1v hY2v K l hKpt hKang hKray
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have hj1 : (D.tile i).pts (j + 1) - D.target.pts k0 ≠ 0 := by
    rw [sub_ne_zero, ← hj]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
  have hj2 : (D.tile i).pts (j + 2) - D.target.pts k0 ≠ 0 := by
    rw [sub_ne_zero, ← hj]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
  have hAne : D.target.pts (k0 + 1) - D.target.pts k0 ≠ 0 := by
    rw [sub_ne_zero]; intro h
    exact (by decide : ∀ x : Fin 3, x + 1 ≠ x) k0 (D.target.indep.injective h)
  have hBne : D.target.pts (k0 + 2) - D.target.pts k0 ≠ 0 := by
    rw [sub_ne_zero]; intro h
    exact (by decide : ∀ x : Fin 3, x + 2 ≠ x) k0 (D.target.indep.injective h)
  have vk1 : k0 ≠ k0 + 1 := (by decide : ∀ x : Fin 3, x ≠ x + 1) k0
  have vk2 : k0 ≠ k0 + 2 := (by decide : ∀ x : Fin 3, x ≠ x + 2) k0
  have v12 : k0 + 1 ≠ k0 + 2 := (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k0
  have hT2swap : (D.tile j').carrier = convexHull ℝ {(D.tile i).pts (j + 2), (D.tile i).pts (j + 1),
      (D.tile i).pts (j + 2) + (D.tile i).pts (j + 1) - D.target.pts k0} := by
    rw [hcar2, Set.insert_comm, add_comm ((D.tile i).pts (j + 2))]
  have hlen' : dist ((D.tile i).pts (j + 2)) ((D.tile i).pts (j + 1)) = a := by rw [dist_comm]; exact hlen
  rcases hcase with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
  · obtain ⟨p1, hp1, hp1e⟩ := rayparam hAne hj1 hr1
    obtain ⟨q2, hq2, hq2e⟩ := rayparam hBne hj2 hr2
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact g2_wire D hα hS hab hac hbc hb0 hbc' hsides hword1 hword2 hwordc i j k0 (k0 + 1) (k0 + 2) vk1 vk2 v12
        (j + 1) (j + 2) (Or.inl ⟨rfl, rfl⟩) hj hang hq2 hp1 hp1e hq2e hOX hOY hlen j' hcar2 K l hKpt hKang hKray
        KQ1 lQ1 hKQ1pt hKQ1ang hKQ1ray hQ1v hY2v
    · exact g2_wire D hα hS hab hac hbc hb0 hbc' hsides hword1 hword2 hwordc i j k0 (k0 + 2) (k0 + 1) vk2 vk1 v12.symm
        (j + 2) (j + 1) (Or.inr ⟨rfl, rfl⟩) hj hang hp1 hq2 hq2e hp1e hOX hOY hlen' j' hT2swap K l hKpt hKang hKray
        KP1 lP1 hKP1pt hKP1ang hKP1ray hQ1v hY2v
  · obtain ⟨p1, hp1, hp1e⟩ := rayparam hBne hj1 hr1
    obtain ⟨q2, hq2, hq2e⟩ := rayparam hAne hj2 hr2
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact g2_wire D hα hS hab hac hbc hb0 hbc' hsides hword1 hword2 hwordc i j k0 (k0 + 2) (k0 + 1) vk2 vk1 v12.symm
        (j + 1) (j + 2) (Or.inl ⟨rfl, rfl⟩) hj hang hq2 hp1 hp1e hq2e hOX hOY hlen j' hcar2 K l hKpt hKang hKray
        KQ1 lQ1 hKQ1pt hKQ1ang hKQ1ray hQ1v hY2v
    · exact g2_wire D hα hS hab hac hbc hb0 hbc' hsides hword1 hword2 hwordc i j k0 (k0 + 1) (k0 + 2) vk1 vk2 v12
        (j + 2) (j + 1) (Or.inr ⟨rfl, rfl⟩) hj hang hp1 hq2 hq2e hp1e hOX hOY hlen' j' hT2swap K l hKpt hKang hKray
        KP1 lP1 hKP1pt hKP1ang hKP1ray hQ1v hY2v

end Erdos634.GLC

#print axioms Erdos634.GLC.corner_G2
