import Erdos634.Draft.ThmDRunSetup

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' run port, module R2b: the sides of a tile  

Mechanical port of `SideRunGFrame` section 2 (`model_distsG`, `edge_length_casesG`, `sides_of_{a,b,c}_edgeG`) to the tile
`(u^2, v^2 - u^2, u v)`, via `ModelDataT`; `TileOKT` replaces `TileOK` (distinct sides, from `tile_distinct`).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.TilePlacement Erdos634.Draft.SideRun Set

structure TileOKT (u v : ℝ) : Prop where
  hab : u ^ 2 ≠ v ^ 2 - u ^ 2
  ac : u ^ 2 ≠ u * v
  bc : v ^ 2 - u ^ 2 ≠ u * v

theorem tileOKT_of_nat {u v : ℕ} (hco : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) :
    TileOKT (u : ℝ) (v : ℝ) :=
  ⟨(tile_distinct hco hu huv).1, (tile_distinct hco hu huv).2.1, (tile_distinct hco hu huv).2.2⟩

namespace SetupT
variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}
theorem tile (S : SetupT D u v α β γ L ax ay) : TileOKT (u : ℝ) (v : ℝ) := tileOKT_of_nat S.hco S.hu S.huv
end SetupT


/-- the model's three side lengths -/
theorem model_distsT {N : ℕ} (D : CongruentDissection N) {u v α β γ : ℝ}
    (hM : ModelDataT D (u ^ 2) (v ^ 2 - u ^ 2) (u * v) α β γ) :
    dist (D.model.pts 0) (D.model.pts 1) = (u * v) ∧ dist (D.model.pts 1) (D.model.pts 2) = u ^ 2 ∧
    dist (D.model.pts 2) (D.model.pts 0) = v ^ 2 - u ^ 2 := by
  have h0 := hM.hs0; have h1 := hM.hs1; have h2 := hM.hs2
  simp only [sideOpp] at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩
  · simpa using h2
  · simpa using h0
  · simpa using h1

/-- every edge of a tile has one of the three lengths -/
theorem edge_length_casesT {N : ℕ} (D : CongruentDissection N) {u v α β γ : ℝ}
    (hM : ModelDataT D (u ^ 2) (v ^ 2 - u ^ 2) (u * v) α β γ) (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = u ^ 2 ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = v ^ 2 - u ^ 2 ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = (u * v) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).dist_eq
  obtain ⟨m01, m12, m20⟩ := model_distsT D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = (u * v) := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = u ^ 2 := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = v ^ 2 - u ^ 2 := by rw [dist_comm]; exact m20
  have hk : k ≠ k + 1 := by fin_cases k <;> decide
  have hne : σ k ≠ σ (k + 1) := fun h => hk (σ.injective h)
  rw [hσ]
  generalize σ k = p at hne ⊢
  generalize σ (k + 1) = q at hne ⊢
  fin_cases p <;> fin_cases q <;> simp_all


/-- **The sides at the third vertex of an `a`-edge**: `{c, b}` in one of the two orders. -/
theorem sides_of_a_edgeT {N : ℕ} (D : CongruentDissection N) {u v α β γ : ℝ} (T : TileOKT u v)
    (hM : ModelDataT D (u ^ 2) (v ^ 2 - u ^ 2) (u * v) α β γ) (j : Fin N) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n)
    (hmn : m ≠ n) (hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = u ^ 2) :
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = (u * v) ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = v ^ 2 - u ^ 2) ∨
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = v ^ 2 - u ^ 2 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = (u * v)) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  obtain ⟨m01, m12, m20⟩ := model_distsT D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = (u * v) := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = u ^ 2 := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = v ^ 2 - u ^ 2 := by rw [dist_comm]; exact m20
  have hinj := σ.injective
  have hkm' : σ k ≠ σ m := fun h => hkm (hinj h)
  have hkn' : σ k ≠ σ n := fun h => hkn (hinj h)
  have hmn' : σ m ≠ σ n := fun h => hmn (hinj h)
  rw [hσ] at hd; rw [hσ, hσ]
  generalize σ k = sk at hd hkm' hkn' ⊢
  generalize σ m = sm at hd hkm' hmn' ⊢
  generalize σ n = sn at hkn' hmn' ⊢
  have hff : (u * v) ≠ u ^ 2 := T.ac.symm
  have hff' : v ^ 2 - u ^ 2 ≠ u ^ 2 := T.hab.symm
  fin_cases sk <;> fin_cases sm <;> fin_cases sn <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, m01, m12, m20, m10, m21, m02,
      dist_self] at hd hkm' hkn' hmn' ⊢ <;>
    first
    | exact absurd rfl hkm'
    | exact absurd rfl hkn'
    | exact absurd rfl hmn'
    | exact absurd hd hff
    | exact absurd hd hff'
    | simp

/-- **The sides at the third vertex of a `b`-edge**: `{a, c}` in one of the two orders. -/
theorem sides_of_b_edgeT {N : ℕ} (D : CongruentDissection N) {u v α β γ : ℝ} (T : TileOKT u v)
    (hM : ModelDataT D (u ^ 2) (v ^ 2 - u ^ 2) (u * v) α β γ) (j : Fin N) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n)
    (hmn : m ≠ n) (hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = v ^ 2 - u ^ 2) :
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = u ^ 2 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = (u * v)) ∨
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = (u * v) ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = u ^ 2) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  obtain ⟨m01, m12, m20⟩ := model_distsT D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = (u * v) := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = u ^ 2 := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = v ^ 2 - u ^ 2 := by rw [dist_comm]; exact m20
  have hinj := σ.injective
  have hkm' : σ k ≠ σ m := fun h => hkm (hinj h)
  have hkn' : σ k ≠ σ n := fun h => hkn (hinj h)
  have hmn' : σ m ≠ σ n := fun h => hmn (hinj h)
  rw [hσ] at hd; rw [hσ, hσ]
  generalize σ k = sk at hd hkm' hkn' ⊢
  generalize σ m = sm at hd hkm' hmn' ⊢
  generalize σ n = sn at hkn' hmn' ⊢
  have hff : (u * v) ≠ v ^ 2 - u ^ 2 := T.bc.symm
  have hff' : u ^ 2 ≠ v ^ 2 - u ^ 2 := T.hab
  fin_cases sk <;> fin_cases sm <;> fin_cases sn <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, m01, m12, m20, m10, m21, m02,
      dist_self] at hd hkm' hkn' hmn' ⊢ <;>
    first
    | exact absurd rfl hkm'
    | exact absurd rfl hkn'
    | exact absurd rfl hmn'
    | exact absurd hd hff
    | exact absurd hd hff'
    | simp

/-- **The sides at the third vertex of a `c`-edge**: `{a, b}` in one of the two orders. -/
theorem sides_of_c_edgeT {N : ℕ} (D : CongruentDissection N) {u v α β γ : ℝ} (T : TileOKT u v)
    (hM : ModelDataT D (u ^ 2) (v ^ 2 - u ^ 2) (u * v) α β γ) (j : Fin N) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n)
    (hmn : m ≠ n) (hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = (u * v)) :
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = u ^ 2 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = v ^ 2 - u ^ 2) ∨
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = v ^ 2 - u ^ 2 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = u ^ 2) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  obtain ⟨m01, m12, m20⟩ := model_distsT D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = (u * v) := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = u ^ 2 := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = v ^ 2 - u ^ 2 := by rw [dist_comm]; exact m20
  have hinj := σ.injective
  have hkm' : σ k ≠ σ m := fun h => hkm (hinj h)
  have hkn' : σ k ≠ σ n := fun h => hkn (hinj h)
  have hmn' : σ m ≠ σ n := fun h => hmn (hinj h)
  rw [hσ] at hd; rw [hσ, hσ]
  generalize σ k = sk at hd hkm' hkn' ⊢
  generalize σ m = sm at hd hkm' hmn' ⊢
  generalize σ n = sn at hkn' hmn' ⊢
  have hff : v ^ 2 - u ^ 2 ≠ (u * v) := T.bc
  have hff' : u ^ 2 ≠ (u * v) := T.ac
  fin_cases sk <;> fin_cases sm <;> fin_cases sn <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, m01, m12, m20, m10, m21, m02,
      dist_self] at hd hkm' hkn' hmn' ⊢ <;>
    first
    | exact absurd rfl hkm'
    | exact absurd rfl hkn'
    | exact absurd rfl hmn'
    | exact absurd hd hff
    | exact absurd hd hff'
    | simp


end Erdos634.Draft.ThmDRun


#print axioms Erdos634.Draft.ThmDRun.sides_of_a_edgeT
#print axioms Erdos634.Draft.ThmDRun.sides_of_b_edgeT
#print axioms Erdos634.Draft.ThmDRun.sides_of_c_edgeT
