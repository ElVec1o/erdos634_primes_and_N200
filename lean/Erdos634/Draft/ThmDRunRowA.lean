import Erdos634.Draft.ThmDRunNext
import Erdos634.Draft.SideRunRow
import Erdos634.Draft.E60Second
import Erdos634.Draft.W2E1Tools

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' run port, module R5a: levels, row distance, run partition, `K2T`, `AT`, `m_nextTr`  

Mechanical port of `SideRunGRow` sections 1, 3, 4 (up to `m_nextGr`).  NOT ported here (they need new mathematics for the
`gamma = 2 alpha` tile): `fig_bg` (the vertex figure as counting statements; the multiplicities at an interior vertex of
this tile are those of `APrimeSeat1`/`ThmDRunSector`, not of `AngleData`), `row_stepG`, `row_bad0G`, `row_sixG`, `row_badG`,
`rowG` (they use `N_pushG`, `chordG`, `fig_bg`).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.TilePlacement Erdos634.Draft.SideRun Set

variable {N : ℕ} {D : CongruentDissection N}


theorem GST_le {u v ε x a b s : ℝ} (he : 0 < u) (hef : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) (h : s ≤ a + b) :
    GST u v ε (lpT u v ε x a b) ≤ -lvT u v ε x s := by
  rw [GST_lp hε]; exact neg_le_neg (lvT_le he hef hv h)

theorem GST_gt {u v ε x a b s : ℝ} (he : 0 < u) (hef : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) (h : a + b < s) :
    -lvT u v ε x s < GST u v ε (lpT u v ε x a b) := by
  rw [GST_lp hε]; exact neg_lt_neg (lvT_lt he hef hv h)

theorem GHT_le {u v ε x a b η : ℝ} (he : 0 < u) (hef : u < v) (hv : v < 2 * u) (h : η ≤ b) :
    GHT u v (lpT u v ε x a b) ≤ -((u * v) * hhT u v * η) := by
  rw [GHT_lp]; exact neg_le_neg (mul_le_mul_of_nonneg_left h (nhT_pos he hef hv).le)

theorem GHT_gt {u v ε x a b η : ℝ} (he : 0 < u) (hef : u < v) (hv : v < 2 * u) (h : b < η) :
    -((u * v) * hhT u v * η) < GHT u v (lpT u v ε x a b) := by
  rw [GHT_lp]; exact neg_lt_neg (mul_lt_mul_of_pos_left h (nhT_pos he hef hv))

/-- the distance along a row -/
theorem dist_rowT {u v ε x : ℝ} (he : 0 < u) (hef : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) {a b η : ℝ} (hab : a ≤ b) :
    dist (lpT u v ε x a η) (lpT u v ε x b η) = (b - a) * (u * v) :=
  dist_lpT he hef hv hε (mul_nonneg (sub_nonneg.mpr hab) (by have := he.trans hef; positivity))
    (by unfold QfT; ring)

/-- **The run partition, arithmetic form**: for a `CongruentDissection` with the tile `(u v, f² − e², f²)`, a clamped run's
length is a nonnegative integer combination of the three sides (the generalization of `RunPartition.run_partition_semigroup`;
`wall_partitionG`, `Draft/SideRunGChordB.lean`, gives the same with a prescribed edge singled out). -/
theorem run_partition_semigroupT {N : ℕ} (D : CongruentDissection N) {u v α β γ : ℝ}
    (hM : ModelDataT D (u ^ 2) (v ^ 2 - u ^ 2) (u * v) α β γ) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {P Q P' Q' : Plane} (hPQ : P ≠ Q) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hS : segment ℝ P Q ⊆ {y | F y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) P' P Q)
    (hQ : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q' Q P) :
    ∃ x y z : ℕ, (x : ℝ) * (u ^ 2) + y * (v ^ 2 - u ^ 2) + z * (u * v) = dist P Q := by
  classical
  have h := run_partition D.toDissection F hF c hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hQ
  rw [← h]
  exact sum_mem_semigroup _ _ (u ^ 2) (v ^ 2 - u ^ 2) ((u * v))
    (fun ed _ => edge_length_casesT D hM ed.1 ed.2)

/-- four tiles whose angles at `p` sum to more than `π`: `p` is interior to the target -/
theorem interior_of_four (D : CongruentDissection N) {p : Plane} {i j k l : Fin N}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (h : Real.pi < (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      + (D.tile l).localAngle p) : p ∈ interior D.target.carrier :=
  Erdos634.Draft.E60Second.interior_of_sum_gt_pi D.toDissection (by
    rw [D.toDissection.sum_localAngle_eq p]
    exact lt_of_lt_of_le h (Erdos634.Draft.W2E1.four_angles_le D.toDissection p hij hik hil hjk hjl hkl))

/-! ## 3. (K2) and the claim `K` for all pairs of a given size -/


/-- **(K2)**: the rows `≤ j0` of `Δ_s` are lattice -/
def K2T (D : CongruentDissection N) (u v ε x : ℝ) (s j0 : ℕ) : Prop :=
  (∀ i j : ℕ, j ≤ j0 → i + j + 1 ≤ s → UTT D u v ε x i j) ∧
  (∀ i j : ℕ, j < j0 → i + j + 2 ≤ s → DTT D u v ε x i j)

/-- **The claim `K(s, j0)` for all pairs of size `m`**: (K2) and (K3) (in the general form `K3T`) are contradictory.  (K1) is in
`CtxT`. -/
def AT (D : CongruentDissection N) (u v : ℕ) (ε x : ℝ) (m : ℕ) : Prop :=
  ∀ s j0 : ℕ, j0 < s → s < v → s - j0 = m → K2T D (u : ℝ) (v : ℝ) ε x s j0 →
    K3T D (u : ℝ) (v : ℝ) ε x (s : ℝ) (j0 : ℝ) → False

/-! ## 4. The tile above a row -/




namespace CtxBaseT
variable {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- `m_nextT` at a real height that is a natural number -/
theorem m_nextTr (C : CtxBaseT D u v α β γ L ax ay ε x) {ξ η : ℝ} (hη : ∃ n : ℕ, η = n) {t₀ : Fin N}
    (hU : HasV D t₀ (lpT (u : ℝ) (v : ℝ) ε x ξ η) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)))
    (hFw : ∃ δ : ℝ, 0 < δ ∧ lpT (u : ℝ) (v : ℝ) ε x (ξ + 1 + δ) η ∈ D.target.carrier)
    (hcl : ClampedBelowT D (u : ℝ) (v : ℝ) ε x (ξ + η + 1) η) :
    (∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η + 1))) ∨
    (∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
      (lpT (u : ℝ) (v : ℝ) ε x (ξ + 2 - muT (u : ℝ) (v : ℝ)) (η + muT (u : ℝ) (v : ℝ)))) ∨
    (∃ w, RhoEdgeT D (u : ℝ) (v : ℝ) ε x w (ξ + η + 1) η) := by
  obtain ⟨n, rfl⟩ := hη
  exact C.m_nextT hU hFw hcl

end CtxBaseT

end Erdos634.Draft.ThmDRun

#print axioms Erdos634.Draft.ThmDRun.run_partition_semigroupT
#print axioms Erdos634.Draft.ThmDRun.interior_of_four
#print axioms Erdos634.Draft.ThmDRun.CtxBaseT.m_nextTr
