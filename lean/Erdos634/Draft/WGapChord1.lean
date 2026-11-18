/-
Draft/WGapChord1.lean -- written 15 November 2026 (session 3).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 chord facts (C), P4 AD).
Not imported by any aggregate.  Module W5c: the CHORD machinery on an arbitrary line (generic functional `F`, so it applies to the mirror lines `m'_j`, `l'_i`).

* `first_len_jaG`   : the first edge of a clamped run of length `j·a`, `1 ≤ j ≤ f-1`, is an `a`-edge (Lemma (Aa), the analogue of `SideRunG.first_len_jbG`).
* `no_straddle_gen` : the top clamp `¬ Straddles` at `X` towards ANY point `Q` of the line (the angle-count clamp `no_straddle` for the run `[X, Q]`).
* `chord_first_a`   : for a clamped run `[P, Q]` of length `j·a`, the far-side tile with a vertex at `P` and an edge in `[P,Q]` has an `a`-edge `[P, P + (Q-P)/j]`
  (vertices `P`, `lineMap P Q (1/j)`, third vertex strictly on the far side).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapW1
import Erdos634.Draft.SideRunGChordB
import Erdos634.Draft.SideRunGArith

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

variable {N : ℕ} {D : CongruentDissection N}

/-- **The first edge of a clamped run of length `j a`, `1 ≤ j ≤ f − 1`, is an `a`-edge** (Lemma (Aa)). -/
theorem first_len_jaG {e f j x y z : ℕ} {ℓ : ℝ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hj1 : 1 ≤ j) (hj : j ≤ f - 1)
    (hℓ : ℓ = (e : ℝ) * f ∨ ℓ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨ ℓ = (f : ℝ) ^ 2)
    (h : ℓ + ((x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2)
      = (j : ℝ) * ((e : ℝ) * f)) : ℓ = (e : ℝ) * f := by
  rcases hℓ with h1 | h1 | h1
  · exact h1
  · exfalso
    have := (SideRunGArith.Aa he hef hco hj1 hj (rep_nat_a (x := x) (y := y + 1) (z := z) hef
      (by push_cast; linarith))).2.1
    omega
  · exfalso
    have := (SideRunGArith.Aa he hef hco hj1 hj (rep_nat_a (x := x) (y := y) (z := z + 1) hef
      (by push_cast; linarith))).2.2
    omega

/-- **the angle-count clamp towards any point `Q` of the line** (generalizes `no_straddle`, which is the case `Q = Y`). -/
theorem no_straddle_gen (D : Dissection N) {X Y Q P' : Plane} (hXY : X ≠ Y)
    (hQ : cross (Y - X) (Q - X) = 0) (hXQ : X ≠ Q)
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Q)
    {Ω θ : ℝ} (hΩ : ∑ i, (D.tile i).localAngle X = Ω) (K : Finset (Fin N))
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - θ) (hθ : θ < Real.pi)
    (hKlt : ∀ k ∈ K, (D.tile k).localAngle X < Real.pi) :
    ∀ ed ∈ D.lineChain (crossL (Y - X)) (cross (Y - X) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Q := by
  intro ed hed hs
  have hu : Y - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hXY)
  have hF := crossL_ne_zero hu
  have hfX : crossL (Y - X) X = cross (Y - X) X := crossL_apply _ _
  have hfQ : crossL (Y - X) Q = cross (Y - X) X := by
    rw [crossL_apply]
    have : cross (Y - X) Q = cross (Y - X) (Q - X) + cross (Y - X) X := by
      rw [← cross_add_right]; congr 1; abel
    rw [this, hQ]; ring
  have hfP' : crossL (Y - X) P' = cross (Y - X) X := by
    rw [crossL_apply]
    have : cross (Y - X) P' = cross (Y - X) (P' - X) + cross (Y - X) X := by
      rw [← cross_add_right]; congr 1; abel
    rw [this, hP']; ring
  obtain ⟨-, hang, -⟩ := straddle_data D (crossL (Y - X)) hF (cross (Y - X) X) hXQ hfX hfQ hfP' hXP hed hs
  have hnot : ed.1 ∉ K := fun hm => absurd (hKlt _ hm) (by rw [hang]; exact lt_irrefl _)
  have hsd := Finset.sum_sdiff (Finset.subset_univ K) (f := fun i => (D.tile i).localAngle X)
  have hle : (D.tile ed.1).localAngle X ≤ ∑ i ∈ Finset.univ \ K, (D.tile i).localAngle X :=
    Finset.single_le_sum (f := fun i => (D.tile i).localAngle X) (fun j _ => Tri.localAngle_nonneg _ _)
      (by simp [hnot])
  rw [hang] at hle
  have h1 : ∑ i, (D.tile i).localAngle X = Ω := hΩ
  have h2 : ∑ i ∈ K, (D.tile i).localAngle X = Ω - θ := hK
  simp only at hsd
  linarith

section chord

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **FIRST `a`-EDGE of a clamped far-side run** of length `j a` (`1 ≤ j ≤ f - 1`): the far-side tile with a vertex at `P` and an edge in `[P, Q]`
has the vertices `P`, `P₁ = lineMap P Q (1/j)` (an `a`-edge `[P, P₁]`) and a third vertex strictly on the far side. -/
theorem chord_first_a (S : SetupG D e f α β γ L ax ay) {j : ℕ} (hj1 : 1 ≤ j) (hjf : j ≤ f - 1)
    (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ) {P Q P' Q' : Plane} (hPQ : P ≠ Q)
    (hfP : F P = c) (hfQ : F Q = c) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) P' P Q)
    (hQ : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q' Q P)
    (hd : dist P Q = (j : ℝ) * ((e : ℝ) * f)) :
    ∃ (i : Fin N) (k m n : Fin 3), k ≠ m ∧ k ≠ n ∧ m ≠ n ∧ (D.tile i).pts k = P ∧
      (D.tile i).pts m = AffineMap.lineMap P Q (1 / (j : ℝ)) ∧ F ((D.tile i).pts n) < c ∧
      ∀ l, F ((D.tile i).pts l) ≤ c := by
  obtain ⟨i, k, m, x, y, z, hkm, hk, hmseg, hle, hsum⟩ :=
    wall_firstG D S.hM F hF c hPQ hfP hfQ hfP' hfQ' hP' hQ' hint hwall hP hQ
  have hℓ := vertex_dist_casesG D S.hM i hkm
  rw [hk] at hℓ
  rw [hd] at hsum
  have hlen := first_len_jaG S.he S.hef S.hco hj1 hjf hℓ hsum
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hmem : AffineMap.lineMap P Q (1 / (j : ℝ)) ∈ segment ℝ P Q := by
    rw [segment_eq_image_lineMap]
    exact ⟨1 / (j : ℝ), ⟨by positivity, by rw [div_le_one hjpos]; exact_mod_cast hj1⟩, rfl⟩
  have hdist : dist P (AffineMap.lineMap P Q (1 / (j : ℝ))) = (e : ℝ) * f := by
    rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_pos (by positivity), hd]
    field_simp
  have hmeq : (D.tile i).pts m = AffineMap.lineMap P Q (1 / (j : ℝ)) :=
    eq_of_mem_segment_of_dist hPQ hmseg hmem (by rw [hlen, hdist])
  obtain ⟨n, hnk, hnm⟩ := fin3_third k m hkm
  have hkn : k ≠ n := hnk.symm
  have hmn : m ≠ n := hnm.symm
  have hlev := RunPartition.CSlot.segment_subset_level F c hfP hfQ
  have hFm : F ((D.tile i).pts m) = c := by
    rw [hmeq]; exact hlev hmem
  refine ⟨i, k, m, n, hkm, hkn, hmn, hk, hmeq, ?_, hle⟩
  rcases lt_or_eq_of_le (hle n) with h | h
  · exact h
  · exfalso
    refine two_vertices_on_line (D.tile i) F c hF (fun l => ?_)
    have hcov := fin3_cover k m n hkm hkn hmn l
    rcases hcov with h' | h' | h'
    · rw [h', hk]; exact hfP
    · rw [h']; exact hFm
    · rw [h']; exact h

end chord

#print axioms first_len_jaG
#print axioms no_straddle_gen
#print axioms chord_first_a

end Erdos634.Draft.WGapStmt
