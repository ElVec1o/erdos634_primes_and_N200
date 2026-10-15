/-
Draft/SideRunGThickCount.lean  Part of `AllThreshold`.  The corners of `W_M(e, f)` at every scale `M`, and the count of the edges `c` on the side from `A'` for the corner run theorem (`prop:cornerrun`).

For `cor:thickw` (a): if `M (f − e) ≤ e`, then a segment of length `|AQ| = M f b` that is a union of segments of lengths `a`, `b`, `c` contains at most `M (f − e) ≤ e` of length `c`, and the triangle `W_M(e, f)` cannot be cut into copies of `(a, b, c)`.
The proof: the side `AQ` of `W_M(e, f)` runs from the corner `2α` to the corner `α + β` and carries at most `e` tiles laying `c`: no run of length `f` and no run of length `e + 1`, against the corner run theorem.

CONTENTS.
* `W_corners_of_sides`: a congruent dissection whose target has the sides `M f b = |τ 2 τ 0|` (`AQ`), `M e (2f² − e²) = |τ 0 τ 1|` (`QB`), `M f³ = |τ 1 τ 2|` (`BA`), `M > 0` real, has the corner angles `2α` at `τ 2` (= `A`), `α + β` at `τ 0`
  (= `Q`), `β` at `τ 1` (= `B`): the cosine rule read backwards, the argument of `angles_witness_W` (which is the case `M = f`), with an arbitrary scale.
* `sideG_counts_gen`: the count of `SetupG.sideG_counts` for runs of every length: a typed chain of length `L` has `x, y, z` letters of lengths `a, b, c` with `x a + y b + z c = L`, and a run of `n` letters `C1` or of `n` letters `C2` gives `n ≤ z`.
* `cornerrun_counts`: the side from the corner `A'` of angle `2α` or `3α` to the corner `Q'` of angle `β` or `α + β` is a union of `x`, `y`, `z` segments of lengths `a`, `b`, `c` with `z ≥ e + 1`, and `z ≥ e + 2` if `e + 2 ≤ f`, `a < b` and `A'` has the angle `2α`.
  (Alternative (i) of `thm_cornerrun` gives `z ≥ f`, alternative (ii) gives `z ≥ k ≥ e + 1` (`e + 2`).)

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGCornerWitness

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.FDBBaseBetaE1 Set

variable {N : ℕ} {D : CongruentDissection N}

/-! ## 1. The corners of `W_M(e, f)` at every scale -/

/-- **The corners of `W_s(e, f)`, any real scale `s > 0`, from the three side lengths** (`|τ 1 τ 2| = s f³`, `|τ 2 τ 0| = s f (f² − e²)`, `|τ 0 τ 1| = s e (2f² − e²)`): the angle `2α` at `τ 2`, `α + β` at `τ 0`, `β` at `τ 1`
(the argument of `angles_witness_W`, which is `s = f`). -/
theorem W_corners_of_sides (e f : ℕ) (he : 1 ≤ e) (hef : e < f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = s * (f : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0))
      = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
      = s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) :
    cornerAngle (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∧
    cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) ∧
    cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) := by
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  have hb := b_posG he0 hefR
  have hK2 : (0 : ℝ) < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := sq_nonneg (f : ℝ); linarith
  have hcosβ := cos_modelBeta he0 hefR
  have hcosα := cos_modelAlpha he0 hefR
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he0 hefR
  have hrel := modelAngle_rel (e : ℝ) (f : ℝ)
  have hα0 : 0 < modelAlpha (e : ℝ) (f : ℝ) := by unfold modelAlpha; linarith
  have hpi := Real.pi_pos
  have hfne : (f : ℝ) ≠ 0 := hf0.ne'
  have hene : (e : ℝ) ≠ 0 := he0.ne'
  have hsne : s ≠ 0 := hs.ne'
  have hbne : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≠ 0 := hb.ne'
  have hK2ne : 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≠ 0 := hK2.ne'
  have hQB : 0 < s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hs (mul_pos he0 hK2)
  have hBA : 0 < s * (f : ℝ) ^ 3 := mul_pos hs (pow_pos hf0 3)
  have hAQ : 0 < s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hs (mul_pos hf0 hb)
  -- the angle at `B` is `β`
  have hB : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
      modelBeta (e : ℝ) (f : ℝ) := by
    refine cornerAngle_eq_of_cosG (a := s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (b := s * (f : ℝ) ^ 3) (d := s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      h3 (by rw [dist_comm]; exact h1) (by rw [dist_comm]; exact h2) hQB hBA hb0.le
      (by linarith [Real.pi_pos]) ?_
    rw [hcosβ]; unfold baseLen Nq
    rw [div_eq_div_iff (by positivity) (mul_pos (mul_pos two_pos hQB) hBA).ne']
    ring
  -- the angle at `A` is `2 α`
  have hA : cornerAngle (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) =
      2 * modelAlpha (e : ℝ) (f : ℝ) := by
    refine cornerAngle_eq_of_cosG (a := s * (f : ℝ) ^ 3)
      (b := s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (d := s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      h1 (by rw [dist_comm]; exact h2) (by rw [dist_comm]; exact h3) hBA hAQ (by linarith)
      (by linarith) ?_
    rw [Real.cos_two_mul, hcosα]; field_simp; try ring
  have hsum := witness_angle_sum D₀ τ
  refine ⟨hA, ?_, hB⟩
  linarith

/-! ## 2. The count of the edges `c` on a side -/

section counts

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- **The counts on the side, for runs of every length** (`SetupG.sideG_counts` has the runs of length `f`): a typed chain of length `L` has `x, y, z` letters of lengths `a, b, c` with `x a + y b + z c = L`, and a run of `n` letters `C1`
or of `n` letters `C2` gives `n ≤ z`. -/
theorem sideG_counts_gen (S : SetupG D e f α β γ L ax ay) (Ch : ChainG D e f L m X tile τ) :
    ∃ x y z : ℕ, (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2 = L ∧
      (∀ i n : ℕ, i + n ≤ m →
        ((∀ j, j < n → τ (i + j) = Ty.C1) ∨ (∀ j, j < n → τ (i + j) = Ty.C2)) → n ≤ z) := by
  have hsub : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left S.hef.le 2)]; push_cast; ring
  have hN : ∑ k ∈ Finset.range m, lenN e f (τ k)
      = (∑ k ∈ Finset.range m, (τ k).cA) * (e * f) + (∑ k ∈ Finset.range m, (τ k).cB) * (f ^ 2 - e ^ 2)
        + (∑ k ∈ Finset.range m, (τ k).cC) * f ^ 2 := by
    simp only [lenN, Finset.sum_add_distrib, Finset.sum_mul]
  have h1 : ∀ k ∈ Finset.range m, (τ k).lenG (e : ℝ) (f : ℝ) = X (k + 1) - X k := by
    intro k hk
    rw [Ch.hstep k (Finset.mem_range.mp hk)]; ring
  have h2 : L = ∑ k ∈ Finset.range m, (τ k).lenG (e : ℝ) (f : ℝ) := by
    rw [Finset.sum_congr rfl h1, Finset.sum_range_sub, Ch.hXm, Ch.hX0, sub_zero]
  have h3 : ∑ k ∈ Finset.range m, (τ k).lenG (e : ℝ) (f : ℝ)
      = ((∑ k ∈ Finset.range m, lenN e f (τ k) : ℕ) : ℝ) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl (fun k _ => lenG_cast S.hef (τ k))
  refine ⟨∑ k ∈ Finset.range m, (τ k).cA, ∑ k ∈ Finset.range m, (τ k).cB,
    ∑ k ∈ Finset.range m, (τ k).cC, ?_, ?_⟩
  · rw [h2, h3, hN]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]
  · intro i n him hrun
    exact cC_run τ i n m him hrun

end counts

/-! ## 3. The count for the side from `A'` -/

/-- **THE SIDE FROM THE CORNER `A'` HAS AT LEAST `e + 1` EDGES `c`** (the counting step of `cor:thickw` (a)): the side `[A', Q']` of the target of `D₀` (corners `2α` or `3α` at `A'`, `β` or `α + β` at `Q'`) is a union of `x`, `y`, `z` segments of
lengths `a = e f`, `b = f² − e²`, `c = f²`, with `z ≥ e + 1`; and `z ≥ e + 2` when `e + 2 ≤ f`, `a < b` and `A'` has the angle `2α`.  (Alternative (i) of `thm_cornerrun` gives `f ≤ z`; alternative (ii), a run `C1^k`, gives `k ≤ z`, `k ≥ e + 1` (`e + 2`).) -/
theorem cornerrun_counts (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hA : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        3 * modelAlpha (e : ℝ) (f : ℝ))
    (hQ : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    ∃ x y z : ℕ, (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2 =
        dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧
      e + 1 ≤ z ∧
      (e + 2 ≤ f → (e : ℝ) * f < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 →
        cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
          2 * modelAlpha (e : ℝ) (f : ℝ) → e + 2 ≤ z) := by
  obtain ⟨D, g, L, ax, ay, hL, hLd, hD, hP, hB, S, Co, h2⟩ :=
    setup_of_corners e f he hef hco D₀ hMod τ hA hQ
  obtain ⟨m, X, tile, τc, Ch⟩ := S.exists_chainG
  obtain ⟨x, y, z, hsum, hz⟩ := sideG_counts_gen S Ch
  refine ⟨x, y, z, by rw [hLd]; exact hsum, ?_⟩
  rcases corner_side_theorem S Co Ch with ⟨i, him, hrun⟩ | ⟨k, hk1, hkf, hkm, hrun, hsucc⟩
  · -- alternative (i): `f` consecutive tiles `C1` or `C2`
    have hfz := hz i f him hrun
    exact ⟨by omega, fun h _ _ => by omega⟩
  · -- alternative (ii): the run `C1^k`
    have hsucc' : k = m ∨ (k < m ∧ τc k ≠ Ty.B1 ∧ τc k ≠ Ty.C1) := by
      rcases hsucc with h | ⟨h, h'⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
    have hek : e + 1 ≤ k := by
      by_contra hlt
      exact corner_run_short S Co Ch hk1 (by omega) hrun hsucc'
    have hkz : k ≤ z := hz 0 k (by omega) (Or.inl (fun j hj => by rw [Nat.zero_add]; exact hrun j hj))
    refine ⟨by omega, fun hef2 hab h2' => ?_⟩
    have hk2 : e + 2 ≤ k := by
      by_contra hlt
      exact corner_run_short_o S Co hab (by omega) (h2 h2') Ch hk1 (by omega) hrun hsucc'
    omega

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.W_corners_of_sides
#print axioms Erdos634.Draft.SideRunGA.sideG_counts_gen
#print axioms Erdos634.Draft.SideRunGA.cornerrun_counts
