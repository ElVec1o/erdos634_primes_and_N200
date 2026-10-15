/-
Draft/ThresholdReduce.lean -- the threshold statement of one member of the base-β row is a FINITE statement.

    theorem threshold_member_iff : for coprime `1 ≤ e < f`,
        (∀ M ≥ 1, ThresholdAt e f M)  ↔
          (∀ M, 2 ≤ M → M < f → ¬ BetaTilable e f M)  ∧  (∀ M, f < M → M < (e − 1)(f − 1) + f → BetaTilable e f M)

`ThresholdAt e f M` is "the base-β target of the member `(e, f)` at scale `M` has a tiling if and only if `M ≥ f`".
Scale `1` is `UniformThreshold.threshold_one` (no tiling), scale `f` is the seed (`betaTilable_self`), and every scale
`M ≥ (e − 1)(f − 1) + f` is the collar (`CollarG.thresholdAt_large`).  What is left for a member is therefore:

  * `f − 2` nonexistence statements (the scales `2 ≤ M < f`), and
  * at most `(e − 1)(f − 1) − 1` existence statements (the scales strictly between `f` and `(e − 1)(f − 1) + f`), of
    which those in `f + ⟨e, f⟩` are already theorems (`CollarG.betaTilable_lin`): `(e − 1)(f − 1)/2` remain, none for
    `e = 1`.

`uniformThreshold_iff` is the same for all members at once.  Nothing here decides any of the remaining instances.
The existence results are formal proofs of constructions of D. Paliy and M. Beeson (see `Draft.CollarG`).
Composite-N statements; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.CollarG

open scoped Classical

namespace Erdos634.Draft.ThresholdReduce
open Erdos634.Draft.UniformThreshold (BetaTilable ThresholdAt UniformThreshold threshold_one betaTilable_self)
open Erdos634.Draft.CollarG (thresholdAt_large betaTilable_lin)

/-- two triangles with the same three side lengths (in some labellings) are congruent -/
theorem congruent_of_hasSides_both {T U : Erdos634.Geometry.Tri} {a b c : ℝ}
    (hT : Erdos634.Draft.FDBBaseBetaE1.HasSides T a b c) (hU : Erdos634.Draft.FDBBaseBetaE1.HasSides U a b c) :
    T.Congruent U := by
  obtain ⟨τ, u12, u20, u01⟩ := hU
  have h : T.Congruent (U.relabel τ) :=
    Erdos634.Draft.FDBBaseBetaE1.congruent_of_hasSides' hT
      (by rw [Erdos634.Geometry.Tri.relabel_pts, Erdos634.Geometry.Tri.relabel_pts]; exact u01)
      (by rw [Erdos634.Geometry.Tri.relabel_pts, Erdos634.Geometry.Tri.relabel_pts]; exact u12)
      (by rw [Erdos634.Geometry.Tri.relabel_pts, Erdos634.Geometry.Tri.relabel_pts, dist_comm]; exact u20)
  exact h.trans (U.congruent_relabel τ).symm

/-- **Certificate interface for the exclusions.**  If `TGT` has the sides of the base-β target of `(e, f)` at scale
`M` and `MODEL` the sides of the tile (in any labellings), and no dissection has a target congruent to `TGT` and a
model congruent to `MODEL` (this is the conclusion `not_dissection` of a search certificate), then the base-β target
has no tiling at scale `M`.  With `threshold_member_iff` every finished and certified search at a scale `2 ≤ M < f`
becomes one of the finitely many statements that the threshold statement of that member needs. -/
theorem not_betaTilable_of_cert {e f M : ℕ} (TGT MODEL : Erdos634.Geometry.Tri)
    (hT : Erdos634.Draft.FDBBaseBetaE1.HasSides TGT ((M : ℝ) * (f : ℝ) ^ 3) ((M : ℝ) * (f : ℝ) ^ 3)
      ((M : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))))
    (hM : Erdos634.Draft.FDBBaseBetaE1.HasSides MODEL ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (cert : ∀ {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N),
      D.target.Congruent TGT → D.model.Congruent MODEL → False) :
    ¬ BetaTilable e f M := by
  rintro ⟨N, D, hDT, hDM⟩
  exact cert D (congruent_of_hasSides_both hDT hT) (congruent_of_hasSides_both hDM hM)

/-- **The threshold statement of a member is a finite statement.** -/
theorem threshold_member_iff (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    (∀ M, 1 ≤ M → ThresholdAt e f M) ↔
      ((∀ M, 2 ≤ M → M < f → ¬ BetaTilable e f M) ∧
        (∀ M, f < M → M < (e - 1) * (f - 1) + f → BetaTilable e f M)) := by
  constructor
  · intro h
    refine ⟨fun M h2 hMf hB => ?_, fun M hfM _ => (h M (by omega)).mpr (by omega)⟩
    have := (h M (by omega)).mp hB
    omega
  · rintro ⟨hno, hyes⟩ M hM
    by_cases h1 : M = 1
    · rw [h1]; exact threshold_one hco he hef
    by_cases h2 : M < f
    · exact ⟨fun hB => absurd hB (hno M (by omega) h2), fun h => by omega⟩
    by_cases h3 : M = f
    · rw [h3]; exact ⟨fun _ => le_rfl, fun _ => betaTilable_self he hef⟩
    by_cases h4 : M < (e - 1) * (f - 1) + f
    · exact ⟨fun _ => by omega, fun _ => hyes M (by omega) h4⟩
    · exact thresholdAt_large e f he hef hco M (by omega)

/-- the existence half only needs the scales outside `f + ⟨e, f⟩` -/
theorem threshold_member_iff' (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    (∀ M, 1 ≤ M → ThresholdAt e f M) ↔
      ((∀ M, 2 ≤ M → M < f → ¬ BetaTilable e f M) ∧
        (∀ M, f < M → M < (e - 1) * (f - 1) + f → (∀ j i : ℕ, 1 ≤ j → M ≠ j * f + i * e) → BetaTilable e f M)) := by
  rw [threshold_member_iff e f he hef hco]
  constructor
  · rintro ⟨hno, hyes⟩
    exact ⟨hno, fun M h1 h2 _ => hyes M h1 h2⟩
  · rintro ⟨hno, hyes⟩
    refine ⟨hno, fun M h1 h2 => ?_⟩
    by_cases h : ∃ j i : ℕ, 1 ≤ j ∧ M = j * f + i * e
    · obtain ⟨j, i, hj, rfl⟩ := h
      exact betaTilable_lin e f he hef j hj i
    · exact hyes M h1 h2 (fun j i hj hM => h ⟨j, i, hj, hM⟩)

/-- **The family `e = 1`** (again, from the general statement): the threshold statement of the member `(1, f)` is
equivalent to the absence of tilings at the scales `2 ≤ M < f`. -/
theorem threshold_e1_member_iff (f : ℕ) (hf : 2 ≤ f) :
    (∀ M, 1 ≤ M → ThresholdAt 1 f M) ↔ (∀ M, 2 ≤ M → M < f → ¬ BetaTilable 1 f M) := by
  rw [threshold_member_iff 1 f le_rfl (by omega) (Nat.coprime_one_left f)]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun M h1 h2 => ?_⟩
    have h0 : (1 - 1) * (f - 1) + f = f := by simp
    rw [h0] at h2
    omega

/-- **The statement under test, for all members at once.** -/
theorem uniformThreshold_iff :
    UniformThreshold ↔
      ∀ e f : ℕ, 1 ≤ e → e < f → Nat.Coprime e f →
        ((∀ M, 2 ≤ M → M < f → ¬ BetaTilable e f M) ∧
          (∀ M, f < M → M < (e - 1) * (f - 1) + f → BetaTilable e f M)) := by
  constructor
  · intro h e f he hef hco
    exact (threshold_member_iff e f he hef hco).mp (fun M hM => h e f M he hef hco hM)
  · intro h e f M he hef hco hM
    exact (threshold_member_iff e f he hef hco).mpr (h e f he hef hco) M hM

end Erdos634.Draft.ThresholdReduce

#print axioms Erdos634.Draft.ThresholdReduce.not_betaTilable_of_cert
#print axioms Erdos634.Draft.ThresholdReduce.threshold_member_iff
#print axioms Erdos634.Draft.ThresholdReduce.threshold_member_iff'
#print axioms Erdos634.Draft.ThresholdReduce.uniformThreshold_iff
