/-
Draft/WGapInv3.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5).
Not imported by any aggregate.  Module P-E3: base case `inv_one`, induction `inv_all`, and the ASSEMBLY `u3_of_suppliers`: the conclusion of S2' (`u3_corner_stmt'`) from the
invariant, with the suppliers `side3`, `case1`, `case3` (WGapInv2) and the chord conclusion `hthird` as named hypotheses.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapInv2

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

section asm

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem inv_one (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) {J : ℕ} (hJ1 : 1 ≤ J)
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) {Bst : ℕ → ℕ → Prop} (hBj : ∀ j, Bst j j) :
    Inv D e f Bst 1 1 := by
  refine ⟨le_rfl, le_rfl, ?_, ?_, side1_botclamp S h2 1, hBj 1⟩
  · intro i i' hi hii
    have h0 : i = 0 := by omega
    have h0' : i' = 0 := by omega
    subst h0 h0'
    simpa using hT 0 (by omega)
  · intro i hi; omega

theorem inv_all (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) {J : ℕ} (hJ1 : 1 ≤ J) (hJf : J ≤ f - 1)
    (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) {Bst : ℕ → ℕ → Prop} (hBj : ∀ j, Bst j j)
    (side3 : ∀ j c : ℕ, Inv D e f Bst j c → j < J → c = j → Unfl D e f j j ∨ Flip D e f j j)
    (case1 : ∀ j c i₁ : ℕ, Inv D e f Bst j c → j < J → 1 ≤ i₁ → i₁ ≤ c → (i₁ < c ∨ c = j) → Flip D e f j i₁ →
        (∀ i : ℕ, 1 ≤ i → i < i₁ → Unfl D e f j i) → BotClamp D e f (j + 1) i₁ ∧ Bst (j + 1) i₁)
    (case3 : ∀ j c : ℕ, Inv D e f Bst j c → j < J → c < j → (∀ i : ℕ, 1 ≤ i → i < c → Unfl D e f j i) →
        BotClamp D e f (j + 1) c ∧ Bst (j + 1) c) :
    ∀ j : ℕ, 1 ≤ j → j ≤ J → ∃ c : ℕ, Inv D e f Bst j c := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; exact ⟨1, inv_one S h2 hJ1 hT hBj⟩
  | succ j hj ih =>
    intro hjJ
    obtain ⟨c, I⟩ := ih (by omega)
    exact inv_step S h2 hJf hU hT hBj side3 case1 case3 hj (by omega) I

/-- **S2' from the suppliers**: the conclusion of `u3_corner_stmt'` (WGapStmt_Scratch2_20261115) -/
theorem u3_of_suppliers (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (J : ℕ) (hJ1 : 1 ≤ J) (hJf : J ≤ f - 1)
    (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) {Bst : ℕ → ℕ → Prop} (hBj : ∀ j, Bst j j)
    (side3 : ∀ j c : ℕ, Inv D e f Bst j c → j < J → c = j → Unfl D e f j j ∨ Flip D e f j j)
    (case1 : ∀ j c i₁ : ℕ, Inv D e f Bst j c → j < J → 1 ≤ i₁ → i₁ ≤ c → (i₁ < c ∨ c = j) → Flip D e f j i₁ →
        (∀ i : ℕ, 1 ≤ i → i < i₁ → Unfl D e f j i) → BotClamp D e f (j + 1) i₁ ∧ Bst (j + 1) i₁)
    (case3 : ∀ j c : ℕ, Inv D e f Bst j c → j < J → c < j → (∀ i : ℕ, 1 ≤ i → i < c → Unfl D e f j i) →
        BotClamp D e f (j + 1) c ∧ Bst (j + 1) c)
    (hthird : ∀ j c : ℕ, Inv D e f Bst j c → j ≤ J → ∀ i : ℕ, i < c → ∃ (τ : Fin N) (W : Plane),
        HasV D τ (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - i)) (mpG (e : ℝ) f 1 0 ((i : ℝ) + 1) ((j : ℝ) - i - 1)) W ∧
        cross (mpG (e : ℝ) f 1 0 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (j : ℝ)) (W - mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - i)) < 0) :
    ∀ j : ℕ, 1 ≤ j → j ≤ J → ∃ c : ℕ, 1 ≤ c ∧ c ≤ j ∧
      (∀ i : ℕ, i < c → UTM D (e : ℝ) (f : ℝ) 1 0 (i : ℝ) ((j - 1 - i : ℕ) : ℝ)) ∧
      (j < J → ∀ i : ℕ, i < c → DTM D (e : ℝ) (f : ℝ) 1 0 (i : ℝ) ((j - 1 - i : ℕ) : ℝ)) ∧
      (∀ i : ℕ, i < c → ∃ (τ : Fin N) (W : Plane),
        HasV D τ (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - i)) (mpG (e : ℝ) f 1 0 ((i : ℝ) + 1) ((j : ℝ) - i - 1)) W ∧
        cross (mpG (e : ℝ) f 1 0 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (j : ℝ)) (W - mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - i)) < 0) := by
  intro j hj1 hjJ
  obtain ⟨c, I⟩ := inv_all S h2 hJ1 hJf hU hT hBj side3 case1 case3 j hj1 hjJ
  refine ⟨c, I.c1, I.cj, ?_, ?_, hthird j c I hjJ⟩
  · intro i hi
    exact I.ha i (j - 1 - i) hi (by have := I.cj; omega)
  · intro hjJ' i hi
    exact (level_data S hJf hU hT hj1 hjJ' I).1 i hi

end asm

end Erdos634.Draft.WGapStmt
