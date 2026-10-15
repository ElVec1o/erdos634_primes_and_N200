import Erdos634.Draft.NogoCount37

/-!
# The γ-junction minimum with standard axioms only

`NogoCount37.nogoGammaJunctions_eq_7` uses `native_decide`.

This file proves `minGammaCount37 = 7` using only [propext, Classical.choice, Quot.sound].

Strategy: mirror the count proof decomposition.
  countValid37     = (allWords37.map perWordCount).sum
  minGammaCount37  = (allWords37.map perWordMin).foldl Nat.min 999

where `perWordMin w = allOrients11.foldl (cond-min) 999`.

Each `perWordMin w` evaluates independently at O(2048) kernel depth.
The outer foldl over 120 pre-evaluated ℕs is O(120) deep.
Max kernel recursion depth ≈ O(2200), within maxRecDepth 8192.
-/

namespace Erdos634.NogoGamma37Kernel

open Erdos634.NogoCount37

-- ─────────────────────────────────────────────────────────────────────────────
-- Per-word minimum: fold over orientations from sentinel 999
-- ─────────────────────────────────────────────────────────────────────────────

@[reducible] private def perWordMin (w : List EqEdge) : ℕ :=
  allOrients11.foldl
    (fun a o => if validConfig w o then Nat.min a (gammaJunctionCount w o) else a) 999

-- ─────────────────────────────────────────────────────────────────────────────
-- Length lemmas for allWords37 elements
-- ─────────────────────────────────────────────────────────────────────────────

private theorem wordsAkCk_length : ∀ (n k : ℕ) (w : List EqEdge),
    w ∈ wordsAkCk n k → w.length = n := by
  intro n
  induction n with
  | zero =>
    intro k w hw
    cases k with
    | zero => unfold wordsAkCk at hw; simp at hw; exact hw ▸ rfl
    | succ => unfold wordsAkCk at hw; simp at hw
  | succ n ih =>
    intro k w hw
    cases k with
    | zero =>
      unfold wordsAkCk at hw; simp at hw; rw [hw]; simp [List.length_replicate]
    | succ k =>
      unfold wordsAkCk at hw
      simp only [List.mem_append, List.mem_map] at hw
      rcases hw with ⟨w', hw'mem, rfl⟩ | ⟨w', hw'mem, rfl⟩
      · simp [ih k w' hw'mem]
      · simp [ih (k + 1) w' hw'mem]

private theorem allWords37_length (w : List EqEdge) (hw : w ∈ allWords37) :
    w.length = 11 := by
  simp only [allWords37, List.mem_map] at hw
  obtain ⟨w', hw'mem, rfl⟩ := hw
  simp [wordsAkCk_length 10 3 w' hw'mem]

-- ─────────────────────────────────────────────────────────────────────────────
-- Bound: gammaJunctionCount ≤ word length
-- ─────────────────────────────────────────────────────────────────────────────

private theorem gammaJunctionCount_le_length : ∀ (w : List EqEdge) (o : List Bool),
    gammaJunctionCount w o ≤ w.length := by
  intro w
  induction w with
  | nil => intro; simp [gammaJunctionCount]
  | cons e₁ t ih =>
    intro o
    cases t with
    | nil => simp [gammaJunctionCount]
    | cons e₂ rest =>
      cases o with
      | nil => simp [gammaJunctionCount]
      | cons o₁ ors =>
        cases ors with
        | nil => simp [gammaJunctionCount]
        | cons o₂ ors' =>
          simp only [gammaJunctionCount, List.length_cons]
          have hih := ih (o₂ :: ors')
          simp only [List.length_cons] at hih
          split <;> omega

-- ─────────────────────────────────────────────────────────────────────────────
-- Monotonicity: the cond-min foldl ≤ initial value
-- ─────────────────────────────────────────────────────────────────────────────

private theorem condFold_le_init (w : List EqEdge) (l : List (List Bool)) (init : ℕ) :
    l.foldl (fun a o => if validConfig w o then Nat.min a (gammaJunctionCount w o) else a) init ≤ init := by
  induction l generalizing init with
  | nil => exact le_rfl
  | cons hd tl ih =>
    cases h : validConfig w hd
    · simp only [List.foldl_cons, h]; exact ih init
    · simp only [List.foldl_cons, h, ↓reduceIte]; exact le_trans (ih _) (min_le_left _ _)

-- ─────────────────────────────────────────────────────────────────────────────
-- Fold-splitting: condFold init = min init (condFold 999), when init ≤ 999
-- ─────────────────────────────────────────────────────────────────────────────

private theorem condFold_gen (w : List EqEdge) (hbound : ∀ o, gammaJunctionCount w o ≤ 999)
    (l : List (List Bool)) (init : ℕ) (hinit : init ≤ 999) :
    l.foldl (fun a o => if validConfig w o then Nat.min a (gammaJunctionCount w o) else a) init =
    Nat.min init
      (l.foldl (fun a o => if validConfig w o then Nat.min a (gammaJunctionCount w o) else a) 999) := by
  induction l generalizing init with
  | nil =>
    simp only [List.foldl_nil]
    exact (min_eq_left hinit).symm
  | cons hd tl ih =>
    cases h : validConfig w hd
    · -- validConfig w hd = false: both sides use same init, directly apply IH
      simp only [List.foldl_cons, h]
      exact ih init hinit
    · -- validConfig w hd = true: use γ = gammaJunctionCount w hd ≤ 999
      simp only [List.foldl_cons, h, ↓reduceIte]
      have hγ : gammaJunctionCount w hd ≤ 999 := hbound hd
      -- Simplify Nat.min 999 γ = γ in the goal first, then apply IH twice
      have h999γ : Nat.min 999 (gammaJunctionCount w hd) = gammaJunctionCount w hd :=
        min_eq_right hγ
      rw [h999γ]
      rw [ih (Nat.min init (gammaJunctionCount w hd)) (le_trans (min_le_left _ _) hinit)]
      rw [ih (gammaJunctionCount w hd) hγ]
      exact min_assoc _ _ _

-- ─────────────────────────────────────────────────────────────────────────────
-- filterMap+foldl = condFold (algebraic equivalence)
-- ─────────────────────────────────────────────────────────────────────────────

private theorem filterMap_foldl_eq_condFold (w : List EqEdge) (init : ℕ)
    (l : List (List Bool)) :
    (l.filterMap (fun o => if validConfig w o then some (gammaJunctionCount w o) else none)
      |>.foldl Nat.min init) =
    l.foldl (fun a o => if validConfig w o then Nat.min a (gammaJunctionCount w o) else a) init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filterMap_cons]
    cases h : validConfig w hd
    · simp only [h, List.foldl_cons]; exact ih init
    · simp only [h, ↓reduceIte, List.foldl_cons]; exact ih (Nat.min init (gammaJunctionCount w hd))

-- ─────────────────────────────────────────────────────────────────────────────
-- Main decomposition: minGammaCount37 = (allWords37.map perWordMin).foldl min 999
-- ─────────────────────────────────────────────────────────────────────────────

private theorem minGammaCount37_eq_map_foldl :
    minGammaCount37 = (allWords37.map perWordMin).foldl Nat.min 999 := by
  unfold minGammaCount37
  suffices h : ∀ (words : List (List EqEdge))
      (hwords : ∀ w ∈ words, w.length ≤ 999) (acc : ℕ) (hacc : acc ≤ 999),
      ((words.flatMap (fun w => allOrients11.map (fun o => (w, o)))).filterMap
          (fun ⟨w, o⟩ => if validConfig w o then some (gammaJunctionCount w o) else none)
        |>.foldl Nat.min acc) =
      (words.map perWordMin).foldl Nat.min acc by
    exact h allWords37 (fun w hw => by have := allWords37_length w hw; omega) 999 le_rfl
  intro words
  induction words with
  | nil => intro _ _ _; rfl
  | cons w ws ih =>
    intro hwords acc hacc
    simp only [List.flatMap_cons, List.filterMap_append, List.foldl_append,
               List.map_cons, List.foldl_cons]
    have per_word : (allOrients11.map (fun o => (w, o))).filterMap
          (fun ⟨w', o⟩ => if validConfig w' o then some (gammaJunctionCount w' o) else none) =
        allOrients11.filterMap
          (fun o => if validConfig w o then some (gammaJunctionCount w o) else none) := by
      simp [List.filterMap_map, Function.comp]
    rw [per_word, filterMap_foldl_eq_condFold w acc allOrients11]
    have hw_in : w ∈ w :: ws := List.mem_cons.mpr (Or.inl rfl)
    have hbound : ∀ o, gammaJunctionCount w o ≤ 999 := fun o =>
      le_trans (gammaJunctionCount_le_length w o) (hwords w hw_in)
    rw [condFold_gen w hbound allOrients11 acc hacc]
    have hacc' : Nat.min acc (perWordMin w) ≤ 999 :=
      le_trans (min_le_left _ _) hacc
    exact ih (fun w' hw' => hwords w' (List.mem_cons.mpr (Or.inr hw'))) _ hacc'

-- ─────────────────────────────────────────────────────────────────────────────
-- Compute: the map-foldl equals 7 (kernel decide, O(2200) max depth)
-- ─────────────────────────────────────────────────────────────────────────────

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem mapFoldl_min_eq_7 :
    (allWords37.map perWordMin).foldl Nat.min 999 = 7 := by
  decide

-- ─────────────────────────────────────────────────────────────────────────────
-- Main theorem: standard axioms only
-- ─────────────────────────────────────────────────────────────────────────────

/-- **`prop:nogocensus` γ-junction minimum — standard axioms only.**
Over all 10,560 valid (word, orientation) configurations, the minimum γ-junction count is 7.
Axioms: [propext, Classical.choice, Quot.sound] only. -/
theorem nogoGammaJunctions_eq_7_std : minGammaCount37 = 7 :=
  minGammaCount37_eq_map_foldl.trans mapFoldl_min_eq_7

#print axioms nogoGammaJunctions_eq_7_std

end Erdos634.NogoGamma37Kernel
