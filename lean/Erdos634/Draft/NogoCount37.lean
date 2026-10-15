import Erdos634.JunctionAutomaton


/-!
# Member-specific count for the (3,7) member

Over all 120 words `a⁷c⁴` ending in `c` and all `2¹¹` orientations, exactly 10 560
configurations satisfy every junction constraint together with the endpoint constraints below.

This file formalises the numerical statement for `(e,f) = (3,7)`.
The general automaton fact (`only_forbidden_pair_is_gg`) lives in `JunctionAutomaton.lean`.

## Orientation convention

A-edge flanks β and γ; C-edge flanks α and β.
Orientation `true` = first-listed flank is on the apex side (top).
  A: true → top=β, bot=γ;  false → top=γ, bot=β
  C: true → top=α, bot=β;  false → top=β, bot=α

Endpoint constraints:
  first-edge bottom = β  (base-corner figure = {β})
  last-edge  top    = α  (apex figure = {3α}, last edge is c with top = α)
-/

namespace Erdos634.NogoCount37

open JunctionAutomaton Angle

/-- Bool-valued version of `admissible`, kernel-reducible via pure match (no Multiset quotient). -/
@[reducible] def admissibleBool (T B : Angle) : Bool :=
  match T, B with
  | .gamma, .gamma => false
  | _, _ => true

/-- `admissibleBool` agrees with `admissible` on all 9 pairs. Proved by the same 9-case
    kernel enumeration as `only_forbidden_pair_is_gg`. -/
theorem admissibleBool_iff (T B : Angle) : admissibleBool T B = true ↔ admissible T B := by
  cases T <;> cases B <;> decide

/-- Edge type on the equal side (no b-edges). -/
inductive EqEdge | A | C deriving DecidableEq, Repr

@[reducible] def topAngle : EqEdge → Bool → Angle
  | .A, true  => beta  | .A, false => gamma
  | .C, true  => alpha | .C, false => beta

@[reducible] def botAngle : EqEdge → Bool → Angle
  | .A, true  => gamma | .A, false => beta
  | .C, true  => beta  | .C, false => alpha

/-- All consecutive junctions are admissible (Bool version, kernel-reducible). -/
@[reducible] def junctionsOK : List EqEdge → List Bool → Bool
  | e₁ :: e₂ :: rest, o₁ :: o₂ :: ors =>
    admissibleBool (topAngle e₁ o₁) (botAngle e₂ o₂) &&
    junctionsOK (e₂ :: rest) (o₂ :: ors)
  | _, _ => true

/-- Endpoint constraints. -/
@[reducible] def endpointsOK (word : List EqEdge) (orients : List Bool) : Bool :=
  match word, orients with
  | e₀ :: _, o₀ :: _ =>
    (botAngle e₀ o₀ == beta) &&
    (match word.getLast?, orients.getLast? with
     | some eL, some oL => topAngle eL oL == alpha
     | _, _ => false)
  | _, _ => false

/-- A configuration passes all checks. -/
@[reducible] def validConfig (word : List EqEdge) (orients : List Bool) : Bool :=
  endpointsOK word orients && junctionsOK word orients

-- ---------------------------------------------------------------------------
-- Word generation: all length-n words with exactly k C's
-- ---------------------------------------------------------------------------

/-- All length-n lists over {A,C} with exactly k C's. -/
@[reducible] def wordsAkCk : ℕ → ℕ → List (List EqEdge)
  | 0, 0       => [[]]
  | 0, _ + 1   => []
  | n + 1, 0   => [List.replicate (n + 1) .A]
  | n + 1, k + 1 =>
    (wordsAkCk n k).map (.C :: ·) ++ (wordsAkCk n (k + 1)).map (.A :: ·)
  termination_by n _k => n

/-- 120 boundary words for (3,7): 11 edges, 7 A + 4 C, last = C. -/
@[reducible] def allWords37 : List (List EqEdge) :=
  (wordsAkCk 10 3).map (· ++ [.C])

-- ---------------------------------------------------------------------------
-- Orientation generation: all 2^n bool lists
-- ---------------------------------------------------------------------------

/-- All 2^n orientation lists. -/
@[reducible] def allOrients : ℕ → List (List Bool)
  | 0     => [[]]
  | n + 1 => List.flatMap (fun L => [false :: L, true :: L]) (allOrients n)

/-- 2048 orientation lists for an 11-edge word. -/
@[reducible] def allOrients11 : List (List Bool) := allOrients 11

-- ---------------------------------------------------------------------------
-- Count
-- ---------------------------------------------------------------------------

/-- Count of valid (word, orientation) pairs. -/
@[reducible] def countValid37 : ℕ :=
  (List.flatMap (fun w => allOrients11.map (fun o => (w, o))) allWords37)
    |>.countP (fun ⟨w, o⟩ => validConfig w o)

-- ---------------------------------------------------------------------------
-- γ-junction count (for prop:nogocensus)
-- ---------------------------------------------------------------------------

/-- A junction between edge i (top T) and edge i+1 (bottom B) carries a γ iff T=γ or B=γ. -/
@[reducible] def hasGamma (T B : Angle) : Bool :=
  (T == Angle.gamma) || (B == Angle.gamma)

/-- Count of γ-present junctions in a valid (word, orientation) configuration. -/
@[reducible] def gammaJunctionCount : List EqEdge → List Bool → ℕ
  | e₁ :: e₂ :: rest, o₁ :: o₂ :: ors =>
    (if hasGamma (topAngle e₁ o₁) (botAngle e₂ o₂) then 1 else 0) +
    gammaJunctionCount (e₂ :: rest) (o₂ :: ors)
  | _, _ => 0

/-- The minimum γ-junction count across all valid configurations. -/
@[reducible] def minGammaCount37 : ℕ :=
  (List.flatMap (fun w => allOrients11.map (fun o => (w, o))) allWords37)
    |>.filterMap (fun ⟨w, o⟩ => if validConfig w o then some (gammaJunctionCount w o) else none)
    |>.foldl Nat.min 999

-- Sanity checks
#eval allWords37.length    -- expect 120
#eval allOrients11.length  -- expect 2048
#eval countValid37         -- expect 10560
#eval minGammaCount37      -- expect 7

-- ---------------------------------------------------------------------------
-- Theorems
-- ---------------------------------------------------------------------------

/-- **(3,7)-member count.**
Over all C(10,3) = 120 boundary words `a⁷c⁴` ending in `c` and all 2¹¹ orientations,
exactly 10 560 configurations satisfy the junction-admissibility and endpoint constraints.
Proved by `native_decide` (uses `Lean.reduceBool`, so not standard axioms only); the same count with
standard axioms only is `NogoCount37Kernel.nogoCount37_eq_10560_std`.  A kernel `decide` on the flat
enumeration of the 245 760 pairs needs too much memory (no memoization across `allOrients11` evaluations). -/
theorem nogoCount37_eq_10560 : countValid37 = 10560 := by native_decide

#print axioms nogoCount37_eq_10560

/-- **γ-junction lower bound, (3,7)-member abstract form.**
In every valid configuration (admissible junctions + endpoint constraints), every junction that
carries γ — necessarily in the {γ,α,β} figure, since {3α,2β} has no γ — accounts for
exactly 7 junctions (one per a-edge; admissibility prevents two adjacent a-edges from both
orienting γ toward their shared junction, since (γ,γ) is the unique inadmissible pair).

This gives `x ≥ 7` for abstract configurations.  The version for real tilings
requires the geometric bridge (junctions carry straight figures), which is not part of this file.
The same statement with standard axioms only is `NogoGamma37Kernel.nogoGammaJunctions_eq_7_std`. -/
theorem nogoGammaJunctions_eq_7 : minGammaCount37 = 7 := by native_decide

#print axioms nogoGammaJunctions_eq_7

end Erdos634.NogoCount37
