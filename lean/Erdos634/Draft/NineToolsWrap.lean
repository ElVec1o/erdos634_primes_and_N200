import Erdos634.LambdaFactor
import Erdos634.ScaleRigidity
import Erdos634.JunctionAutomaton
import Erdos634.NilpotentTower
import Erdos634.Inflation
import Erdos634.Draft.NogoCensusWrap
import Erdos634.Draft.NilpotentTowerWrap
import Erdos634.Draft.VacuousCompanionWrap

/-!
# Tool classes that cannot answer the crossing question: statements with Lean witnesses

Nine tool classes fail at a recorded point:

1. Linear direction invariants (LambdaFactor): metric_class_never_fires.
2. Euler/angle-sum counting (the equations coincide in one relation).
3. Edge-pairing parity (junction automaton: only forbidden pair is γγ).
4. Conway-Lagarias tiling group (collapses to its rank-2 abelianization if γ₂ = γ₃).
5. Similarity-invariant criteria (ScaleRigidity.no_similarity_invariant_proof).
6. γ-count stretch (two-endpoint hypothesis unsatisfiable).
7. b-residue calculus (constraints count, but do not locate).
8. De Bruijn-Hamel functionals (require metric incommensurability; tile sides are integers, hence ℤ-dependent).
9. Equilibrium stresses (balance equations have slack ≥ 2 at every vertex type; see `NineToolsFull`).

Lean content:
1. **`ninetools_metric_never_fires`**: λ-factor bound never fires: 11·(3f-2e)(f+e) ≤ 6m·f·(3f²-e²)
   (`LambdaFactor.metric_class_never_fires`).
2. **`ninetools_census_one_relation`**: census gives one linearly dependent relation (identity 13=13)
   (`NogoCensusWrap.nogoCensus_abstract`).
3. **`ninetools_junction_automaton`**: only forbidden junction pair is (γ,γ)
   (`JunctionAutomaton.only_forbidden_pair_is_gg`).
4. **`ninetools_group_no_higher_nilpotent`**: tiling group: if γ₂=γ₃ then no layer past class 2
   (`NilpotentTower.no_layer_past_class_two`; the premise γ₂=γ₃ is a hypothesis).
5. **`ninetools_no_similarity_proof`**: no similarity-invariant criterion can work
   (`ScaleRigidity.no_similarity_invariant_proof`).
6. **`ninetools_gamma_two_endpoints_unsat`**: tool 6 (γ-count stretch): any non-empty admissible
   orientation sequence cannot have both endpoints presenting γ (first=BG, last=GB), because
   orient_monotone forces GB^j ++ BG^k — if j≥1 then first≠BG; if j=0 then last=BG≠GB.
8. **`ninetools_dBH_linear_dep`**: tile sides ef, f²-e², f² satisfy f·(ef) = e·(f²) over ℕ,
   so they are ℤ-linearly dependent; De Bruijn-Hamel requires incommensurability.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.NineToolsWrap

open Erdos634.LambdaFactor Erdos634.ScaleRigidity

/-- prop:ninetools (tool 1): metric-class bound never fires on any member (metric_class_never_fires). -/
theorem ninetools_metric_never_fires (e f m : ℤ) (he : 1 ≤ e) (hef : e < f) (hm : 1 ≤ m) :
    11 * ((3 * f - 2 * e) * (f + e)) ≤ 6 * (m * f * (3 * f ^ 2 - e ^ 2)) :=
  metric_class_never_fires e f m he hef hm

/-- Tool 2: Euler/angle-sum counting coincides with one relation.
The side census for the (3,7) member gives α- and β-count equations that are linearly
dependent (sum to identity 13=13) and do not constrain the junction count x.
(`NogoCensusWrap.nogoCensus_abstract`, standard axioms, 0 sorry.) -/
theorem ninetools_census_one_relation :
    (∀ u x A B : ℤ, A + B = 2 * (10 - x) →
      ((7 - u) + (x - 7) + A) + (u + (x - 7) + B) = 13) ∧
    (∃ x₁ x₂ : ℤ, x₁ ≠ x₂ ∧
      (∃ u A B : ℤ, A + B = 2 * (10 - x₁) ∧
        (7 - u) + (x₁ - 7) + A = 3 ∧ u + (x₁ - 7) + B = 10) ∧
      (∃ u A B : ℤ, A + B = 2 * (10 - x₂) ∧
        (7 - u) + (x₂ - 7) + A = 3 ∧ u + (x₂ - 7) + B = 10)) :=
  let h := Erdos634.Draft.NogoCensusWrap.nogoCensus_abstract
  ⟨h.2.1, h.2.2⟩

/-- prop:ninetools (tool 3): edge-pairing parity / junction automaton: the only inadmissible
junction pair over all nine angle-kind pairs is (γ,γ). This is the failure point for any
parity-based approach: the automaton is consistent and hugely so (10,560 solutions exist).
(JunctionAutomaton.only_forbidden_pair_is_gg, standard axioms, 0 sorry.) -/
theorem ninetools_junction_automaton :
    ∀ (T B : Erdos634.JunctionAutomaton.Angle),
      ¬ Erdos634.JunctionAutomaton.admissible T B ↔
        T = Erdos634.JunctionAutomaton.Angle.gamma ∧ B = Erdos634.JunctionAutomaton.Angle.gamma :=
  Erdos634.JunctionAutomaton.only_forbidden_pair_is_gg

/-- Tool 4: Conway-Lagarias tiling group: the implication
"if γ₂ = γ₃ (for the tiling group) then it collapses to its rank-two abelianization"
is formalized.  The premise γ₂=γ₃ for the actual tiling group is a hypothesis.
(NilpotentTower.no_layer_past_class_two, standard axioms, 0 sorry.) -/
theorem ninetools_group_no_higher_nilpotent {G : Type*} [Group G]
    (h : Subgroup.lowerCentralSeries G 3 = Subgroup.lowerCentralSeries G 2) :
    ∀ k ≥ 2, Subgroup.lowerCentralSeries G k = Subgroup.lowerCentralSeries G 2 :=
  Erdos634.NilpotentTower.no_layer_past_class_two h

/-- prop:ninetools (tool 5): no similarity-invariant criterion can exclude tileability
(ScaleRigidity.no_similarity_invariant_proof). -/
theorem ninetools_no_similarity_proof
    {Tile Target Data Scale : Type}
    (Tileable : Tile → Target → Prop)
    (scale : Scale → Target → Target)
    (data : Tile → Target → Data)
    (hdata : ∀ (k : Scale) (T : Tile) (S : Target), data T (scale k S) = data T S)
    (P : Data → Prop)
    (hsound : ∀ (T : Tile) (S : Target), P (data T S) → ¬ Tileable T S)
    (T : Tile) (S : Target) (k : Scale)
    (hTileable : Tileable T (scale k S)) :
    ¬ P (data T S) :=
  no_similarity_invariant_proof Tileable scale data hdata P hsound T S k hTileable

/-- prop:ninetools (tool 8): De Bruijn-Hamel functionals require that side lengths are
linearly independent over ℤ ("metrically incommensurable"), but the base-β tile's sides
ef, f²-e², f² satisfy f·(ef) = e·(f²), so they are ℤ-linearly dependent.
(Pure ring identity, no axioms beyond the standard three.) -/
theorem ninetools_dBH_linear_dep (e f : ℕ) :
    f * (e * f) = e * f ^ 2 := by ring

/-- prop:ninetools (tool 6): γ-count stretch — any non-empty admissible orientation sequence
cannot have both endpoints presenting γ (first element = BG presenting γ at its right AND last
element = GB presenting γ at its left). Under orient_monotone, the sequence is GB^j ++ BG^k:
if j≥1, first=GB (presents β at right, not γ); if j=0, sequence is BG^k, last=BG (presents β
at left, not γ). So the two-endpoint γ hypothesis is unsatisfiable for any non-empty sequence.
(orient_monotone from Inflation.lean, standard axioms, 0 sorry.) -/
theorem ninetools_gamma_two_endpoints_unsat (L : List Erdos634.Inflation.Orient)
    (hne : L ≠ [])
    (hadm : L.Chain' (fun l r => Erdos634.Inflation.admissiblePair l r = true)) :
    ¬ (L.head? = some Erdos634.Inflation.Orient.BG ∧
       L.getLast? = some Erdos634.Inflation.Orient.GB) := by
  open Erdos634.Inflation Erdos634.Inflation.Orient in
  obtain ⟨j, k, hjk⟩ := orient_monotone L hadm
  subst hjk
  intro ⟨hfirst, hlast⟩
  cases j with
  | zero =>
    -- L = BG^k; first=BG is consistent; but last must also be BG
    simp only [List.replicate_zero, List.nil_append] at hfirst hlast hne
    have hk : 0 < k := Nat.pos_of_ne_zero (fun hk => hne (by simp [hk]))
    have : (List.replicate k Erdos634.Inflation.Orient.BG).getLast? =
           some Erdos634.Inflation.Orient.BG := by
      have hne2 : List.replicate k Erdos634.Inflation.Orient.BG ≠ [] := by
        simp only [ne_eq, List.replicate_eq_nil_iff]; omega
      rw [List.getLast?_eq_some_getLast hne2, List.getLast_replicate hne2]
    rw [this] at hlast; exact absurd hlast (by simp)
  | succ j' =>
    -- L starts with GB (not BG)
    simp only [List.replicate_succ, List.cons_append, List.head?] at hfirst
    exact absurd hfirst (by simp)

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord in
/-- prop:ninetools (tool 7): b-residue calculus — vacuous in the base-β setting:
no base-β tiling exists (basebeta_full_unc), so the calculus's failure to constrain
locations (58 of 60 b-edges with non-junction endpoint in certs) holds vacuously. -/
theorem ninetools_b_residue_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  Erdos634.Draft.VacuousCompanionWrap.prop_ninetools_tool7_vacuous D hco he hef htgt h0 h1 h2

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord in
/-- prop:ninetools (tool 9): equilibrium stresses — vacuous in the base-β setting:
no base-β tiling exists (basebeta_full_unc), so the slack-≥2 failure holds vacuously. -/
theorem ninetools_equilibrium_stress_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  Erdos634.Draft.VacuousCompanionWrap.prop_ninetools_tool9_vacuous D hco he hef htgt h0 h1 h2

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord in
/-- prop:ninetools (combined): given a hypothetical base-β CongruentDissection, False.
This is the single combined theorem for all nine tool classes: since no base-β tiling exists
(basebeta_full_unc), all nine tools vacuously fail to answer the crossing question. The seven
non-vacuous witnesses (tools 1,2,3,4,5,6,8) remain available as standalone theorems above. -/
theorem ninetools_all_nine_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  Erdos634.Draft.VacuousCompanionWrap.base_beta_false D hco he hef htgt h0 h1 h2

#print axioms ninetools_gamma_two_endpoints_unsat
#print axioms ninetools_metric_never_fires
#print axioms ninetools_census_one_relation
#print axioms ninetools_junction_automaton
#print axioms ninetools_group_no_higher_nilpotent
#print axioms ninetools_no_similarity_proof
#print axioms ninetools_dBH_linear_dep
#print axioms ninetools_b_residue_vacuous
#print axioms ninetools_equilibrium_stress_vacuous
#print axioms ninetools_all_nine_vacuous

end Erdos634.Draft.NineToolsWrap
