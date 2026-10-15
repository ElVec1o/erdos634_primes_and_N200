-- Draft/FluxGRow3Step1.lean — Lemma A, Step 1: the geometric corner fact connecting a real
-- `CongruentDissection` by the right tile `(α, π/2−α, π/2)` to the abstract `(p,q,r)` hypothesis
-- of `lemmaA_case_split` (`Draft/FluxGRow3LemmaA.lean`). Not imported into `All.lean`.
--
-- `TilePlacement.corner_multiplicities` is angle-generic: at any target corner it gives
-- `card(α)·α + card(β)·β + card(γ)·γ + card(π)·π = C` (`C` the corner angle) for any tile whose local
-- angles lie in `{α,β,γ,π,0}`. Substituting `β = π/2−α`, `γ = π/2` and folding the straight-angle count
-- into the `π/2` coefficient (`π = 2·(π/2)`) gives the shape `p·α + q·(π/2−α) + r·(π/2)` of
-- `Row3.cornerAngle`, with `r := card(γ) + 2·card(π)`.
--
-- Contents:
--   (1) `corner_step1_dissection` — at a `Dissection` level, with `hvals` a hypothesis: at any target
--       corner there are `(p,q,r) : ℕ×ℕ×ℕ` with `1 ≤ p+q+r` such that `Row3.cornerAngle α p q r` equals
--       the corner angle.
--   (2) `congruentDissection_corner_step1` — the same for a real `CongruentDissection`, with `hvals`
--       derived from `TileAt.congruentDissection_localAngle_mem`.
--   (3) `congruentDissection_row3_lemmaA` — apply (2) at the three target corners `k = 0, 1, 2`, combine
--       with `Erdos634.Geometry.cornerAngle_sum` (the three corner angles sum to `π`),
--       `Erdos634.MarchFlank.cornerAngle_pos` and `RouteOneVertexKill.cornerAngle_lt_pi`, and feed the
--       bundle into `Row3.lemmaA_case_split`. The conclusion is Lemma A's full case split for the three
--       corners of the target of a real `CongruentDissection`.
--
-- The hypotheses `hα' hβ' hγ'` (the corners of the model tile are `α, β, γ`) are hypotheses of the
-- theorem. They are discharged at a concrete dissection in `FluxGRow3WitnessFinal`.
import Erdos634.TileAt
import Erdos634.RouteOneVertexKill
import Erdos634.Draft.FluxGRow3LemmaA

namespace Erdos634.Row3Step1

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {N : ℕ}

/-! ## Part 1: Dissection level — the raw corner-multiplicities fact, repackaged -/

/-- **Step 1, Dissection level.** At any target corner of a dissection whose tiles' local angles
there are confined to `{α, β, γ, π, 0}` with `β = π/2 − α`, `γ = π/2` (the right tile's own three
angles), SOME `(p, q, r) : ℕ × ℕ × ℕ`, not all zero, makes `Row3.cornerAngle α p q r` equal the
real corner angle — with `r` absorbing both the `γ`-count and twice the straight-angle count
(`π = 2·(π/2)`). No uniqueness of `(p,q,r)` is claimed or needed: this is pure existence, exactly
what Lemma A's case split (`FluxGRow3LemmaA.lean`, P79) consumes as its hypothesis. -/
theorem corner_step1_dissection {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hβdef : β = Real.pi / 2 - α) (hγdef : γ = Real.pi / 2) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ)) :
    ∃ p q r : ℕ, 1 ≤ p + q + r ∧
      Erdos634.Geometry.Row3.cornerAngle α p q r < Real.pi ∧
      Erdos634.Geometry.Row3.cornerAngle α p q r
        = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) := by
  classical
  have h := Erdos634.TilePlacement.corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 k hvals
  set p := ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card with hpdef
  set q := ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card with hqdef
  set z := ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card with hzdef
  set w := ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card with hwdef
  have heq : Erdos634.Geometry.Row3.cornerAngle α p q (z + 2 * w)
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) := by
    unfold Erdos634.Geometry.Row3.cornerAngle
    rw [hβdef, hγdef] at h
    push_cast
    linarith [h]
  refine ⟨p, q, z + 2 * w, ?_, ?_, heq⟩
  · by_contra hcon
    push_neg at hcon
    have hp0 : p = 0 := by omega
    have hq0 : q = 0 := by omega
    have hzw0 : z + 2 * w = 0 := by omega
    rw [hp0, hq0, hzw0] at heq
    have hzero : Erdos634.Geometry.Row3.cornerAngle α 0 0 0 = 0 := by
      unfold Erdos634.Geometry.Row3.cornerAngle; push_cast; ring
    rw [hzero] at heq
    have hposC := Erdos634.MarchFlank.cornerAngle_pos D.target k
    linarith [heq, hposC]
  · rw [heq]
    exact Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target k

/-! ## Part 2: `CongruentDissection` level — `hvals` derived, not hypothesised -/

/-- **Step 1, `CongruentDissection` level.** Same conclusion as `corner_step1_dissection`, with
`hvals` derived from `TileAt.congruentDissection_localAngle_mem` (reused verbatim; angle-generic,
never mentions the right tile's own relation). -/
theorem congruentDissection_corner_step1 (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hβdef : β = Real.pi / 2 - α) (hγdef : γ = Real.pi / 2)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ) (k : Fin 3) :
    ∃ p q r : ℕ, 1 ≤ p + q + r ∧
      Erdos634.Geometry.Row3.cornerAngle α p q r < Real.pi ∧
      Erdos634.Geometry.Row3.cornerAngle α p q r
        = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) :=
  corner_step1_dissection D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hβdef hγdef k (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i)

/-! ## Part 3: the assembly — Lemma A's full conclusion for a real `CongruentDissection`

Combines Part 2 at the target's three labelled corners `k = 0, 1, 2` with
`Erdos634.Geometry.cornerAngle_sum` (Mathlib's triangle angle-sum theorem, already in the corpus,
`Dissection.lean:281-296`) and feeds the bundle into `Row3.lemmaA_case_split`
(`FluxGRow3LemmaA.lean`, P79). This is Step 1, closed and connected to a real `CongruentDissection`
— the disjunction is Lemma A's own conclusion, for the three ACTUAL corners of `D.target`, not an
abstract hypothesis. -/
theorem congruentDissection_row3_lemmaA (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hβdef : β = Real.pi / 2 - α) (hγdef : γ = Real.pi / 2)
    (hαpos : 0 < α) (hirr : Irrational (α / Real.pi))
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ) :
    ∃ p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℕ,
    (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = 2 * (Real.pi / 2 - α) ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = 2 * (Real.pi / 2 - α) ∧
        Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = 2 * (Real.pi / 2 - α) ∧
        Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = α ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = 2 * α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = 2 * α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = 2 * α) := by
  have hv0 : ∀ i, (D.tile i).localAngle (D.target.pts 0) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' 0 i
  have hv1 : ∀ i, (D.tile i).localAngle (D.target.pts 1) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' 1 i
  have hv2 : ∀ i, (D.tile i).localAngle (D.target.pts 2) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' 2 i
  obtain ⟨p0, q0, r0, hpos0, hlt0, heq0⟩ :=
    corner_step1_dissection D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
      hβdef hγdef 0 hv0
  obtain ⟨p1, q1, r1, hpos1, hlt1, heq1⟩ :=
    corner_step1_dissection D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
      hβdef hγdef 1 hv1
  obtain ⟨p2, q2, r2, hpos2, hlt2, heq2⟩ :=
    corner_step1_dissection D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
      hβdef hγdef 2 hv2
  have hsum : Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0
      + Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1
      + Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi := by
    rw [heq0, heq1, heq2]
    exact Erdos634.Geometry.cornerAngle_sum D.target
  refine ⟨p0, q0, r0, p1, q1, r1, p2, q2, r2, ?_⟩
  exact Erdos634.Geometry.Row3.lemmaA_case_split hirr hαpos p0 q0 r0 p1 q1 r1 p2 q2 r2
    hpos0 hpos1 hpos2 hsum hlt0 hlt1 hlt2

-- Non-vacuity note, matching every other bridge file's own honesty section
-- (`FluxCRow5Bridge.lean:215-223`, reused verbatim in spirit): the hypotheses `hα'`/`hβ'`/`hγ'`
-- above are jointly satisfiable in the abstract (any `α ∈ (0, π/2)` with `α/π` irrational, model
-- corners `α, π/2 − α, π/2` in the stated cyclic order), but no real Lean `CongruentDissection`
-- witnessing them for row 3's RIGHT tile specifically is built anywhere in this corpus as of this
-- writing (`FluxGRow3Witness.lean`'s `N = 2` witness uses row 3's OLD isosceles construction, not
-- independently checked here to instantiate `hα' hβ' hγ'` for `rightTilePlacement`'s tile up to
-- the needed congruence — not claimed). So `congruentDissection_row3_lemmaA` above is Step 1
-- CLOSED as a bridge theorem — real `CongruentDissection` in, Lemma A's conclusion out, no
-- abstract corner-fact hypothesis anywhere in its statement — but its own antecedent (a real
-- `CongruentDissection` with these particular model corners) inherits the same paper-level
-- conditionality every other row's corner-count bridge does. This is not a new gap: it is the same
-- "is there a real witness" question `FluxCRow5Bridge.lean`, `FluxDRow4Bridge.lean` and P74's own
-- N=2 witness already answer differently case by case, not attempted here.

end Erdos634.Row3Step1

#print axioms Erdos634.Row3Step1.corner_step1_dissection
#print axioms Erdos634.Row3Step1.congruentDissection_corner_step1
#print axioms Erdos634.Row3Step1.congruentDissection_row3_lemmaA
