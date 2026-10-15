import Mathlib.Tactic
import Erdos634.EdgeWordConversion
import Erdos634.Draft.ChordFar
import Erdos634.Draft.ChordWord
import Erdos634.Draft.T30LSectorFill

/-!
# `Pi3Corner`: the corner chord is a single `c`-edge, and the C2 rule model

* `far_chain_single_gen` (real dissection): for a `CongruentDissection` whose model sides are among `s0, s1, s2`, a chord of
  length `L` clamped on the target as in `ChordFar.chord_far_sum_cong`, and an arithmetic hypothesis `hword`
  (`x s0 + y s1 + z s2 = L → x + y + z = 1`), the far chain consists of exactly one edge, of length `L`.
* `t30_corner_chord_single`: the instance for the T30 tile `(9+√21, 9−√21, 12)` and the chord `L = c = 12`, where
  `hword` is `ChordWord.chord_c` (the irrational split (I)).  The corner chord `PR`
  (a `c`-edge of the corner tile `T`) is covered, on the far side, by a single `c`-edge.
* Witness on a real dissection (`wall_far_single`): `EdgeWordConversion.wallCongruentDissection` (2 congruent tiles,
  sides `√2, √2, 2`), median chord of length `√2`, with `hword` proved from the irrationality of `√2`: the far chain is
  one edge of length `√2`.  `hword_fails_two`: for the chord `2√2` the arithmetic hypothesis
  is false (`(2,0,0)` solves it with `x+y+z = 2`), so the single-edge conclusion needs the word lemma.
* C2 rule model (`OEdge`, `valid3`): the fan rule on a side (adjacent end angles one of `PP, PA, PB, AB`), corner ends
  `P`, and C2 (second tile starts with `P`, second-to-last ends with `P`).  `x1_fan_only : 2` side words,
  `x1_with_C2 : 0` (by `decide`); and abstractly
  `no_PP_edge` (no edge has both ends `P`) so C2 kills every 3-edge side.  These are statements about the rule model, not about a dissection `D`.
-/

namespace Erdos634.Pi3Corner

open Erdos634.Geometry Erdos634.EdgeWordConversion Erdos634.ChordFar Erdos634.ChordWord

/-- Sum of terms in `{a,b,c}`: `x a + y b + z c` with `x + y + z` the number of terms. -/
theorem sum_mem_card {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ) (a b c : ℝ)
    (h : ∀ i ∈ s, g i = a ∨ g i = b ∨ g i = c) :
    ∃ x y z : ℕ, (x : ℝ) * a + y * b + z * c = ∑ i ∈ s, g i ∧ x + y + z = s.card := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, by simp, by simp⟩
  | insert i s hi ih =>
    obtain ⟨x, y, z, hxyz, hc⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    rcases h i (Finset.mem_insert_self i s) with hg | hg | hg
    · exact ⟨x + 1, y, z, by rw [hg]; push_cast; linarith, by omega⟩
    · exact ⟨x, y + 1, z, by rw [hg]; push_cast; linarith, by omega⟩
    · exact ⟨x, y, z + 1, by rw [hg]; push_cast; linarith, by omega⟩

/-- **The far chain of a chord is a single edge, given the word lemma.** -/
theorem far_chain_single_gen {N : ℕ} (D : CongruentDissection N) {s0 s1 s2 L : ℝ}
    (hsides : ∀ i : Fin 3, sideLen D i = s0 ∨ sideLen D i = s1 ∨ sideLen D i = s2)
    (hword : ∀ x y z : ℕ, (x : ℝ) * s0 + y * s1 + z * s2 = L → x + y + z = 1)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P Q : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c) (hfQ : f Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdist : dist P Q = L) :
    ∃ e₀ ∈ D.lineChain (-f) (-c), D.lineChain (-f) (-c) = {e₀} ∧
      dist ((D.tile e₀.1).pts e₀.2) ((D.tile e₀.1).pts (e₀.2 + 1)) = L := by
  have hsum := chord_far_sum_cong D f hf c hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall
  rw [hdist] at hsum
  have hmem : ∀ e ∈ D.lineChain (-f) (-c),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = s0 ∨
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = s1 ∨
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = s2 := by
    intro e _
    rcases edge_length_trichotomy D e.1 e.2 with h' | h' | h'
    · rw [h']; exact hsides 0
    · rw [h']; exact hsides 1
    · rw [h']; exact hsides 2
  obtain ⟨x, y, z, hxyz, hcard⟩ := sum_mem_card (D.lineChain (-f) (-c))
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) s0 s1 s2 hmem
  have h1 := hword x y z (by rw [hxyz]; exact hsum)
  obtain ⟨e₀, he⟩ := Finset.card_eq_one.mp (by omega : (D.lineChain (-f) (-c)).card = 1)
  refine ⟨e₀, by rw [he]; simp, he, ?_⟩
  rw [he, Finset.sum_singleton] at hsum
  exact hsum

/-! ## T30 step L1 -/

/-- **L1, far side.**  The corner chord of length `c = 12` of the T30 tile is covered, on the far side, by exactly one
edge, of length `c`.  (`hsides`: the model's three sides are `a, b, c` in some order.) -/
theorem t30_corner_chord_single {N : ℕ} (D : CongruentDissection N)
    (hsides : ∀ i : Fin 3, sideLen D i = sa ∨ sideLen D i = sb ∨ sideLen D i = sc)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P Q : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c) (hfQ : f Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdist : dist P Q = sc) :
    ∃ e₀ ∈ D.lineChain (-f) (-c), D.lineChain (-f) (-c) = {e₀} ∧
      dist ((D.tile e₀.1).pts e₀.2) ((D.tile e₀.1).pts (e₀.2 + 1)) = sc :=
  far_chain_single_gen D hsides
    (fun x y z hxyz => by
      have := chord_c x y z (by unfold wordLen; exact hxyz)
      omega)
    f hf c hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP hint hwall hdist

/-! ## Witness: the real 2-tile dissection (sides √2, √2, 2), chord of length √2 -/

section witness

open Erdos634.TPErdos Erdos634.CertCoord

theorem hword_sqrt2 (x y z : ℕ)
    (h : (x : ℝ) * Real.sqrt 2 + y * Real.sqrt 2 + z * 2 = Real.sqrt 2) : x + y + z = 1 := by
  have hs := irrational_sqrt_two
  have h1 : (((x : ℤ) + y - 1 : ℤ) : ℝ) * Real.sqrt 2 = -(2 * z) := by push_cast; linarith
  have hxy : (x : ℤ) + y - 1 = 0 := by
    by_contra hne
    apply hs
    refine ⟨(-(2 * (z : ℚ))) / (((x : ℤ) + y - 1 : ℤ) : ℚ), ?_⟩
    have hm : (((x : ℤ) + y - 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne
    push_cast at hm h1 ⊢
    field_simp
    linarith
  have hz : (z : ℝ) = 0 := by
    have : (((x : ℤ) + y - 1 : ℤ) : ℝ) = 0 := by exact_mod_cast hxy
    rw [this] at h1; linarith
  have hz' : z = 0 := by exact_mod_cast hz
  omega

/-- For the chord `2√2` the arithmetic hypothesis fails: `(2,0,0)` solves
`x√2 + y√2 + 2z = 2√2` with `x+y+z = 2 ≠ 1`, so without `hword` the single-edge conclusion is false. -/
theorem hword_fails_two : ∃ x y z : ℕ,
    (x : ℝ) * Real.sqrt 2 + y * Real.sqrt 2 + z * 2 = 2 * Real.sqrt 2 ∧ x + y + z ≠ 1 :=
  ⟨2, 0, 0, by push_cast; ring, by norm_num⟩

theorem wall_sideLen_cases (i : Fin 3) :
    sideLen wallCongruentDissection i = Real.sqrt 2 ∨ sideLen wallCongruentDissection i = Real.sqrt 2
      ∨ sideLen wallCongruentDissection i = 2 := by
  have hsq : ∀ d : ℝ, 0 ≤ d → d ^ 2 = 2 → d = Real.sqrt 2 := fun d hd h => by
    rw [← h, Real.sqrt_sq hd]
  fin_cases i
  · left
    have h : dist (mkPt 0 0) (mkPt 1 1) ^ 2 = 2 := by rw [dist_sq_mkPt]; norm_num
    exact hsq _ dist_nonneg h
  · left
    have h : dist (mkPt 1 1) (mkPt 2 0) ^ 2 = 2 := by rw [dist_sq_mkPt]; norm_num
    exact hsq _ dist_nonneg h
  · right; right
    have h : dist (mkPt 2 0) (mkPt 0 0) ^ 2 = 2 ^ 2 := by rw [dist_sq_mkPt]; norm_num
    exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp h

theorem wall_dist_uv : dist wallU wallV = Real.sqrt 2 := by
  have h : dist wallU wallV ^ 2 = 2 := by
    rw [wallU, wallV, dist_sq_mkPt]; norm_num
  rw [← h, Real.sqrt_sq dist_nonneg]

/-- **`far_chain_single_gen` on a real dissection.**  The far side of the median chord of the 2-tile wall
dissection is a single edge of length `√2`. -/
theorem wall_far_single :
    ∃ e₀ ∈ wallCongruentDissection.lineChain (-wallF) (-0),
      wallCongruentDissection.lineChain (-wallF) (-0) = {e₀} ∧
      dist ((wallCongruentDissection.tile e₀.1).pts e₀.2)
        ((wallCongruentDissection.tile e₀.1).pts (e₀.2 + 1)) = Real.sqrt 2 :=
  far_chain_single_gen wallCongruentDissection wall_sideLen_cases hword_sqrt2
    wallF wallF_ne 0 wallU_ne_wallV wallF_u wallF_v
    gBase 0 gBase_bound_target (by rw [wallU, gBase_pt]; norm_num)
    (by rw [wallV, gBase_pt]; norm_num)
    hHyp 2 hHyp_bound (by rw [wallV, hHyp_pt]; norm_num)
    (by rw [wallU, hHyp_pt]; norm_num) wall_hint wall_hwall wall_dist_uv

end witness

/-! ## The C2 rule model and the x = 1 control -/

/-- Vertex angle labels: `P = π/3`, `A = α`, `B = β`. -/
inductive Ang | P | A | B
  deriving DecidableEq

open Ang

/-- An oriented edge: letter `0 = a`, `1 = b`, `2 = c` and a flip.  Edge `a` (opposite `α`) has end angles `{β, P}`,
`b` `{α, P}`, `c` `{α, β}`. -/
structure OEdge where
  letter : ℕ
  flip : Bool

def ends : ℕ → Ang × Ang
  | 0 => (B, P)
  | 1 => (A, P)
  | _ => (A, B)

def OEdge.st (e : OEdge) : Ang := if e.flip then (ends e.letter).2 else (ends e.letter).1
def OEdge.en (e : OEdge) : Ang := if e.flip then (ends e.letter).1 else (ends e.letter).2

/-- Allowed pair of end angles at an interior side vertex (the fan rule: `PP`, `PA`, `PB`, `AB`, either order;
`Pi3Tile.boundary_cases`). -/
def okPair : Ang → Ang → Bool
  | P, P => true
  | P, A => true
  | A, P => true
  | P, B => true
  | B, P => true
  | A, B => true
  | B, A => true
  | _, _ => false

/-- No edge has both ends `P`. -/
theorem no_PP_edge (e : OEdge) : ¬ (e.st = P ∧ e.en = P) := by
  rcases e with ⟨l, fl⟩
  rcases l with _ | _ | l <;> cases fl <;> simp [OEdge.st, OEdge.en, ends]

/-- A 3-edge side word: first start `P`, last end `P`, fan rule, and (if `c2`) the second tile starts with `P` and
the second-to-last (= second) ends with `P`. -/
def valid3 (c2 : Bool) (e1 e2 e3 : OEdge) : Bool :=
  e1.st == P && e3.en == P && okPair e1.en e2.st && okPair e2.en e3.st
    && (!c2 || (e2.st == P && e2.en == P))

def perms3 : List (ℕ × ℕ × ℕ) := [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]

def count3 (c2 : Bool) : ℕ :=
  (perms3.flatMap fun (p, q, r) => [false, true].flatMap fun f1 => [false, true].flatMap fun f2 =>
    [false, true].flatMap fun f3 =>
      if valid3 c2 ⟨p, f1⟩ ⟨q, f2⟩ ⟨r, f3⟩ = true then [()] else []).length

/-- x = 1, fan rule only: 2 side words (matches the hand enumeration). -/
theorem x1_fan_only : count3 false = 2 := by decide

/-- **x = 1 control.**  With C2 no side word survives (the pin exclusion on the boundary alone). -/
theorem x1_with_C2 : count3 true = 0 := by decide

/-- The same, abstractly: C2 is impossible for every 3-edge side, whatever the letters. -/
theorem c2_dead_3 (e1 e2 e3 : OEdge) : valid3 true e1 e2 e3 = false := by
  have := no_PP_edge e2
  unfold valid3
  by_cases h : e2.st = P ∧ e2.en = P
  · exact absurd h this
  · have h' : ¬ (e2.st = P) ∨ ¬ (e2.en = P) := by tauto
    rcases h' with h' | h' <;> simp [h']

#print axioms t30_corner_chord_single
#print axioms wall_far_single
#print axioms x1_fan_only
#print axioms x1_with_C2
#print axioms c2_dead_3

end Erdos634.Pi3Corner
