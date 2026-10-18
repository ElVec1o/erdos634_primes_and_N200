import Mathlib.Tactic

/-!
# APRIME seat 1 — straight-vertex lemma, pair transition table, counting identity
for the γ = 2α tile (angles α, β = π − 3α, γ = 2α).  

Source: the written proofs of the paper (re-checked here).
Level: the exact angle-arithmetic core.  BLOCKER (named): there is no "leg" layer over a real
`Dissection` (a straight boundary segment, the tiles along it as an ordered edge list with their
oriented angles at each boundary vertex, fans at boundary points); `Leg.Valid` below is the
combinatorial model whose hypotheses are exactly "each leg vertex carries a fan of the straight-vertex
lemma", and the connection real dissection -> `Valid` is not formalized.  Nothing here uses the tile
sides (u²,v²−u²,uv): only α/π irrational, which is hypothesis of the first theorem.
-/

namespace Erdos634.Draft.APrimeSeat1

/-- Straight-vertex lemma: `xα + yβ + zγ = π` with `α/π` irrational forces `y = 1`, `x + 2z = 3`. -/
theorem straight_vertex (α : ℝ) (hirr : Irrational (α / Real.pi)) (x y z : ℕ)
    (h : (x : ℝ) * α + y * (Real.pi - 3 * α) + z * (2 * α) = Real.pi) :
    y = 1 ∧ x + 2 * z = 3 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have key : ((x : ℤ) + 2 * z - 3 * y : ℤ) * α = ((1 : ℤ) - y : ℤ) * Real.pi := by
    push_cast; linarith
  by_cases hk : ((x : ℤ) + 2 * z - 3 * y : ℤ) = 0
  · have h2 : (((1 : ℤ) - y : ℤ) : ℝ) * Real.pi = 0 := by rw [← key, hk]; simp
    have h3 : (((1 : ℤ) - y : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hpi
    have h4 : ((1 : ℤ) - y) = 0 := by exact_mod_cast h3
    omega
  · exfalso
    apply hirr
    refine ⟨(((1 : ℤ) - y : ℤ) : ℚ) / ((x : ℤ) + 2 * z - 3 * y : ℤ), ?_⟩
    have hk' : (((x : ℤ) + 2 * z - 3 * y : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hk
    push_cast
    rw [div_eq_div_iff (by exact_mod_cast hk') hpi]
    push_cast at key
    linarith

/-- Hypothesis witness: `α = π√2/10` has `α/π` irrational and `0 < α < π/3` (so a genuine tile angle). -/
theorem straight_vertex_hyp_witness :
    ∃ α : ℝ, Irrational (α / Real.pi) ∧ 0 < α ∧ 3 * α < Real.pi := by
  refine ⟨Real.pi * Real.sqrt 2 / 10, ?_, ?_, ?_⟩
  · have : Real.pi * Real.sqrt 2 / 10 / Real.pi = Real.sqrt 2 / 10 := by
      field_simp
    rw [this]
    have h2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
    have := h2.div_natCast (m := 10) (by norm_num)
    simpa using this
  · have := Real.pi_pos; positivity
  · have := Real.pi_pos
    have hs : Real.sqrt 2 < 2 := by
      rw [show (2:ℝ) = Real.sqrt 4 by
        rw [show (4:ℝ) = 2^2 by norm_num]; simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    nlinarith

/-! ### Angles, oriented edges -/

inductive Ang | al | be | ga deriving DecidableEq, Repr

/-- Oriented edge tiles: `a>` has (left,right) angles (β,γ), `b>` (α,γ), `c>` (α,β); `<` mirrors. -/
inductive OE | ap | am | bp | bm | cp | cm deriving DecidableEq, Repr, Fintype

def OE.l : OE → Ang
  | .ap => .be | .am => .ga | .bp => .al | .bm => .ga | .cp => .al | .cm => .be
def OE.r : OE → Ang
  | .ap => .ga | .am => .be | .bp => .ga | .bm => .al | .cp => .be | .cm => .al

/-- Angle counts `(#α, #β, #γ)`. -/
abbrev Cnt := ℕ × ℕ × ℕ

def Ang.cnt : Ang → Cnt
  | .al => (1, 0, 0) | .be => (0, 1, 0) | .ga => (0, 0, 1)

def Cnt.add (a b : Cnt) : Cnt := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

/-- A multiset of angles at a boundary point is a fan (sums to π, by `straight_vertex`). -/
abbrev Fan (c : Cnt) : Prop := c.2.1 = 1 ∧ c.1 + 2 * c.2.2 = 3

/-- All possible middle contents between two consecutive leg edges `e₁ e₂`. -/
def mids (e₁ e₂ : OE) : List Cnt :=
  ((List.range 4).flatMap fun x => (List.range 2).flatMap fun y => (List.range 3).map fun z => (x, y, z)).filter
    fun m => decide (Fan (Cnt.add (Cnt.add e₁.r.cnt e₂.l.cnt) m))

/-- Pair transition table (seat 1 §2). -/
def table : OE → OE → List Cnt
  | .ap, .ap => [(1,0,0)] | .ap, .bp => [(0,1,0)] | .ap, .cp => [(0,1,0)] | .ap, .cm => [(1,0,0)]
  | .ap, .am => [] | .ap, .bm => []
  | .am, .am => [(1,0,0)] | .am, .bp => [(0,0,1),(2,0,0)] | .am, .bm => [(1,0,0)] | .am, .cp => [(0,0,1),(2,0,0)]
  | .am, .ap => [] | .am, .cm => []
  | .cp, .cp => [(0,0,1),(2,0,0)] | .cp, .cm => []
  | .cm, .cm => [(0,0,1),(2,0,0)] | .cm, .cp => [(1,1,0)]
  | _, _ => []

/-- Seat 1 table for the rows "after a>", "after a<", "c c" and `c< c>`: verified against `mids`. -/
theorem pair_table_rows :
    mids .ap .ap = table .ap .ap ∧ mids .ap .bp = table .ap .bp ∧ mids .ap .cp = table .ap .cp ∧
    mids .ap .cm = table .ap .cm ∧ mids .ap .am = ([] : List Cnt) ∧ mids .ap .bm = ([] : List Cnt) ∧
    mids .am .am = table .am .am ∧ mids .am .bp = table .am .bp ∧ mids .am .bm = table .am .bm ∧
    mids .am .cp = table .am .cp ∧ mids .am .ap = ([] : List Cnt) ∧ mids .am .cm = ([] : List Cnt) ∧
    mids .cp .cp = table .cp .cp ∧ mids .cp .cm = ([] : List Cnt) ∧ mids .cm .cm = table .cm .cm ∧
    mids .cm .cp = table .cm .cp := by
  repeat' apply And.intro
  all_goals decide

/-- Before an `a`-edge: `c> a<` (α); `c< a>` (αα|γ), `c< a<` (β); `b> a>` (α); `b< a>` (αα|γ); `b< a<` (β);
and `c> a>` is impossible. -/
theorem pair_table_before_a :
    mids .cp .am = [(1,0,0)] ∧ mids .cp .ap = ([] : List Cnt) ∧ mids .cm .ap = [(0,0,1),(2,0,0)] ∧
    mids .cm .am = [(0,1,0)] ∧ mids .bp .ap = [(1,0,0)] ∧ mids .bm .ap = [(0,0,1),(2,0,0)] ∧
    mids .bm .am = [(0,1,0)] := by
  repeat' apply And.intro
  all_goals decide

/-- Between consecutive leg edges there is always at least one middle tile (all 36 pairs). -/
theorem mids_nonempty_content : ∀ e₁ e₂ : OE, ∀ m ∈ mids e₁ e₂, m ≠ (0, 0, 0) := by decide

/-- Hypothesis witness: the table is not vacuous (a valid transition exists). -/
theorem mids_witness : mids .cp .am ≠ [] := by decide

/-! ### Counting identity -/

/-- A leg: first edge, then steps (middle content, next edge); every vertex carries a fan. -/
def Valid : OE → List (Cnt × OE) → Prop
  | _, [] => True
  | e, (m, e') :: t => Fan (Cnt.add (Cnt.add e.r.cnt e'.l.cnt) m) ∧ Valid e' t

def lastE : OE → List (Cnt × OE) → OE
  | e, [] => e
  | _, (_, e') :: t => lastE e' t

def edges (e : OE) (t : List (Cnt × OE)) : List OE := e :: t.map Prod.snd

def muB : List (Cnt × OE) → ℕ
  | [] => 0 | (m, _) :: t => m.2.1 + muB t
def muAG : List (Cnt × OE) → ℕ
  | [] => 0 | (m, _) :: t => (m.1 + 2 * m.2.2) + muAG t

def betaEnds (e : OE) : ℕ := (e.l.cnt.2.1 + e.r.cnt.2.1)
def agEnds (e : OE) : ℕ := (e.l.cnt.1 + 2 * e.l.cnt.2.2) + (e.r.cnt.1 + 2 * e.r.cnt.2.2)

def sumList (f : OE → ℕ) : List OE → ℕ
  | [] => 0 | e :: t => f e + sumList f t

/-- General bookkeeping: all edge ends except the first left and last right sit at the `n-1` leg vertices. -/
theorem valid_beta (e : OE) (t : List (Cnt × OE)) (hv : Valid e t) :
    muB t + sumList betaEnds (edges e t) = t.length + e.l.cnt.2.1 + (lastE e t).r.cnt.2.1 := by
  induction t generalizing e with
  | nil => simp [muB, sumList, edges, lastE, betaEnds]
  | cons p t ih =>
    obtain ⟨m, e'⟩ := p
    obtain ⟨h1, h2⟩ := hv
    have := ih e' h2
    simp only [muB, edges, List.map, sumList, lastE, List.length_cons] at this ⊢
    obtain ⟨h1a, h1b⟩ := h1
    simp only [Cnt.add] at h1a h1b
    simp only [betaEnds] at this ⊢
    omega

theorem valid_ag (e : OE) (t : List (Cnt × OE)) (hv : Valid e t) :
    muAG t + sumList agEnds (edges e t) =
      3 * t.length + (e.l.cnt.1 + 2 * e.l.cnt.2.2) + ((lastE e t).r.cnt.1 + 2 * (lastE e t).r.cnt.2.2) := by
  induction t generalizing e with
  | nil => simp [muAG, sumList, edges, lastE, agEnds]
  | cons p t ih =>
    obtain ⟨m, e'⟩ := p
    obtain ⟨h1, h2⟩ := hv
    have := ih e' h2
    simp only [muAG, edges, List.map, sumList, lastE, List.length_cons] at this ⊢
    obtain ⟨h1a, h1b⟩ := h1
    simp only [Cnt.add] at h1a h1b
    simp only [agEnds] at this ⊢
    omega

def cntLetter (f : OE → Bool) (es : List OE) : ℕ := (es.filter f).length
def isA : OE → Bool | .ap | .am => true | _ => false
def isB : OE → Bool | .bp | .bm => true | _ => false
def isC : OE → Bool | .cp | .cm => true | _ => false

theorem sumBeta_eq (es : List OE) : sumList betaEnds es = cntLetter isA es + cntLetter isC es := by
  induction es with
  | nil => rfl
  | cons e t ih =>
    simp only [sumList, cntLetter, List.filter_cons] at ih ⊢
    cases e <;> simp [betaEnds, OE.l, OE.r, Ang.cnt, isA, isC] <;> omega

theorem sumAG_eq (es : List OE) :
    sumList agEnds es = 2 * cntLetter isA es + 3 * cntLetter isB es + cntLetter isC es := by
  induction es with
  | nil => rfl
  | cons e t ih =>
    simp only [sumList, cntLetter, List.filter_cons] at ih ⊢
    cases e <;> simp [agEnds, OE.l, OE.r, Ang.cnt, isA, isB, isC] <;> omega

theorem length_eq (es : List OE) : es.length = cntLetter isA es + cntLetter isB es + cntLetter isC es := by
  induction es with
  | nil => rfl
  | cons e t ih =>
    simp only [cntLetter, List.filter_cons, List.length_cons] at ih ⊢
    cases e <;> simp [isA, isB, isC] <;> omega

/-- **Counting identity.**  A leg with first left angle `α` (G1) and last right angle `α` or `β`;
`p,q,r` the numbers of `a,b,c` edges, `ε = 1` iff the last edge has `β` at the apex.  Then
`μ_β = q − 1 + ε` and `μ_α + 2μ_γ = p + 2r − 1 − ε` (written additively over ℕ). -/
theorem counting_identity (e : OE) (t : List (Cnt × OE)) (hv : Valid e t)
    (hfirst : e.l = .al) (hlast : (lastE e t).r = .al ∨ (lastE e t).r = .be) (ε : ℕ)
    (hε : ε = (lastE e t).r.cnt.2.1) :
    muB t + 1 = cntLetter isB (edges e t) + ε ∧
    muAG t + 1 + ε = cntLetter isA (edges e t) + 2 * cntLetter isC (edges e t) := by
  have h1 := valid_beta e t hv
  have h2 := valid_ag e t hv
  rw [sumBeta_eq] at h1
  rw [sumAG_eq] at h2
  have hl := length_eq (edges e t)
  have hlen : (edges e t).length = t.length + 1 := by simp [edges]
  have hf1 : e.l.cnt.2.1 = 0 := by rw [hfirst]; rfl
  have hf2 : e.l.cnt.1 + 2 * e.l.cnt.2.2 = 1 := by rw [hfirst]; rfl
  have hr1 : (lastE e t).r.cnt.2.1 = ε := hε.symm
  have hr2 : (lastE e t).r.cnt.1 + 2 * (lastE e t).r.cnt.2.2 + ε = 1 := by
    rcases hlast with hr | hr <;> rw [hr] at hε ⊢ <;> simp [Ang.cnt] at hε ⊢ <;> omega
  omega

/-- Witness: a concrete valid leg `c> a<` with middle α (apex right angle β): `p=1,q=0,r=1`, `ε=1`. -/
theorem counting_witness :
    Valid .cp [((1,0,0), .am)] ∧ (OE.cp).l = .al ∧ (lastE .cp [((1,0,0), .am)]).r = .be := by
  refine ⟨?_, rfl, rfl⟩
  simp [Valid, Fan, Cnt.add, OE.r, OE.l, Ang.cnt]

end Erdos634.Draft.APrimeSeat1
