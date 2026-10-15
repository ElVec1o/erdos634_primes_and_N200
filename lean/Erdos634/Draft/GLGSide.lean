import Mathlib.Tactic

/-!
# The combinatorial boundary model of one side (Beeson 11.13 / 11.17 pigeonhole), no geometry

A side is a list of `n` supported tiles of types `a,b,c`, each with an orientation (which end is at the south vertex).
Ends: `a = (β,γ)`, `b = (α,γ)`, `c = (α,β)`.  Vertices `0..n`; tile `i` has south vertex `i`, north vertex `i+1`.
`pigeon`: tiles with exactly one `X`-end (`X = β` or `γ`) are injected into the interior vertices
`1..n-1` (at most one `X` per vertex, `V`), minus any set `E` of vertices known to carry no such end.
The geometry → model interface (angle sum at a boundary vertex ⇒ `V`; corner angle ⇒ `sa 0 = α`; apex) is not proved in this module.
-/

namespace Erdos634.GLG

inductive TT | a | b | c deriving DecidableEq, Fintype
inductive Ang | al | be | ga deriving DecidableEq, Fintype

def ends : TT → Ang × Ang
  | .a => (.be, .ga) | .b => (.al, .ga) | .c => (.al, .be)

def sAng (t : TT) (f : Bool) : Ang := if f then (ends t).2 else (ends t).1
def nAng (t : TT) (f : Bool) : Ang := if f then (ends t).1 else (ends t).2

/-- A side: `n` supported tiles with types and orientations. -/
structure Side where
  n : ℕ
  ty : ℕ → TT
  fl : ℕ → Bool

namespace Side
def sa (S : Side) (i : ℕ) : Ang := sAng (S.ty i) (S.fl i)
def na (S : Side) (i : ℕ) : Ang := nAng (S.ty i) (S.fl i)
def cnt (S : Side) (t : TT) : ℕ := ((Finset.range S.n).filter (fun i => S.ty i = t)).card

/-- Vertex rule: at an interior vertex at most one `γ` and at most one `β` among supported tiles. -/
structure V (S : Side) : Prop where
  vg : ∀ i, i + 1 < S.n → ¬ (S.na i = .ga ∧ S.sa (i + 1) = .ga)
  vb : ∀ i, i + 1 < S.n → ¬ (S.na i = .be ∧ S.sa (i + 1) = .be)
end Side

theorem gam_end (t : TT) (f : Bool) (h : t ≠ .c) : sAng t f = .ga ∨ nAng t f = .ga := by
  cases t <;> cases f <;> simp_all [sAng, nAng, ends]

theorem bet_end (t : TT) (f : Bool) (h : t ≠ .b) : sAng t f = .be ∨ nAng t f = .be := by
  cases t <;> cases f <;> simp_all [sAng, nAng, ends]

/-- Generic pigeonhole. -/
theorem pigeon (S : Side) (X : Ang) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ i < S.n, P i → S.sa i = X ∨ S.na i = X)
    (hV : ∀ i, i + 1 < S.n → ¬ (S.na i = X ∧ S.sa (i + 1) = X))
    (h0 : 0 < S.n → S.sa 0 ≠ X) (hn : 0 < S.n → S.na (S.n - 1) ≠ X)
    (E : Finset ℕ) (hE : E ⊆ Finset.Icc 1 (S.n - 1))
    (hEd : ∀ i < S.n, P i → (if S.sa i = X then i else i + 1) ∉ E) :
    ((Finset.range S.n).filter P).card + E.card ≤ S.n - 1 := by
  set f : ℕ → ℕ := fun i => if S.sa i = X then i else i + 1 with hf
  have hmap : ∀ i ∈ (Finset.range S.n).filter P, f i ∈ Finset.Icc 1 (S.n - 1) \ E := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hin, hPi⟩ := hi
    rw [Finset.mem_sdiff]
    refine ⟨?_, hEd i hin hPi⟩
    rw [Finset.mem_Icc]
    by_cases hs : S.sa i = X
    · have : i ≠ 0 := by
        rintro rfl; exact h0 hin hs
      simp only [hf, hs, if_true]; omega
    · have hna : S.na i = X := (hP i hin hPi).resolve_left hs
      have : i ≠ S.n - 1 := by
        intro hh; subst hh; exact hn (by omega) hna
      simp only [hf, hs, if_false]; omega
  have hinj : Set.InjOn f ((Finset.range S.n).filter P : Finset ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
    by_contra hne
    by_cases hsi : S.sa i = X <;> by_cases hsj : S.sa j = X <;> simp only [hf, hsi, hsj, if_true, if_false] at hij
    · omega
    · have hnj : S.na j = X := (hP j hj.1 hj.2).resolve_left hsj
      exact hV j (by omega) ⟨hnj, by rw [show j + 1 = i by omega]; exact hsi⟩
    · have hni : S.na i = X := (hP i hi.1 hi.2).resolve_left hsi
      exact hV i (by omega) ⟨hni, by rw [show i + 1 = j by omega]; exact hsj⟩
    · omega
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  rw [Finset.card_sdiff_of_subset hE] at hc
  have := Finset.card_le_card hE
  simp only [Nat.card_Icc] at this hc
  omega

/-- Sum over the tiles = sum over types weighted by counts. -/
theorem sumty (S : Side) (g : TT → ℕ) :
    ∑ i ∈ Finset.range S.n, g (S.ty i) = S.cnt .a * g .a + S.cnt .b * g .b + S.cnt .c * g .c := by
  have h : ∀ i, g (S.ty i) = (if S.ty i = .a then g .a else 0) + (if S.ty i = .b then g .b else 0)
      + (if S.ty i = .c then g .c else 0) := by
    intro i; cases S.ty i <;> simp
  simp only [h, Finset.sum_add_distrib]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, Side.cnt]

theorem cnt_total (S : Side) : S.cnt .a + S.cnt .b + S.cnt .c = S.n := by
  have := sumty S (fun _ => 1)
  simpa using this.symm

theorem card_nonc (S : Side) :
    ((Finset.range S.n).filter (fun i => S.ty i ≠ .c)).card + S.cnt .c = S.n := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range S.n) (fun i => S.ty i = .c)
  rw [Finset.card_range] at h
  simp only [ne_eq]
  unfold Side.cnt; omega

theorem card_nonb (S : Side) :
    ((Finset.range S.n).filter (fun i => S.ty i ≠ .b)).card + S.cnt .b = S.n := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range S.n) (fun i => S.ty i = .b)
  rw [Finset.card_range] at h
  simp only [ne_eq]
  unfold Side.cnt; omega

/-- `γ`-pigeonhole in count form: `r + |E| ≥ 1 + |E|` i.e. `r ≥ 1 + |E|`. -/
theorem gamma_count (S : Side) (hv : S.V) (hn0 : 0 < S.n) (h0 : S.sa 0 = .al) (hn : S.na (S.n - 1) ≠ .ga)
    (E : Finset ℕ) (hE : E ⊆ Finset.Icc 1 (S.n - 1))
    (hEd : ∀ i < S.n, S.ty i ≠ .c → (if S.sa i = .ga then i else i + 1) ∉ E) :
    1 + E.card ≤ S.cnt .c := by
  have := pigeon S .ga (fun i => S.ty i ≠ .c)
    (fun i _ hi => gam_end _ _ hi) hv.vg (fun _ => by rw [h0]; simp) (fun _ => hn) E hE hEd
  have h2 := card_nonc S
  omega

/-- `β`-pigeonhole: `q ≥ 1 + |E|`, if no `β` at the south end `0` and none at the north end. -/
theorem beta_count (S : Side) (hv : S.V) (hn0 : 0 < S.n) (h0 : S.sa 0 = .al) (hn : S.na (S.n - 1) ≠ .be) :
    1 ≤ S.cnt .b := by
  have := pigeon S .be (fun i => S.ty i ≠ .b)
    (fun i _ hi => bet_end _ _ hi) hv.vb (fun _ => by rw [h0]; simp) (fun _ => hn) ∅ (by simp)
    (by simp)
  have h2 := card_nonb S
  simp only [Finset.card_empty, add_zero, ne_eq] at this h2
  omega

end Erdos634.GLG
