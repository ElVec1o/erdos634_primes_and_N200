import Mathlib.Tactic
import Erdos634.Draft.APrimeSeat1

/-!
# Theorem D', (b) the pigeonhole of stopped ends on the word of a leg  

Pure combinatorics on a list of oriented edges (no geometry).  `Compat e e'` : the junction of `e` and `e'` carries a fan
(`∃ m, Fan (e.r + e'.l + m)`), which is what `APrimeSeat1.Valid` records.  `Ch l` : consecutive edges are compatible.

* `pig` (Beeson-Rosu Lemma 34, first half): a nonempty list with `Ch` whose first edge does not start with `γ` and whose last edge
  does not end with `γ` has a nonempty block of `c`-edges `run` with `l = pre ++ run ++ post`, `pre` empty or ending with an edge
  ending in `γ`, `post` empty or starting with an edge starting with `γ`: a `c`-run stopped at both ends (a stop at an end of the
  list = a vertex of the target).
* `run_shape` : a `c`-block with `Ch` is `cm^j cp^i` (no `β|β`).
-/

namespace Erdos634.Draft.ThmD

open Erdos634.Draft.APrimeSeat1

def Compat (e e' : OE) : Prop := ∃ m : Cnt, Fan (Cnt.add (Cnt.add e.r.cnt e'.l.cnt) m)

def Ch : List OE → Prop
  | [] => True
  | [_] => True
  | e :: e' :: t => Compat e e' ∧ Ch (e' :: t)

theorem compat_not_gg {e e' : OE} (h : Compat e e') : ¬ (e.r = .ga ∧ e'.l = .ga) := by
  rintro ⟨h1, h2⟩
  obtain ⟨⟨m1, m2, m3⟩, hf⟩ := h
  rw [h1, h2] at hf
  simp [Fan, Cnt.add, Ang.cnt] at hf
  omega

theorem compat_not_bb {e e' : OE} (h : Compat e e') : ¬ (e.r = .be ∧ e'.l = .be) := by
  rintro ⟨h1, h2⟩
  obtain ⟨⟨m1, m2, m3⟩, hf⟩ := h
  rw [h1, h2] at hf
  simp [Fan, Cnt.add, Ang.cnt] at hf
  omega

theorem isC_ends (e : OE) : isC e = true ↔ (e.l ≠ .ga ∧ e.r ≠ .ga) := by
  cases e <;> simp [isC, OE.l, OE.r]

theorem nonW_cases (e : OE) (h : e.l ≠ .ga) : isC e = true ∨ e.r = .ga := by
  cases e <;> simp_all [isC, OE.l, OE.r]

theorem pig (l : List OE) (hne : l ≠ []) (hch : Ch l)
    (hh : ∀ e t, l = e :: t → e.l ≠ .ga) (hl : ∀ q e, l = q ++ [e] → e.r ≠ .ga) :
    ∃ pre run post : List OE, l = pre ++ run ++ post ∧ run ≠ [] ∧ (∀ e ∈ run, isC e = true) ∧
      (pre = [] ∨ ∃ q e, pre = q ++ [e] ∧ e.r = .ga) ∧ (post = [] ∨ ∃ e q, post = e :: q ∧ e.l = .ga) := by
  induction l with
  | nil => exact absurd rfl hne
  | cons e t ih =>
    have hel : e.l ≠ .ga := hh e t rfl
    cases t with
    | nil =>
      have her : e.r ≠ .ga := hl [] e rfl
      have hc : isC e = true := (isC_ends e).2 ⟨hel, her⟩
      exact ⟨[], [e], [], by simp, by simp, by simpa using hc, Or.inl rfl, Or.inl rfl⟩
    | cons e' t' =>
      have hcomp : Compat e e' := hch.1
      have hch' : Ch (e' :: t') := hch.2
      have hl' : ∀ q x, (e' :: t') = q ++ [x] → x.r ≠ .ga := by
        intro q x hx
        exact hl (e :: q) x (by rw [hx]; rfl)
      by_cases hCe : isC e = true
      · by_cases hw : e'.l = .ga
        · exact ⟨[], [e], e' :: t', by simp, by simp, by simpa using hCe, Or.inl rfl,
            Or.inr ⟨e', t', rfl, hw⟩⟩
        · have hh' : ∀ x y, (e' :: t') = x :: y → x.l ≠ .ga := by
            intro x y hxy
            have : x = e' := by injection hxy with h1; exact h1.symm
            subst this; exact hw
          obtain ⟨pre, run, post, hl2, hr, hrc, hpre, hpost⟩ := ih (List.cons_ne_nil _ _) hch' hh' hl'
          rcases hpre with hp | ⟨q, x, hq, hx⟩
          · subst hp
            refine ⟨[], e :: run, post, ?_, by simp, ?_, Or.inl rfl, hpost⟩
            · simp at hl2 ⊢; exact hl2
            · intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact hCe
              · exact hrc y hy
          · refine ⟨e :: pre, run, post, ?_, hr, hrc, Or.inr ⟨e :: q, x, by rw [hq]; rfl, hx⟩, hpost⟩
            simp at hl2 ⊢; exact hl2
      · have her : e.r = .ga := (nonW_cases e hel).resolve_left hCe
        have hw : e'.l ≠ .ga := fun h => compat_not_gg hcomp ⟨her, h⟩
        have hh' : ∀ x y, (e' :: t') = x :: y → x.l ≠ .ga := by
          intro x y hxy
          have : x = e' := by injection hxy with h1; exact h1.symm
          subst this; exact hw
        obtain ⟨pre, run, post, hl2, hr, hrc, hpre, hpost⟩ := ih (List.cons_ne_nil _ _) hch' hh' hl'
        rcases hpre with hp | ⟨q, x, hq, hx⟩
        · subst hp
          refine ⟨[e], run, post, ?_, hr, hrc, Or.inr ⟨[], e, rfl, her⟩, hpost⟩
          simp at hl2 ⊢; exact hl2
        · refine ⟨e :: pre, run, post, ?_, hr, hrc, Or.inr ⟨e :: q, x, by rw [hq]; rfl, hx⟩, hpost⟩
          simp at hl2 ⊢; exact hl2

/-- a block of `c`-edges with compatible neighbours is `cm^j cp^i` -/
theorem run_shape (run : List OE) (hc : ∀ e ∈ run, isC e = true) (hch : Ch run) :
    ∃ j i : ℕ, run = List.replicate j OE.cm ++ List.replicate i OE.cp := by
  induction run with
  | nil => exact ⟨0, 0, rfl⟩
  | cons e t ih =>
    have hce : isC e = true := hc e (List.mem_cons_self)
    have hct : ∀ x ∈ t, isC x = true := fun x hx => hc x (List.mem_cons_of_mem _ hx)
    cases t with
    | nil =>
      cases e <;> simp [isC] at hce
      · exact ⟨0, 1, rfl⟩
      · exact ⟨1, 0, rfl⟩
    | cons e' t' =>
      have hcomp : Compat e e' := hch.1
      obtain ⟨j, i, hji⟩ := ih hct hch.2
      have hce' : isC e' = true := hct e' (List.mem_cons_self)
      cases e with
      | cm =>
        exact ⟨j + 1, i, by rw [hji]; simp [List.replicate_succ]⟩
      | cp =>
        -- the next edge cannot be a cm (β|β): so j = 0
        cases j with
        | zero => exact ⟨0, i + 1, by simp at hji; rw [hji]; simp [List.replicate_succ]⟩
        | succ j =>
          exfalso
          simp [List.replicate_succ] at hji
          obtain ⟨h1, -⟩ := hji
          subst h1
          exact compat_not_bb hcomp ⟨rfl, rfl⟩
      | ap => simp [isC] at hce
      | am => simp [isC] at hce
      | bp => simp [isC] at hce
      | bm => simp [isC] at hce

end Erdos634.Draft.ThmD
