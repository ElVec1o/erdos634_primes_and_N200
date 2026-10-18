import Mathlib.Tactic
import Erdos634.Draft.ThmDPig

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (5)): list bookkeeping for the pigeonhole run  

Pure list lemmas: `Ch` of a sub-block, the indices of a run `cm^j cp^i` inside `pre ++ run ++ post`, and the count of `c`-letters.
-/

namespace Erdos634.Draft.ThmD

open Erdos634.Draft.APrimeSeat1

theorem ch_of_valid : ∀ (e : OE) (t : List (Cnt × OE)), Valid e t → Ch (edges e t)
  | e, [], _ => trivial
  | e, (m, e') :: t, ⟨hf, hv⟩ => ⟨⟨m, hf⟩, ch_of_valid e' t hv⟩

theorem ch_cons_tail {e : OE} {l : List OE} (h : Ch (e :: l)) : Ch l := by
  cases l with
  | nil => trivial
  | cons e' t => exact h.2

theorem ch_append_right : ∀ (l1 l2 : List OE), Ch (l1 ++ l2) → Ch l2
  | [], l2, h => by simpa using h
  | e :: t, l2, h => ch_append_right t l2 (ch_cons_tail (by simpa using h))

theorem ch_append_left : ∀ (l1 l2 : List OE), Ch (l1 ++ l2) → Ch l1
  | [], l2, h => trivial
  | [e], l2, h => trivial
  | e :: e' :: t, l2, h => by
    have h' : Compat e e' ∧ Ch (e' :: (t ++ l2)) := by simpa using h
    exact ⟨h'.1, ch_append_left (e' :: t) l2 (by simpa using h'.2)⟩

theorem ch_middle (pre run post : List OE) (h : Ch (pre ++ run ++ post)) : Ch run := by
  have h1 : Ch (pre ++ run) := ch_append_left (pre ++ run) post h
  exact ch_append_right pre run h1

theorem idx_cm (pre post : List OE) (j i : ℕ) {k : ℕ} (hk : k < j) :
    (pre ++ (List.replicate j OE.cm ++ List.replicate i OE.cp) ++ post)[pre.length + k]? = some OE.cm := by
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa using hk)]
  simp [List.getElem?_replicate, hk]

theorem idx_cp (pre post : List OE) (j i : ℕ) {k : ℕ} (hk : k < i) :
    (pre ++ (List.replicate j OE.cm ++ List.replicate i OE.cp) ++ post)[pre.length + j + k]? = some OE.cp := by
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), show pre.length + j + k - pre.length = j + k by omega,
    List.getElem?_append_right (by simp), show j + k - (List.replicate j OE.cm).length = k by simp,
    List.getElem?_append_left (by simpa using hk)]
  simp [hk]

theorem len_decomp (pre post : List OE) (j i : ℕ) :
    (pre ++ (List.replicate j OE.cm ++ List.replicate i OE.cp) ++ post).length = pre.length + (j + i) + post.length := by
  simp; omega

theorem idx_pre (pre post run : List OE) {q : List OE} {o : OE} (hq : pre = q ++ [o]) :
    (pre ++ run ++ post)[pre.length - 1]? = some o := by
  subst hq
  simp

theorem idx_post (pre run : List OE) {o : OE} {q : List OE} :
    (pre ++ run ++ (o :: q))[pre.length + run.length]? = some o := by
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp

theorem cnt_ge (pre run post : List OE) (hrun : ∀ e ∈ run, isC e = true) :
    run.length ≤ cntLetter isC (pre ++ run ++ post) := by
  unfold cntLetter
  rw [List.filter_append, List.filter_append, List.length_append, List.length_append,
    List.filter_eq_self.mpr hrun]
  omega

end Erdos634.Draft.ThmD
