-- No sorry, no native_decide, no axioms.
-- Generic chunked front end for `G3CCert.Cert.ok`: the per-cluster checks (BSP ok, positivity, containment, congruence,
-- area sum, leaf count) are proved in separate modules (one `ClOK` fact per cluster), and `ok_of_chunks` assembles
-- `cert.ok = true` from them plus the cheap cross-cluster separation check, without re-evaluating the whole tile list
-- in one kernel call.  This keeps the memory use of each module bounded for N in the thousands.
import Erdos634.Draft.G3CCert

namespace Erdos634.Draft.G3NChunk

open Erdos634.Draft.G3CCert

def area (t : LT) : ℤ := cross t.1 t.2.1 t.2.2

/-- the per-cluster facts (target T, model M) -/
structure ClOK (T M : LT) (b : Bsp) (s : ℤ) (n : ℕ) : Prop where
  ok : b.ok = true
  pos : b.leaves.all posT = true
  ins : b.leaves.all (insideT T) = true
  cong : b.leaves.all (congT M) = true
  sum : (b.leaves.map area).sum = s
  len : b.leaves.length = n

theorem facts {T M : LT} : ∀ {cs : List Bsp} {ss : List ℤ} {ns : List ℕ},
    List.Forall₂ (fun (b : Bsp) (sn : ℤ × ℕ) => ClOK T M b sn.1 sn.2) cs (ss.zip ns) → ss.length = ns.length →
    cs.all Bsp.ok = true ∧ ((cs.map Bsp.leaves).flatten).all posT = true ∧
    ((cs.map Bsp.leaves).flatten).all (insideT T) = true ∧ ((cs.map Bsp.leaves).flatten).all (congT M) = true ∧
    (((cs.map Bsp.leaves).flatten).map area).sum = ss.sum ∧ ((cs.map Bsp.leaves).flatten).length = ns.sum := by
  intro cs
  induction cs with
  | nil =>
    intro ss ns h hl
    cases ss with
    | nil => cases ns with
      | nil => simp
      | cons _ _ => simp at hl
    | cons s ss' => cases ns with
      | nil => simp at hl
      | cons n ns' => simp at h
  | cons b cs ih =>
    intro ss ns h hl
    cases ss with
    | nil => cases ns with
      | nil => simp at h
      | cons _ _ => simp at hl
    | cons s ss' => cases ns with
      | nil => simp at hl
      | cons n ns' =>
        simp only [List.zip_cons_cons, List.forall₂_cons] at h
        obtain ⟨hb, hrest⟩ := h
        have hl' : ss'.length = ns'.length := by simpa using hl
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih hrest hl'
        simp only [List.map_cons, List.flatten_cons, List.all_cons, List.all_append, List.map_append,
          List.sum_append, List.length_append, List.sum_cons, Bool.and_eq_true]
        exact ⟨⟨hb.ok, a1⟩, ⟨hb.pos, a2⟩, ⟨hb.ins, a3⟩, ⟨hb.cong, a4⟩, by rw [hb.sum, a5], by rw [hb.len, a6]⟩

theorem ok_of_chunks (c : Cert) (ss : List ℤ) (ns : List ℕ) (hl : ss.length = ns.length)
    (hT : posT c.target = true) (hM : posT c.model = true)
    (hF : List.Forall₂ (fun (b : Bsp) (sn : ℤ × ℕ) => ClOK c.target c.model b sn.1 sn.2) c.clusters (ss.zip ns))
    (hs : ss.sum = cross c.target.1 c.target.2.1 c.target.2.2)
    (hp : pairsOK c.clusters c.seps = some []) : c.ok = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := facts hF hl
  have hs' : ((c.clusters.map Bsp.leaves).flatten.map area).sum = cross c.target.1 c.target.2.1 c.target.2.2 := by
    rw [a5]; exact hs
  simp only [Cert.ok, Cert.leaves, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨hT, hM⟩, a1⟩, hp⟩, a2⟩, a3⟩, a4⟩, ?_⟩
  exact hs'

theorem len_of_chunks (c : Cert) (ss : List ℤ) (ns : List ℕ) (hl : ss.length = ns.length)
    (hF : List.Forall₂ (fun (b : Bsp) (sn : ℤ × ℕ) => ClOK c.target c.model b sn.1 sn.2) c.clusters (ss.zip ns)) :
    c.leaves.length = ns.sum := (facts hF hl).2.2.2.2.2

end Erdos634.Draft.G3NChunk
