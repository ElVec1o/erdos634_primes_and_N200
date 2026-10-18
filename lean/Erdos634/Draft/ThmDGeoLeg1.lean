import Mathlib.Tactic
import Erdos634.Draft.ThmDGeoStop

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha is ours.

# Theorem D' (ThmDGeo, item (1')): Lemma K (K2) for the positioned base leg  

`leg_K2_start` (corner `Q`, `ε = 1`, `x = 0`) and `leg_K2_end` (corner `B`, `ε = -1`, `x = L`): in a `SetupT` frame with the ray data of
`ThmDGeoCtx`, the positioned leg `[Q, B]` of the base side cannot begin (end) with `n` edges `c>` (`c<`), `1 ≤ n < v`, followed by
an edge with left (right) angle `γ`, or reach the far vertex.  Here `hrun`, `hstop`, `hVnv` of `lemmaK2_corner(_m)` are all DERIVED from
the leg (`hrun_start/end`, `stop_start/end`, and, when the run is the whole leg, from `hnoγ`).  Remaining hypotheses: the context
`CtxBaseT`, the ray data (`d2`, `hax`, `hsq`, `hbig`) and `hnoγ`.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.Draft.APrimeLegBuild
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem leg_K2_start (C : CtxBaseT D u v α β γ L ax ay 1 0) {d2 : ℝ} (hd2 : 0 < d2)
    (hax : 2 * (u : ℝ) * ax = (v : ℝ) * d2) (hsq : ax ^ 2 + ay ^ 2 = d2 ^ 2)
    (hbig : (v : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) < d2) {n : ℕ} (hn1 : 1 ≤ n) (hnv : n < v)
    {r : List (LegStep N)} {t : Fin N} {e : OE}
    (hRL : RealLeg D.toDissection α t e r)
    (hLP : LegPos D.toDissection D.model (mkPt 0 0) (mkPt L 0) t e 0 r)
    (hLE : LegEnd D.toDissection α (mkPt L 0) t e r)
    (hang : (D.tile t).localAngle (mkPt 0 0) = angVal α e.l)
    (hcp : ∀ j < n, (legEdges e r)[j]? = some OE.cp)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : n = (legEdges e r).length ∨ ∃ o, (legEdges e r)[n]? = some o ∧ o.l = Ang.ga) : False := by
  have S := C.S
  have hL := S.hL
  have hLne : L ≠ 0 := hL.ne'
  have hrun := hrun_start S hRL hLP hLE hang hcp
  rcases hstop with hall | hnext
  · -- the run is the whole leg: `V = B`
    subst hall
    have hd : dist (mkPt 0 0) (mkPt L 0) = L := by
      have := Erdos634.MarchInduction.dist_mkPt_base 0 L hL.le
      simpa using this
    obtain ⟨f, hf0, hfl, hfi⟩ := legseq D.toDissection D.model α (mkPt 0 0) (mkPt L 0) r t e 0 hRL hLP hLE
      (by rw [AffineMap.lineMap_apply_zero]; exact hang)
    set len := (legEdges e r).length with hlen
    have hfn : ∀ i, i ≤ len → f i = (i : ℝ) * ((u : ℝ) * v / L) := by
      intro i
      induction i with
      | zero => intro _; simpa using hf0
      | succ i ih =>
        intro hi
        obtain ⟨t', j', k', -, -, -, -, -, hw⟩ := hfi i (by omega)
        have hget : ∀ (h : i < (legEdges e r).length), (legEdges e r)[i]'h = OE.cp := by
          intro h
          have := hcp i (by omega)
          rw [List.getElem?_eq_getElem h] at this
          exact Option.some.inj this
        rw [hget _, hd, wlen_cp_eq S OE.cp rfl] at hw
        have := ih (by omega)
        push_cast
        field_simp at this ⊢
        nlinarith
    have hV : lpT (u : ℝ) (v : ℝ) 1 0 (len : ℝ) 0 = D.target.pts 1 := by
      rw [(target_pts01 S).2.1, lpT_w0]
      have := hfn len le_rfl
      rw [hfl] at this
      congr 1
      field_simp at this ⊢
      linarith
    refine lemmaK2_corner C hd2 hax hsq hbig hn1 hnv hrun ?_ hnoγ (Or.inl ⟨1, hV.symm⟩)
    rintro ⟨t', k, m, -, hk, -, -, hang'⟩
    exact absurd hang' (hnoγ t' k ⟨1, by rw [hk, hV]⟩ |> fun h => by simpa [hk] using h)
  · obtain ⟨hs, hvn⟩ := stop_start S hn1 hRL hLP hLE hang hcp hnext
    exact lemmaK2_corner C hd2 hax hsq hbig hn1 hnv hrun (fun _ => hvn) hnoγ (Or.inr hs)



theorem leg_K2_end (C : CtxBaseT D u v α β γ L ax ay (-1) L) {d2 : ℝ} (hd2 : 0 < d2)
    (hax : 2 * (u : ℝ) * (L - ax) = (v : ℝ) * d2) (hsq : (L - ax) ^ 2 + ay ^ 2 = d2 ^ 2)
    (hbig : (v : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) < d2) {n : ℕ} (hn1 : 1 ≤ n) (hnv : n < v)
    {r : List (LegStep N)} {t : Fin N} {e : OE}
    (hRL : RealLeg D.toDissection α t e r)
    (hLP : LegPos D.toDissection D.model (mkPt 0 0) (mkPt L 0) t e 0 r)
    (hLE : LegEnd D.toDissection α (mkPt L 0) t e r)
    (hang : (D.tile t).localAngle (mkPt 0 0) = angVal α e.l)
    (hn : n ≤ (legEdges e r).length)
    (hcm : ∀ j < n, (legEdges e r)[(legEdges e r).length - 1 - j]? = some OE.cm)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : n < (legEdges e r).length →
      ∃ o, (legEdges e r)[(legEdges e r).length - 1 - n]? = some o ∧ o.r = Ang.ga) : False := by
  have S := C.S
  have hL := S.hL
  have hLne : L ≠ 0 := hL.ne'
  have hrun := hrun_end S hRL hLP hLE hang hn hcm
  rcases eq_or_lt_of_le hn with hall | hlt0
  · have hd : dist (mkPt 0 0) (mkPt L 0) = L := by
      have := Erdos634.MarchInduction.dist_mkPt_base 0 L hL.le
      simpa using this
    obtain ⟨f, hf0, hfl, hfi⟩ := legseq D.toDissection D.model α (mkPt 0 0) (mkPt L 0) r t e 0 hRL hLP hLE
      (by rw [AffineMap.lineMap_apply_zero]; exact hang)
    have hpos : ∀ j, j ≤ n → f ((legEdges e r).length - j) = 1 - (j : ℝ) * ((u : ℝ) * v / L) := by
      intro j
      induction j with
      | zero => intro _; simpa using hfl
      | succ j ihj =>
        intro hj
        have hjn : j < n := by omega
        have hlt : (legEdges e r).length - 1 - j < (legEdges e r).length := by omega
        obtain ⟨t', j', k', -, -, -, -, -, hw⟩ := hfi ((legEdges e r).length - 1 - j) hlt
        have hget : ∀ (h : (legEdges e r).length - 1 - j < (legEdges e r).length),
            (legEdges e r)[(legEdges e r).length - 1 - j]'h = OE.cm := by
          intro h
          have := hcm j hjn
          rw [List.getElem?_eq_getElem h] at this
          exact Option.some.inj this
        rw [hget _, hd, wlen_cp_eq S OE.cm rfl] at hw
        have e1 : (legEdges e r).length - 1 - j + 1 = (legEdges e r).length - j := by omega
        have e2 : (legEdges e r).length - (j + 1) = (legEdges e r).length - 1 - j := by omega
        rw [e1] at hw
        rw [e2]
        have := ihj (by omega)
        push_cast
        field_simp at this ⊢
        nlinarith
    have hV : lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0 = D.target.pts 0 := by
      rw [(target_pts01 S).1, lpT_w0_m]
      have := hpos n le_rfl
      rw [← hall, Nat.sub_self, hf0] at this
      congr 1
      field_simp at this ⊢
      linarith
    refine lemmaK2_corner_m C hd2 hax hsq hbig hn1 hnv hrun ?_ hnoγ (Or.inl ⟨0, hV.symm⟩)
    rintro ⟨t', k, m, -, hk, -, -, hang'⟩
    exact absurd hang' (hnoγ t' k ⟨0, by rw [hk, hV]⟩ |> fun h => by simpa [hk] using h)
  · obtain ⟨hs, hvn⟩ := stop_end S hn1 hRL hLP hLE hang (by omega) hcm (hstop hlt0)
    exact lemmaK2_corner_m C hd2 hax hsq hbig hn1 hnv hrun (fun _ => hvn) hnoγ (Or.inr hs)

#print axioms leg_K2_start
#print axioms leg_K2_end
end Erdos634.Draft.ThmDRun
