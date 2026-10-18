import Mathlib.Tactic
import Erdos634.Draft.ThmDGeoRunCorner

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha is ours.

# Theorem D' (ThmDGeo, item (1')): the stop of a corner c-run, `hstop` and `hVnv`  

For the base leg in a `SetupT` frame: if the first `n ≥ 1` edges are `c>` and the next edge has left angle `γ` (`am`, `bm`), then at
`V = lp n 0` (`ε = 1`, `x = 0`) the next tile has `γ` at `V` and a second vertex on the base line (`hstop`, second disjunct), and
`V` is not a vertex of the target (`hVnv`).  `stop_end` is the mirror (`ε = -1`, `x = L`): the last `n ≥ 1` edges are `c<` and the edge
before them has right angle `γ`.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.Draft.APrimeLegBuild
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem wlen_pos (S : SetupT D u v α β γ L ax ay) (o : OE) : 0 < Erdos634.Draft.ThmD.wlen D.model o := by
  have hu := S.u0
  have hb := S.b_pos
  have hc := S.c_pos
  have ha : (0 : ℝ) < (u : ℝ) ^ 2 := by positivity
  cases o
  · rw [Erdos634.Draft.ThmD.wlen_a _ _ rfl, S.hM.hs0]; exact ha
  · rw [Erdos634.Draft.ThmD.wlen_a _ _ rfl, S.hM.hs0]; exact ha
  · rw [Erdos634.Draft.ThmD.wlen_b _ _ rfl, S.hM.hs1]; exact hb
  · rw [Erdos634.Draft.ThmD.wlen_b _ _ rfl, S.hM.hs1]; exact hb
  · rw [Erdos634.Draft.ThmD.wlen_c _ _ rfl, S.hM.hs2]; exact hc
  · rw [Erdos634.Draft.ThmD.wlen_c _ _ rfl, S.hM.hs2]; exact hc

theorem target_pts01 (S : SetupT D u v α β γ L ax ay) :
    D.target.pts 0 = mkPt 0 0 ∧ D.target.pts 1 = mkPt L 0 ∧ D.target.pts 2 = mkPt ax ay := by
  rw [S.tgt]; exact ⟨Tg_pts0 _ _, Tg_pts1 _ _, Tg_pts2 _ _⟩

theorem base_vertex_not (S : SetupT D u v α β γ L ax ay) {x : ℝ} (hx0 : 0 < x) (hxL : x < L) :
    mkPt x 0 ∉ Set.range D.target.pts := by
  rintro ⟨i, hi⟩
  obtain ⟨h0, h1, h2⟩ := target_pts01 S
  have hay := S.hay
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at hi
    rw [h0] at hi
    have := congrArg (fun p : Plane => p 0) hi
    simp only [mkPt_zero] at this; linarith
  · simp only [Fin.mk_one, Fin.isValue] at hi
    rw [h1] at hi
    have := congrArg (fun p : Plane => p 0) hi
    simp only [mkPt_zero] at this; linarith
  · simp only [Fin.reduceFinMk, Fin.isValue] at hi
    rw [h2] at hi
    have := congrArg (fun p : Plane => p 1) hi
    simp only [mkPt_one] at this; linarith

theorem stop_start (S : SetupT D u v α β γ L ax ay) {n : ℕ} (hn1 : 1 ≤ n) {r : List (LegStep N)}
    {t : Fin N} {e : OE}
    (hRL : RealLeg D.toDissection α t e r)
    (hLP : LegPos D.toDissection D.model (mkPt 0 0) (mkPt L 0) t e 0 r)
    (hLE : LegEnd D.toDissection α (mkPt L 0) t e r)
    (hang : (D.tile t).localAngle (mkPt 0 0) = angVal α e.l)
    (hcp : ∀ j < n, (legEdges e r)[j]? = some OE.cp)
    (hnext : ∃ o, (legEdges e r)[n]? = some o ∧ o.l = Ang.ga) :
    (∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0) = γ) ∧
      lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0 ∉ Set.range D.target.pts := by
  have hL := S.hL
  have hLne : L ≠ 0 := hL.ne'
  have hd : dist (mkPt 0 0) (mkPt L 0) = L := by
    have := Erdos634.MarchInduction.dist_mkPt_base 0 L hL.le
    simpa using this
  obtain ⟨o, ho, hol⟩ := hnext
  have hlt : n < (legEdges e r).length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at ho
    exact absurd ho (by simp)
  obtain ⟨f, hf0, hfl, hfi⟩ := legseq D.toDissection D.model α (mkPt 0 0) (mkPt L 0) r t e 0 hRL hLP hLE
    (by rw [AffineMap.lineMap_apply_zero]; exact hang)
  have hfn : ∀ i, i ≤ n → f i = (i : ℝ) * ((u : ℝ) * v / L) := by
    intro i
    induction i with
    | zero => intro _; simpa using hf0
    | succ i ih =>
      intro hi
      obtain ⟨t', j', k', -, -, -, -, -, hw⟩ := hfi i (by omega)
      have hget : (legEdges e r)[i] = OE.cp := by
        have := hcp i (by omega)
        rw [List.getElem?_eq_getElem (by omega)] at this
        exact Option.some.inj this
      rw [hget, hd, wlen_cp_eq S OE.cp rfl] at hw
      have := ih (by omega)
      push_cast
      field_simp at this ⊢
      nlinarith
  obtain ⟨t', j, k, hjk, hj, hk, hjang, hkang, hw⟩ := hfi n hlt
  have hgetn : (legEdges e r)[n] = o := by
    rw [List.getElem?_eq_getElem hlt] at ho
    exact Option.some.inj ho
  rw [hgetn, hd] at hw
  rw [hgetn] at hjang
  have hwpos := wlen_pos S o
  rw [← hw] at hwpos
  have hfpos : f n < f (n + 1) := by
    by_contra h
    push Not at h
    nlinarith
  have hjy : (D.tile t').pts j 1 = 0 := by rw [hj, lineMap_base]; simp
  have hky : (D.tile t').pts k 1 = 0 := by rw [hk, lineMap_base]; simp
  have hV : lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0 = (D.tile t').pts j := by
    rw [hj, lineMap_base, lpT_w0, hfn n le_rfl]
    congr 1; field_simp
  refine ⟨⟨t', j, k, hjk, hV.symm, hky, ?_, ?_⟩, ?_⟩
  · rw [hV]; exact (D.tile t').indep.injective.ne hjk.symm
  · rw [hV, hjang, hol, S.hγ]; simp [angVal]
  · rw [lpT_w0]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hc := S.c_pos
    -- x(V) = f n * L and x(k) = f (n+1) * L ≤ L
    have hkx : (D.tile t').pts k = mkPt (f (n + 1) * L) 0 := by rw [hk, lineMap_base]
    have hbr := S.base_range (x := f (n + 1) * L) (by rw [← hkx]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t' k)
    have hfn' := hfn n le_rfl
    refine base_vertex_not S (by positivity) ?_
    have : (n : ℝ) * (u * v) = f n * L := by rw [hfn']; field_simp
    rw [this]
    nlinarith [hbr.2, mul_pos (sub_pos.2 hfpos) hL]



theorem stop_end (S : SetupT D u v α β γ L ax ay) {n : ℕ} (hn1 : 1 ≤ n) {r : List (LegStep N)}
    {t : Fin N} {e : OE}
    (hRL : RealLeg D.toDissection α t e r)
    (hLP : LegPos D.toDissection D.model (mkPt 0 0) (mkPt L 0) t e 0 r)
    (hLE : LegEnd D.toDissection α (mkPt L 0) t e r)
    (hang : (D.tile t).localAngle (mkPt 0 0) = angVal α e.l)
    (hn : n + 1 ≤ (legEdges e r).length)
    (hcm : ∀ j < n, (legEdges e r)[(legEdges e r).length - 1 - j]? = some OE.cm)
    (hprev : ∃ o, (legEdges e r)[(legEdges e r).length - 1 - n]? = some o ∧ o.r = Ang.ga) :
    (∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0) = γ) ∧
      lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0 ∉ Set.range D.target.pts := by
  have hL := S.hL
  have hLne : L ≠ 0 := hL.ne'
  have hd : dist (mkPt 0 0) (mkPt L 0) = L := by
    have := Erdos634.MarchInduction.dist_mkPt_base 0 L hL.le
    simpa using this
  obtain ⟨o, ho, hor⟩ := hprev
  obtain ⟨f, hf0, hfl, hfi⟩ := legseq D.toDissection D.model α (mkPt 0 0) (mkPt L 0) r t e 0 hRL hLP hLE
    (by rw [AffineMap.lineMap_apply_zero]; exact hang)
  set len := (legEdges e r).length with hlen
  have hpos : ∀ j, j ≤ n → f (len - j) = 1 - (j : ℝ) * ((u : ℝ) * v / L) := by
    intro j
    induction j with
    | zero => intro _; simpa using hfl
    | succ j ihj =>
      intro hj
      have hjn : j < n := by omega
      have hlt : len - 1 - j < len := by omega
      obtain ⟨t', j', k', -, -, -, -, -, hw⟩ := hfi (len - 1 - j) hlt
      have hget : (legEdges e r)[len - 1 - j] = OE.cm := by
        have := hcm j hjn
        rw [List.getElem?_eq_getElem hlt] at this
        exact Option.some.inj this
      rw [hget, hd, wlen_cp_eq S OE.cm rfl] at hw
      have e1 : len - 1 - j + 1 = len - j := by omega
      have e2 : len - (j + 1) = len - 1 - j := by omega
      rw [e1] at hw
      rw [e2]
      have := ihj (by omega)
      push_cast
      field_simp at this ⊢
      nlinarith
  have hlt : len - 1 - n < len := by omega
  obtain ⟨t', j, k, hjk, hj, hk, hjang, hkang, hw⟩ := hfi (len - 1 - n) hlt
  have hgetn : (legEdges e r)[len - 1 - n] = o := by
    rw [List.getElem?_eq_getElem hlt] at ho
    exact Option.some.inj ho
  rw [hgetn, hd] at hw
  rw [hgetn] at hjang hkang
  have e1 : len - 1 - n + 1 = len - n := by omega
  rw [e1] at hk hw
  have hwpos := wlen_pos S o
  rw [← hw] at hwpos
  have hfpos : f (len - 1 - n) < f (len - n) := by
    by_contra h
    push Not at h
    nlinarith
  have hpn := hpos n le_rfl
  have hjy : (D.tile t').pts j 1 = 0 := by rw [hj, lineMap_base]; simp
  have hV : lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0 = (D.tile t').pts k := by
    rw [hk, lineMap_base, lpT_w0_m, hpn]
    congr 1; field_simp
  have hjx : (D.tile t').pts j = mkPt (f (len - 1 - n) * L) 0 := by rw [hj, lineMap_base]
  have hbr := S.base_range (x := f (len - 1 - n) * L)
    (by rw [← hjx]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection t' j)
  refine ⟨⟨t', k, j, hjk.symm, hV.symm, hjy, ?_, ?_⟩, ?_⟩
  · intro h
    exact (D.tile t').indep.injective.ne hjk (h.trans hV)
  · rw [hV, hkang, hor, S.hγ]; simp [angVal]
  · rw [lpT_w0_m]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hc := S.c_pos
    have hxV : L - (n : ℝ) * (u * v) = f (len - n) * L := by rw [hpn]; field_simp
    refine base_vertex_not S ?_ (by nlinarith [mul_pos hnpos hc])
    rw [hxV]
    nlinarith [hbr.1, mul_pos (sub_pos.2 hfpos) hL]

#print axioms stop_start
#print axioms stop_end
end Erdos634.Draft.ThmDRun
