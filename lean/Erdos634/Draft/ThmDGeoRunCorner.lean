import Mathlib.Tactic
import Erdos634.Draft.ThmDGeoRun
import Erdos634.Draft.ThmDGeoLegRun
import Erdos634.Draft.ThmDGeoMirror

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha is ours.

# Theorem D' (ThmDGeo, item (1')): `hrun` from a corner c-run of the base leg  

In a `SetupT` frame (`Q = (0,0)`, `B = (L, 0)`), for the positioned leg of the base side `[Q, B]`:
* `hrun_start` (`ε = 1`, `x = 0`): the first `n` edges are `c>` ⟹ `UTT D u v 1 0 i 0` for `i < n`;
* `hrun_end` (`ε = -1`, `x = L`): the last `n` edges are `c<` (`cm`) ⟹ `UTT D u v (-1) L i 0` for `i < n`.
They are the `hrun` hypotheses of `lemmaK2_corner` and `lemmaK2_corner_m`.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.Draft.APrimeLegBuild
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem lineMap_base (L s : ℝ) :
    (AffineMap.lineMap (mkPt 0 0) (mkPt L 0) s : Plane) = mkPt (s * L) 0 := by
  ext i
  fin_cases i <;> simp [AffineMap.lineMap_apply, mkPt]

theorem wlen_cp_eq (S : SetupT D u v α β γ L ax ay) (o : OE) (h : isC o = true) :
    Erdos634.Draft.ThmD.wlen D.model o = (u : ℝ) * v := by
  rw [Erdos634.Draft.ThmD.wlen_c _ _ h]; exact S.hM.hs2

theorem hrun_start (S : SetupT D u v α β γ L ax ay) {n : ℕ} {r : List (LegStep N)} {t : Fin N} {e : OE}
    (hRL : RealLeg D.toDissection α t e r)
    (hLP : LegPos D.toDissection D.model (mkPt 0 0) (mkPt L 0) t e 0 r)
    (hLE : LegEnd D.toDissection α (mkPt L 0) t e r)
    (hang : (D.tile t).localAngle (mkPt 0 0) = angVal α e.l)
    (hcp : ∀ j < n, (legEdges e r)[j]? = some OE.cp) :
    ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) 1 0 (i : ℝ) 0 := by
  have hL := S.hL
  have hd : dist (mkPt 0 0) (mkPt L 0) = L := by
    have := Erdos634.MarchInduction.dist_mkPt_base 0 L hL.le
    simpa using this
  have hdpos : 0 < dist (mkPt 0 0) (mkPt L 0) := by rw [hd]; exact hL
  have hc : Erdos634.Draft.ThmD.wlen D.model OE.cp = (u : ℝ) * v := wlen_cp_eq S OE.cp rfl
  refine hrun_of_tiles S (by norm_num) ?_
  intro i hi
  obtain ⟨t', j, k, hjk, hj, hk, hα, hβ⟩ :=
    legpos_run D.toDissection D.model α (mkPt 0 0) (mkPt L 0) _ hc hdpos i r t e 0 hRL hLP hLE
      (by rw [AffineMap.lineMap_apply_zero]; exact hang) (fun j hj => hcp j (by omega))
  have hLne : L ≠ 0 := hL.ne'
  refine ⟨t', j, k, hjk, ?_, ?_, hα, ?_⟩
  · rw [hj, lineMap_base, lpT_w0]
    congr 1; rw [hd]; field_simp; ring
  · rw [hk, lineMap_base, lpT_w0]
    congr 1; rw [hd]; field_simp; ring
  · rw [hβ, S.hβ]

theorem hrun_end (S : SetupT D u v α β γ L ax ay) {n : ℕ} {r : List (LegStep N)} {t : Fin N} {e : OE}
    (hRL : RealLeg D.toDissection α t e r)
    (hLP : LegPos D.toDissection D.model (mkPt 0 0) (mkPt L 0) t e 0 r)
    (hLE : LegEnd D.toDissection α (mkPt L 0) t e r)
    (hang : (D.tile t).localAngle (mkPt 0 0) = angVal α e.l)
    (hn : n ≤ (legEdges e r).length)
    (hcm : ∀ j < n, (legEdges e r)[(legEdges e r).length - 1 - j]? = some OE.cm) :
    ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) (-1) L (i : ℝ) 0 := by
  have hL := S.hL
  have hd : dist (mkPt 0 0) (mkPt L 0) = L := by
    have := Erdos634.MarchInduction.dist_mkPt_base 0 L hL.le
    simpa using this
  have hLne : L ≠ 0 := hL.ne'
  obtain ⟨f, hf0, hfl, hfi⟩ := legseq D.toDissection D.model α (mkPt 0 0) (mkPt L 0) r t e 0 hRL hLP hLE
    (by rw [AffineMap.lineMap_apply_zero]; exact hang)
  set len := (legEdges e r).length with hlen
  -- the breakpoints from the end
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
  refine hrun_of_tiles S (by norm_num) ?_
  intro i hi
  have hlt : len - 1 - i < len := by omega
  obtain ⟨t', j', k', hjk, hj, hk, hjang, hkang, -⟩ := hfi (len - 1 - i) hlt
  have hget : (legEdges e r)[len - 1 - i] = OE.cm := by
    have := hcm i hi
    rw [List.getElem?_eq_getElem hlt] at this
    exact Option.some.inj this
  rw [hget] at hjang hkang
  have e1 : len - 1 - i + 1 = len - i := by omega
  have p1 := hpos i hi.le
  have p2 := hpos (i + 1) hi
  have e2 : len - (i + 1) = len - 1 - i := by omega
  rw [e2] at p2
  rw [e1] at hk
  refine ⟨t', k', j', hjk.symm, ?_, ?_, ?_, ?_⟩
  · rw [hk, p1, lineMap_base, lpT_w0_m]
    congr 1; field_simp
  · rw [hj, p2, lineMap_base, lpT_w0_m]
    congr 1; push_cast; field_simp
  · rw [hkang]; simp [OE.r, angVal]
  · rw [hjang, S.hβ]; simp [OE.l, angVal]

#print axioms hrun_start
#print axioms hrun_end
end Erdos634.Draft.ThmDRun
