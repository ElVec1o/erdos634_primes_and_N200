import Mathlib.Tactic
import Erdos634.Draft.ThmDRowVertex

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D': the R-mirror row step, formalized  

`thmD_lean.md`, "fifth agent": along the diagonal `PQ` made of the `w` `a`-edges `e_i = [x(i+1,w-1-i), x(i,w-i)]` of the
near tiles `U(i,w-1-i)`, the tile `T_i` across `e_i` is the point-reflected tile `D_i` (not the mirror `N_i`).

* `far_type` — a tile across an `a`-edge has end angles `(γ,β)` (type `D`) or `(β,γ)` (type `N`) (`m_edge_casesT`, `D_anglesT`, `N_anglesT`);
* `far_ne_consec`, `near_ne_far` — the distinctness of tiles needed by the fans;
* `row_orient` — from the fans at the interior diagonal vertices (`vertexfan_T`, one-sided) and at the frontier end
  (`pinfan_ang`), every `T_i` is `D_i`.  This replaces `N_push` (which fails: `mu < 1` at `(3,5)`).
-/

open scoped Classical
open Metric
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.TilePlacement Erdos634.Draft.SideRun Set
  Erdos634.Draft.ThmDHalf Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N}

theorem hasV_congr {t : Fin N} {A B C A' B' C' : Plane} (h : HasV D t A B C) (hA : A = A') (hB : B = B')
    (hC : C = C') : HasV D t A' B' C' := by subst hA hB hC; exact h

section row

variable {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **The type of the tile across an `a`-edge.** -/
theorem far_type (C : CtxBaseT D u v α β γ L ax ay ε x) {t : Fin N} {k m : Fin 3} (hkm : k ≠ m) {ξ η : ℝ}
    (hk : (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
    (hm : (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
    (hle : ∀ i, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts i) ≤ -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1)) :
    ∃ b : Bool,
      (D.tile t).localAngle (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) = angVal α (lowA b) ∧
      (D.tile t).localAngle (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)) = angVal α (upA b) := by
  have S := C.S
  have hε := C.e2
  have hT := S.tile
  rcases m_edge_casesT S hε hkm hk hm hle with hD | hN
  · obtain ⟨h1, h2, -⟩ := D_anglesT S.u0 S.uv' S.v2 hε hT.hab hT.ac hT.bc S.hM hD
    refine ⟨true, ?_, ?_⟩
    · rw [h1, S.hγ]; simp [lowA, angVal]
    · rw [h2, S.hβ]; simp [upA, angVal]
  · obtain ⟨h1, h2⟩ := N_anglesT S.u0 S.uv' S.v2 hε hT.hab hT.ac hT.bc S.hM hN
    refine ⟨false, ?_, ?_⟩
    · rw [h1, S.hβ]; simp [lowA, angVal]
    · rw [h2, S.hγ]; simp [upA, angVal]

/-- **The type `D` carries its third vertex.** (Used to export the conclusion.) -/
theorem far_type_D (C : CtxBaseT D u v α β γ L ax ay ε x) {t : Fin N} {k m : Fin 3} (hkm : k ≠ m) {ξ η : ℝ}
    (hk : (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
    (hm : (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
    (hle : ∀ i, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts i) ≤ -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1))
    (hang : (D.tile t).localAngle (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) = angVal α Ang.ga) :
    HasV D t (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
      (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η + 1)) := by
  have S := C.S
  have hε := C.e2
  have hT := S.tile
  rcases m_edge_casesT S hε hkm hk hm hle with hD | hN
  · exact hD
  · exfalso
    obtain ⟨h1, -⟩ := N_anglesT S.u0 S.uv' S.v2 hε hT.hab hT.ac hT.bc S.hM hN
    rw [h1] at hang
    -- β = γ is impossible : π - 3α = 2α would make α/π rational
    have h5 : (5 : ℝ) * α = Real.pi := by
      have : β = 2 * α := by rw [hang]; simp [angVal, S.hβ]
      rw [S.hβ] at this; linarith
    apply S.hirr
    refine ⟨(1 : ℚ) / 5, ?_⟩
    have : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp
    linarith

/-- Distinct far tiles at consecutive `a`-edges. -/
theorem far_ne_consec (C : CtxBaseT D u v α β γ L ax ay ε x) {ξ η : ℝ} {t t' : Fin N} {k m k' m' : Fin 3}
    (hkm : k ≠ m) (hk : (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
    (hm : (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
    (hkm' : k' ≠ m') (hk' : (D.tile t').pts k' = lpT (u : ℝ) (v : ℝ) ε x (ξ + 2) (η - 1))
    (hm' : (D.tile t').pts m' = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) : t ≠ t' := by
  rintro rfl
  have S := C.S
  have hε := C.e2
  have hmk : m' = k := (D.tile t).indep.injective (hm'.trans hk.symm)
  subst hmk
  have hk'k : k' ≠ m' := hkm'
  have hmk' : m ≠ k' := by
    intro h
    rw [h] at hm
    have := lpT_eta_eq S.u0 S.uv' S.v2 (hk'.symm.trans hm)
    linarith
  refine two_vertices_on_line (D.tile t) (GST (u : ℝ) (v : ℝ) ε)
    (-lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1)) (GST_ne S.u0 S.uv' S.v2 hε) (fun i => ?_)
  rcases fin3_cover m' m k' hkm hk'k.symm hmk' i with h | h | h
  · rw [h, hk, GST_lp hε]; congr 2; ring
  · rw [h, hm, GST_lp hε]; congr 2; ring
  · rw [h, hk', GST_lp hε]; congr 2; ring

/-- The near tile and the far tile at the same `a`-edge are different tiles. -/
theorem near_ne_far (C : CtxBaseT D u v α β γ L ax ay ε x) {ξ η : ℝ} {n t : Fin N}
    (hn : HasV D n (lpT (u : ℝ) (v : ℝ) ε x ξ η) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)))
    (hle : ∀ i, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts i) ≤ -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1)) : n ≠ t := by
  rintro rfl
  have S := C.S
  have hε := C.e2
  obtain ⟨k, m, j, -, -, -, hk, -, -⟩ := hn
  have h1 := hle k
  rw [hk, GST_lp hε] at h1
  have := lvT_lt (u := (u : ℝ)) (v := (v : ℝ)) (ε := ε) (x := x) (s := ξ + η) (s' := ξ + η + 1)
    S.u0 S.uv' S.v2 (by linarith)
  linarith

/-- the row coordinate -/
def ηw (w i : ℕ) : ℝ := (w : ℝ) - 1 - i

/-- **Row orientation (R-mirror row step, no `N_push`).**
`w` near tiles `U(i, ηw w i)` (the towers of `H(w)`), `w` far tiles across their `a`-edges (all on the far side of the
diagonal `GST = -lv w`), the interior diagonal vertices interior to the target, and the end `P = lp 0 w` a frontier non-vertex
of the target.  Then every far tile is the point-reflected tile `D_i`. -/
theorem row_orient_gen (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ)
    (hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)))
    (hfar : ∀ i : ℕ, i < w → ∃ (t : Fin N) (k m : Fin 3), k ≠ m ∧
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∧
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1) ∧
      ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ))
    (hint : ∀ i : ℕ, i + 1 < w → lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∈ interior D.target.carrier)
    (hPfan : 0 < w → ∀ (tW tE : Fin N), tW ≠ tE →
      (∃ k, (D.tile tW).pts k = lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1)) →
      (∃ k, (D.tile tE).pts k = lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1)) → ∀ a a' : Ang,
      (D.tile tW).localAngle (lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1)) = angVal α a →
      (D.tile tE).localAngle (lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1)) = angVal α a' →
      ∃ m : Cnt, Fan (Cnt.add (Cnt.add a.cnt a'.cnt) m)) :
    ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)) (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i + 1)) := by
  have S := C.S
  have hε := C.e2
  have hlevel : ∀ i : ℕ, (i : ℝ) + ηw w i + 1 = (w : ℝ) := by intro i; unfold ηw; ring
  -- total choices
  have hN0 : 0 < N := D.pos
  have hnear' : ∀ i : ℕ, ∃ t : Fin N, i < w → HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)) := by
    intro i
    by_cases h : i < w
    · obtain ⟨t, ht⟩ := hnear i h; exact ⟨t, fun _ => ht⟩
    · exact ⟨⟨0, hN0⟩, fun h' => absurd h' h⟩
  have hfar' : ∀ i : ℕ, ∃ (t : Fin N) (k m : Fin 3), i < w → k ≠ m ∧
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∧
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1) ∧
      ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) := by
    intro i
    by_cases h : i < w
    · obtain ⟨t, k, m, hx⟩ := hfar i h; exact ⟨t, k, m, fun _ => hx⟩
    · exact ⟨⟨0, hN0⟩, 0, 0, fun h' => absurd h' h⟩
  choose nF hnF using hnear'
  choose tF kF mF hF using hfar'
  have hle' : ∀ i : ℕ, i < w → ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile (tF i)).pts j)
      ≤ -lvT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + ηw w i + 1) := by
    intro i hi j
    rw [hlevel i]; exact (hF i hi).2.2.2 j
  -- the types
  have htype : ∀ i : ℕ, ∃ b : Bool, i < w →
      (D.tile (tF i)).localAngle (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) = angVal α (lowA b) ∧
      (D.tile (tF i)).localAngle (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)) = angVal α (upA b) := by
    intro i
    by_cases h : i < w
    · obtain ⟨hkm, hk, hm, -⟩ := hF i h
      obtain ⟨b, hb⟩ := far_type C hkm hk hm (hle' i h)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨true, fun h' => absurd h' h⟩
  choose bF hbF using htype
  -- mid fans
  have hmid : ∀ i, i + 1 < w →
      ∃ m : Cnt, Fan (Cnt.add (Cnt.add (lowA (bF i)).cnt (upA (bF (i + 1))).cnt) m) := by
    intro i hi
    have hi' : i < w := by omega
    have e1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have e2 : ηw w (i + 1) = ηw w i - 1 := by unfold ηw; push_cast; ring
    -- near tiles
    have hn1 := hnF i hi'
    have hn2' := hnF (i + 1) hi
    have hn2 : HasV D (nF (i + 1)) (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i - 1))
        (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 2) (ηw w i - 1)) (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) :=
      hasV_congr hn2' (lpT_congr (by push_cast; ring) (by rw [e2]))
        (lpT_congr (by push_cast; ring) (by rw [e2]))
        (lpT_congr (by push_cast; ring) (by rw [e2]; ring))
    have heq : ((i + 1 : ℕ) : ℝ) + ηw w (i + 1) + 1 = (i : ℝ) + ηw w i + 1 := by
      rw [e2]; push_cast; ring
    refine vertexfan_T C (hint i hi) hn1 hn2 (tW := tF i) (tE := tF (i + 1))
      (hle' i hi') (fun j => by have := hle' (i + 1) hi j; rwa [heq] at this) ?_
      (lowA (bF i)) (upA (bF (i + 1))) ((hbF i hi').1) ?_
    · -- distinct far tiles
      obtain ⟨hkm, hk, hm, -⟩ := hF i hi'
      obtain ⟨hkm', hk', hm', -⟩ := hF (i + 1) hi
      refine far_ne_consec C hkm hk hm hkm' ?_ ?_
      · rw [hk']; exact lpT_congr (by push_cast; ring) (by rw [e2])
      · rw [hm']; exact lpT_congr (by push_cast; ring) (by rw [e2]; ring)
    · have := (hbF (i + 1) hi).2
      rw [← this]
      congr 1
      exact lpT_congr (by push_cast; ring) (by rw [e2]; ring)
  -- end fan
  have hP : 0 < w → ∃ m : Cnt, Fan (Cnt.add (Cnt.add Ang.ga.cnt (upA (bF 0)).cnt) m) := by
    intro hw
    have hβpos : 0 < β := by
      have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
      have e : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
      rw [e] at h; exact h
    have h3α : 3 * α < Real.pi := by have := S.hβ; linarith
    have hnear0 := hnF 0 hw
    obtain ⟨hkm, hk, hm, -⟩ := hF 0 hw
    have hU := U_anglesT S.u0 S.uv' S.v2 hε S.tile.hab S.tile.ac S.tile.bc S.hM hnear0
    have hvN : ∃ k, (D.tile (nF 0)).pts k = lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) := by
      obtain ⟨k, m, j, -, -, -, -, -, hj⟩ := hnear0
      exact ⟨j, hj⟩
    have hvF : ∃ k, (D.tile (tF 0)).pts k = lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) := by
      obtain ⟨hkm', hk', hm', -⟩ := hF 0 hw
      exact ⟨mF 0, hm'⟩
    refine hPfan hw (nF 0) (tF 0) ?_ hvN hvF
      Ang.ga (upA (bF 0)) ?_ ((hbF 0 hw).2)
    · refine near_ne_far C hnear0 ?_
      intro j
      have := hle' 0 hw j
      rwa [show ((0 : ℕ) : ℝ) + ηw w 0 + 1 = ((0 : ℕ) : ℝ) + ηw w 0 + 1 from rfl] at this
    · rw [hU.2.2, S.hγ]; simp [angVal]
  have hT := row_orient_comb w bF hmid hP
  intro i hi
  refine ⟨tF i, ?_⟩
  obtain ⟨hkm, hk, hm, -⟩ := hF i hi
  refine far_type_D C hkm hk hm (hle' i hi) ?_
  have := (hbF i hi).1
  rw [hT i hi] at this
  rw [this]; simp [lowA]

/-- the corner version: `P` a frontier non-vertex of the target -/
theorem row_orient (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ)
    (hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)))
    (hfar : ∀ i : ℕ, i < w → ∃ (t : Fin N) (k m : Fin 3), k ≠ m ∧
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∧
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1) ∧
      ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ))
    (hint : ∀ i : ℕ, i + 1 < w → lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∈ interior D.target.carrier)
    (hP0 : 0 < w → lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) ∈ frontier D.target.carrier ∧
      lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) ∉ Set.range D.target.pts) :
    ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)) (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i + 1)) := by
  have S := C.S
  have hβpos : 0 < β := by
    have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
    have e : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
    rw [e] at h; exact h
  have h3α : 3 * α < Real.pi := by have := S.hβ; linarith
  refine row_orient_gen C w hnear hfar hint (fun hw tW tE hne _ _ a a' hW hE => ?_)
  obtain ⟨hfr, hnv⟩ := hP0 hw
  exact pinfan_ang D S.hirr S.hM.hα' (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α hfr hnv tW tE hne a a' hW hE

end row

#print axioms far_type
#print axioms far_type_D
#print axioms far_ne_consec
#print axioms near_ne_far
#print axioms row_orient_gen
#print axioms row_orient
end Erdos634.Draft.ThmDRun
