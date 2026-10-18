import Mathlib.Tactic
import Erdos634.Draft.ThmDWallEdge
import Erdos634.Draft.ThmDPGoodWall
import Erdos634.Draft.ThmDL32A2
import Erdos634.Draft.ThmDRunRep

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: Lemma 33, the step "the tiles west of UP partition wb with an a/c edge, impossible, hence P is interior to a west edge" (window u, `first_len_jb`).
# Theorem D' item (4): the ray continues as a wall beyond `P_w`  

`west_edge_at_ray` : on the ray `UP` (`U = lp 0 0`, the `b`-edges of `Δ_{0,j}`, `j < w`, on it, `w < u`), with a tile `T₀` west of the ray having
an `a`- or `c`-edge from `U` along it, the point `P_w = lp 0 w` lies in the relative interior of an edge of a tile west of the ray.
Otherwise the west chain would partition `[U, P_w]` (`run_partition`, the end `U` is clamped by the outside of the target) into edges,
the first of length `a` or `c`, against `RB` (`first_len_jb`).
`westCover_at_ray` : hence `WestCover D FXT P_w`.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- a point strictly between two points of a segment is interior to it -/
theorem openSeg_of_between {a b y1 y2 Q : Plane} (hy1 : y1 ∈ segment ℝ a b) (hy2 : y2 ∈ segment ℝ a b)
    (hne : y1 ≠ y2) (hQ : Q ∈ openSegment ℝ y1 y2) : Q ∈ openSegment ℝ a b := by
  rw [segment_eq_image_lineMap] at hy1 hy2
  obtain ⟨s1, ⟨h10, h11⟩, rfl⟩ := hy1
  obtain ⟨s2, ⟨h20, h21⟩, rfl⟩ := hy2
  rw [openSegment_eq_image_lineMap] at hQ ⊢
  obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := hQ
  have hs : s1 ≠ s2 := fun h => hne (by rw [h])
  refine ⟨(1 - r) * s1 + r * s2, ⟨?_, ?_⟩, ?_⟩
  · rcases lt_or_gt_of_ne hs with h | h <;> nlinarith
  · rcases lt_or_gt_of_ne hs with h | h <;> nlinarith
  · simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    module

theorem west_edge_at_ray (C : CtxBaseT D u v α β γ L ax ay ε x) {w : ℕ} (hw1 : 1 ≤ w) (hwu : w < u)
    (hray : ∀ j : ℕ, j < w → UTT D (u : ℝ) (v : ℝ) ε x 0 (j : ℝ))
    (hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 0) (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) ⊆
      interior D.target.carrier)
    (hT0 : ∃ (e : Fin N) (k m : Fin 3) (t : ℝ), k ≠ m ∧ (D.tile e).pts k = lpT (u : ℝ) (v : ℝ) ε x 0 0 ∧ 0 < t ∧
        (D.tile e).pts m = lpT (u : ℝ) (v : ℝ) ε x 0 t ∧
        (dist ((D.tile e).pts k) ((D.tile e).pts m) = (u : ℝ) ^ 2 ∨
          dist ((D.tile e).pts k) ((D.tile e).pts m) = (u : ℝ) * v) ∧
        (∀ i, FXT (u : ℝ) (v : ℝ) ε ((D.tile e).pts i) ≤ lvT (u : ℝ) (v : ℝ) ε x 0)) :
    ∃ (tE : Fin N) (k m : Fin 3), k ≠ m ∧ FXT (u : ℝ) (v : ℝ) ε ((D.tile tE).pts k) = lvT (u : ℝ) (v : ℝ) ε x 0 ∧
      FXT (u : ℝ) (v : ℝ) ε ((D.tile tE).pts m) = lvT (u : ℝ) (v : ℝ) ε x 0 ∧
      (∀ i, FXT (u : ℝ) (v : ℝ) ε ((D.tile tE).pts i) ≤ lvT (u : ℝ) (v : ℝ) ε x 0) ∧
      lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ∈ openSegment ℝ ((D.tile tE).pts k) ((D.tile tE).pts m) := by
  by_contra hno
  push_neg at hno
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw1
  set g := FXT (u : ℝ) (v : ℝ) ε with hg
  set c : ℝ := lvT (u : ℝ) (v : ℝ) ε x 0 with hc
  set P := lpT (u : ℝ) (v : ℝ) ε x 0 0 with hPdef
  set Q := lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) with hQdef
  have hgne : g ≠ 0 := FXT_ne hu huv hv2 hε
  have hPQ : P ≠ Q := lpT_ne_eta hu huv hv2 (by intro h; linarith)
  have hgl : ∀ η : ℝ, g (lpT (u : ℝ) (v : ℝ) ε x 0 η) = c := fun η => FXT_lp hε 0 η
  have hS : segment ℝ P Q ⊆ {y | g y = c} :=
    Erdos634.RunPartition.CSlot.segment_subset_level _ _ (hgl 0) (hgl w)
  -- the ends
  set P' := lpT (u : ℝ) (v : ℝ) ε x 0 (-1) with hP'def
  set Q' := lpT (u : ℝ) (v : ℝ) ε x 0 ((w : ℝ) + 1) with hQ'def
  have hP'm : P ∈ openSegment ℝ P' Q := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨1 / ((w : ℝ) + 1), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith
    · rw [hP'def, hQdef, lineMap_lpT, hPdef]
      refine lpT_congr (by ring) ?_
      field_simp; ring
  have hQ'm : Q ∈ openSegment ℝ P Q' := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨(w : ℝ) / ((w : ℝ) + 1), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith
    · rw [hQ'def, hPdef, hQdef, lineMap_lpT]
      refine lpT_congr (by ring) ?_
      field_simp; ring
  -- the wall: the `b`-edges of `Δ_{0,j}`
  have hwall : ∀ y ∈ openSegment ℝ P Q, ∀ j, y ∉ interior (D.tile j).carrier := by
    intro y hy j
    have hys : y ∈ segment ℝ P Q := openSegment_subset_segment ℝ P Q hy
    have hQe : Q = lpT (u : ℝ) (v : ℝ) ε x (0 + (w : ℝ) * 0) (0 + (w : ℝ) * 1) := lpT_congr (by ring) (by ring)
    rw [hQe] at hys
    obtain ⟨i, hi, hyi⟩ := seg_split_lpT (u := (u : ℝ)) (v := (v : ℝ)) (ε := ε) (x := x) (ξ := 0) (η := 0)
      (dξ := 0) (dη := 1) (q := w) hw1 hys
    obtain ⟨t, ht⟩ := hray i hi
    obtain ⟨k, m, j', hkm, hkj, hmj, hk, hm, hj⟩ := ht
    have hseg : y ∈ segment ℝ ((D.tile t).pts k) ((D.tile t).pts j') := by
      rw [hk, hj]
      have e1 : lpT (u : ℝ) (v : ℝ) ε x (0 + (i : ℝ) * 0) (0 + (i : ℝ) * 1) = lpT (u : ℝ) (v : ℝ) ε x 0 (i : ℝ) :=
        lpT_congr (by ring) (by ring)
      have e2 : lpT (u : ℝ) (v : ℝ) ε x (0 + ((i : ℝ) + 1) * 0) (0 + ((i : ℝ) + 1) * 1)
          = lpT (u : ℝ) (v : ℝ) ε x 0 ((i : ℝ) + 1) := lpT_congr (by ring) (by ring)
      rw [e1, e2] at hyi
      exact hyi
    exact seg_wall D.toDissection hkj hseg j
  -- clamp at `P`: below the base is outside
  have hout : ∀ y ∈ openSegment ℝ P' P, y ∉ D.target.carrier := by
    intro y hy hmem
    rw [openSegment_eq_image_lineMap] at hy
    obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
    have := (S.mem hmem).1
    rw [hP'def, hPdef, lineMap_lpT, lpT_snd] at this
    have hh := S.hhpos
    nlinarith [mul_pos (show (0 : ℝ) < 1 - τ by linarith) hh]
  have hclP : ∀ e ∈ D.toDissection.lineChain g c,
      ¬ Straddles ((D.tile e.1).edge e.2) P' P Q := fun e _ =>
    not_straddles_of_outside D.toDissection hout e.1 e.2
  -- clamp at `Q`: from the negated conclusion
  have hclQ : ∀ e ∈ D.toDissection.lineChain g c,
      ¬ Straddles ((D.tile e.1).edge e.2) Q' Q P := by
    intro e he hstr
    obtain ⟨⟨y1, hy1E, hy1⟩, ⟨y2, hy2E, hy2⟩⟩ := hstr
    obtain ⟨h1, h2, hle⟩ := Dissection.mem_lineChain.mp he
    have hE : (D.tile e.1).edge e.2 = segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := rfl
    rw [hE] at hy1E hy2E
    rw [hQ'def, hQdef, openSegment_eq_image_lineMap] at hy1
    rw [hQdef, hPdef, openSegment_eq_image_lineMap] at hy2
    obtain ⟨τ1, ⟨a1, b1⟩, hy1e⟩ := hy1
    obtain ⟨τ2, ⟨a2, b2⟩, hy2e⟩ := hy2
    rw [lineMap_lpT] at hy1e hy2e
    set η1 : ℝ := ((w : ℝ) + 1) + τ1 * ((w : ℝ) - ((w : ℝ) + 1)) with hη1
    set η2 : ℝ := (w : ℝ) + τ2 * (0 - (w : ℝ)) with hη2
    have hη1w : (w : ℝ) < η1 := by rw [hη1]; nlinarith
    have hηw2 : η2 < (w : ℝ) := by rw [hη2]; nlinarith
    have hy1' : y1 = lpT (u : ℝ) (v : ℝ) ε x 0 η1 := by rw [← hy1e]; exact lpT_congr (by ring) rfl
    have hy2' : y2 = lpT (u : ℝ) (v : ℝ) ε x 0 η2 := by rw [← hy2e]; exact lpT_congr (by ring) rfl
    refine hno e.1 e.2 (e.2 + 1) (fin3_succ_ne e.2).2.1.symm h1 h2 hle ?_
    refine openSeg_of_between (a := (D.tile e.1).pts e.2) (b := (D.tile e.1).pts (e.2 + 1)) hy1E hy2E ?_ ?_
    · intro hEq
      rw [hy1', hy2'] at hEq
      have := lpT_eta_eq hu huv hv2 hEq
      linarith
    · rw [hy1', hy2', openSegment_eq_image_lineMap]
      refine ⟨(η1 - (w : ℝ)) / (η1 - η2), ⟨div_pos (by linarith) (by linarith), ?_⟩, ?_⟩
      · rw [div_lt_one (by linarith)]; linarith
      · rw [lineMap_lpT, hQdef]
        refine lpT_congr (by ring) ?_
        have hne : η1 - η2 ≠ 0 := (by linarith : 0 < η1 - η2).ne'
        field_simp; ring
  have hrun := run_partition D.toDissection g hgne c hPQ (hgl (-1)) (hgl ((w : ℝ) + 1)) hP'm hQ'm hS hint hwall
    hclP hclQ
  -- the first edge, from `T₀`
  obtain ⟨e0t, k0, m0, t0, hk0m0, hk0, ht0, hm0, hd0, hle0⟩ := hT0
  have hν : t0 ≤ w := by
    by_contra hlt
    push_neg at hlt
    refine hno e0t k0 m0 hk0m0 (by rw [hk0]; exact hgl 0) (by rw [hm0]; exact hgl t0) hle0 ?_
    rw [hk0, hm0, openSegment_eq_image_lineMap]
    refine ⟨(w : ℝ) / t0, ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one ht0]; exact hlt
    · rw [lineMap_lpT, hQdef]
      refine lpT_congr (by ring) ?_
      field_simp; ring
  have hg0 : g ((D.tile e0t).pts k0) = c := by rw [hk0]; exact hgl 0
  have hg1 : g ((D.tile e0t).pts m0) = c := by rw [hm0]; exact hgl t0
  obtain ⟨e0, he0, hedge0, hdist0⟩ : ∃ e0 ∈ D.toDissection.lineChain g c,
      (D.tile e0.1).edge e0.2 = segment ℝ P (lpT (u : ℝ) (v : ℝ) ε x 0 t0) ∧
      dist ((D.tile e0.1).pts e0.2) ((D.tile e0.1).pts (e0.2 + 1)) =
        dist ((D.tile e0t).pts k0) ((D.tile e0t).pts m0) := by
    rcases pair_index k0 m0 hk0m0 with h | h
    · refine ⟨(e0t, k0), Dissection.mem_lineChain.mpr ⟨?_, ?_, hle0⟩, ?_, ?_⟩
      · exact hg0
      · show g ((D.tile e0t).pts (k0 + 1)) = c
        rw [← h]; exact hg1
      · show segment ℝ ((D.tile e0t).pts k0) ((D.tile e0t).pts (k0 + 1)) = _
        rw [← h, hk0, hm0]
      · show dist ((D.tile e0t).pts k0) ((D.tile e0t).pts (k0 + 1)) = _
        rw [← h]
    · refine ⟨(e0t, m0), Dissection.mem_lineChain.mpr ⟨?_, ?_, hle0⟩, ?_, ?_⟩
      · exact hg1
      · show g ((D.tile e0t).pts (m0 + 1)) = c
        rw [← h]; exact hg0
      · show segment ℝ ((D.tile e0t).pts m0) ((D.tile e0t).pts (m0 + 1)) = _
        rw [← h, hk0, hm0, segment_symm]
      · show dist ((D.tile e0t).pts m0) ((D.tile e0t).pts (m0 + 1)) = _
        rw [← h, dist_comm]
  have hsub0 : (D.tile e0.1).edge e0.2 ⊆ segment ℝ P Q := by
    rw [hedge0]
    refine (convex_segment P Q).segment_subset (left_mem_segment ℝ P Q) ?_
    rw [segment_eq_image_lineMap]
    refine ⟨t0 / (w : ℝ), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_le_one (by linarith)]; exact hν
    · rw [lineMap_lpT]
      refine lpT_congr (by ring) ?_
      field_simp; ring
  obtain ⟨x', y', z', hxyz⟩ := Erdos634.Draft.W2E1.sum_split_semigroup _
    (fun e : Fin N × Fin 3 => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    ((u : ℝ) ^ 2) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((u : ℝ) * v)
    (dist P Q) (fun e _ => edge_length_casesT D S.hM e.1 e.2)
    (Finset.mem_filter.mpr ⟨he0, hsub0⟩) hrun
  have hdPQ : dist P Q = (w : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) := by
    rw [hPdef, hQdef]
    exact dist_lpT hu huv hv2 hε (by have := S.b_pos; positivity) (by unfold QfT; ring)
  rw [hdist0, hdPQ] at hxyz
  have hℓ : dist ((D.tile e0t).pts k0) ((D.tile e0t).pts m0) = (u : ℝ) ^ 2 ∨
      dist ((D.tile e0t).pts k0) ((D.tile e0t).pts m0) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 ∨
      dist ((D.tile e0t).pts k0) ((D.tile e0t).pts m0) = (u : ℝ) * v := by
    rcases hd0 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hb := first_len_jb S.hco S.hu S.huv hwu hℓ hxyz
  rcases hd0 with h | h
  · exact S.tile.hab (h.symm.trans hb)
  · exact S.tile.bc (hb.symm.trans h)

#print axioms west_edge_at_ray
end Erdos634.Draft.ThmDRun
