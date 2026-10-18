import Mathlib.Tactic
import Erdos634.Draft.ThmDGeoCorner

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha is ours.

# Theorem D' (ThmDGeo, item (1')): the mirror corner  

The `ε = -1` corner sits at `B = (L, 0)` (`x = L`).  `lpT_mirror`: `lpT u v (-1) L 0 w` is the reflection `X ↦ L - X` of `lpT u v 1 0 0 w`.
`lp0w_facts_m` (the mirror of `ThmDGeoCtx.lp0w_facts` with `d2 = |BA|`, `2u(L - ax) = v d2`), `lemmaK2_corner_m` (the mirror of
`lemmaK2_corner`): the hypotheses `hPf, hQf, hint` of `lemmaK2_final` at `ε = -1`, `x = L` are derived.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.MarchSlots Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem lpT_mirror (u v L w : ℝ) :
    lpT u v (-1) L 0 w = mkPt (L - (lpT u v 1 0 0 w) 0) ((lpT u v 1 0 0 w) 1) := by
  unfold lpT
  simp only [mkPt_zero, mkPt_one]
  exact mkPt_congr (by ring) rfl

theorem lpT_w0_m (u v L w : ℝ) : lpT u v (-1) L w 0 = mkPt (L - w * (u * v)) 0 := by
  unfold lpT; exact mkPt_congr (by ring) (by ring)

theorem lp0w_facts_m (S : SetupT D u v α β γ L ax ay) {d2 : ℝ} (hd2 : 0 < d2)
    (hax : 2 * (u : ℝ) * (L - ax) = (v : ℝ) * d2)
    (hsq : (L - ax) ^ 2 + ay ^ 2 = d2 ^ 2) (hbig : (v : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) < d2)
    {w : ℝ} (hw1 : 1 ≤ w) (hwv : w < v) :
    lpT (u : ℝ) (v : ℝ) (-1) L 0 w ∈ D.target.carrier ∧ lpT (u : ℝ) (v : ℝ) (-1) L 0 w ∈ frontier D.target.carrier ∧
      lpT (u : ℝ) (v : ℝ) (-1) L 0 w ∉ Set.range D.target.pts ∧
      gB L ax ay (lpT (u : ℝ) (v : ℝ) (-1) L 0 w) = 0 ∧ 0 < gA ax ay (lpT (u : ℝ) (v : ℝ) (-1) L 0 w) ∧
      0 < (lpT (u : ℝ) (v : ℝ) (-1) L 0 w) 1 := by
  have hu := S.u0
  have hb := S.b_pos
  have hay := S.hay
  have hL := S.hL
  set t : ℝ := w * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) / d2 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hd2]
    nlinarith [S.uv', mul_pos hb (sub_pos.2 hwv)]
  have hray := lp0w_ray hu S.v0 S.v2 hd2 hax hay (by linarith [hsq]) w
  rw [← ht] at hray
  rw [lpT_mirror, hray]
  simp only [mkPt_zero, mkPt_one]
  have hmem : mkPt (L - t * (L - ax)) (t * ay) ∈ D.target.carrier := by
    rw [S.tgt]
    have hconv := Tri.convex (Tg L ax ay S.hL S.hay)
    have hA : mkPt ax ay ∈ (Tg L ax ay S.hL S.hay).carrier :=
      subset_convexHull ℝ _ ⟨2, (Tg_pts2 S.hL S.hay)⟩
    have hB : mkPt L 0 ∈ (Tg L ax ay S.hL S.hay).carrier :=
      subset_convexHull ℝ _ ⟨1, (Tg_pts1 S.hL S.hay)⟩
    have := hconv hA hB ht0.le (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
    convert this using 1
    ext i
    fin_cases i <;> simp [mkPt] <;> ring
  have hgB : gB L ax ay (mkPt (L - t * (L - ax)) (t * ay)) = 0 := by rw [gB_mk]; ring
  have hgA : 0 < gA ax ay (mkPt (L - t * (L - ax)) (t * ay)) := by
    rw [gA_mk]
    have : ay * (L - t * (L - ax)) - ax * (t * ay) = ay * L * (1 - t) := by ring
    rw [this]
    exact mul_pos (mul_pos hay hL) (by linarith)
  have hy : 0 < t * ay := by positivity
  refine ⟨hmem, S.frontier_gB0 hmem hgB, ?_, hgB, hgA, hy⟩
  rintro ⟨k, hk⟩
  rw [S.tgt] at hk
  have h1 := congrArg (fun p : Plane => p 1) hk
  simp only [mkPt_one] at h1
  fin_cases k
  · have e : (Tg L ax ay S.hL S.hay).pts 0 = mkPt 0 0 := Tg_pts0 _ _
    simp only [Fin.zero_eta, Fin.isValue] at h1
    rw [e, mkPt_one] at h1
    linarith
  · have e : (Tg L ax ay S.hL S.hay).pts 1 = mkPt L 0 := Tg_pts1 _ _
    simp only [Fin.mk_one, Fin.isValue] at h1
    rw [e, mkPt_one] at h1
    linarith
  · have e : (Tg L ax ay S.hL S.hay).pts 2 = mkPt ax ay := Tg_pts2 _ _
    simp only [Fin.reduceFinMk, Fin.isValue] at h1
    rw [e, mkPt_one] at h1
    nlinarith [mul_pos ht0 hay, sub_pos.2 ht1]

theorem lemmaK2_corner_m (C : CtxBaseT D u v α β γ L ax ay (-1) L) {d2 : ℝ} (hd2 : 0 < d2)
    (hax : 2 * (u : ℝ) * (L - ax) = (v : ℝ) * d2) (hsq : (L - ax) ^ 2 + ay ^ 2 = d2 ^ 2)
    (hbig : (v : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) < d2) {n : ℕ} (hn1 : 1 ≤ n) (hnv : n < v)
    (hrun : ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) (-1) L (i : ℝ) 0)
    (hVnv : (∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0) = γ) →
      lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0 ∉ Set.range D.target.pts)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0 ∈ Set.range D.target.pts ∨
      ∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) (-1) L (n : ℝ) 0) = γ) : False := by
  have S := C.S
  have hnvR : (n : ℝ) < v := by exact_mod_cast hnv
  have hPw : ∀ w : ℕ, 1 ≤ w → w ≤ n →
      lpT (u : ℝ) (v : ℝ) (-1) L 0 (w : ℝ) ∈ D.target.carrier ∧
      lpT (u : ℝ) (v : ℝ) (-1) L 0 (w : ℝ) ∈ frontier D.target.carrier ∧
      lpT (u : ℝ) (v : ℝ) (-1) L 0 (w : ℝ) ∉ Set.range D.target.pts ∧
      gB L ax ay (lpT (u : ℝ) (v : ℝ) (-1) L 0 (w : ℝ)) = 0 ∧
      0 < gA ax ay (lpT (u : ℝ) (v : ℝ) (-1) L 0 (w : ℝ)) ∧
      0 < (lpT (u : ℝ) (v : ℝ) (-1) L 0 (w : ℝ)) 1 := fun w hw1 hwn =>
    lp0w_facts_m S hd2 hax hsq hbig (w := (w : ℝ)) (by exact_mod_cast hw1)
      (lt_of_le_of_lt (by exact_mod_cast hwn) hnvR)
  have hQmem : ∀ w : ℕ, 1 ≤ w → w ≤ n → lpT (u : ℝ) (v : ℝ) (-1) L (w : ℝ) 0 ∈ D.target.carrier := by
    intro w hw1 hwn
    obtain ⟨t, k, m, j, -, -, -, -, hm, -⟩ := hrun (w - 1) (by omega)
    have hc : ((w - 1 : ℕ) : ℝ) + 1 = (w : ℝ) := by
      rw [Nat.cast_sub hw1]; push_cast; ring
    rw [hc] at hm
    rw [← hm]
    exact Erdos634.MarchInduction.pts_mem_target D.toDissection t m
  refine lemmaK2_final C hn1 hnv hrun ?_ ?_ ?_ hVnv hnoγ hstop
  · intro w hw1 hwn
    obtain ⟨-, hf, hnv', hgB, -, -⟩ := hPw w hw1 hwn
    exact ⟨hf, hnv', Or.inr ⟨rfl, hgB⟩⟩
  · intro w hw1 hwn
    refine S.frontier_y0 (hQmem w hw1 hwn) ?_
    rw [lpT_w0_m]; simp
  · intro w hw1 hwn
    obtain ⟨hPm, -, -, -, hgA, hy⟩ := hPw w hw1 hwn
    refine S.interior_seg hPm (hQmem w hw1 hwn) (Or.inl hy) (Or.inl hgA) (Or.inr ?_)
    rw [lpT_w0_m, gB_mk]
    have hw : (1 : ℝ) ≤ w := by exact_mod_cast hw1
    have := S.hay
    have := S.u0
    have := S.v0
    nlinarith [mul_pos (mul_pos S.u0 S.v0) S.hay]

#print axioms lemmaK2_corner_m
end Erdos634.Draft.ThmDRun
