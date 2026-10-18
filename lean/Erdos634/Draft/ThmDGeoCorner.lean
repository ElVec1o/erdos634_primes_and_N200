import Erdos634.Draft.ThmDGeoCtx
import Erdos634.Draft.ThmDK2Final

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha is ours.

# Theorem D' (ThmDGeo, item (1)): Lemma K at a corner of a real frame

`lemmaK2_corner`: in a `SetupT` frame with `ε = 1`, `x = 0` and the geometry of the side `QA` (`ThmDGeoCtx`), the hypotheses `hPf`, `hQf`,
`hint` of `lemmaK2_final` are DERIVED (from `lp0w_facts`, `frontier_y0`, `interior_seg`); what remains of the context are the run
tiles `hrun`, `hVnv`, `hnoγ` (`ThmDNoGamma.no_gamma_at_corner`) and `hstop`.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.MarchSlots Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem lpT_w0 (u v : ℝ) (w : ℝ) : lpT u v 1 0 w 0 = mkPt (w * (u * v)) 0 := by
  unfold lpT; exact mkPt_congr (by ring) (by ring)

theorem lemmaK2_corner (C : CtxBaseT D u v α β γ L ax ay 1 0) {d2 : ℝ} (hd2 : 0 < d2)
    (hax : 2 * (u : ℝ) * ax = (v : ℝ) * d2) (hsq : ax ^ 2 + ay ^ 2 = d2 ^ 2)
    (hbig : (v : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ≤ d2) {n : ℕ} (hn1 : 1 ≤ n) (hnv : n < v)
    (hrun : ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) 1 0 (i : ℝ) 0)
    (hVnv : (∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0) = γ) →
      lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0 ∉ Set.range D.target.pts)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0 ∈ Set.range D.target.pts ∨
      ∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) 1 0 (n : ℝ) 0) = γ) : False := by
  have S := C.S
  have hnvR : (n : ℝ) < v := by exact_mod_cast hnv
  have hPw : ∀ w : ℕ, 1 ≤ w → w ≤ n →
      lpT (u : ℝ) (v : ℝ) 1 0 0 (w : ℝ) ∈ D.target.carrier ∧ lpT (u : ℝ) (v : ℝ) 1 0 0 (w : ℝ) ∈ frontier D.target.carrier ∧
      lpT (u : ℝ) (v : ℝ) 1 0 0 (w : ℝ) ∉ Set.range D.target.pts ∧
      gA ax ay (lpT (u : ℝ) (v : ℝ) 1 0 0 (w : ℝ)) = 0 ∧ 0 < gB L ax ay (lpT (u : ℝ) (v : ℝ) 1 0 0 (w : ℝ)) ∧
      0 < (lpT (u : ℝ) (v : ℝ) 1 0 0 (w : ℝ)) 1 := fun w hw1 hwn =>
    lp0w_facts S hd2 hax hsq hbig (w := (w : ℝ)) (by exact_mod_cast hw1)
      (lt_of_le_of_lt (by exact_mod_cast hwn) hnvR)
  have hQmem : ∀ w : ℕ, 1 ≤ w → w ≤ n → lpT (u : ℝ) (v : ℝ) 1 0 (w : ℝ) 0 ∈ D.target.carrier := by
    intro w hw1 hwn
    obtain ⟨t, k, m, j, -, -, -, -, hm, -⟩ := hrun (w - 1) (by omega)
    have hc : ((w - 1 : ℕ) : ℝ) + 1 = (w : ℝ) := by
      rw [Nat.cast_sub hw1]; push_cast; ring
    rw [hc] at hm
    rw [← hm]
    exact Erdos634.MarchInduction.pts_mem_target D.toDissection t m
  refine lemmaK2_final C hn1 hnv hrun ?_ ?_ ?_ hVnv hnoγ hstop
  · intro w hw1 hwn
    obtain ⟨-, hf, hnv', hgA, -, -⟩ := hPw w hw1 hwn
    exact ⟨hf, hnv', Or.inl ⟨rfl, hgA⟩⟩
  · intro w hw1 hwn
    refine S.frontier_y0 (hQmem w hw1 hwn) ?_
    rw [lpT_w0]; simp
  · intro w hw1 hwn
    obtain ⟨hPm, -, -, -, hgB, hy⟩ := hPw w hw1 hwn
    refine S.interior_seg hPm (hQmem w hw1 hwn) (Or.inl hy) (Or.inr ?_) (Or.inl hgB)
    rw [lpT_w0, gA_mk]
    have hw : (1 : ℝ) ≤ w := by exact_mod_cast hw1
    have := S.hay
    have := S.u0
    have := S.v0
    nlinarith [mul_pos (mul_pos S.u0 S.v0) S.hay]

#print axioms lemmaK2_corner
end Erdos634.Draft.ThmDRun
