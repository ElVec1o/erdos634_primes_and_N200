import Mathlib.Tactic
import Erdos634.Draft.ThmDLegT0b

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (4)/(5)): a stopped `c`-block of length `< u` with `T₀` is impossible  

`east_big` (`c>` block at the index `a`, `ε = 1`, `x = f a * L`) and `west_big` (`c<` block ending at the index `b`, `ε = -1`, `x = f b * L`):
a block of `n < u` edges stopped at its far end (`γ` after it, or the vertex `B`; before it, or `Q`) whose first tile has the tile `T₀`
across its `b`-ray cannot exist.  This is `lemma33_interior` with `hrun`, `hch`, `hT0`, `hVnv`, `hstop` derived from the leg.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.Draft.APrimeLegBuild
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Erdos634.MarchSlots Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem Brk.pos_of {S : SetupT D u v α β γ L ax ay} {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f) {a : ℕ}
    (ha1 : 1 ≤ a) (haw : a ≤ W.length) : 0 < f a := by
  have := hB.lt_of_lt (i := 0) (j := a) (by omega) haw
  rwa [hB.f0] at this

theorem Brk.lt_one_of {S : SetupT D u v α β γ L ax ay} {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f) {a : ℕ}
    (haw : a < W.length) : f a < 1 := by
  have h1 := hB.lt_succ haw
  have h2 := hB.le_one (i := a + 1) (by omega)
  linarith

theorem east_big (S : SetupT D u v α β γ L ax ay) {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f) {a n : ℕ}
    (ha1 : 1 ≤ a) (hn1 : 1 ≤ n) (hnu : n < u) (han : a + n ≤ W.length) (haw : a < W.length)
    (hcp : ∀ j < n, W[a + j]? = some OE.cp)
    (hT0 : ∃ t1 : Fin N, RayTileAC D u v (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0) (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 1)
      (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 1 0) t1)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : a + n = W.length ∨ ∃ o, W[a + n]? = some o ∧ o.l = Ang.ga) : False := by
  have hL := S.hL
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have C : CtxBaseT D u v α β γ L ax ay 1 (f a * L) := ⟨S, Or.inl rfl⟩
  obtain ⟨hpos, hrun⟩ := blk_cp S hB han hcp
  have hX0 : lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0 = mkPt (f a * L) 0 := by
    rw [lpT_base]; exact mkPt_congr (by ring) rfl
  have hx0 : 0 < f a * L := mul_pos (hB.pos_of ha1 haw.le) hL
  have hxL : f a * L < L := by nlinarith [hB.lt_one_of haw]
  obtain ⟨hVnv, hst⟩ := cp_stop S hB hn1 han hcp hnoγ hstop
  obtain ⟨t1, hasV⟩ := hrun 0 (by omega)
  have hXm : mkPt (f a * L) 0 ∈ D.target.carrier := by
    have := hasV.mem₁
    simpa [hX0] using this
  have hch : ∀ j : ℕ, 1 ≤ j → lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 (j : ℝ) ∈ D.target.carrier →
      openSegment ℝ (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 0) (lpT (u : ℝ) (v : ℝ) 1 (f a * L) 0 (j : ℝ)) ⊆
        interior D.target.carrier := by
    intro j hj hjm
    rw [hX0]
    refine seg_int_base S hx0 hxL hXm hjm ?_
    rw [lpT_snd]
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have := hhT_pos hu huv hv2
    nlinarith
  obtain ⟨t1', hRay⟩ := hT0
  exact lemma33_interior C hn1 hnu hrun hch (hT0_of_ray C hRay) hVnv hnoγ hst

theorem west_big (S : SetupT D u v α β γ L ax ay) {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f) {b n : ℕ}
    (hn1 : 1 ≤ n) (hnu : n < u) (hb : b < W.length) (hn : n ≤ b)
    (hcm : ∀ j < n, W[b - 1 - j]? = some OE.cm)
    (hT0 : ∃ t1 : Fin N, RayTileAC D u v (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0) (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 1)
      (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 1 0) t1)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : n = b ∨ (n < b ∧ ∃ o, W[b - 1 - n]? = some o ∧ o.r = Ang.ga)) : False := by
  have hL := S.hL
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have C : CtxBaseT D u v α β γ L ax ay (-1) (f b * L) := ⟨S, Or.inr rfl⟩
  obtain ⟨hpos, hrun⟩ := blk_cm S hB hb.le hn hcm
  have hX0 : lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0 = mkPt (f b * L) 0 := by
    rw [lpT_base]; exact mkPt_congr (by ring) rfl
  have hx0 : 0 < f b * L := mul_pos (hB.pos_of (by omega) hb.le) hL
  have hxL : f b * L < L := by nlinarith [hB.lt_one_of hb]
  obtain ⟨hVnv, hst⟩ := cm_stop S hB hn1 hb.le hn hcm hnoγ hstop
  obtain ⟨t1, hasV⟩ := hrun 0 (by omega)
  have hXm : mkPt (f b * L) 0 ∈ D.target.carrier := by
    have := hasV.mem₁
    simpa [hX0] using this
  have hch : ∀ j : ℕ, 1 ≤ j → lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 (j : ℝ) ∈ D.target.carrier →
      openSegment ℝ (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 0) (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) 0 (j : ℝ)) ⊆
        interior D.target.carrier := by
    intro j hj hjm
    rw [hX0]
    refine seg_int_base S hx0 hxL hXm hjm ?_
    rw [lpT_snd]
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have := hhT_pos hu huv hv2
    nlinarith
  obtain ⟨t1', hRay⟩ := hT0
  exact lemma33_interior C hn1 hnu hrun hch (hT0_of_ray C hRay) hVnv hnoγ hst

#print axioms east_big
#print axioms west_big
end Erdos634.Draft.ThmDRun
