import Mathlib.Tactic
import Erdos634.Draft.ThmDGeoLeg1
import Erdos634.Draft.ThmDNoGamma
import Erdos634.Draft.ThmDRunSetup

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha is ours.

# Theorem D' (ThmDGeo, item (1')): corner K2 for a leg of a dissection, in its own frame  

`leg_corner_start` / `leg_corner_end`: let `D₀` be a congruent dissection whose target has the sides `L = |τ0 τ1|`, `d₂ = |τ2 τ0|`, `d₁ = |τ1 τ2|`
(`τ` any labelling) and the model has the sides `u², v² - u², uv`.  After the isometry of `setup_of_sidesT_pinned` the side `[τ0, τ1]`
is the base `[Q, B]` of a `SetupT` frame, and `exists_chain_leg_pos` gives a positioned real leg of it.  If the corner `Q` (`B`) has the
ray data of `ThmDGeoCtx` then the leg does not begin (end) with `n` edges `c>` (`c<`), `1 ≤ n < v`, followed by an edge with left (right)
angle `γ` or reaching the far vertex (Lemma K (K2)).  Hypothesis kept: all three corners of the target are `α` or `π - 2α`
(`hcor`, stated on `Tg`).
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.Draft.APrimeLegBuild
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Set

variable {N : ℕ}

/-- the common setup: the normalised dissection and its positioned leg on the base side -/
theorem normal_leg (u v : ℕ) (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hco : Nat.Coprime u v)
    (hirr : Irrational (alphaT (u : ℝ) (v : ℝ) / Real.pi))
    {L ax ay d₁ d₂ : ℝ} (hL : 0 < L) (hay : 0 < ay)
    (hd₁ : dist (mkPt L 0) (mkPt ax ay) = d₁) (hd₂ : dist (mkPt ax ay) (mkPt 0 0) = d₂)
    (hcor : ∀ k : Fin 3, cornerAngle ((Tg L ax ay hL hay).pts (k + 1)) ((Tg L ax ay hL hay).pts k)
        ((Tg L ax ay hL hay).pts (k + 2)) = alphaT (u : ℝ) (v : ℝ) ∨
      cornerAngle ((Tg L ax ay hL hay).pts (k + 1)) ((Tg L ax ay hL hay).pts k)
        ((Tg L ax ay hL hay).pts (k + 2)) = Real.pi - 2 * alphaT (u : ℝ) (v : ℝ))
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = d₁)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = d₂)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L)
    (hMod : HasSidesT D₀.model ((u : ℝ) ^ 2) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((u : ℝ) * v)) :
    ∃ (D : CongruentDissection N) (S : SetupT D u v (alphaT (u : ℝ) (v : ℝ))
        (Real.pi - 3 * alphaT (u : ℝ) (v : ℝ)) (2 * alphaT (u : ℝ) (v : ℝ)) L ax ay)
      (r : List (LegStep N)) (t : Fin N) (e : OE),
      RealLeg D.toDissection (alphaT (u : ℝ) (v : ℝ)) t e r ∧
      LegPos D.toDissection D.model (mkPt 0 0) (mkPt L 0) t e 0 r ∧
      LegEnd D.toDissection (alphaT (u : ℝ) (v : ℝ)) (mkPt L 0) t e r ∧
      (D.tile t).localAngle (mkPt 0 0) = angVal (alphaT (u : ℝ) (v : ℝ)) e.l ∧
      (∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
        (D.tile t).localAngle ((D.tile t).pts k) ≠ 2 * alphaT (u : ℝ) (v : ℝ)) := by
  obtain ⟨D, g, -, -, -, S⟩ := setup_of_sidesT_pinned u v hu huv hv hco hirr hL hay hd₁ hd₂ D₀ τ h1 h2 h3 hMod
  have hu0 := S.u0
  have hA0 := S.hM.hα'
  have hA1 := S.hM.hβ'
  have hA2 := S.hM.hγ'
  rw [S.hβ] at hA1
  rw [S.hγ] at hA2
  have hα := S.hα
  have h3α : 3 * alphaT (u : ℝ) (v : ℝ) < Real.pi := by
    have hβpos : 0 < Real.pi - 3 * alphaT (u : ℝ) (v : ℝ) := by
      have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
      have e : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) =
          Real.pi - 3 * alphaT (u : ℝ) (v : ℝ) := hA1
      rw [e] at h; exact h
    linarith
  have hcong : ∀ i, D.model.Congruent (D.tile i) := fun i => (D.tiles_congruent i).symm
  obtain ⟨t0, e0, r, hleg, hfirst, hlast, -, -, -, -, hpos⟩ :=
    exists_chain_leg_pos D.toDissection D.model hcong (alphaT (u : ℝ) (v : ℝ)) S.hirr hα hA0 hA1 hA2 0
  obtain ⟨hp0, hp1, -⟩ := target_pts01 S
  have hB : D.toDissection.target.pts (0 + 1) = mkPt L 0 := by simpa using hp1
  refine ⟨D, S, r, t0, e0, hleg, ?_, ?_, ?_, ?_⟩
  · rw [hp0, hB] at hpos; exact hpos
  · refine legEnd_of_last D.toDissection _ _ r t0 e0 ?_
    rw [← hB]; exact hlast
  · rw [← hp0]; exact hfirst
  · intro t k hk
    obtain ⟨i, hi⟩ := hk
    rw [← hi]
    have hcorD : ∀ k : Fin 3, cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) =
        alphaT (u : ℝ) (v : ℝ) ∨ cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) =
        Real.pi - 2 * alphaT (u : ℝ) (v : ℝ) := by
      intro k; rw [S.tgt]; exact hcor k
    exact Erdos634.Draft.ThmD.no_gamma_at_corner D.toDissection D.model hcong S.hirr hA0 hA1 hA2 hα h3α i (hcorD i) t



/-- **Lemma K (K2) at the corner `Q` of the leg `[τ0, τ1]` of any congruent dissection** (ray data at `Q`). -/
theorem leg_corner_start {N : ℕ}
    (u v : ℕ) (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hco : Nat.Coprime u v)
    (hirr : Irrational (alphaT (u : ℝ) (v : ℝ) / Real.pi))
    {L ax ay d₁ d₂ : ℝ} (hL : 0 < L) (hay : 0 < ay)
    (hd₁ : dist (mkPt L 0) (mkPt ax ay) = d₁) (hd₂ : dist (mkPt ax ay) (mkPt 0 0) = d₂)
    (hcor : ∀ k : Fin 3, cornerAngle ((Tg L ax ay hL hay).pts (k + 1)) ((Tg L ax ay hL hay).pts k)
        ((Tg L ax ay hL hay).pts (k + 2)) = alphaT (u : ℝ) (v : ℝ) ∨
      cornerAngle ((Tg L ax ay hL hay).pts (k + 1)) ((Tg L ax ay hL hay).pts k)
        ((Tg L ax ay hL hay).pts (k + 2)) = Real.pi - 2 * alphaT (u : ℝ) (v : ℝ))
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = d₁)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = d₂)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L)
    (hMod : HasSidesT D₀.model ((u : ℝ) ^ 2) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((u : ℝ) * v))
    (hd2 : 0 < d₂) (hax : 2 * (u : ℝ) * ax = (v : ℝ) * d₂) (hsq : ax ^ 2 + ay ^ 2 = d₂ ^ 2)
    (hbig : (v : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) < d₂) :
    ∃ (D : CongruentDissection N) (S : SetupT D u v (alphaT (u : ℝ) (v : ℝ))
        (Real.pi - 3 * alphaT (u : ℝ) (v : ℝ)) (2 * alphaT (u : ℝ) (v : ℝ)) L ax ay)
      (r : List (LegStep N)) (t : Fin N) (e : OE),
      RealLeg D.toDissection (alphaT (u : ℝ) (v : ℝ)) t e r ∧
      LegPos D.toDissection D.model (mkPt 0 0) (mkPt L 0) t e 0 r ∧
      LegEnd D.toDissection (alphaT (u : ℝ) (v : ℝ)) (mkPt L 0) t e r ∧
      (D.tile t).localAngle (mkPt 0 0) = angVal (alphaT (u : ℝ) (v : ℝ)) e.l ∧
      ∀ n : ℕ, 1 ≤ n → n < v → (∀ j < n, (legEdges e r)[j]? = some OE.cp) →
        (n = (legEdges e r).length ∨ ∃ o, (legEdges e r)[n]? = some o ∧ o.l = Ang.ga) → False := by
  obtain ⟨D, S, r, t, e, hRL, hLP, hLE, hang, hnoγ⟩ := normal_leg u v hu huv hv hco hirr hL hay hd₁ hd₂ hcor D₀ τ
    h1 h2 h3 hMod
  refine ⟨D, S, r, t, e, hRL, hLP, hLE, hang, ?_⟩
  intro n hn1 hnv hcp hstop
  refine leg_K2_start ⟨S, Or.inl rfl⟩ hd2 hax hsq hbig hn1 hnv hRL hLP hLE hang hcp ?_ hstop
  intro t k hk
  rw [S.hγ]; exact hnoγ t k hk

/-- **Lemma K (K2) at the corner `B` of the leg `[τ0, τ1]`** (ray data at `B`; the run is read from the end). -/
theorem leg_corner_end {N : ℕ}
    (u v : ℕ) (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hco : Nat.Coprime u v)
    (hirr : Irrational (alphaT (u : ℝ) (v : ℝ) / Real.pi))
    {L ax ay d₁ d₂ : ℝ} (hL : 0 < L) (hay : 0 < ay)
    (hd₁ : dist (mkPt L 0) (mkPt ax ay) = d₁) (hd₂ : dist (mkPt ax ay) (mkPt 0 0) = d₂)
    (hcor : ∀ k : Fin 3, cornerAngle ((Tg L ax ay hL hay).pts (k + 1)) ((Tg L ax ay hL hay).pts k)
        ((Tg L ax ay hL hay).pts (k + 2)) = alphaT (u : ℝ) (v : ℝ) ∨
      cornerAngle ((Tg L ax ay hL hay).pts (k + 1)) ((Tg L ax ay hL hay).pts k)
        ((Tg L ax ay hL hay).pts (k + 2)) = Real.pi - 2 * alphaT (u : ℝ) (v : ℝ))
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = d₁)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = d₂)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L)
    (hMod : HasSidesT D₀.model ((u : ℝ) ^ 2) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((u : ℝ) * v))
    (hd2 : 0 < d₁) (hax : 2 * (u : ℝ) * (L - ax) = (v : ℝ) * d₁)
    (hsq : (L - ax) ^ 2 + ay ^ 2 = d₁ ^ 2)
    (hbig : (v : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) < d₁) :
    ∃ (D : CongruentDissection N) (S : SetupT D u v (alphaT (u : ℝ) (v : ℝ))
        (Real.pi - 3 * alphaT (u : ℝ) (v : ℝ)) (2 * alphaT (u : ℝ) (v : ℝ)) L ax ay)
      (r : List (LegStep N)) (t : Fin N) (e : OE),
      RealLeg D.toDissection (alphaT (u : ℝ) (v : ℝ)) t e r ∧
      LegPos D.toDissection D.model (mkPt 0 0) (mkPt L 0) t e 0 r ∧
      LegEnd D.toDissection (alphaT (u : ℝ) (v : ℝ)) (mkPt L 0) t e r ∧
      (D.tile t).localAngle (mkPt 0 0) = angVal (alphaT (u : ℝ) (v : ℝ)) e.l ∧
      ∀ n : ℕ, 1 ≤ n → n < v → n ≤ (legEdges e r).length →
        (∀ j < n, (legEdges e r)[(legEdges e r).length - 1 - j]? = some OE.cm) →
        (n < (legEdges e r).length →
          ∃ o, (legEdges e r)[(legEdges e r).length - 1 - n]? = some o ∧ o.r = Ang.ga) → False := by
  obtain ⟨D, S, r, t, e, hRL, hLP, hLE, hang, hnoγ⟩ := normal_leg u v hu huv hv hco hirr hL hay hd₁ hd₂ hcor D₀ τ
    h1 h2 h3 hMod
  refine ⟨D, S, r, t, e, hRL, hLP, hLE, hang, ?_⟩
  intro n hn1 hnv hn hcm hstop
  refine leg_K2_end ⟨S, Or.inr rfl⟩ hd2 hax hsq hbig hn1 hnv hRL hLP hLE hang hn hcm ?_ hstop
  intro t k hk
  rw [S.hγ]; exact hnoγ t k hk

#print axioms leg_corner_start
#print axioms leg_corner_end
end Erdos634.Draft.ThmDRun
