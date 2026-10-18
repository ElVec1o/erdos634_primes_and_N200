import Mathlib.Tactic
import Erdos634.Draft.ThmDRunSetup
import Erdos634.Draft.ThmDLegTransport

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (3)/(5)): the normalised frame of a side of `T(g)`, with the isometry exposed  

`setup_of_sidesT_pinned2` is `setup_of_sidesT_pinned` returning the isometry `g` with `g (D₀.target.pts k) = Tg.pts (τ⁻¹ k)` and the target
equality; `frame_leg` transports a positioned leg of `D₀` to the frame (`mapSteps g`), with the numeric side data of `T(g)`:
`L = G u b`, S1 (`τ = id`-shift at the corner end of the leg): `ax = G b v²/(2u)`; S2: `ax = G b (2u² - v²)/(2u)`; `ay = G b v rt/(2u)`.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.APrimeLegBuild Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg Erdos634.Draft.SideRun Erdos634.TilePlacement

variable {N : ℕ}

theorem setup_of_sidesT_pinned2 (u v : ℕ) (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hco : Nat.Coprime u v)
    (hirr : Irrational (alphaT u v / Real.pi))
    {L ax ay d₁ d₂ : ℝ} (hL : 0 < L) (hay : 0 < ay)
    (hd₁ : dist (mkPt L 0) (mkPt ax ay) = d₁) (hd₂ : dist (mkPt ax ay) (mkPt 0 0) = d₂)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = d₁)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = d₂)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L)
    (hMod : HasSidesT D₀.model ((u : ℝ) ^ 2) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((u : ℝ) * v)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane),
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      (∀ k, g (D₀.target.pts k) = (Tg L ax ay hL hay).pts (τ.symm k)) ∧
      SetupT D u v (alphaT u v) (Real.pi - 3 * alphaT u v) (2 * alphaT u v) L ax ay := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (v : ℝ) < 2 * u := by exact_mod_cast hv
  have huvR : (u : ℝ) < v := by exact_mod_cast huv
  have h12 : dist ((Tg L ax ay hL hay).pts 1) ((Tg L ax ay hL hay).pts 2) = d₁ := hd₁
  have h20 : dist ((Tg L ax ay hL hay).pts 2) ((Tg L ax ay hL hay).pts 0) = d₂ := hd₂
  have h01 : dist ((Tg L ax ay hL hay).pts 0) ((Tg L ax ay hL hay).pts 1) = L := by
    show dist (mkPt 0 0) (mkPt L 0) = L
    have := Erdos634.MarchInduction.dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  obtain ⟨g, hg0⟩ := exists_iso_of_dist3T (T := D₀.target.relabel τ) (U := Tg L ax ay hL hay)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h3.trans h01.symm)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h1.trans h12.symm)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h2.trans h20.symm)
  have hg : ∀ k, g (D₀.target.pts k) = (Tg L ax ay hL hay).pts (τ.symm k) := by
    intro k
    have := hg0 (τ.symm k)
    rwa [Tri.relabel_pts, Equiv.apply_symm_apply] at this
  obtain ⟨σm, m0, m1, m2⟩ := sideOpp_relabel_of_hasSidesT hMod
  have hmod : D₀.model.Congruent (D₀.model.relabel σm) := Tri.congruent_relabel D₀.model σm
  have hMD := modelDataT_of_sides (Erdos634.E1NormalForm.normalFormC D₀ g τ.symm hmod) hu huv hv m0 m1 m2
  exact ⟨Erdos634.E1NormalForm.normalFormC D₀ g τ.symm hmod, g, fun _ _ => rfl, hg,
    ⟨hu, huv, hv, hco, hirr, alphaT_pos hu0 hvR (by linarith), rfl, rfl, hMD, hL, hay,
      fun _ _ => Erdos634.E1NormalForm.normalFormC_target D₀ hg hmod⟩⟩

theorem wlen_eq_of_sides (M M' : Tri) (h0 : sideOpp M 0 = sideOpp M' 0) (h1 : sideOpp M 1 = sideOpp M' 1)
    (h2 : sideOpp M 2 = sideOpp M' 2) (o : OE) :
    Erdos634.Draft.ThmD.wlen M o = Erdos634.Draft.ThmD.wlen M' o := by
  cases o
  · rw [Erdos634.Draft.ThmD.wlen_a _ _ rfl, Erdos634.Draft.ThmD.wlen_a _ _ rfl, h0]
  · rw [Erdos634.Draft.ThmD.wlen_a _ _ rfl, Erdos634.Draft.ThmD.wlen_a _ _ rfl, h0]
  · rw [Erdos634.Draft.ThmD.wlen_b _ _ rfl, Erdos634.Draft.ThmD.wlen_b _ _ rfl, h1]
  · rw [Erdos634.Draft.ThmD.wlen_b _ _ rfl, Erdos634.Draft.ThmD.wlen_b _ _ rfl, h1]
  · rw [Erdos634.Draft.ThmD.wlen_c _ _ rfl, Erdos634.Draft.ThmD.wlen_c _ _ rfl, h2]
  · rw [Erdos634.Draft.ThmD.wlen_c _ _ rfl, Erdos634.Draft.ThmD.wlen_c _ _ rfl, h2]

/-- the target of the frame and the target of `D₀`: frontier and vertices correspond under the isometry -/
theorem frame_target_iso {D₀ D : CongruentDissection N} (g : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3)) {U : Tri}
    (hg : ∀ k, g (D₀.target.pts k) = U.pts (σ k)) (hT : D.target = U) :
    (∀ p, p ∈ frontier D₀.target.carrier → g p ∈ frontier D.target.carrier) ∧
    (∀ p, p ∉ Set.range D₀.target.pts → g p ∉ Set.range D.target.pts) := by
  have hcar : D.target.carrier = g '' D₀.target.carrier := by
    rw [hT]
    unfold Tri.carrier
    have h1 : Set.range U.pts = g '' Set.range D₀.target.pts := by
      ext y
      constructor
      · rintro ⟨m, rfl⟩
        refine ⟨D₀.target.pts (σ.symm m), ⟨_, rfl⟩, ?_⟩
        rw [hg, Equiv.apply_symm_apply]
      · rintro ⟨x, ⟨k, rfl⟩, rfl⟩
        exact ⟨σ k, (hg k).symm⟩
    rw [h1]
    exact (AffineMap.image_convexHull (𝕜 := ℝ) (Erdos634.Ladder.isoAff g).toAffineMap (Set.range D₀.target.pts)).symm
  refine ⟨fun p hp => ?_, fun p hp ⟨m, hm⟩ => ?_⟩
  · rw [hcar]
    have := g.toHomeomorph.image_frontier D₀.target.carrier
    simp only [IsometryEquiv.coe_toHomeomorph] at this
    rw [← this]
    exact ⟨p, hp, rfl⟩
  · apply hp
    rw [hT] at hm
    obtain ⟨k, hk⟩ : ∃ k, σ k = m := ⟨σ.symm m, by simp⟩
    refine ⟨k, ?_⟩
    apply g.injective
    rw [hg, hk, hm]

#print axioms setup_of_sidesT_pinned2
#print axioms frame_target_iso
end Erdos634.Draft.ThmDRun
