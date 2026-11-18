/-
Draft/IsoTransferF1.lean -- the F1 -> Iso transfer applied to the Lean F1 strip family (Erdos #634; work item internal working notes).

`iso_main` has the hypotheses of `F1StripCert.f1_main` (one dissection of `T_3`, split at `p = B`), and concludes that the isosceles triangle
`(m b c, m b c, m b (a + 2b))` is dissected into `m * m * (B (A + 2 B))` copies of the tile, for every `m >= 2` (proof of `f1_main`, then
`IsoTransfer.isoTiled_of_f1Tiled`; `f1_main` itself hides the region tiling, hence the repeated proof).  Instances for the tiles (7,8,13) and
(8,7,13): `184 m^2` and `154 m^2` (CONTROL: N = B(A+2B)m^2 = B(A+B)m^2 + (mB)^2; (7,8): 120 + 64 = 184, (8,7): 105 + 49 = 154).
CREDIT: Zhang (arXiv 2512.22696, Props 8-9), Paliy (transfers), internal notes S1.5, the F1Strip* modules of 2026-11-12.
UNAUDITED beyond the internal build.  No sorry, no native_decide.
-/
import Erdos634.Draft.F1StripCert
import Erdos634.Draft.IsoTransfer
import Erdos634.Draft.F1Strip78Base
import Erdos634.Draft.F1Strip87Base
import Erdos634.Draft.TileCountFamilies

namespace Erdos634.Draft.IsoTransferF1

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling Erdos634.Draft.F1StripGeom
  Erdos634.Draft.F1StripLemma Erdos634.Draft.F1StripDissect Erdos634.Draft.F1StripExtract Erdos634.Draft.F1StripCert
  Erdos634.Draft.IsoTransfer Erdos634.Draft.TileCountFamilies

noncomputable section

/-- **F1 strip family -> Iso family.** -/
theorem iso_main {A B : ℕ} (hA : 0 < A) (hB : 0 < B) {u : ℝ} (hu : 0 < u)
    {N n₁ n₂ : ℕ} (hN : n₁ + n₂ = N)
    (hn₁ : n₁ = 5 * (B * (A + B))) (hn₂ : n₂ = 4 * (B * (A + B)))
    (D : CongruentDissection N)
    (hT : D.target.carrier = triR (u * A) (u * B) (A : ℝ) (B : ℝ) 3)
    (hM : D.model.Congruent (model hA hB hu))
    (hl : ∀ i : Fin N, i.val < n₁ → ∀ x ∈ (D.tile i).carrier, pc (u * A) x ≤ B)
    (hr : ∀ i : Fin N, n₁ ≤ i.val → ∀ x ∈ (D.tile i).carrier, (B : ℝ) ≤ pc (u * A) x) :
    ∀ m : ℕ, 2 ≤ m → TileCount (m * m * (B * (A + 2 * B))) := by
  intro m hm
  have ha := scale_pos hA hu
  have hb := scale_pos hB hu
  have hA' := real_pos hA
  have hB' := real_pos hB
  set f := ch (u * (A : ℝ)) (u * (B : ℝ)) 1 0 with hf
  have hfx : ∀ x, f x = pc (u * (A : ℝ)) x := by
    intro x; rw [hf, ch_apply]; ring
  have hmem0 : (mkPt 0 0 : Plane) ∈ D.target.carrier := by
    rw [hT]
    simp only [triR, Set.mem_setOf_eq]
    rw [pc_c1_0 ha, qc_c1_0 hb]
    refine ⟨le_refl _, le_refl _, ?_⟩
    have : 0 < (3 : ℝ) * ((B : ℝ) * ((A : ℝ) + B)) := by positivity
    linarith
  have hmem1 : (mkPt (3 * (B : ℝ) * (u * (A : ℝ))) 0 : Plane) ∈ D.target.carrier := by
    rw [hT]
    simp only [triR, Set.mem_setOf_eq]
    rw [pc_t1 (B := (B : ℝ)) ha 3, qc_t1 (b := u * (B : ℝ)) (a := u * (A : ℝ)) (B := (B : ℝ)) 3]
    refine ⟨by positivity, le_refl _, ?_⟩
    linarith
  obtain ⟨hS, hTT⟩ := split_tiled_thr hN D f (B : ℝ)
    (fun i hi x hx => by rw [hfx]; exact hl i hi x hx)
    (fun i hi x hx => by rw [hfx]; exact hr i hi x hx)
    ⟨mkPt 0 0, hmem0, by rw [hfx, pc_c1_0 ha]; exact hB'⟩
    ⟨mkPt (3 * (B : ℝ) * (u * (A : ℝ))) 0, hmem1, by
      rw [hfx, pc_t1 (B := (B : ℝ)) ha 3]; linarith⟩
  -- the strip S_3
  have hS3 : Tiled (stripR (u * (A : ℝ)) (u * (B : ℝ)) (A : ℝ) (B : ℝ) (((2 + 1 : ℕ)) : ℝ))
      (model hA hB hu) ((2 * 2 + 1) * (B * (A + B))) := by
    have h1 := Tiled.remodel hS hM
    refine (h1.congr_count (by omega)).congr_set ?_
    ext x
    rw [hT]
    simp only [Set.mem_setOf_eq, triR, stripR, hfx]
    push_cast
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h4, h2, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h3, by linarith⟩, h2⟩
  -- T_2, as a translate of the tiles in {p >= b}
  have hT2 : Tiled (triR (u * (A : ℝ)) (u * (B : ℝ)) (A : ℝ) (B : ℝ) ((2 : ℕ) : ℝ))
      (model hA hB hu) (2 * 2 * (B * (A + B))) := by
    have h1 := (Tiled.remodel hTT hM).shift (-(psiPt (u * (A : ℝ)) (u * (B : ℝ)) (B : ℝ) 0))
    refine (h1.congr_count (by omega)).congr_set ?_
    ext x
    simp only [neg_neg, Set.mem_setOf_eq, hfx, pc_add, qc_add, pc_psi ha, qc_psi hb]
    rw [hT]
    simp only [Set.mem_setOf_eq, triR, pc_add, qc_add, pc_psi ha, qc_psi hb]
    push_cast
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨by linarith, by linarith, ?_⟩
      nlinarith
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨by linarith, by linarith, ?_⟩, by linarith⟩
      nlinarith
  obtain ⟨i, rfl⟩ : ∃ i, m = 2 + i := ⟨m - 2, by omega⟩
  have key := strip_lemma hA hB hu 2 (by norm_num) hT2 hS3 i
  obtain ⟨hK, hL, hI⟩ := isoTiled_of_f1Tiled hA hB hu (2 + i) (by omega) key
  obtain ⟨R⟩ := hI.congr_count (n' := (2 + i) * (2 + i) * (B * (A + 2 * B))) (by push_cast; ring)
  exact ⟨toCD R⟩

end

theorem tileCount_184_mul_sq (m : ℕ) (hm : 2 ≤ m) : TileCount (184 * m ^ 2) := by
  have h := iso_main (A := 7) (B := 8) (u := 26) (by norm_num) (by norm_num) (by norm_num)
    (n₁ := 600) (n₂ := 480)
    (by have := Erdos634.Draft.F1Strip78Base.tiles_length; omega) (by norm_num) (by norm_num)
    Erdos634.F1Strip78TilingBridge.dissection Erdos634.Draft.F1Strip78Base.target_carrier
    Erdos634.Draft.F1Strip78Base.model_cong
    (fun i hi x hx => Erdos634.Draft.F1Strip78Base.tile_left i hi x hx)
    (fun i hi x hx => Erdos634.Draft.F1Strip78Base.tile_right i hi x hx) m hm
  rwa [show m * m * (8 * (7 + 2 * 8)) = 184 * m ^ 2 by ring] at h

theorem tileCount_154_mul_sq (m : ℕ) (hm : 2 ≤ m) : TileCount (154 * m ^ 2) := by
  have h := iso_main (A := 8) (B := 7) (u := 26) (by norm_num) (by norm_num) (by norm_num)
    (n₁ := 525) (n₂ := 420)
    (by have := Erdos634.Draft.F1Strip87Base.tiles_length; omega) (by norm_num) (by norm_num)
    Erdos634.F1Strip87TilingBridge.dissection Erdos634.Draft.F1Strip87Base.target_carrier
    Erdos634.Draft.F1Strip87Base.model_cong
    (fun i hi x hx => Erdos634.Draft.F1Strip87Base.tile_left i hi x hx)
    (fun i hi x hx => Erdos634.Draft.F1Strip87Base.tile_right i hi x hx) m hm
  rwa [show m * m * (7 * (8 + 2 * 7)) = 154 * m ^ 2 by ring] at h

end Erdos634.Draft.IsoTransferF1

#print axioms Erdos634.Draft.IsoTransferF1.iso_main
#print axioms Erdos634.Draft.IsoTransferF1.tileCount_184_mul_sq
#print axioms Erdos634.Draft.IsoTransferF1.tileCount_154_mul_sq
