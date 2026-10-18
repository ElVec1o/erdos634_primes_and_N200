import Mathlib.Tactic
import Erdos634.Draft.ThmDFrameNum
import Erdos634.Draft.ThmDLegD1
import Erdos634.Draft.ThmDLegApex
import Erdos634.Draft.ThmDGeoLegCorner

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (5)): D1 for a positioned leg of `T(g)`  

`leg_c_count_S1` : a positioned leg of a unit-scaled dissection of `T(g)` (`g ≥ 2`) from the `α`-corner `pts i` to the apex `pts (i+1)` has at least
`u` edges `c`.  `leg_c_count_S2` : the leg from the apex `pts (i+1)` to the `α`-corner `pts (i+2)`.  The leg is transported to the normalised frame
(`ThmDFrame`) and `leg_D1` is applied with `leg_K2_start`/`apex_end` (S1), `apex_start`/`leg_K2_end` (S2).
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.Draft.APrimeLegBuild
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Erdos634.TilePlacement

variable {N : ℕ}

theorem hasSides_of_model (M : Tri) (a b c : ℝ) (h0 : sideOpp M 0 = a) (h1 : sideOpp M 1 = b)
    (h2 : sideOpp M 2 = c) : HasSidesT M a b c := by
  refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
  · exact h0
  · exact h1
  · exact h2

theorem leg_c_count_S1 (u v : ℕ) (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hco : Nat.Coprime u v)
    (hirr : Irrational (alphaT (u : ℝ) (v : ℝ) / Real.pi)) (G : ℝ) (hG : 1 < G)
    (D₀ : CongruentDissection N) (i : Fin 3)
    (hM0 : sideOpp D₀.model 0 = (u : ℝ) ^ 2) (hM1 : sideOpp D₀.model 1 = (v : ℝ) ^ 2 - (u : ℝ) ^ 2)
    (hM2 : sideOpp D₀.model 2 = (u : ℝ) * v)
    (hA : dist (D₀.target.pts i) (D₀.target.pts (i + 1)) = G * u * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2))
    (hB : dist (D₀.target.pts (i + 1)) (D₀.target.pts (i + 2)) = G * u * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2))
    (hC : dist (D₀.target.pts (i + 2)) (D₀.target.pts i) = G * v * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2))
    {r : List (LegStep N)} {t : Fin N} {e : OE}
    (hRL : RealLeg D₀.toDissection (alphaT (u : ℝ) (v : ℝ)) t e r)
    (hLP : LegPos D₀.toDissection D₀.model (D₀.target.pts i) (D₀.target.pts (i + 1)) t e 0 r)
    (hLE : LegEnd D₀.toDissection (alphaT (u : ℝ) (v : ℝ)) (D₀.target.pts (i + 1)) t e r)
    (hang : (D₀.tile t).localAngle (D₀.target.pts i) = angVal (alphaT (u : ℝ) (v : ℝ)) e.l) :
    u ≤ cntLetter isC (legEdges e r) := by
  obtain ⟨hL, hay, hd1, hd2, hax, hsq, hbig, hwedge, hc0, hc1, hc2⟩ := nums_S1 u v G hu huv hv hG
  set b : ℝ := (v : ℝ) ^ 2 - (u : ℝ) ^ 2 with hbdef
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have huvR : (u : ℝ) < v := by exact_mod_cast huv
  have hb0 : 0 < b := by simp only [hbdef]; nlinarith
  have hd20 : 0 < G * v * b := mul_pos (mul_pos (by linarith) (by linarith)) hb0
  set L : ℝ := G * u * b with hLdef
  set ax : ℝ := G * b * (v : ℝ) ^ 2 / (2 * u) with haxdef
  set ay : ℝ := G * b * v * rtT (u : ℝ) (v : ℝ) / (2 * u) with haydef
  have hMod := hasSides_of_model D₀.model _ _ _ hM0 hM1 hM2
  obtain ⟨F, g, htile, hg, S⟩ := setup_of_sidesT_pinned2 u v hu huv hv hco hirr hL hay hd1 hd2 D₀
    (Equiv.addLeft i) (by simpa using hB) (by simpa using hC) (by simpa using hA) hMod
  have hgk : ∀ k, g (D₀.target.pts (Equiv.addLeft i k)) = (Tg L ax ay hL hay).pts k := fun k => by
    rw [hg, Equiv.symm_apply_apply]
  have hgA : g (D₀.target.pts i) = mkPt 0 0 := by
    have := hgk 0
    simpa using this
  have hgB : g (D₀.target.pts (i + 1)) = mkPt L 0 := by
    have := hgk 1
    simpa using this
  have hT : F.target = Tg L ax ay hL hay := S.tgt
  obtain ⟨hfr, hnv⟩ := frame_target_iso (D₀ := D₀) (D := F) g (Equiv.addLeft i).symm hg hT
  have hw : ∀ o, Erdos634.Draft.ThmD.wlen F.model o = Erdos634.Draft.ThmD.wlen D₀.model o :=
    wlen_eq_of_sides _ _ (S.hM.hs0.trans hM0.symm) (S.hM.hs1.trans hM1.symm) (S.hM.hs2.trans hM2.symm)
  have hRL' := realLeg_iso (D₀ := D₀.toDissection) (D := F.toDissection) g htile hfr hnv _ r t e hRL
  have hLP' := legPos_iso (D₀ := D₀.toDissection) (D := F.toDissection) g htile hw
    (D₀.target.pts i) (D₀.target.pts (i + 1)) r t e 0 hLP
  rw [hgA, hgB] at hLP'
  have hLE' := legEnd_iso (D₀ := D₀.toDissection) (D := F.toDissection) g htile _ _ r t e hLE
  rw [hgB] at hLE'
  have hang' : (F.tile t).localAngle (mkPt 0 0) = angVal (alphaT (u : ℝ) (v : ℝ)) e.l := by
    rw [← hgA, localAngle_iso g (htile t)]; exact hang
  -- model facts
  have hcong : ∀ j, F.model.Congruent (F.tile j) := fun j => (F.tiles_congruent j).symm
  have hA0 := S.hM.hα'
  have hA1 := S.hM.hβ'
  have hA2 := S.hM.hγ'
  rw [S.hβ] at hA1
  rw [S.hγ] at hA2
  have h3α : 3 * alphaT (u : ℝ) (v : ℝ) < Real.pi := by
    have hβpos : 0 < Real.pi - 3 * alphaT (u : ℝ) (v : ℝ) := by
      have h := Erdos634.MarchFlank.cornerAngle_pos F.model 1
      have e' : cornerAngle (F.model.pts (1 + 1)) (F.model.pts 1) (F.model.pts (1 + 2)) =
          Real.pi - 3 * alphaT (u : ℝ) (v : ℝ) := hA1
      rw [e'] at h; exact h
    linarith
  have hcorF : ∀ k : Fin 3, cornerAngle (F.target.pts (k + 1)) (F.target.pts k) (F.target.pts (k + 2)) =
      alphaT (u : ℝ) (v : ℝ) ∨ cornerAngle (F.target.pts (k + 1)) (F.target.pts k) (F.target.pts (k + 2)) =
      Real.pi - 2 * alphaT (u : ℝ) (v : ℝ) := by
    intro k
    rw [hT]
    fin_cases k
    · exact Or.inl hc0
    · exact Or.inr hc1
    · exact Or.inl hc2
  have hnoγ : ∀ (t : Fin N) (k : Fin 3), (F.tile t).pts k ∈ Set.range F.target.pts →
      (F.tile t).localAngle ((F.tile t).pts k) ≠ 2 * alphaT (u : ℝ) (v : ℝ) := by
    intro t k hk
    obtain ⟨j, hj⟩ := hk
    rw [← hj]
    exact Erdos634.Draft.ThmD.no_gamma_at_corner F.toDissection F.model hcong S.hirr hA0 hA1 hA2 S.hα h3α j
      (hcorF j) t
  have hapexB : cornerAngle (F.target.pts (1 + 1)) (F.target.pts 1) (F.target.pts (1 + 2)) =
      Real.pi - 2 * alphaT (u : ℝ) (v : ℝ) := by
    rw [hT]; exact hc1
  have hres := leg_D1 S hRL' hLP' hLE' hang' hnoγ
    (fun n hn1 hnu hcp hst => leg_K2_start ⟨S, Or.inl rfl⟩ (d2 := G * v * b) hd20 hax hsq hbig hn1
      (lt_trans hnu huv) hRL' hLP' hLE' hang' hcp hnoγ hst)
    (fun n hn1 hnu hn hcm hst => by
      obtain ⟨f, hBr⟩ := brk_of_leg S hRL' hLP' hLE' hang'
      exact apex_end S hBr hnoγ hapexB hwedge hn1 hnu hn hcm hst)
  rwa [legEdges_mapSteps] at hres

#print axioms leg_c_count_S1

theorem leg_c_count_S2 (u v : ℕ) (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hco : Nat.Coprime u v)
    (hirr : Irrational (alphaT (u : ℝ) (v : ℝ) / Real.pi)) (G : ℝ) (hG : 1 < G)
    (D₀ : CongruentDissection N) (i : Fin 3)
    (hM0 : sideOpp D₀.model 0 = (u : ℝ) ^ 2) (hM1 : sideOpp D₀.model 1 = (v : ℝ) ^ 2 - (u : ℝ) ^ 2)
    (hM2 : sideOpp D₀.model 2 = (u : ℝ) * v)
    (hA : dist (D₀.target.pts i) (D₀.target.pts (i + 1)) = G * u * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2))
    (hB : dist (D₀.target.pts (i + 1)) (D₀.target.pts (i + 2)) = G * u * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2))
    (hC : dist (D₀.target.pts (i + 2)) (D₀.target.pts i) = G * v * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2))
    {r : List (LegStep N)} {t : Fin N} {e : OE}
    (hRL : RealLeg D₀.toDissection (alphaT (u : ℝ) (v : ℝ)) t e r)
    (hLP : LegPos D₀.toDissection D₀.model (D₀.target.pts (i + 1)) (D₀.target.pts (i + 1 + 1)) t e 0 r)
    (hLE : LegEnd D₀.toDissection (alphaT (u : ℝ) (v : ℝ)) (D₀.target.pts (i + 1 + 1)) t e r)
    (hang : (D₀.tile t).localAngle (D₀.target.pts (i + 1)) = angVal (alphaT (u : ℝ) (v : ℝ)) e.l) :
    u ≤ cntLetter isC (legEdges e r) := by
  obtain ⟨hL, hay, hd1, hd2, hax, hsq, hbig, hwedge, hc0, hc1, hc2⟩ := nums_S2 u v G hu huv hv hG
  set b : ℝ := (v : ℝ) ^ 2 - (u : ℝ) ^ 2 with hbdef
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have huvR : (u : ℝ) < v := by exact_mod_cast huv
  have hb0 : 0 < b := by simp only [hbdef]; nlinarith
  have hd10 : 0 < G * v * b := mul_pos (mul_pos (by linarith) (by linarith)) hb0
  set L : ℝ := G * u * b with hLdef
  set ax : ℝ := G * b * (2 * (u : ℝ) ^ 2 - (v : ℝ) ^ 2) / (2 * u) with haxdef
  set ay : ℝ := G * b * v * rtT (u : ℝ) (v : ℝ) / (2 * u) with haydef
  have hMod := hasSides_of_model D₀.model _ _ _ hM0 hM1 hM2
  obtain ⟨F, g, htile, hg, S⟩ := setup_of_sidesT_pinned2 u v hu huv hv hco hirr hL hay hd1 hd2 D₀
    (Equiv.addLeft (i + 1)) (by simpa [add_assoc] using hC) (by simpa [add_assoc] using hA)
    (by simpa [add_assoc] using hB) hMod
  have hgk : ∀ k, g (D₀.target.pts (Equiv.addLeft (i + 1) k)) = (Tg L ax ay hL hay).pts k := fun k => by
    rw [hg, Equiv.symm_apply_apply]
  have hgA : g (D₀.target.pts (i + 1)) = mkPt 0 0 := by
    have := hgk 0
    simpa using this
  have hgB : g (D₀.target.pts (i + 1 + 1)) = mkPt L 0 := by
    have := hgk 1
    exact this
  have hT : F.target = Tg L ax ay hL hay := S.tgt
  obtain ⟨hfr, hnv⟩ := frame_target_iso (D₀ := D₀) (D := F) g (Equiv.addLeft (i + 1)).symm hg hT
  have hw : ∀ o, Erdos634.Draft.ThmD.wlen F.model o = Erdos634.Draft.ThmD.wlen D₀.model o :=
    wlen_eq_of_sides _ _ (S.hM.hs0.trans hM0.symm) (S.hM.hs1.trans hM1.symm) (S.hM.hs2.trans hM2.symm)
  have hRL' := realLeg_iso (D₀ := D₀.toDissection) (D := F.toDissection) g htile hfr hnv _ r t e hRL
  have hLP' := legPos_iso (D₀ := D₀.toDissection) (D := F.toDissection) g htile hw
    (D₀.target.pts (i + 1)) (D₀.target.pts (i + 1 + 1)) r t e 0 hLP
  rw [hgA, hgB] at hLP'
  have hLE' := legEnd_iso (D₀ := D₀.toDissection) (D := F.toDissection) g htile _ _ r t e hLE
  rw [hgB] at hLE'
  have hang' : (F.tile t).localAngle (mkPt 0 0) = angVal (alphaT (u : ℝ) (v : ℝ)) e.l := by
    rw [← hgA, localAngle_iso g (htile t)]; exact hang
  have hcong : ∀ j, F.model.Congruent (F.tile j) := fun j => (F.tiles_congruent j).symm
  have hA0 := S.hM.hα'
  have hA1 := S.hM.hβ'
  have hA2 := S.hM.hγ'
  rw [S.hβ] at hA1
  rw [S.hγ] at hA2
  have h3α : 3 * alphaT (u : ℝ) (v : ℝ) < Real.pi := by
    have hβpos : 0 < Real.pi - 3 * alphaT (u : ℝ) (v : ℝ) := by
      have h := Erdos634.MarchFlank.cornerAngle_pos F.model 1
      have e' : cornerAngle (F.model.pts (1 + 1)) (F.model.pts 1) (F.model.pts (1 + 2)) =
          Real.pi - 3 * alphaT (u : ℝ) (v : ℝ) := hA1
      rw [e'] at h; exact h
    linarith
  have hcorF : ∀ k : Fin 3, cornerAngle (F.target.pts (k + 1)) (F.target.pts k) (F.target.pts (k + 2)) =
      alphaT (u : ℝ) (v : ℝ) ∨ cornerAngle (F.target.pts (k + 1)) (F.target.pts k) (F.target.pts (k + 2)) =
      Real.pi - 2 * alphaT (u : ℝ) (v : ℝ) := by
    intro k
    rw [hT]
    fin_cases k
    · exact Or.inr hc0
    · exact Or.inl hc1
    · exact Or.inl hc2
  have hnoγ : ∀ (t : Fin N) (k : Fin 3), (F.tile t).pts k ∈ Set.range F.target.pts →
      (F.tile t).localAngle ((F.tile t).pts k) ≠ 2 * alphaT (u : ℝ) (v : ℝ) := by
    intro t k hk
    obtain ⟨j, hj⟩ := hk
    rw [← hj]
    exact Erdos634.Draft.ThmD.no_gamma_at_corner F.toDissection F.model hcong S.hirr hA0 hA1 hA2 S.hα h3α j
      (hcorF j) t
  have hapexQ : cornerAngle (F.target.pts (0 + 1)) (F.target.pts 0) (F.target.pts (0 + 2)) =
      Real.pi - 2 * alphaT (u : ℝ) (v : ℝ) := by
    rw [hT]; exact hc0
  have hres := leg_D1 S hRL' hLP' hLE' hang' hnoγ
    (fun n hn1 hnu hcp hst => by
      obtain ⟨f, hBr⟩ := brk_of_leg S hRL' hLP' hLE' hang'
      have hnW : n ≤ (legEdges e (mapSteps g r)).length := by
        rcases hst with h | ⟨o, ho, -⟩
        · exact h.le
        · by_contra hnot
          rw [List.getElem?_eq_none (by omega)] at ho
          exact absurd ho (by simp)
      exact apex_start S hBr hnoγ hapexQ hwedge hn1 hnu hnW hcp hst)
    (fun n hn1 hnu hn hcm hst => leg_K2_end ⟨S, Or.inr rfl⟩ (d2 := G * v * b) hd10
      (by simpa [hLdef] using hax) (by simpa [hLdef] using hsq) hbig hn1 (lt_trans hnu huv) hRL' hLP' hLE' hang'
      hn hcm hnoγ hst)
  rwa [legEdges_mapSteps] at hres

#print axioms leg_c_count_S2

end Erdos634.Draft.ThmDRun
