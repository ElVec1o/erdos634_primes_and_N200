import Mathlib.Tactic
import Erdos634.Draft.ThmDFrameLeg
import Erdos634.Draft.ThmDGeoLegs

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo): no dissection of `T(g)` by the `γ = 2α` tile when `(g-1) d < u`  (unit scale; )

`thmD_geo_unit` : a `CongruentDissection` whose model has the sides `u², d(2u+d), u(u+d)` and whose target has the legs `g u d(2u+d)` (two, meeting at the
apex `i+1`) and the base `g (u+d) d(2u+d)`, with `gcd(u, u+d) = 1`, `2 ≤ g`, `(g-1) d < u`, does not exist.  This is Theorem D' with D1 PROVED
(`leg_c_count_S1/S2`) instead of assumed: the α-apex leg (`alpha_apex_leg_pos`) has `q ≥ 1` hence `r < u` (`alpha_leg_word_bound`) and `r ≥ u` (D1).
-/

open scoped Classical

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg
  Erdos634.Draft.APrimeLegBuild

theorem fin3_pp (i : Fin 3) : i + 1 + 1 = i + 2 := by fin_cases i <;> decide

theorem thmD_geo_unit {N : ℕ} (D : CongruentDissection N) (u d g : ℕ) (i : Fin 3)
    (hd : 0 < d) (hu : 0 < u) (hcop : Nat.Coprime u (u + d)) (hg2 : 2 ≤ g) (hcond : (g - 1) * d < u)
    (hirr : Irrational (alphaT (u : ℝ) ((u + d : ℕ) : ℝ) / Real.pi))
    (hs0 : sideOpp D.model 0 = ((u * u : ℕ) : ℝ))
    (hs1 : sideOpp D.model 1 = ((d * (u + (u + d)) : ℕ) : ℝ))
    (hs2 : sideOpp D.model 2 = ((u * (u + d) : ℕ) : ℝ))
    (hL1 : dist (D.target.pts i) (D.target.pts (i + 1)) = ((g * u * (d * (u + (u + d))) : ℕ) : ℝ))
    (hL2 : dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) = ((g * u * (d * (u + (u + d))) : ℕ) : ℝ))
    (hbase : dist (D.target.pts (i + 2)) (D.target.pts i) = ((g * (u + d) * (d * (u + (u + d))) : ℕ) : ℝ))
    (hcA : cornerAngle (D.target.pts (i + 1)) (D.target.pts i) (D.target.pts (i + 2)) =
      alphaT (u : ℝ) ((u + d : ℕ) : ℝ))
    (hcApex : cornerAngle (D.target.pts (i + 1 + 1)) (D.target.pts (i + 1)) (D.target.pts (i + 1 + 2)) =
      Real.pi - 2 * alphaT (u : ℝ) ((u + d : ℕ) : ℝ))
    (hcB : cornerAngle (D.target.pts (i + 1 + 1 + 1)) (D.target.pts (i + 1 + 1)) (D.target.pts (i + 1 + 1 + 2)) =
      alphaT (u : ℝ) ((u + d : ℕ) : ℝ)) : False := by
  set v : ℕ := u + d with hv
  have huv : u < v := by omega
  have hv2 : v < 2 * u := by
    have : d ≤ (g - 1) * d := Nat.le_mul_of_pos_left d (by omega)
    omega
  have hco : Nat.Coprime u v := hcop
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have huvR : (u : ℝ) < v := by exact_mod_cast huv
  have hvR : (v : ℝ) < 2 * u := by exact_mod_cast hv2
  have hv0 : (0 : ℝ) < v := by linarith
  have hb : ((d * (u + (u + d)) : ℕ) : ℝ) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
    rw [hv]; push_cast; ring
  have hM0 : sideOpp D.model 0 = (u : ℝ) ^ 2 := by rw [hs0]; push_cast; ring
  have hM1 : sideOpp D.model 1 = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by rw [hs1, hb]
  have hM2 : sideOpp D.model 2 = (u : ℝ) * v := by rw [hs2]; rw [hv]; push_cast; ring
  obtain ⟨hA0, hA1, hA2⟩ := modelAngles_of_sidesT D.model hu huv hv2 hM0 hM1 hM2
  have hα : 0 < alphaT (u : ℝ) (v : ℝ) := alphaT_pos hu0 hvR hv0
  have h3α : 3 * alphaT (u : ℝ) (v : ℝ) < Real.pi := by
    have hβpos : 0 < Real.pi - 3 * alphaT (u : ℝ) (v : ℝ) := by
      have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
      have e' : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) =
          Real.pi - 3 * alphaT (u : ℝ) (v : ℝ) := hA1
      rw [e'] at h; exact h
    linarith
  have hcong : ∀ j, D.model.Congruent (D.tile j) := fun j => (D.tiles_congruent j).symm
  obtain ⟨t0, e0, r, hleg, he0, hel, hword, hq⟩ := Erdos634.Draft.ThmD.alpha_apex_leg_pos D.toDissection D.model hcong
    (alphaT (u : ℝ) (v : ℝ)) hirr hA0 hA1 hA2 hα h3α i hcA hcApex hcB (u * u) (d * (u + (u + d))) (u * (u + d))
    (g * u * (d * (u + (u + d)))) hs0 hs1 hs2 hL1 hL2
  have hRbound := Erdos634.Draft.ThmD.alpha_leg_word_bound hd hu hcop hcond hq hword
  have hG : (1 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 1 < g)
  have hLR : ((g * u * (d * (u + (u + d))) : ℕ) : ℝ) = (g : ℝ) * u * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) := by
    push_cast; rw [hv]; push_cast; ring
  have hBR : ((g * (u + d) * (d * (u + (u + d))) : ℕ) : ℝ) = (g : ℝ) * v * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) := by
    push_cast; rw [hv]; push_cast; ring
  have hf2i : i + 1 + 1 = i + 2 := fin3_pp i
  rcases hleg with ⟨hf, hpos, hend⟩ | ⟨hf, hpos, hend⟩
  · have hang := hf.2.1
    have hc := leg_c_count_S1 u v hu huv hv2 hco hirr (g : ℝ) hG D i hM0 hM1 hM2
      (by rw [hL1, hLR]) (by rw [← hf2i, hL2, hLR]) (by rw [hbase, hBR]) hf.1 hpos hend (by rw [hang, he0])
    omega
  · have hang := hf.2.1
    have hc := leg_c_count_S2 u v hu huv hv2 hco hirr (g : ℝ) hG D i hM0 hM1 hM2
      (by rw [hL1, hLR]) (by rw [← hf2i, hL2, hLR]) (by rw [hbase, hBR]) hf.1 hpos hend (by rw [hang, he0])
    omega

#print axioms thmD_geo_unit
end Erdos634.Draft.ThmDRun
