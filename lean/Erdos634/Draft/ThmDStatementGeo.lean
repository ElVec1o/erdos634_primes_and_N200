import Mathlib.Tactic
import Erdos634.Draft.ThmDStmt2
import Erdos634.Draft.ThmDGeoUnit
import Erdos634.Draft.ThmDScale
import Erdos634.Draft.G3CAng

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo): `ThmDStatement'` UNCONDITIONALLY  

`thmDStatement_geo : ThmDStatement'` is `ThmDStmt2.thmDStatement_of_D1` with the hypothesis `D1Spec` replaced by its proof: the dissection is scaled by `1/s`
to unit scale (`scaleDissection`) and `thmD_geo_unit` (D1 for the positioned α-apex leg + the word bound) gives `False`.  The reduction `GPair` data -> `(u,d,g,s)`
is the one of `thmDStatement_of_D1`.
-/

open scoped Classical

namespace Erdos634.Draft.ThmD

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.ThmC Erdos634.SssCongruent Erdos634.Draft.TheoremPConditional
  Erdos634.Realizable

/-- **Theorem D' without the irrationality hypothesis**: `IrrPi α` is derived (Niven, `G3CAng.irrPi_of_cos`) from
`cos α = v/(2u)`, `u < v < 2u` (the model triangle has sides `u², v²−u², uv`). -/
theorem thmD_standalone (N M M' : ℕ) (hM : 0 < M) (hMM' : M * M' = N) (hlt : 3 * M < M') (hpar : M % 2 = M' % 2)
    (hchk : thmDChk M M') (D : CongruentDissection N) {α a b c : ℝ} (hdata : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α)
    (hX1 : ((M : ℤ) : ℝ) * (a + c) = D.target.oppLen 0) (hX2 : ((M' : ℤ) : ℝ) * (c - a) = D.target.oppLen 0) :
    False := by
  obtain ⟨g, u, d, hg2, hd, hdu, hcop, hMg, hM'g, hcond⟩ := thmDChk_param hM hlt hpar hchk
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := hdata
  have hdata' : D.model.TwoAlphaData α a b c := ⟨σ, h0, o0, h1, o1, h2, o2⟩
  obtain ⟨κ, hκ1, hκ2, ha, hX, hc, hb, hY, hX1'⟩ := Row4.sides D hdata' hA hB
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hMR : ((M : ℤ) : ℝ) = (g : ℝ) * d := by rw [hMg]; push_cast; ring
  have hM'R : ((M' : ℤ) : ℝ) = (g : ℝ) * (u + (u + d)) := by rw [hM'g]; push_cast; ring
  rw [hMR] at hX1
  rw [hM'R] at hX2
  -- the ratio  u c = (u+d) a
  have hratio : (u : ℝ) * c = ((u : ℝ) + d) * a := by
    have e : (g : ℝ) * (((d : ℝ) * (a + c)) - ((u + (u + d)) * (c - a))) = 0 := by linear_combination hX1 - hX2
    have e2 := (mul_eq_zero.mp e).resolve_left hg0.ne'
    linear_combination (-1 / 2 : ℝ) * e2
  set s : ℝ := a / (u : ℝ) ^ 2 with hs
  have hspos : 0 < s := by positivity
  have has : a = s * ((u * u : ℕ) : ℝ) := by rw [hs]; push_cast; field_simp
  have hcs : c = s * ((u * (u + d) : ℕ) : ℝ) := by
    have : (u : ℝ) * c = (u : ℝ) * (s * ((u * (u + d) : ℕ) : ℝ)) := by
      rw [hratio, has]; push_cast; ring
    exact mul_left_cancel₀ hu0.ne' this
  have hab : a * b = c ^ 2 - a ^ 2 := by rw [hc, hb]; ring
  have hbs : b = s * ((d * (u + (u + d)) : ℕ) : ℝ) := by
    have : (s * (u : ℝ) ^ 2) * b = (s * (u : ℝ) ^ 2) * (s * ((d * (u + (u + d)) : ℕ) : ℝ)) := by
      have e1 : a = s * (u : ℝ) ^ 2 := by rw [has]; push_cast; ring
      have e2 : c = s * ((u : ℝ) * (u + d)) := by rw [hcs]; push_cast; ring
      rw [e1, e2] at hab
      push_cast
      linear_combination hab
    exact mul_left_cancel₀ (by positivity) this
  have hXs : D.target.oppLen 0 = s * ((g * u * (d * (u + (u + d))) : ℕ) : ℝ) := by
    rw [← hX1, has, hcs]; push_cast; ring
  -- the relabelled model
  have hα : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβ : 0 < Real.pi - 3 * α := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hcong : ∀ j, (permTri D.model σ).Congruent (D.tile j) :=
    fun j => (congruent_permTri D.model σ).trans (D.tiles_congruent j).symm
  have hA0 : cornerAngle ((permTri D.model σ).pts 1) ((permTri D.model σ).pts 0) ((permTri D.model σ).pts 2) = α := by
    have := angleAt_permTri D.model σ 0
    rw [h0] at this
    exact this
  have hA1 : cornerAngle ((permTri D.model σ).pts 2) ((permTri D.model σ).pts 1) ((permTri D.model σ).pts 0)
      = Real.pi - 3 * α := by
    have := angleAt_permTri D.model σ 1
    rw [h1] at this
    exact this
  have hA2 : cornerAngle ((permTri D.model σ).pts 0) ((permTri D.model σ).pts 2) ((permTri D.model σ).pts 1)
      = 2 * α := by
    have := angleAt_permTri D.model σ 2
    rw [h2] at this
    exact this
  have hs0 : sideOpp (permTri D.model σ) 0 = s * ((u * u : ℕ) : ℝ) := by
    rw [sideOpp_permTri, o0, has]
  have hs1 : sideOpp (permTri D.model σ) 1 = s * ((d * (u + (u + d)) : ℕ) : ℝ) := by
    rw [sideOpp_permTri, o1, hbs]
  have hs2 : sideOpp (permTri D.model σ) 2 = s * ((u * (u + d) : ℕ) : ℝ) := by
    rw [sideOpp_permTri, o2, hcs]
  have hC : D.target.angleAt 2 = Real.pi - 2 * α := by
    have hsum := D.target.angleAt_sum; rw [hA, hB] at hsum; linarith
  have h3α : 3 * α < Real.pi := by linarith
  have hL1 : dist (D.target.pts 1) (D.target.pts (1 + 1)) = s * ((g * u * (d * (u + (u + d))) : ℕ) : ℝ) := by
    rw [← hXs]; rfl
  have hL2 : dist (D.target.pts (1 + 1)) (D.target.pts (1 + 1 + 1)) = s * ((g * u * (d * (u + (u + d))) : ℕ) : ℝ) := by
    rw [← hXs, ← hX1']; rfl
  -- unit scale
  have hr : (1 / s) ≠ 0 := by positivity
  have hr0 : 0 < 1 / s := by positivity
  let D' : CongruentDissection N := ⟨D.toDissection, permTri D.model σ, fun j => (hcong j).symm⟩
  let D1 : CongruentDissection N := scaleDissection (D.target.pts 0) (1 / s) hr D'
  have hD1t : ∀ k, D1.target.pts k = homothetyEquiv (D.target.pts 0) (1 / s) hr (D.target.pts k) := fun k =>
    scaleDissection_target_pts _ _ hr D' k
  have hdist : ∀ a b, dist (D1.target.pts a) (D1.target.pts b) = (1 / s) * dist (D.target.pts a) (D.target.pts b) := by
    intro a b
    rw [hD1t, hD1t, homothetyEquiv_dist, abs_of_pos hr0]
  have hang : ∀ a b c, cornerAngle (D1.target.pts a) (D1.target.pts b) (D1.target.pts c) =
      cornerAngle (D.target.pts a) (D.target.pts b) (D.target.pts c) := by
    intro a b c
    rw [hD1t, hD1t, hD1t]
    exact Erdos634.Draft.ThmDRun.angle_homothety _ _ hr hr0 _ _ _
  have hside : ∀ j, sideOpp D1.model j = (1 / s) * sideOpp (permTri D.model σ) j := by
    intro j
    have := Erdos634.Draft.ThmDRun.sideOpp_scale (D.target.pts 0) (1 / s) hr (permTri D.model σ) j
    rw [abs_of_pos hr0] at this
    exact this
  have hs0' : sideOpp D1.model 0 = (u * u : ℕ) := by rw [hside, hs0]; field_simp
  have hs1' : sideOpp D1.model 1 = (d * (u + (u + d)) : ℕ) := by rw [hside, hs1]; field_simp
  have hs2' : sideOpp D1.model 2 = (u * (u + d) : ℕ) := by rw [hside, hs2]; field_simp
  have hL1' : dist (D1.target.pts 1) (D1.target.pts (1 + 1)) = ((g * u * (d * (u + (u + d))) : ℕ) : ℝ) := by
    rw [hdist, hL1]; field_simp
  have hL2' : dist (D1.target.pts (1 + 1)) (D1.target.pts (1 + 1 + 1)) = ((g * u * (d * (u + (u + d))) : ℕ) : ℝ) := by
    rw [hdist, hL2]; field_simp
  -- the base
  have hbase : dist (D.target.pts (1 + 2)) (D.target.pts 1) = s * ((g * (u + d) * (d * (u + (u + d))) : ℕ) : ℝ) := by
    have e1 : dist (D.target.pts (1 + 2)) (D.target.pts 1) = D.target.oppLen 2 := by
      show dist (D.target.pts (1 + 2)) (D.target.pts 1) = dist (D.target.pts (2 + 1)) (D.target.pts (2 + 2))
      rfl
    rw [e1, hY, hXs]
    have hκ : 2 * κ = ((u : ℝ) + d) / u := by
      have h1 : 2 * κ * a = c := hc.symm
      rw [hcs, has] at h1
      push_cast at h1
      have h2 : s * u * (2 * κ * u - (u + d)) = 0 := by linear_combination h1
      have h3 : 2 * κ * u - (u + d) = 0 :=
        (mul_eq_zero.mp h2).resolve_left (mul_ne_zero hspos.ne' hu0.ne')
      rw [eq_div_iff hu0.ne']
      linarith
    rw [hκ]; push_cast; field_simp
  have hbase' : dist (D1.target.pts (1 + 2)) (D1.target.pts 1) = ((g * (u + d) * (d * (u + (u + d))) : ℕ) : ℝ) := by
    rw [hdist, hbase]; field_simp
  -- the angle of the unit model, and the irrationality of `alphaT`
  have hM0 : sideOpp D1.model 0 = (u : ℝ) ^ 2 := by rw [hs0']; push_cast; ring
  have hM1 : sideOpp D1.model 1 = ((u + d : ℕ) : ℝ) ^ 2 - (u : ℝ) ^ 2 := by rw [hs1']; push_cast; ring
  have hM2 : sideOpp D1.model 2 = (u : ℝ) * ((u + d : ℕ) : ℝ) := by rw [hs2']; push_cast; ring
  have huv : u < u + d := by omega
  have hv2 : u + d < 2 * u := by
    have : d ≤ (g - 1) * d := Nat.le_mul_of_pos_left d (by omega)
    omega
  have hmodang := Erdos634.Draft.ThmDRun.modelAngles_of_sidesT D1.model (by omega : 0 < u) huv hv2 hM0 hM1 hM2
  have hαeq : α = Erdos634.Draft.ThmDRun.alphaT (u : ℝ) ((u + d : ℕ) : ℝ) := by
    rw [← hmodang.1]
    have := hang  -- unused
    have e1 : cornerAngle (D1.model.pts 1) (D1.model.pts 0) (D1.model.pts 2) =
        cornerAngle ((permTri D.model σ).pts 1) ((permTri D.model σ).pts 0) ((permTri D.model σ).pts 2) := by
      show cornerAngle (homothetyEquiv (D.target.pts 0) (1 / s) hr ((permTri D.model σ).pts 1)) _ _ = _
      exact Erdos634.Draft.ThmDRun.angle_homothety _ _ hr hr0 _ _ _
    rw [e1, hA0]
  have hirr' : Irrational (Erdos634.Draft.ThmDRun.alphaT (u : ℝ) ((u + d : ℕ) : ℝ) / Real.pi) := by
    have huR : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
    have huvR : (u : ℝ) < ((u + d : ℕ) : ℝ) := by exact_mod_cast huv
    have hv2R : ((u + d : ℕ) : ℝ) < 2 * u := by exact_mod_cast hv2
    have hcos := Erdos634.Draft.ThmDRun.cos_alphaT huR huvR hv2R
    have huQ : (0 : ℚ) < u := by exact_mod_cast (by omega : 0 < u)
    have huvQ : (u : ℚ) < ((u + d : ℕ) : ℚ) := by exact_mod_cast huv
    have hv2Q : ((u + d : ℕ) : ℚ) < 2 * u := by exact_mod_cast hv2
    have hpos : (0 : ℚ) < ((u + d : ℕ) : ℚ) / (2 * u) := by positivity
    have hirrpi := Erdos634.Draft.G3CAng.irrPi_of_cos _ (((u + d : ℕ) : ℚ) / (2 * u))
      (by rw [hcos]; push_cast; rfl) hpos.ne'
      (by intro h; rw [div_eq_one_iff_eq (by positivity)] at h; linarith)
      (by intro h; linarith)
      (by intro h; rw [div_eq_iff (by positivity)] at h; linarith)
      (by intro h; linarith)
    exact irrational_of_irrPi hirrpi
  have hcA' : cornerAngle (D1.target.pts (1 + 1)) (D1.target.pts 1) (D1.target.pts (1 + 2)) =
      Erdos634.Draft.ThmDRun.alphaT (u : ℝ) ((u + d : ℕ) : ℝ) := by
    rw [hang, ← hαeq]; exact hB
  have hcApex' : cornerAngle (D1.target.pts (1 + 1 + 1)) (D1.target.pts (1 + 1)) (D1.target.pts (1 + 1 + 2)) =
      Real.pi - 2 * Erdos634.Draft.ThmDRun.alphaT (u : ℝ) ((u + d : ℕ) : ℝ) := by
    rw [hang, ← hαeq]; exact hC
  have hcB' : cornerAngle (D1.target.pts (1 + 1 + 1 + 1)) (D1.target.pts (1 + 1 + 1)) (D1.target.pts (1 + 1 + 1 + 2)) =
      Erdos634.Draft.ThmDRun.alphaT (u : ℝ) ((u + d : ℕ) : ℝ) := by
    rw [hang, ← hαeq]; exact hA
  exact Erdos634.Draft.ThmDRun.thmD_geo_unit D1 u d g 1 hd (by omega) hcop hg2 hcond hirr' hs0' hs1' hs2' hL1' hL2'
    hbase' hcA' hcApex' hcB'

end Erdos634.Draft.ThmD

namespace Erdos634.Draft.ThmD
theorem thmDStatement_geo : ThmDStatement' := by
  intro N M M' hM hMM' hlt hpar hchk D α a b c _ hdata hA hB hX1 hX2
  exact thmD_standalone N M M' hM hMM' hlt hpar hchk D hdata hA hB hX1 hX2
end Erdos634.Draft.ThmD

#print axioms Erdos634.Draft.ThmD.thmD_standalone
#print axioms Erdos634.Draft.ThmD.thmDStatement_geo
