/-
Draft/F2Row357.lean -- the row `F₂` of the tile `(3, 5, 7)`.

For a tile with angles `α`, `π/3 − α`, `2π/3` and sides `K·3, K·5, K·7`, the shape `F₂` is the triangle with angles
`(2α, 2(π/3 − α), π/3)`.  `OtherSpectraFull.otherspectra` (clause `F₂`) says that a tiling of such a triangle has
`143 k²` tiles; `N143.dissection_143_unit` is a tiling with `143` tiles and `Ladder.ladder` scales it.  Hence

    theorem f2_row_357 (N : ℕ) :
        (∃ (D : CongruentDissection N) (α K : ℝ), 0 < K ∧ D.model.TwoPiThreeData α (K * 3) (K * 5) (K * 7) ∧
            TgtAngles D (2 * α) (2 * (π / 3 − α)) (α + (π / 3 − α)))
          ↔ ∃ k : ℕ, 0 < k ∧ N = 143 * k ^ 2

and the hypotheses of the clause `F₂` of the other-spectra classification hold on a real dissection
(`f2_witness_143`).

Attribution: the values `143 k²` with `k ≥ 2` are due to D. Paliy (corner construction, unrefereed) and those with
`k ∈ ⟨5, 7⟩` to Y. X. Zhang (arXiv:2512.22696); the necessity is Zhang's Lemma 5.  The case `k = 1` is the tiling
`N143.dissection_143_unit`.

No sorry, no native_decide.
-/
import Erdos634.Draft.N143
import Erdos634.Draft.OtherSpectraFull
import Erdos634.Draft.RWEast

open scoped Classical

namespace Erdos634.Draft.F2Row357

open Erdos634.Geometry Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional Erdos634.Draft.N143
open Erdos634.Draft.OtherSpectraFull Erdos634.Draft.FluxPaperWitness

/-- the angles of a triangle with sides `K·49, K·55, K·39` (opposite the vertices `0, 1, 2`), in terms of the
angle `α` with `cos α = 13/14` -/
theorem tgt_angles (T : Erdos634.Geometry.Tri) {K α : ℝ} (hK : 0 < K) (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi)
    (hcos : Real.cos α = 13 / 14)
    (h0 : T.oppLen 0 = K * 49) (h1 : T.oppLen 1 = K * 55) (h2 : T.oppLen 2 = K * 39) :
    T.angleAt 2 = 2 * α ∧ T.angleAt 1 = 2 * (Real.pi / 3 - α) ∧ T.angleAt 0 = α + (Real.pi / 3 - α) := by
  have hpi := Real.pi_pos
  have p0 : 0 < T.oppLen 0 := by rw [h0]; positivity
  have p1 : 0 < T.oppLen 1 := by rw [h1]; positivity
  have p2 : 0 < T.oppLen 2 := by rw [h2]; positivity
  have hα2 : α < Real.pi / 2 := by
    by_contra hge
    have hge' : Real.pi / 2 ≤ α := not_lt.mp hge
    have hle := Real.cos_nonpos_of_pi_div_two_le_of_le hge' (by linarith)
    rw [hcos] at hle
    norm_num at hle
  have c0 : Real.cos (T.angleAt 0) = 1 / 2 := by
    have h : Real.cos (T.angleAt 0) =
        (T.oppLen 1 ^ 2 + T.oppLen 2 ^ 2 - T.oppLen 0 ^ 2) / (2 * T.oppLen 1 * T.oppLen 2) :=
      cos_angleAt_opp T 0 p1 p2
    rw [h, h0, h1, h2, div_eq_iff (by positivity)]
    ring
  have a0 : T.angleAt 0 = Real.pi / 3 :=
    Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by positivity, by linarith⟩ (c0.trans Real.cos_pi_div_three.symm)
  have c2 : Real.cos (T.angleAt 2) = 71 / 98 := by
    have h : Real.cos (T.angleAt 2) =
        (T.oppLen 0 ^ 2 + T.oppLen 1 ^ 2 - T.oppLen 2 ^ 2) / (2 * T.oppLen 0 * T.oppLen 1) :=
      cos_angleAt_opp T 2 p0 p1
    rw [h, h0, h1, h2, div_eq_iff (by positivity)]
    ring
  have c2α : Real.cos (2 * α) = 71 / 98 := by
    rw [Real.cos_two_mul, hcos]; norm_num
  have a2 : T.angleAt 2 = 2 * α :=
    Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by linarith, by linarith⟩ (c2.trans c2α.symm)
  have hs := T.angleAt_sum
  refine ⟨a2, ?_, ?_⟩
  · linarith
  · rw [a0]; ring

/-- a tile with sides `K·3, K·5, K·7` (opposite the vertices `2, 0, 1`) is a `2π/3` tile; its angle opposite
`K·3` has cosine `13/14` and is not a rational multiple of `π` -/
theorem model_data (M : Erdos634.Geometry.Tri) {K : ℝ} (hK : 0 < K)
    (m2 : M.oppLen 2 = K * 3) (m0 : M.oppLen 0 = K * 5) (m1 : M.oppLen 1 = K * 7) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ Real.pi ∧ Real.cos α = 13 / 14 ∧ IrrPi α ∧
      M.TwoPiThreeData α (K * 3) (K * 5) (K * 7) := by
  obtain ⟨r0, r1, r2⟩ := rot_vals
  have o0 : M.oppLen (rot 0) = K * 3 := by rw [r0]; exact m2
  have o1 : M.oppLen (rot 1) = K * 5 := by rw [r1]; exact m0
  have o2 : M.oppLen (rot 2) = K * 7 := by rw [r2]; exact m1
  have cosα : Real.cos (M.angleAt (rot 0)) = 13 / 14 := by
    rw [cos_s0 M rot (by rw [o1]; positivity) (by rw [o2]; positivity), o0, o1, o2,
      div_eq_iff (by positivity)]
    ring
  refine ⟨M.angleAt (rot 0), (cornerAngle_mem' _ _ _).1, (cornerAngle_mem' _ _ _).2, cosα, ?_, ?_⟩
  · exact irrPi_of_cos _ (13 / 14) (by rw [cosα]; norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact tp_data M rot K 3 5 7 hK (by norm_num) (by norm_num) (by norm_num) o0 o1 o2

/-- **The hypotheses of the clause `F₂` of `prop:otherspectra` hold on a real dissection**: the kernel-checked
143-tiling has a `2π/3` tile with sides `3, 5, 7`, an angle `α ∉ ℚπ`, and a target with angles
`(2α, 2(π/3 − α), π/3)`. -/
theorem f2_witness_143 :
    ∃ (D : CongruentDissection 143) (α : ℝ), IrrPi α ∧ D.model.TwoPiThreeData α (1 * 3) (1 * 5) (1 * 7) ∧
      TgtAngles D (2 * α) (2 * (Real.pi / 3 - α)) (α + (Real.pi / 3 - α)) := by
  obtain ⟨D, t2, t1, t0, m2, m0, m1⟩ := dissection_143_unit
  obtain ⟨α, h0, hπ, hcos, hirr, hdata⟩ := model_data D.model one_pos
    (by rw [m2]; norm_num) (by rw [m0]; norm_num) (by rw [m1]; norm_num)
  obtain ⟨a2, a1, a0⟩ := tgt_angles D.target one_pos h0 hπ hcos
    (by rw [t0]; norm_num) (by rw [t1]; norm_num) (by rw [t2]; norm_num)
  obtain ⟨s0, s1, s2⟩ := swap_vals02
  exact ⟨D, α, hirr, hdata, Equiv.swap 0 2, by rw [s0]; exact a2, by rw [s1]; exact a1, by rw [s2]; exact a0⟩

/-- the clause `F₂` evaluated on the 143-tiling: `143 = 13 · 11 · k²` -/
theorem f2_clause_143 : ∃ k : ℕ, 0 < k ∧ (143 : ℕ) = (3 + 2 * 5) * (2 * 3 + 5) * k ^ 2 := by
  obtain ⟨D, α, -, hm, ht⟩ := f2_witness_143
  have hm' : D.model.TwoPiThreeData α (1 * ((3 : ℕ) : ℝ)) (1 * ((5 : ℕ) : ℝ)) (1 * ((7 : ℕ) : ℝ)) := by
    exact_mod_cast hm
  exact (otherspectra D one_pos 3 5 7 (by decide) (by norm_num) hm').2.1 ht

/-- **The row `F₂` of the tile `(3, 5, 7)` is complete**: a triangle with angles `(2α, 2(π/3 − α), π/3)` is cut into
`N` congruent triangles with angles `α, π/3 − α, 2π/3` and sides in the ratio `3 : 5 : 7` if and only if
`N = 143 k²` for some `k ≥ 1`. -/
theorem f2_row_357 (N : ℕ) :
    (∃ (D : CongruentDissection N) (α K : ℝ), 0 < K ∧ D.model.TwoPiThreeData α (K * 3) (K * 5) (K * 7) ∧
        TgtAngles D (2 * α) (2 * (Real.pi / 3 - α)) (α + (Real.pi / 3 - α)))
      ↔ ∃ k : ℕ, 0 < k ∧ N = 143 * k ^ 2 := by
  constructor
  · rintro ⟨D, α, K, hK, hm, ht⟩
    have hm' : D.model.TwoPiThreeData α (K * ((3 : ℕ) : ℝ)) (K * ((5 : ℕ) : ℝ)) (K * ((7 : ℕ) : ℝ)) := by
      exact_mod_cast hm
    obtain ⟨k, hk, hN⟩ := (otherspectra D hK 3 5 7 (by decide) (by norm_num) hm').2.1 ht
    exact ⟨k, hk, by rw [hN]⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨D, t2, t1, t0, m2, m0, m1⟩ := dissection_143_unit
    obtain ⟨hind, heta⟩ := Erdos634.Draft.RWEast.tri_eta D.target
    obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (D.target.pts 0) (D.target.pts 1) (D.target.pts 2)
      hind D heta k hk
    have hnum : k * k * 143 = 143 * k ^ 2 := by ring
    obtain ⟨E', hT', hM'⟩ := Erdos634.R143TilingBridge.exists_cast hnum E
    have hd := Erdos634.Draft.RWEast.dist_bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind k hk
    have hB : E'.target =
        Erdos634.Subdivision.bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind k hk :=
      hT'.trans hEt
    have t0' : dist (D.target.pts 1) (D.target.pts 2) = 49 := t0
    have t1' : dist (D.target.pts 2) (D.target.pts 0) = 55 := t1
    have t2' : dist (D.target.pts 0) (D.target.pts 1) = 39 := t2
    have hB0 : E'.target.oppLen 0 = (k : ℝ) * 49 := by
      rw [hB]
      have h := hd 1 2
      have h' : dist ((Erdos634.Subdivision.bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind k hk).pts 1)
          ((Erdos634.Subdivision.bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind k hk).pts 2)
          = (k : ℝ) * dist (D.target.pts 1) (D.target.pts 2) := h
      rw [t0'] at h'
      exact h'
    have hB1 : E'.target.oppLen 1 = (k : ℝ) * 55 := by
      rw [hB]
      have h := hd 2 0
      have h' : dist ((Erdos634.Subdivision.bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind k hk).pts 2)
          ((Erdos634.Subdivision.bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind k hk).pts 0)
          = (k : ℝ) * dist (D.target.pts 2) (D.target.pts 0) := h
      rw [t1'] at h'
      exact h'
    have hB2 : E'.target.oppLen 2 = (k : ℝ) * 39 := by
      rw [hB]
      have h := hd 0 1
      have h' : dist ((Erdos634.Subdivision.bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind k hk).pts 0)
          ((Erdos634.Subdivision.bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind k hk).pts 1)
          = (k : ℝ) * dist (D.target.pts 0) (D.target.pts 1) := h
      rw [t2'] at h'
      exact h'
    obtain ⟨α, h0, hπ, hcos, -, hdata⟩ := model_data D.model one_pos
      (by rw [m2]; norm_num) (by rw [m0]; norm_num) (by rw [m1]; norm_num)
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    obtain ⟨a2, a1, a0⟩ := tgt_angles E'.target hkR h0 hπ hcos hB0 hB1 hB2
    obtain ⟨s0, s1, s2⟩ := swap_vals02
    have hdataE : E'.model.TwoPiThreeData α (1 * 3) (1 * 5) (1 * 7) := by
      rw [hM', hEm]; exact hdata
    exact ⟨E', α, 1, one_pos, hdataE, Equiv.swap 0 2, by rw [s0]; exact a2, by rw [s1]; exact a1,
      by rw [s2]; exact a0⟩

end Erdos634.Draft.F2Row357

#print axioms Erdos634.Draft.F2Row357.f2_witness_143
#print axioms Erdos634.Draft.F2Row357.f2_row_357
