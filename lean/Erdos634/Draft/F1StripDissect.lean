/-
Draft/F1StripDissect.lean -- from a region tiling of `T_m` to a `CongruentDissection` of an actual
triangle, with its side lengths (Erdos #634, F1 strip lemma).

BRIDGE.  `T_m` is the carrier of the triangle `targTri` with vertices `(0,0)`, `(m B a, 0)`,
`(m (A+B) b / 2, m (A+B) b sqrt3 / 2)` (`a = u A`, `b = u B` the chart scales), whose sides are
`m u A B`, `m u B C`, `m u B (A+B)` where `C^2 = A^2 + A B + B^2`.  A tiling `Tiled (triR ..) M n` is
then literally a `RTiling targTri.carrier M n`, which `RegionTiling.toCD` turns into a
`CongruentDissection n` (target `targTri`, model `M`).  The model `cell1` has sides `u A`, `u B`, `u C`.

CREDIT: Yan Zhang (arXiv 2512.22696) for the family; Laczkovich for strip decompositions.
UNAUDITED beyond the internal build.  No sorry, no native_decide.
-/
import Erdos634.Draft.F1StripLemma

namespace Erdos634.Draft.F1StripDissect

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling Erdos634.Draft.F1StripGeom
  Erdos634.Draft.F1StripLemma

noncomputable section

theorem r3_sq' : r3 ^ 2 = 3 := by have := r3_sq; nlinarith

theorem eq_of_sq {d c : ℝ} (hd : 0 ≤ d) (hc : 0 ≤ c) (h : d ^ 2 = c ^ 2) : d = c := by
  have h2 : (d - c) * (d + c) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · linarith

section targ
variable {a b A B : ℝ}

/-- the triangle `T_m` as a `Tri` -/
def targTri (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B) (m : ℝ) (hm : 0 < m) : Tri :=
  mkTri 0 0 (m * B * a) 0 (m * (A + B) * b / 2) (m * (A + B) * b * r3 / 2) (by
    have := r3_pos
    simp only [det3]
    have : 0 < m * B * a * (m * (A + B) * b * r3 / 2) := by positivity
    nlinarith)

theorem pc_t1 (ha : 0 < a) (m : ℝ) : pc a (mkPt (m * B * a) 0) = m * B := by
  have := ha.ne'
  simp only [pc_mkPt]; field_simp; ring

theorem qc_t1 (m : ℝ) : qc b (mkPt (m * B * a) 0) = 0 := by simp [qc_mkPt]

theorem pc_t2 (ha : 0 < a) (m : ℝ) :
    pc a (mkPt (m * (A + B) * b / 2) (m * (A + B) * b * r3 / 2)) = 0 := by
  have := ha.ne'
  have := r3_ne
  simp only [pc_mkPt]; field_simp; ring

theorem qc_t2 (hb : 0 < b) (m : ℝ) :
    qc b (mkPt (m * (A + B) * b / 2) (m * (A + B) * b * r3 / 2)) = m * (A + B) := by
  have := hb.ne'
  have := r3_ne
  simp only [qc_mkPt]; field_simp

/-- **The carrier of the triangle is the region `T_m`.** -/
theorem carrier_targ (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B) (m : ℝ) (hm : 0 < m) :
    (targTri ha hb hA hB m hm).carrier = triR a b A B m := by
  ext x
  constructor
  · intro hx
    have hv : ∀ k, 0 ≤ pc a ((targTri ha hb hA hB m hm).pts k) ∧
        0 ≤ qc b ((targTri ha hb hA hB m hm).pts k) ∧
        (A + B) * pc a ((targTri ha hb hA hB m hm).pts k) +
          B * qc b ((targTri ha hb hA hB m hm).pts k) ≤ m * (B * (A + B)) := by
      intro k
      fin_cases k
      · show 0 ≤ pc a (mkPt 0 0) ∧ 0 ≤ qc b (mkPt 0 0) ∧
          (A + B) * pc a (mkPt 0 0) + B * qc b (mkPt 0 0) ≤ m * (B * (A + B))
        rw [pc_c1_0 ha, qc_c1_0 hb]
        refine ⟨le_refl _, le_refl _, ?_⟩
        have : 0 < m * (B * (A + B)) := by positivity
        linarith
      · show 0 ≤ pc a (mkPt (m * B * a) 0) ∧ 0 ≤ qc b (mkPt (m * B * a) 0) ∧
          (A + B) * pc a (mkPt (m * B * a) 0) + B * qc b (mkPt (m * B * a) 0) ≤ m * (B * (A + B))
        rw [pc_t1 ha, qc_t1]
        refine ⟨by positivity, le_refl _, ?_⟩
        linarith
      · show 0 ≤ pc a (mkPt (m * (A + B) * b / 2) (m * (A + B) * b * r3 / 2)) ∧
          0 ≤ qc b (mkPt (m * (A + B) * b / 2) (m * (A + B) * b * r3 / 2)) ∧
          (A + B) * pc a (mkPt (m * (A + B) * b / 2) (m * (A + B) * b * r3 / 2)) +
            B * qc b (mkPt (m * (A + B) * b / 2) (m * (A + B) * b * r3 / 2)) ≤ m * (B * (A + B))
        rw [pc_t2 ha, qc_t2 hb]
        refine ⟨le_refl _, by positivity, ?_⟩
        linarith
    have h1 := Erdos634.CertGeom.le_of_forall_pts_le (t := targTri ha hb hA hB m hm)
      (ch a b (-1) 0) (c := 0)
      (fun k => by rw [ch_apply]; obtain ⟨g, _, _⟩ := hv k; linarith) x hx
    have h2 := Erdos634.CertGeom.le_of_forall_pts_le (t := targTri ha hb hA hB m hm)
      (ch a b 0 (-1)) (c := 0)
      (fun k => by rw [ch_apply]; obtain ⟨_, g, _⟩ := hv k; linarith) x hx
    have h3 := Erdos634.CertGeom.le_of_forall_pts_le (t := targTri ha hb hA hB m hm)
      (ch a b (A + B) B) (c := m * (B * (A + B)))
      (fun k => by rw [ch_apply]; obtain ⟨_, _, g⟩ := hv k; linarith) x hx
    rw [ch_apply] at h1 h2 h3
    exact ⟨by linarith, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩
    set p := pc a x with hp
    set q := qc b x with hq
    have hmb : 0 < m * B := by positivity
    have hma : 0 < m * (A + B) := by positivity
    refine Erdos634.CertGeom.mem_carrier_of_combo _ x ![1 - p / (m * B) - q / (m * (A + B)),
      p / (m * B), q / (m * (A + B))] ?_ ?_ ?_
    · show (1 - p / (m * B) - q / (m * (A + B))) + p / (m * B) + q / (m * (A + B)) = 1
      ring
    · intro k
      fin_cases k
      · show 0 ≤ 1 - p / (m * B) - q / (m * (A + B))
        have e : 1 - p / (m * B) - q / (m * (A + B)) =
            (m * (B * (A + B)) - ((A + B) * p + B * q)) / (m * (B * (A + B))) := by
          field_simp
          ring
        rw [e]
        apply div_nonneg (by linarith) (by positivity)
      · show 0 ≤ p / (m * B)
        positivity
      · show 0 ≤ q / (m * (A + B))
        positivity
    · obtain ⟨c0, c1⟩ := coords ha hb x
      have := ha.ne'
      have := hb.ne'
      have := hm.ne'
      have := hA.ne'
      have := hB.ne'
      have := r3_ne
      have hab : A + B ≠ 0 := by positivity
      refine PiLp.ext ?_
      intro i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · show x 0 = (1 - p / (m * B) - q / (m * (A + B))) * (mkPt 0 0 : Plane) 0 +
          p / (m * B) * (mkPt (m * B * a) 0 : Plane) 0 +
          q / (m * (A + B)) * (mkPt (m * (A + B) * b / 2) (m * (A + B) * b * r3 / 2) : Plane) 0
        simp only [mkPt_zero]
        rw [c0]; simp only [hp, hq]; field_simp; ring
      · show x 1 = (1 - p / (m * B) - q / (m * (A + B))) * (mkPt 0 0 : Plane) 1 +
          p / (m * B) * (mkPt (m * B * a) 0 : Plane) 1 +
          q / (m * (A + B)) * (mkPt (m * (A + B) * b / 2) (m * (A + B) * b * r3 / 2) : Plane) 1
        simp only [mkPt_one]
        rw [c1]; simp only [hp, hq]; field_simp; ring

end targ

section sides
variable {A B C : ℕ}

/-- **The shape of the dissection of `T_m`**: target sides `m u A B`, `m u B C`, `m u B (A+B)`, tile sides
`u A`, `u B`, `u C`, where `C² = A² + A B + B²`. -/
theorem dissection_of_tiled (hA : 0 < A) (hB : 0 < B) {u : ℝ} (hu : 0 < u)
    (hC : C * C = A * A + A * B + B * B)
    (m : ℕ) (hm : 0 < m) (n : ℕ)
    (h : Tiled (triR (u * A) (u * B) (A : ℝ) (B : ℝ) (m : ℝ)) (model hA hB hu) n) :
    ∃ D : CongruentDissection n,
      dist (D.target.pts 0) (D.target.pts 1) = (m : ℝ) * u * A * B ∧
      dist (D.target.pts 1) (D.target.pts 2) = (m : ℝ) * u * B * C ∧
      dist (D.target.pts 2) (D.target.pts 0) = (m : ℝ) * u * B * ((A : ℝ) + B) ∧
      dist (D.model.pts 0) (D.model.pts 1) = u * A ∧
      dist (D.model.pts 1) (D.model.pts 2) = u * B ∧
      dist (D.model.pts 2) (D.model.pts 0) = u * C := by
  have ha := scale_pos hA hu
  have hb := scale_pos hB hu
  have hA' := real_pos hA
  have hB' := real_pos hB
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hC' : (C : ℝ) * C = (A : ℝ) * A + (A : ℝ) * B + (B : ℝ) * B := by exact_mod_cast hC
  obtain ⟨R⟩ := h
  have R' : RTiling (targTri ha hb hA' hB' (m : ℝ) hm').carrier (model hA hB hu) n :=
    (carrier_targ ha hb hA' hB' (m : ℝ) hm').symm ▸ R
  refine ⟨toCD R', ?_⟩
  have hr3 := r3_sq'
  have hr3p := r3_pos
  show dist ((targTri ha hb hA' hB' (m : ℝ) hm').pts 0) ((targTri ha hb hA' hB' (m : ℝ) hm').pts 1) = _ ∧
    dist ((targTri ha hb hA' hB' (m : ℝ) hm').pts 1) ((targTri ha hb hA' hB' (m : ℝ) hm').pts 2) = _ ∧
    dist ((targTri ha hb hA' hB' (m : ℝ) hm').pts 2) ((targTri ha hb hA' hB' (m : ℝ) hm').pts 0) = _ ∧
    dist ((model hA hB hu).pts 0) ((model hA hB hu).pts 1) = _ ∧
    dist ((model hA hB hu).pts 1) ((model hA hB hu).pts 2) = _ ∧
    dist ((model hA hB hu).pts 2) ((model hA hB hu).pts 0) = _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt 0 0) (mkPt ((m : ℝ) * B * (u * A)) 0) ^ 2 = _
    rw [dist_sq_mkPt]; ring
  · refine eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt ((m : ℝ) * B * (u * A)) 0)
      (mkPt ((m : ℝ) * (A + B) * (u * B) / 2) ((m : ℝ) * (A + B) * (u * B) * r3 / 2)) ^ 2 = _
    rw [dist_sq_mkPt]
    linear_combination (((m : ℝ) * u * B) * (A + B) / 2) ^ 2 * hr3 - ((m : ℝ) * u * B) ^ 2 * hC'
  · refine eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt ((m : ℝ) * (A + B) * (u * B) / 2) ((m : ℝ) * (A + B) * (u * B) * r3 / 2))
      (mkPt 0 0) ^ 2 = _
    rw [dist_sq_mkPt]
    linear_combination ((m : ℝ) * (A + B) * (u * B) / 2) ^ 2 * hr3
  · refine eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt 0 0) (mkPt (u * (A : ℝ)) 0) ^ 2 = _
    rw [dist_sq_mkPt]; ring
  · refine eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt (u * (A : ℝ)) 0) (mkPt (u * (A : ℝ) + u * B / 2) (u * (B : ℝ) * r3 / 2)) ^ 2 = _
    rw [dist_sq_mkPt]
    linear_combination ((u * (B : ℝ)) / 2) ^ 2 * hr3
  · refine eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt (u * (A : ℝ) + u * B / 2) (u * (B : ℝ) * r3 / 2)) (mkPt 0 0) ^ 2 = _
    rw [dist_sq_mkPt]
    linear_combination ((u * (B : ℝ)) / 2) ^ 2 * hr3 - u ^ 2 * hC'

end sides

end

end Erdos634.Draft.F1StripDissect

#print axioms Erdos634.Draft.F1StripDissect.dissection_of_tiled
