/-
Draft/IsoTransfer.lean -- the F1 -> Iso TRANSFER as a Lean theorem (Erdos #634; work item internal working notes).

SETTING (chart of `F1StripGeom`, tile `(u A, u B, u C)`, `C^2 = A^2 + A B + B^2`): `T_m = triR (u A) (u B) A B m` is the F1 triangle
`(m a b, m b c, m b (a+b))` (60 degrees at the origin `P0`, `P1 = (m B, 0)`, `P2 = (0, m (A+B))` in chart coordinates).  Let `K = m B`, `L = m (A+B)`.
`isoTri` is the triangle `Q P1 P2` with `Q = (0, -K)`; it is the union of `T_m` and the triangle `tau = P1 P0 Q` (120 degrees at `P0`, sides
`K a`, `K b`, `K c`), which is the tile scaled by `K`: tiled by `K * K` copies (`StripStepScaled.scaled_tiled`).

  `isoTiled_of_f1Tiled`   : `Tiled (triR .. m) model n  ->  Tiled (isoTri ..).carrier model (n + (m B)^2)`.
  `tileCount_iso_of_f1`   : an F1 tile count `B(A+B) m^2` gives the Iso tile count `B(A+2B) m^2` (angles alpha+... isosceles
                            `(m b c, m b c, m b (a + 2b))`).
  `iso_dissection`        : the same as a `CongruentDissection` with the three side lengths of the target.

This is the construction `(T)` of internal notes S1.5 (Zhang; Paliy: `F_m + (m b)-tile = I_m`), as implemented by `assemble.rs` of work item LIFT_FOLLOWON_2026-11-16.
CREDIT: Zhang (arXiv 2512.22696, Props 8, 9: F1 and Iso shapes, scaled-tile gluing), Paliy (transfers), the internal notes work item (S1.5), F1StripGeom/Lemma/Dissect of the project.
UNAUDITED beyond the internal build.  No sorry, no native_decide.
-/
import Erdos634.Draft.F1StripDissect
import Erdos634.Draft.StripStepScaled

namespace Erdos634.Draft.IsoTransfer

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling Erdos634.Draft.F1StripGeom
  Erdos634.Draft.F1StripLemma Erdos634.Draft.F1StripDissect Erdos634.Draft.StripStepScaled

noncomputable section

section pts
variable {a b : ℝ}

theorem pc_P1 (ha : 0 < a) (K : ℝ) : pc a (mkPt (K * a) 0) = K := by
  have := ha.ne'
  simp only [pc_mkPt]; field_simp; ring

theorem qc_P1 (K : ℝ) : qc b (mkPt (K * a) 0) = 0 := by simp [qc_mkPt]

theorem pc_P2 (ha : 0 < a) (L : ℝ) : pc a (mkPt (L * b / 2) (L * b * r3 / 2)) = 0 := by
  have := ha.ne'
  have := r3_ne
  simp only [pc_mkPt]; field_simp; ring

theorem qc_P2 (hb : 0 < b) (L : ℝ) : qc b (mkPt (L * b / 2) (L * b * r3 / 2)) = L := by
  have := hb.ne'
  have := r3_ne
  simp only [qc_mkPt]; field_simp

theorem pc_Q (ha : 0 < a) (K : ℝ) : pc a (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) = 0 := by
  have := ha.ne'
  have := r3_ne
  simp only [pc_mkPt]; field_simp; ring

theorem qc_Q (hb : 0 < b) (K : ℝ) : qc b (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) = -K := by
  have := hb.ne'
  have := r3_ne
  simp only [qc_mkPt]; field_simp

end pts

section tri
variable {a b : ℝ}

/-- the isosceles triangle `Q P1 P2` of the transfer: `Q = (0,-K)`, `P1 = (K,0)`, `P2 = (0,L)` in chart coordinates -/
def isoTri (ha : 0 < a) (hb : 0 < b) {K L : ℝ} (hK : 0 < K) (hL : 0 < L) : Tri :=
  mkTri (-(K * b / 2)) (-(K * b * r3 / 2)) (K * a) 0 (L * b / 2) (L * b * r3 / 2) (by
    have := r3_pos
    have h : det3 (-(K * b / 2)) (-(K * b * r3 / 2)) (K * a) 0 (L * b / 2) (L * b * r3 / 2) =
        (L + K) * b * r3 / 2 * (K * a) := by
      simp only [det3]; ring
    rw [h]; positivity)

/-- the triangle `tau = P1 P0 Q` (120 degrees at `P0`): the tile scaled by `K`, in the vertex order `(a, b, c)` of `cell1` -/
def tauTri (ha : 0 < a) (hb : 0 < b) {K : ℝ} (hK : 0 < K) : Tri :=
  mkTri (K * a) 0 0 0 (-(K * b / 2)) (-(K * b * r3 / 2)) (by
    have := r3_pos
    have h : det3 (K * a) 0 0 0 (-(K * b / 2)) (-(K * b * r3 / 2)) = K * a * (K * b * r3 / 2) := by
      simp only [det3]; ring
    rw [h]; positivity)

/-- the region `{p >= 0, p - q <= K, L p + K q <= K L}` -/
def isoR (a b K L : ℝ) : Set Plane :=
  {x | 0 ≤ pc a x ∧ pc a x - qc b x ≤ K ∧ L * pc a x + K * qc b x ≤ K * L}

theorem carrier_iso (ha : 0 < a) (hb : 0 < b) {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    (isoTri ha hb hK hL).carrier = isoR a b K L := by
  ext x
  constructor
  · intro hx
    have hv : ∀ k, 0 ≤ pc a ((isoTri ha hb hK hL).pts k) ∧
        pc a ((isoTri ha hb hK hL).pts k) - qc b ((isoTri ha hb hK hL).pts k) ≤ K ∧
        L * pc a ((isoTri ha hb hK hL).pts k) + K * qc b ((isoTri ha hb hK hL).pts k) ≤ K * L := by
      intro k
      fin_cases k
      · show 0 ≤ pc a (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) ∧
          pc a (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) - qc b (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) ≤ K ∧
          L * pc a (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) + K * qc b (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) ≤ K * L
        rw [pc_Q ha, qc_Q hb]
        refine ⟨le_refl _, by linarith, by nlinarith⟩
      · show 0 ≤ pc a (mkPt (K * a) 0) ∧ pc a (mkPt (K * a) 0) - qc b (mkPt (K * a) 0) ≤ K ∧
          L * pc a (mkPt (K * a) 0) + K * qc b (mkPt (K * a) 0) ≤ K * L
        rw [pc_P1 ha, qc_P1]
        refine ⟨hK.le, by linarith, by linarith⟩
      · show 0 ≤ pc a (mkPt (L * b / 2) (L * b * r3 / 2)) ∧
          pc a (mkPt (L * b / 2) (L * b * r3 / 2)) - qc b (mkPt (L * b / 2) (L * b * r3 / 2)) ≤ K ∧
          L * pc a (mkPt (L * b / 2) (L * b * r3 / 2)) + K * qc b (mkPt (L * b / 2) (L * b * r3 / 2)) ≤ K * L
        rw [pc_P2 ha, qc_P2 hb]
        refine ⟨le_refl _, by linarith, by linarith⟩
    have h1 := Erdos634.CertGeom.le_of_forall_pts_le (t := isoTri ha hb hK hL)
      (ch a b (-1) 0) (c := 0)
      (fun k => by rw [ch_apply]; obtain ⟨g, _, _⟩ := hv k; linarith) x hx
    have h2 := Erdos634.CertGeom.le_of_forall_pts_le (t := isoTri ha hb hK hL)
      (ch a b 1 (-1)) (c := K)
      (fun k => by rw [ch_apply]; obtain ⟨_, g, _⟩ := hv k; linarith) x hx
    have h3 := Erdos634.CertGeom.le_of_forall_pts_le (t := isoTri ha hb hK hL)
      (ch a b L K) (c := K * L)
      (fun k => by rw [ch_apply]; obtain ⟨_, _, g⟩ := hv k; linarith) x hx
    rw [ch_apply] at h1 h2 h3
    exact ⟨by linarith, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩
    set p := pc a x with hp
    set q := qc b x with hq
    have hKL : 0 < K + L := by linarith
    refine Erdos634.CertGeom.mem_carrier_of_combo _ x
      ![(K * L - p * L - K * q) / (K * (K + L)), p / K, (q + K - p) / (K + L)] ?_ ?_ ?_
    · show (K * L - p * L - K * q) / (K * (K + L)) + p / K + (q + K - p) / (K + L) = 1
      field_simp
      ring
    · intro k
      fin_cases k
      · show 0 ≤ (K * L - p * L - K * q) / (K * (K + L))
        apply div_nonneg (by linarith) (by positivity)
      · show 0 ≤ p / K
        positivity
      · show 0 ≤ (q + K - p) / (K + L)
        apply div_nonneg (by linarith) hKL.le
    · obtain ⟨c0, c1⟩ := coords ha hb x
      have := ha.ne'
      have := hb.ne'
      have := hK.ne'
      have := hL.ne'
      have := hKL.ne'
      have := r3_ne
      refine PiLp.ext ?_
      intro i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · show x 0 = (K * L - p * L - K * q) / (K * (K + L)) * (mkPt (-(K * b / 2)) (-(K * b * r3 / 2)) : Plane) 0 +
          p / K * (mkPt (K * a) 0 : Plane) 0 + (q + K - p) / (K + L) * (mkPt (L * b / 2) (L * b * r3 / 2) : Plane) 0
        simp only [mkPt_zero]
        rw [c0]; simp only [hp, hq]; field_simp; ring
      · show x 1 = (K * L - p * L - K * q) / (K * (K + L)) * (mkPt (-(K * b / 2)) (-(K * b * r3 / 2)) : Plane) 1 +
          p / K * (mkPt (K * a) 0 : Plane) 1 + (q + K - p) / (K + L) * (mkPt (L * b / 2) (L * b * r3 / 2) : Plane) 1
        simp only [mkPt_one]
        rw [c1]; simp only [hp, hq]; field_simp; ring

/-- the carrier of `tau` contains `{p >= 0, q <= 0, p - q <= K}` and lies in `{q <= 0}` -/
theorem tau_sub (ha : 0 < a) (hb : 0 < b) {K : ℝ} (hK : 0 < K) (x : Plane)
    (h1 : 0 ≤ pc a x) (h2 : qc b x ≤ 0) (h3 : pc a x - qc b x ≤ K) : x ∈ (tauTri ha hb hK).carrier := by
  set p := pc a x with hp
  set q := qc b x with hq
  refine Erdos634.CertGeom.mem_carrier_of_combo _ x ![p / K, (K - p + q) / K, -q / K] ?_ ?_ ?_
  · show p / K + (K - p + q) / K + -q / K = 1
    field_simp; ring
  · intro k
    fin_cases k
    · show 0 ≤ p / K
      positivity
    · show 0 ≤ (K - p + q) / K
      exact div_nonneg (by linarith) hK.le
    · show 0 ≤ -q / K
      exact div_nonneg (by linarith) hK.le
  · obtain ⟨c0, c1⟩ := coords ha hb x
    have := ha.ne'
    have := hb.ne'
    have := hK.ne'
    have := r3_ne
    refine PiLp.ext ?_
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · show x 0 = p / K * (mkPt (K * a) 0 : Plane) 0 + (K - p + q) / K * (mkPt 0 0 : Plane) 0 +
        -q / K * (mkPt (-(K * b / 2)) (-(K * b * r3 / 2)) : Plane) 0
      simp only [mkPt_zero]
      rw [c0]; simp only [hp, hq]; field_simp; ring
    · show x 1 = p / K * (mkPt (K * a) 0 : Plane) 1 + (K - p + q) / K * (mkPt 0 0 : Plane) 1 +
        -q / K * (mkPt (-(K * b / 2)) (-(K * b * r3 / 2)) : Plane) 1
      simp only [mkPt_one]
      rw [c1]; simp only [hp, hq]; field_simp; ring

theorem tau_nonpos (ha : 0 < a) (hb : 0 < b) {K : ℝ} (hK : 0 < K) :
    ∀ x ∈ (tauTri ha hb hK).carrier, qc b x ≤ 0 := by
  have hv : ∀ k, (ch a b 0 1) ((tauTri ha hb hK).pts k) ≤ 0 := by
    intro k
    rw [ch_apply]
    fin_cases k
    · show 0 * pc a (mkPt (K * a) 0) + 1 * qc b (mkPt (K * a) 0) ≤ 0
      rw [qc_P1]; simp
    · show 0 * pc a (mkPt 0 0) + 1 * qc b (mkPt 0 0) ≤ 0
      rw [qc_c1_0 hb]; simp
    · show 0 * pc a (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) + 1 * qc b (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) ≤ 0
      rw [qc_Q hb]; linarith
  intro x hx
  have := Erdos634.CertGeom.le_of_forall_pts_le (t := tauTri ha hb hK) (ch a b 0 1) (c := 0) hv x hx
  rwa [ch_apply, zero_mul, zero_add, one_mul] at this

/-- `tau` is the `K`-fold dilate of the model `cell1`: tiled by `K*K` copies -/
theorem tau_tiled (ha : 0 < a) (hb : 0 < b) (k : ℕ) (hk : 0 < k) (hK : 0 < (k : ℝ)) :
    Tiled (tauTri ha hb hK).carrier (cell1 ha hb) (k * k) := by
  refine scaled_tiled (cell1 ha hb) (tauTri ha hb hK) k hk ?_ ?_ ?_
  · have hk0 : (0 : ℝ) ≤ k := hK.le
    refine Erdos634.Draft.F1StripDissect.eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt ((k : ℝ) * a) 0) (mkPt 0 0) ^ 2 = ((k : ℝ) * dist (mkPt 0 0) (mkPt a 0)) ^ 2
    rw [mul_pow, dist_sq_mkPt, dist_sq_mkPt]; ring
  · refine Erdos634.Draft.F1StripDissect.eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt 0 0) (mkPt (-((k : ℝ) * b / 2)) (-((k : ℝ) * b * r3 / 2))) ^ 2 =
      ((k : ℝ) * dist (mkPt a 0) (mkPt (a + b / 2) (b * r3 / 2))) ^ 2
    have h3 := r3_sq
    rw [mul_pow, dist_sq_mkPt, dist_sq_mkPt]; linear_combination ((k : ℝ) * b / 2) ^ 2 * h3 - (k * (b / 2)) ^ 2 * h3 + 0
  · refine Erdos634.Draft.F1StripDissect.eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt (-((k : ℝ) * b / 2)) (-((k : ℝ) * b * r3 / 2))) (mkPt ((k : ℝ) * a) 0) ^ 2 =
      ((k : ℝ) * dist (mkPt (a + b / 2) (b * r3 / 2)) (mkPt 0 0)) ^ 2
    have h3 := r3_sq
    rw [mul_pow, dist_sq_mkPt, dist_sq_mkPt]
    linear_combination ((k : ℝ) * b / 2) ^ 2 * h3 - ((k : ℝ) * (b / 2)) ^ 2 * h3

end tri

section union
variable {a b : ℝ}

/-- the carrier of `tau` lies in `isoR` -/
theorem tau_sub_isoR (ha : 0 < a) (hb : 0 < b) {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    ∀ x ∈ (tauTri ha hb hK).carrier, x ∈ isoR a b K L := by
  have hv : ∀ k, 0 ≤ pc a ((tauTri ha hb hK).pts k) ∧
      pc a ((tauTri ha hb hK).pts k) - qc b ((tauTri ha hb hK).pts k) ≤ K ∧
      L * pc a ((tauTri ha hb hK).pts k) + K * qc b ((tauTri ha hb hK).pts k) ≤ K * L := by
    intro k
    fin_cases k
    · show 0 ≤ pc a (mkPt (K * a) 0) ∧ pc a (mkPt (K * a) 0) - qc b (mkPt (K * a) 0) ≤ K ∧
        L * pc a (mkPt (K * a) 0) + K * qc b (mkPt (K * a) 0) ≤ K * L
      rw [pc_P1 ha, qc_P1]
      refine ⟨hK.le, by linarith, by linarith⟩
    · show 0 ≤ pc a (mkPt 0 0) ∧ pc a (mkPt 0 0) - qc b (mkPt 0 0) ≤ K ∧
        L * pc a (mkPt 0 0) + K * qc b (mkPt 0 0) ≤ K * L
      rw [pc_c1_0 ha, qc_c1_0 hb]
      refine ⟨le_refl _, by linarith, by nlinarith⟩
    · show 0 ≤ pc a (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) ∧
        pc a (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) - qc b (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) ≤ K ∧
        L * pc a (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) + K * qc b (mkPt (-(K * b / 2)) (-(K * b * r3 / 2))) ≤ K * L
      rw [pc_Q ha, qc_Q hb]
      refine ⟨le_refl _, by linarith, by nlinarith⟩
  intro x hx
  have h1 := Erdos634.CertGeom.le_of_forall_pts_le (t := tauTri ha hb hK) (ch a b (-1) 0) (c := 0)
    (fun k => by rw [ch_apply]; obtain ⟨g, _, _⟩ := hv k; linarith) x hx
  have h2 := Erdos634.CertGeom.le_of_forall_pts_le (t := tauTri ha hb hK) (ch a b 1 (-1)) (c := K)
    (fun k => by rw [ch_apply]; obtain ⟨_, g, _⟩ := hv k; linarith) x hx
  have h3 := Erdos634.CertGeom.le_of_forall_pts_le (t := tauTri ha hb hK) (ch a b L K) (c := K * L)
    (fun k => by rw [ch_apply]; obtain ⟨_, _, g⟩ := hv k; linarith) x hx
  rw [ch_apply] at h1 h2 h3
  exact ⟨by linarith, by linarith, h3⟩

end union

/-- **THE TRANSFER (T).**  If the F1 triangle `T_m` (`m` natural) is tiled by `n` copies of the model `(u A, u B, u C)`, then the
isosceles triangle `Q P1 P2` is tiled by `n + (m B)^2` copies. -/
theorem isoTiled_of_f1Tiled {A B : ℕ} (hA : 0 < A) (hB : 0 < B) {u : ℝ} (hu : 0 < u) (m : ℕ) (hm : 0 < m) {n : ℕ}
    (h : Tiled (triR (u * A) (u * B) (A : ℝ) (B : ℝ) (m : ℝ)) (model hA hB hu) n) :
    ∃ (hK : (0 : ℝ) < ((m * B : ℕ) : ℝ)) (hL : (0 : ℝ) < ((m * (A + B) : ℕ) : ℝ)),
      Tiled (isoTri (scale_pos hA hu) (scale_pos hB hu) hK hL).carrier (model hA hB hu) (n + (m * B) * (m * B)) := by
  have ha := scale_pos hA hu
  have hb := scale_pos hB hu
  have hk0 : 0 < m * B := Nat.mul_pos hm hB
  have hK : (0 : ℝ) < ((m * B : ℕ) : ℝ) := Nat.cast_pos.mpr hk0
  have hL : (0 : ℝ) < ((m * (A + B) : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hm (by omega))
  refine ⟨hK, hL, ?_⟩
  have htau := tau_tiled ha hb (m * B) hk0 hK
  have hA' : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hB' : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have eK : (((m * B : ℕ)) : ℝ) = m * B := by push_cast; ring
  have eL : (((m * (A + B) : ℕ)) : ℝ) = m * (A + B) := by push_cast; ring
  have hu' := Tiled.union h htau (n := n + (m * B) * (m * B)) ?_ rfl
  · refine hu'.congr_set ?_
    rw [carrier_iso ha hb hK hL]
    ext x
    constructor
    · rintro (⟨h1, h2, h3⟩ | hx)
      · rw [eK, eL]
        have hp : pc (u * A) x ≤ m * B := by
          by_contra hcon
          push_neg at hcon
          nlinarith [mul_pos hB' hm', mul_nonneg hB'.le h2]
        refine ⟨h1, by linarith, ?_⟩
        have e1 : (m : ℝ) * (A + B) * pc (u * A) x + m * B * qc (u * B) x =
            m * ((A + B) * pc (u * A) x + B * qc (u * B) x) := by ring
        have e2 : (m : ℝ) * B * (m * (A + B)) = m * (m * (B * (A + B))) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left h3 hm'.le
      · exact tau_sub_isoR ha hb hK hL x hx
    · rintro ⟨h1, h2, h3⟩
      rw [eK] at h2
      rw [eK, eL] at h3
      rcases le_total 0 (qc (u * B) x) with hq | hq
      · left
        refine ⟨h1, hq, ?_⟩
        have e1 : (m : ℝ) * (A + B) * pc (u * A) x + m * B * qc (u * B) x =
            m * ((A + B) * pc (u * A) x + B * qc (u * B) x) := by ring
        have e2 : (m : ℝ) * B * (m * (A + B)) = m * (m * (B * (A + B))) := by ring
        rw [e1, e2] at h3
        exact le_of_mul_le_mul_left h3 hm'
      · right
        exact tau_sub ha hb hK x h1 hq (by rw [eK]; exact h2)
  · refine disj_of_sep (ch (u * A) (u * B) 0 (-1))
      (ch_linear_ne_zero ha hb (Or.inr (by norm_num))) 0 ?_ ?_
    · intro x hx
      rw [ch_apply]; have := hx.2.1; linarith
    · intro x hx
      rw [ch_apply]; have := tau_nonpos ha hb hK x hx; linarith

end

end Erdos634.Draft.IsoTransfer

#print axioms Erdos634.Draft.IsoTransfer.isoTiled_of_f1Tiled
