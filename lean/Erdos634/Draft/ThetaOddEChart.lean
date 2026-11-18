-- Draft/ThetaOddEChart.lean -- ODD-E formalization, module 7: the chart (u,v) of Rh, hexagon regions, piece builders, hexagon joins.
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
The chart of the notch parallelogram Rh (PROOF.md S1.3, RESULT.md S0): `(u,v) -> apex point (M - u/F + F v/b, K - F v/b)`, `K = k`, `b = F^2-E^2`.
Real squared length of a chart vector `(du,dv)`: `Qc = b^2 du^2 - E^2 b du dv + (E F)^2 dv^2` (PROOF.md Lemma 1.A).
Every piece of the R group is a lattice parallelogram or a lattice triangle whose sides lie in the chart directions `u`, `v`, `u+v = const`;
it lies in a "hexagon" `ulo <= u <= uhi, vlo <= v <= vhi, slo <= u+v <= shi` (`HexS`).  Disjointness of pieces and containment in the
pentagon `rReg2` are read off the hexagons (`hexS_disj`, `hexS_sub_rReg2`).  Degenerate pieces (zero cell count) are the empty family.
The notch construction is the project's (Bonfioli); the first instance `theta_13(3,4)` was found by computer search on 2026-11-15; the
pieces are the AI assistant's Theorem B (internal working notes S2), the skew frame and lattice cells are Beeson-Rosu's.
INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddEMain

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

/-! ### the chart -/

def ch (E F M K u v : ℝ) : ℝ × ℝ := (M - u / F + F * v / (F ^ 2 - E ^ 2), K - F * v / (F ^ 2 - E ^ 2))
def chv (E F du dv : ℝ) : ℝ × ℝ := (-du / F + F * dv / (F ^ 2 - E ^ 2), -(F * dv / (F ^ 2 - E ^ 2)))
def Qc (E F du dv : ℝ) : ℝ := (F ^ 2 - E ^ 2) ^ 2 * du ^ 2 - E ^ 2 * (F ^ 2 - E ^ 2) * du * dv + (E * F) ^ 2 * dv ^ 2

theorem ch_add_chv (E F M K u v du dv : ℝ) :
    ch E F M K u v + chv E F du dv = ch E F M K (u + du) (v + dv) := by
  ext <;> simp only [ch, chv, Prod.fst_add, Prod.snd_add] <;> ring

theorem Psi_comb (E F M K s u0 v0 α β d1u d1v d2u d2v : ℝ) :
    cH E F s (ch E F M K (u0 + α * d1u + β * d2u) (v0 + α * d1v + β * d2v)) =
      cH E F s (ch E F M K u0 v0) + α • cHv E F (chv E F d1u d1v) + β • cHv E F (chv E F d2u d2v) := by
  ext <;> simp only [cH, ch, cHv, chv, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem Psi_preg (E F M K s u0 v0 u1 v1 u2 v2 α β : ℝ) :
    cH E F s (ch E F M K (u0 + α * (u1 - u0) + β * (u2 - u0)) (v0 + α * (v1 - v0) + β * (v2 - v0))) =
      cH E F s (ch E F M K u0 v0) + α • (cH E F s (ch E F M K u1 v1) - cH E F s (ch E F M K u0 v0)) +
        β • (cH E F s (ch E F M K u2 v2) - cH E F s (ch E F M K u0 v0)) := by
  ext <;> simp only [cH, ch, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem par_image (E F M K s u0 v0 d1u d1v d2u d2v p q : ℝ) :
    Par (cH E F s (ch E F M K u0 v0)) (cHv E F (chv E F d1u d1v)) (cHv E F (chv E F d2u d2v)) p q =
      (fun c : ℝ × ℝ => cH E F s (ch E F M K c.1 c.2)) '' Par (u0, v0) (d1u, d1v) (d2u, d2v) p q := by
  ext x
  constructor
  · rintro ⟨α, β, hα, hα', hβ, hβ', rfl⟩
    refine ⟨(u0 + α * d1u + β * d2u, v0 + α * d1v + β * d2v), ⟨α, β, hα, hα', hβ, hβ', ?_⟩, ?_⟩
    · ext <;> simp
    · exact Psi_comb E F M K s u0 v0 α β d1u d1v d2u d2v
  · rintro ⟨c, ⟨α, β, hα, hα', hβ, hβ', rfl⟩, rfl⟩
    refine ⟨α, β, hα, hα', hβ, hβ', ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact Psi_comb E F M K s u0 v0 α β d1u d1v d2u d2v

theorem preg_image (E F M K s u0 v0 u1 v1 u2 v2 : ℝ) :
    Preg (cH E F s (ch E F M K u0 v0)) (cH E F s (ch E F M K u1 v1)) (cH E F s (ch E F M K u2 v2)) 0 =
      (fun c : ℝ × ℝ => cH E F s (ch E F M K c.1 c.2)) '' Preg (u0, v0) (u1, v1) (u2, v2) 0 := by
  ext x
  constructor
  · rintro ⟨α, β, hα, hβ, h1, h2, rfl⟩
    refine ⟨(u0 + α * (u1 - u0) + β * (u2 - u0), v0 + α * (v1 - v0) + β * (v2 - v0)), ⟨α, β, hα, hβ, h1, h2, ?_⟩, ?_⟩
    · ext <;> simp
    · exact Psi_preg E F M K s u0 v0 u1 v1 u2 v2 α β
  · rintro ⟨c, ⟨α, β, hα, hβ, h1, h2, rfl⟩, rfl⟩
    refine ⟨α, β, hα, hβ, h1, h2, ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    exact Psi_preg E F M K s u0 v0 u1 v1 u2 v2 α β

section chartalg
variable {E F : ℝ} (hE : 0 < E) (hEF : E < F)
include hE hEF

theorem chart_pos : 0 < F ∧ 0 < F ^ 2 - E ^ 2 := frame_pos hE hEF

theorem qf_ch (M K u v u' v' : ℝ) : qf E F (ch E F M K u v) (ch E F M K u' v') = Qc E F (u' - u) (v' - v) := by
  obtain ⟨hF, hb⟩ := chart_pos hE hEF
  simp only [qf, ch, Qc]
  field_simp
  ring

theorem chv_det (du1 dv1 du2 dv2 : ℝ) :
    (chv E F du1 dv1).1 * (chv E F du2 dv2).2 - (chv E F du2 dv2).1 * (chv E F du1 dv1).2 =
      (du1 * dv2 - du2 * dv1) / (F ^ 2 - E ^ 2) := by
  obtain ⟨hF, hb⟩ := chart_pos hE hEF
  simp only [chv]
  field_simp
  ring

theorem ch_det (M K u0 v0 u1 v1 u2 v2 : ℝ) :
    ((ch E F M K u1 v1).1 - (ch E F M K u0 v0).1) * ((ch E F M K u2 v2).2 - (ch E F M K u0 v0).2) -
      ((ch E F M K u2 v2).1 - (ch E F M K u0 v0).1) * ((ch E F M K u1 v1).2 - (ch E F M K u0 v0).2) =
      ((u1 - u0) * (v2 - v0) - (u2 - u0) * (v1 - v0)) / (F ^ 2 - E ^ 2) := by
  obtain ⟨hF, hb⟩ := chart_pos hE hEF
  simp only [ch]
  field_simp
  ring

end chartalg

/-! ### hexagon regions -/

structure OBx where
  ulo : ℝ
  uhi : ℝ
  vlo : ℝ
  vhi : ℝ
  slo : ℝ
  shi : ℝ

/-- chart-level hexagon -/
def ChartHex (bx : OBx) (u v : ℝ) : Prop :=
  bx.ulo ≤ u ∧ u ≤ bx.uhi ∧ bx.vlo ≤ v ∧ v ≤ bx.vhi ∧ bx.slo ≤ u + v ∧ u + v ≤ bx.shi

/-- the hexagon, as a set of skew-frame points, in the `LF` shape `al * ax + be * ay <= ga` -/
def HexS (E F s M K : ℝ) (bx : OBx) : Set (ℝ × ℝ) :=
  {q | (-F) * ax E F q + (-F) * ay E F s q ≤ bx.uhi - F * (M + K) ∧
    F * ax E F q + F * ay E F s q ≤ F * (M + K) - bx.ulo ∧
    0 * ax E F q + (-((F ^ 2 - E ^ 2) / F)) * ay E F s q ≤ bx.vhi - (F ^ 2 - E ^ 2) / F * K ∧
    0 * ax E F q + ((F ^ 2 - E ^ 2) / F) * ay E F s q ≤ (F ^ 2 - E ^ 2) / F * K - bx.vlo ∧
    (-F) * ax E F q + (-(F + (F ^ 2 - E ^ 2) / F)) * ay E F s q ≤ bx.shi - F * (M + K) - (F ^ 2 - E ^ 2) / F * K ∧
    F * ax E F q + (F + (F ^ 2 - E ^ 2) / F) * ay E F s q ≤ F * (M + K) + (F ^ 2 - E ^ 2) / F * K - bx.slo}

theorem hexS_of_chart {E F : ℝ} (hE : 0 < E) (hEF : E < F) (s M K : ℝ) (bx : OBx) (T : Set (ℝ × ℝ))
    (hT : ∀ c ∈ T, ChartHex bx c.1 c.2) :
    (fun c : ℝ × ℝ => cH E F s (ch E F M K c.1 c.2)) '' T ⊆ HexS E F s M K bx := by
  obtain ⟨hF, hb⟩ := chart_pos hE hEF
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hT c hc
  have ax' : ax E F (cH E F s (ch E F M K c.1 c.2)) = (ch E F M K c.1 c.2).1 := ax_cH s hE hEF _
  have ay' : ay E F s (cH E F s (ch E F M K c.1 c.2)) = (ch E F M K c.1 c.2).2 := ay_cH s hE hEF _
  rw [HexS, Set.mem_setOf_eq, ax', ay']
  have e1 : (-F) * (ch E F M K c.1 c.2).1 + (-F) * (ch E F M K c.1 c.2).2 = c.1 - F * (M + K) := by
    simp only [ch]; field_simp; ring
  have e2 : (-((F ^ 2 - E ^ 2) / F)) * (ch E F M K c.1 c.2).2 = c.2 - (F ^ 2 - E ^ 2) / F * K := by
    simp only [ch]; field_simp; ring
  have e3 : (-F) * (ch E F M K c.1 c.2).1 + (-(F + (F ^ 2 - E ^ 2) / F)) * (ch E F M K c.1 c.2).2 =
      c.1 + c.2 - F * (M + K) - (F ^ 2 - E ^ 2) / F * K := by
    simp only [ch]; field_simp; ring
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem hexS_mono {E F s M K : ℝ} {bx bx' : OBx} (h1 : bx'.ulo ≤ bx.ulo) (h2 : bx.uhi ≤ bx'.uhi) (h3 : bx'.vlo ≤ bx.vlo)
    (h4 : bx.vhi ≤ bx'.vhi) (h5 : bx'.slo ≤ bx.slo) (h6 : bx.shi ≤ bx'.shi) :
    HexS E F s M K bx ⊆ HexS E F s M K bx' := by
  rintro q ⟨a1, a2, a3, a4, a5, a6⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- separation of two hexagons -/
def OSep (b1 b2 : OBx) : Prop :=
  b1.uhi ≤ b2.ulo ∨ b2.uhi ≤ b1.ulo ∨ b1.vhi ≤ b2.vlo ∨ b2.vhi ≤ b1.vlo ∨ b1.shi ≤ b2.slo ∨ b2.shi ≤ b1.slo

theorem hexS_disj {E F : ℝ} (hE : 0 < E) (hEF : E < F) (s M K : ℝ) {φ : ℝ} (hφ : 1 < φ) {A B : Set (ℝ × ℝ)} {b1 b2 : OBx}
    (hA : A ⊆ HexS E F s M K b1) (hB : B ⊆ HexS E F s M K b2) (hsep : OSep b1 b2) :
    Disjoint (interior (Phi φ '' A)) (interior (Phi φ '' B)) := by
  obtain ⟨hF, hb⟩ := chart_pos hE hEF
  have hbF : 0 < (F ^ 2 - E ^ 2) / F := div_pos hb hF
  refine disjoint_image hφ ?_
  rcases hsep with h | h | h | h | h | h
  · refine disjLF (al := -F) (be := -F) (ga := b1.uhi - F * (M + K)) (al2 := F) (be2 := F) (ga2 := -(b1.uhi - F * (M + K)))
      s hE hEF (Or.inl (neg_ne_zero.mpr hF.ne')) (by ring) (by ring) (by ring) (fun p hp => (hA hp).1) ?_
    intro p hp; have := (hB hp).2.1; linarith
  · refine (disjLF (al := -F) (be := -F) (ga := b2.uhi - F * (M + K)) (al2 := F) (be2 := F) (ga2 := -(b2.uhi - F * (M + K)))
      s hE hEF (Or.inl (neg_ne_zero.mpr hF.ne')) (by ring) (by ring) (by ring) (fun p hp => (hB hp).1) ?_).symm
    intro p hp; have := (hA hp).2.1; linarith
  · refine disjLF (al := 0) (be := -((F ^ 2 - E ^ 2) / F)) (ga := b1.vhi - (F ^ 2 - E ^ 2) / F * K) (al2 := 0)
      (be2 := (F ^ 2 - E ^ 2) / F) (ga2 := -(b1.vhi - (F ^ 2 - E ^ 2) / F * K))
      s hE hEF (Or.inr (neg_ne_zero.mpr hbF.ne')) (by ring) (by ring) (by ring) (fun p hp => (hA hp).2.2.1) ?_
    intro p hp; have := (hB hp).2.2.2.1; linarith
  · refine (disjLF (al := 0) (be := -((F ^ 2 - E ^ 2) / F)) (ga := b2.vhi - (F ^ 2 - E ^ 2) / F * K) (al2 := 0)
      (be2 := (F ^ 2 - E ^ 2) / F) (ga2 := -(b2.vhi - (F ^ 2 - E ^ 2) / F * K))
      s hE hEF (Or.inr (neg_ne_zero.mpr hbF.ne')) (by ring) (by ring) (by ring) (fun p hp => (hB hp).2.2.1) ?_).symm
    intro p hp; have := (hA hp).2.2.2.1; linarith
  · refine disjLF (al := -F) (be := -(F + (F ^ 2 - E ^ 2) / F)) (ga := b1.shi - F * (M + K) - (F ^ 2 - E ^ 2) / F * K)
      (al2 := F) (be2 := F + (F ^ 2 - E ^ 2) / F) (ga2 := -(b1.shi - F * (M + K) - (F ^ 2 - E ^ 2) / F * K))
      s hE hEF (Or.inl (neg_ne_zero.mpr hF.ne')) (by ring) (by ring) (by ring) (fun p hp => (hA hp).2.2.2.2.1) ?_
    intro p hp; have := (hB hp).2.2.2.2.2; linarith
  · refine (disjLF (al := -F) (be := -(F + (F ^ 2 - E ^ 2) / F)) (ga := b2.shi - F * (M + K) - (F ^ 2 - E ^ 2) / F * K)
      (al2 := F) (be2 := F + (F ^ 2 - E ^ 2) / F) (ga2 := -(b2.shi - F * (M + K) - (F ^ 2 - E ^ 2) / F * K))
      s hE hEF (Or.inl (neg_ne_zero.mpr hF.ne')) (by ring) (by ring) (by ring) (fun p hp => (hB hp).2.2.2.2.1) ?_).symm
    intro p hp; have := (hA hp).2.2.2.2.2; linarith

/-- the pentagon `rReg2` contains the hexagon `[0,p] x [0,H] x (u+v >= en)` -/
theorem hexS_sub_rReg2 {E F : ℝ} (hE : 0 < E) (hEF : E < F) (s M K j n pp H shi : ℝ) (hK : K = j * F)
    (hH : H = (F ^ 2 - E ^ 2) / F * K) (hp : pp = (M + K - s) * F) :
    HexS E F s M K ⟨0, pp, 0, H, E * n, shi⟩ ⊆ rReg2 E F M n j s := by
  obtain ⟨hF, hb⟩ := chart_pos hE hEF
  have hbF : 0 < (F ^ 2 - E ^ 2) / F := div_pos hb hF
  rintro q ⟨h1, h2, h3, h4, h5, h6⟩
  simp only at h1 h2 h3 h4 h5 h6
  have hbFF : (F ^ 2 - E ^ 2) / F * F = F ^ 2 - E ^ 2 := by field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra hc; push_neg at hc
    nlinarith [mul_pos hbF (neg_pos.mpr (show ay E F s q < 0 by linarith))]
  · by_contra hc; push_neg at hc
    nlinarith [mul_pos hbF (show 0 < ay E F s q - j * F by linarith)]
  · by_contra hc; push_neg at hc
    nlinarith [mul_pos hF (show 0 < -ax E F q - ay E F s q + s by linarith)]
  · by_contra hc; push_neg at hc
    nlinarith [mul_pos hF (show 0 < ax E F q + ay E F s q - (M + j * F) by linarith)]
  · unfold c5f
    rw [← hK]
    generalize hbF' : (F ^ 2 - E ^ 2) / F = bF at h6
    have hbFF : F * bF = F ^ 2 - E ^ 2 := by rw [← hbF']; field_simp
    have h6F := mul_le_mul_of_nonneg_left h6 hF.le
    have e1 : F * bF * ay E F s q = (F ^ 2 - E ^ 2) * ay E F s q := by rw [hbFF]
    have e2 : F * bF * K = (F ^ 2 - E ^ 2) * K := by rw [hbFF]
    nlinarith [h6F, e1, e2]

end

end Erdos634.Draft.ThetaNotch
