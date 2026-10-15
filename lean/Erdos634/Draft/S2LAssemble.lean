-- Assembly of the Beeson III Thm 10 layout (p = 1).
--
-- Main results (no sorry, no native_decide):
--   * `s2_family_model (q ≥ 2)`: ∃ D : CongruentDissection ((2q²-1)(3q²-1)), D.model = MF q ∧ D.target = tgt q, where
--       - `MF q` is the tile with side lengths (q²-1, q, q²) on edges 01,12,20 (`MF_sides`),
--       - `tgt q` is the triangle with sides ((3q²-1)(q²-1), q⁴, q²(2q²-1)) (`tgt_sides`); in tile units (A·c, c², B·b), A=2q²-1,
--         B=3q²-1, b=q²-1, c=q², i.e. the angles (2α, 2β, α) target of Beeson III Thm 10 with ℓ = q².
--   * `s2_family`: Nonempty (CongruentDissection ((2q²-1)(3q²-1))) for every natural q ≥ 2   (q=2: 77, q=3: 442, q=4: 1457 as `example`s).
-- Construction (in the skew frame Φ_q, g1=(1,0), g2=u(θ), cos θ=1/(2q); coordinates in S2LLayout):
--   three scale-q² triangles (3q⁴ tiles), a scale-q triangle (q²), a scale-(q²-1) triangle ((q²-1)²), and a q(q²-2)×q grid of
--   two-tile bricks (2q²(q²-2) tiles), total (2q²-1)(3q²-1).  Triangles: `Subdivision.ladderDissection` (the tile-scaling half of
--   thm:ladder) via `S2LCore.scaledRT`; grid: `BrickGridF.gridB` shifted.  Covering is derived from
--   containment, pairwise interior-disjointness (6 separating lines, S2LLayout) and the area identity (`ConvexCover.ofCertificate`).
-- Scope: p = 1 only (tile (e,f) = (1,q)).  All N here are composite, so this gives no prime tile count;
--   it is spectrum data for Beeson III Thm 10, p = 1.
import Erdos634.Draft.S2LLayout

set_option linter.unusedSectionVars false
open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.S2L
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.BrickGridF (gridB shift_rect)

section pieces
variable {q : ℝ} (hq : 2 ≤ q)
include hq

/-! ### non-degeneracy of the pieces -/
theorem det1 : ((pQ q).1 - pA.1) * ((pC q).2 - pA.2) - ((pC q).1 - pA.1) * ((pQ q).2 - pA.2) ≠ 0 := by
  have h := q_pos hq; have hb := b_pos hq
  have e : ((pQ q).1 - pA.1) * ((pC q).2 - pA.2) - ((pC q).1 - pA.1) * ((pQ q).2 - pA.2)
      = -(q ^ 5 * (q ^ 2 - 1)) := by simp only [pA, pQ, pC]; ring
  rw [e]; exact neg_ne_zero.mpr (mul_pos (pow_pos h 5) hb).ne'
theorem det2 : ((pQ q).1 - pA.1) * ((pP q).2 - pA.2) - ((pP q).1 - pA.1) * ((pQ q).2 - pA.2) ≠ 0 := by
  have h := q_pos hq; have hb := b_pos hq
  have e : ((pQ q).1 - pA.1) * ((pP q).2 - pA.2) - ((pP q).1 - pA.1) * ((pQ q).2 - pA.2)
      = q ^ 5 * (q ^ 2 - 1) := by simp only [pA, pQ, pP]; ring
  rw [e]; exact (mul_pos (pow_pos h 5) hb).ne'
theorem det3 : ((pQ q).1 - (pR q).1) * ((pC q).2 - (pR q).2) - ((pC q).1 - (pR q).1) * ((pQ q).2 - (pR q).2) ≠ 0 := by
  have h := q_pos hq; have hb := b_pos hq
  have e : ((pQ q).1 - (pR q).1) * ((pC q).2 - (pR q).2) - ((pC q).1 - (pR q).1) * ((pQ q).2 - (pR q).2)
      = q ^ 5 * (q ^ 2 - 1) := by simp only [pR, pQ, pC]; ring
  rw [e]; exact (mul_pos (pow_pos h 5) hb).ne'
theorem det4 : ((pW q).1 - (pP q).1) * ((pQ q).2 - (pP q).2) - ((pQ q).1 - (pP q).1) * ((pW q).2 - (pP q).2) ≠ 0 := by
  have h := q_pos hq; have hb := b_pos hq
  have e : ((pW q).1 - (pP q).1) * ((pQ q).2 - (pP q).2) - ((pQ q).1 - (pP q).1) * ((pW q).2 - (pP q).2)
      = -(q ^ 3 * (q ^ 2 - 1)) := by simp only [pW, pQ, pP]; ring
  rw [e]; exact neg_ne_zero.mpr (mul_pos (pow_pos h 3) hb).ne'
theorem det5 : ((pU q).1 - (pB q).1) * ((pR q).2 - (pB q).2) - ((pR q).1 - (pB q).1) * ((pU q).2 - (pB q).2) ≠ 0 := by
  have h := q_pos hq; have hb := b_pos hq
  have e : ((pU q).1 - (pB q).1) * ((pR q).2 - (pB q).2) - ((pR q).1 - (pB q).1) * ((pU q).2 - (pB q).2)
      = q * (q ^ 2 - 1) ^ 3 := by simp only [pB, pU, pR]; ring
  rw [e]; exact (mul_pos h (pow_pos hb 3)).ne'
theorem detT : ((pB q).1 - pA.1) * ((pC q).2 - pA.2) - ((pC q).1 - pA.1) * ((pB q).2 - pA.2) ≠ 0 := by
  have h := q_pos hq; have hb := b_pos hq; have h4 := q2_ge hq
  have h3 : 0 < 3 * q ^ 2 - 1 := by nlinarith
  have h2 : 0 < 2 * q ^ 2 - 1 := by nlinarith
  have e : ((pB q).1 - pA.1) * ((pC q).2 - pA.2) - ((pC q).1 - pA.1) * ((pB q).2 - pA.2)
      = -((3 * q ^ 2 - 1) * (q ^ 2 - 1) * (q * (2 * q ^ 2 - 1))) := by simp only [pA, pB, pC]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)

/-! ### SSS data: the base tiles are congruent to `MF q` -/


end pieces

theorem cast_sq (n : ℕ) : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring

theorem hqn {n : ℕ} (hn : 2 ≤ n) : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
theorem hq1n {n : ℕ} (hn : 2 ≤ n) : (1 : ℝ) < (n : ℝ) := by
  have := hqn hn; linarith

theorem cast_sq1 {n : ℕ} (hn : 2 ≤ n) : ((n ^ 2 - 1 : ℕ) : ℝ) = (n : ℝ) ^ 2 - 1 := by
  have : 1 ≤ n ^ 2 := by nlinarith
  rw [Nat.cast_sub this]; push_cast; ring

/-- Piece 1: triangle `A Q C`, scale `n²`. -/
noncomputable def R1 (n : ℕ) (hn : 2 ≤ n) :
    RTiling (Phi (n : ℝ) '' H1 (n : ℝ)) (MF (n : ℝ) (hq1n hn)) (n ^ 2 * n ^ 2) :=
  scaledRT (n : ℝ) (hq1n hn) pA (pQ (n : ℝ)) (pC (n : ℝ)) (n ^ 2) (pow_pos (by omega) 2)
    (det1 (hqn hn)) _ (baseTri_cong _ _ _ _ _ _ _ _
      (by have := q_pos (hqn hn); rw [cast_sq]; simp only [pA, pQ]; field_simp; ring)
      (by have := q_pos (hqn hn); rw [cast_sq]; simp only [pQ, pC]; field_simp; ring)
      (by have := q_pos (hqn hn); rw [cast_sq]; simp only [pA, pC]; field_simp; ring))

/-- Piece 2: triangle `A Q P`, scale `n²`. -/
noncomputable def R2 (n : ℕ) (hn : 2 ≤ n) :
    RTiling (Phi (n : ℝ) '' H2 (n : ℝ)) (MF (n : ℝ) (hq1n hn)) (n ^ 2 * n ^ 2) :=
  scaledRT (n : ℝ) (hq1n hn) pA (pQ (n : ℝ)) (pP (n : ℝ)) (n ^ 2) (pow_pos (by omega) 2)
    (det2 (hqn hn)) _ (baseTri_cong _ _ _ _ _ _ _ _
      (by have := q_pos (hqn hn); rw [cast_sq]; simp only [pA, pQ]; field_simp; ring)
      (by have := q_pos (hqn hn); rw [cast_sq]; simp only [pQ, pP]; field_simp; ring)
      (by have := q_pos (hqn hn); rw [cast_sq]; simp only [pA, pP]; field_simp; ring))

/-- Piece 3: triangle `R Q C`, scale `n²`. -/
noncomputable def R3 (n : ℕ) (hn : 2 ≤ n) :
    RTiling (Phi (n : ℝ) '' H3 (n : ℝ)) (MF (n : ℝ) (hq1n hn)) (n ^ 2 * n ^ 2) :=
  scaledRT (n : ℝ) (hq1n hn) (pR (n : ℝ)) (pQ (n : ℝ)) (pC (n : ℝ)) (n ^ 2) (pow_pos (by omega) 2)
    (det3 (hqn hn)) _ (baseTri_cong _ _ _ _ _ _ _ _
      (by have := q_pos (hqn hn); rw [cast_sq]; simp only [pR, pQ]; field_simp; ring)
      (by have := q_pos (hqn hn); rw [cast_sq]; simp only [pQ, pC]; field_simp; ring)
      (by have := q_pos (hqn hn); rw [cast_sq]; simp only [pR, pC]; field_simp; ring))

/-- Piece 4: triangle `P W Q`, scale `n`. -/
noncomputable def R4 (n : ℕ) (hn : 2 ≤ n) :
    RTiling (Phi (n : ℝ) '' H4 (n : ℝ)) (MF (n : ℝ) (hq1n hn)) (n * n) :=
  scaledRT (n : ℝ) (hq1n hn) (pP (n : ℝ)) (pW (n : ℝ)) (pQ (n : ℝ)) n (by omega)
    (det4 (hqn hn)) _ (baseTri_cong _ _ _ _ _ _ _ _
      (by have := q_pos (hqn hn); simp only [pP, pW]; field_simp; ring)
      (by have := q_pos (hqn hn); simp only [pW, pQ]; field_simp; ring)
      (by have := q_pos (hqn hn); simp only [pP, pQ]; field_simp; ring))

/-- Piece 5: triangle `B U R`, scale `n²-1`. -/
noncomputable def R5 (n : ℕ) (hn : 2 ≤ n) :
    RTiling (Phi (n : ℝ) '' H5 (n : ℝ)) (MF (n : ℝ) (hq1n hn)) ((n ^ 2 - 1) * (n ^ 2 - 1)) :=
  scaledRT (n : ℝ) (hq1n hn) (pB (n : ℝ)) (pU (n : ℝ)) (pR (n : ℝ)) (n ^ 2 - 1)
    (by have : 2 ≤ n ^ 2 := by nlinarith
        omega)
    (det5 (hqn hn)) _ (baseTri_cong _ _ _ _ _ _ _ _
      (by have := q_pos (hqn hn); rw [cast_sq1 hn]; simp only [pB, pU]; field_simp; ring)
      (by have := q_pos (hqn hn); rw [cast_sq1 hn]; simp only [pU, pR]; field_simp; ring)
      (by have := q_pos (hqn hn); rw [cast_sq1 hn]; simp only [pB, pR]; field_simp; ring))


/-- Piece 6: the parallelogram `Φ[q⁴, 2q²(q²-1)] × [-q(q²-1), 0]`, a `q(q²-2) × q` grid of `q × (q²-1)` bricks. -/
noncomputable def R6 (n : ℕ) (hn : 2 ≤ n) :
    RTiling (Phi (n : ℝ) '' H6 (n : ℝ)) (MF (n : ℝ) (hq1n hn)) (2 * (n ^ 3 - 2 * n) * n) := by
  have hq1 := hq1n hn
  have h2 : 2 * n + 1 ≤ n ^ 3 := by
    have : 4 * n ≤ n ^ 3 := by nlinarith [Nat.mul_le_mul hn hn, Nat.zero_le n]
    omega
  have e1 : n ^ 3 - 2 * n - 1 + 1 = n ^ 3 - 2 * n := by omega
  have e2 : n - 1 + 1 = n := by omega
  have hk1 : (((n ^ 3 - 2 * n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) ^ 3 - 2 * (n : ℝ) := by
    have : (((n ^ 3 - 2 * n - 1 : ℕ) : ℝ) + 1) = ((n ^ 3 - 2 * n - 1 + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [this, e1, Nat.cast_sub (by omega)]; push_cast; ring
  have hl1 : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
    have : (((n - 1 : ℕ) : ℝ) + 1) = ((n - 1 + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this, e2]
  have S := shift_rect (gridB hq1 (n ^ 3 - 2 * n - 1) (n - 1)) ((n : ℝ) ^ 4)
    (-((n : ℝ) * ((n : ℝ) ^ 2 - 1))) (2 * (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 - 1)) 0
    (by rw [hk1]; ring) (by rw [hl1]; ring)
  refine RTiling.castN ?_ S
  rw [e1, e2]

def regionOf (q : ℝ) : Fin 6 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi q '' H1 q
  | ⟨1, _⟩ => Phi q '' H2 q
  | ⟨2, _⟩ => Phi q '' H3 q
  | ⟨3, _⟩ => Phi q '' H4 q
  | ⟨4, _⟩ => Phi q '' H5 q
  | ⟨5, _⟩ => Phi q '' H6 q
  | ⟨k + 6, h⟩ => absurd h (by omega)

def cnt (n : ℕ) : Fin 6 → ℕ := fun i => match i with
  | ⟨0, _⟩ => n ^ 2 * n ^ 2
  | ⟨1, _⟩ => n ^ 2 * n ^ 2
  | ⟨2, _⟩ => n ^ 2 * n ^ 2
  | ⟨3, _⟩ => n * n
  | ⟨4, _⟩ => (n ^ 2 - 1) * (n ^ 2 - 1)
  | ⟨5, _⟩ => 2 * (n ^ 3 - 2 * n) * n
  | ⟨k + 6, h⟩ => absurd h (by omega)

noncomputable def Rall (n : ℕ) (hn : 2 ≤ n) :
    ∀ a : Fin 6, RTiling (regionOf (n : ℝ) a) (MF (n : ℝ) (hq1n hn)) (cnt n a) := fun a => match a with
  | ⟨0, _⟩ => R1 n hn
  | ⟨1, _⟩ => R2 n hn
  | ⟨2, _⟩ => R3 n hn
  | ⟨3, _⟩ => R4 n hn
  | ⟨4, _⟩ => R5 n hn
  | ⟨5, _⟩ => R6 n hn
  | ⟨k + 6, h⟩ => absurd h (by omega)

theorem hS_all {q : ℝ} (hq : 2 ≤ q) :
    ∀ a b : Fin 6, a ≠ b → Disjoint (interior (regionOf q a)) (interior (regionOf q b)) :=
  fun a b hab => match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hab
  | ⟨0, _⟩, ⟨1, _⟩ => (d12 hq)
  | ⟨0, _⟩, ⟨2, _⟩ => (d13 hq)
  | ⟨0, _⟩, ⟨3, _⟩ => (d14 hq)
  | ⟨0, _⟩, ⟨4, _⟩ => (d15 hq)
  | ⟨0, _⟩, ⟨5, _⟩ => (d16 hq)
  | ⟨1, _⟩, ⟨0, _⟩ => (d12 hq).symm
  | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hab
  | ⟨1, _⟩, ⟨2, _⟩ => ((d32 hq).symm)
  | ⟨1, _⟩, ⟨3, _⟩ => ((d42 hq).symm)
  | ⟨1, _⟩, ⟨4, _⟩ => ((d52 hq).symm)
  | ⟨1, _⟩, ⟨5, _⟩ => ((d62 hq).symm)
  | ⟨2, _⟩, ⟨0, _⟩ => (d13 hq).symm
  | ⟨2, _⟩, ⟨1, _⟩ => (d32 hq)
  | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hab
  | ⟨2, _⟩, ⟨3, _⟩ => (d34 hq)
  | ⟨2, _⟩, ⟨4, _⟩ => (d35 hq)
  | ⟨2, _⟩, ⟨5, _⟩ => (d36 hq)
  | ⟨3, _⟩, ⟨0, _⟩ => (d14 hq).symm
  | ⟨3, _⟩, ⟨1, _⟩ => (d42 hq)
  | ⟨3, _⟩, ⟨2, _⟩ => (d34 hq).symm
  | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hab
  | ⟨3, _⟩, ⟨4, _⟩ => (d45 hq)
  | ⟨3, _⟩, ⟨5, _⟩ => (d46 hq)
  | ⟨4, _⟩, ⟨0, _⟩ => (d15 hq).symm
  | ⟨4, _⟩, ⟨1, _⟩ => (d52 hq)
  | ⟨4, _⟩, ⟨2, _⟩ => (d35 hq).symm
  | ⟨4, _⟩, ⟨3, _⟩ => (d45 hq).symm
  | ⟨4, _⟩, ⟨4, _⟩ => absurd rfl hab
  | ⟨4, _⟩, ⟨5, _⟩ => ((d65 hq).symm)
  | ⟨5, _⟩, ⟨0, _⟩ => (d16 hq).symm
  | ⟨5, _⟩, ⟨1, _⟩ => (d62 hq)
  | ⟨5, _⟩, ⟨2, _⟩ => (d36 hq).symm
  | ⟨5, _⟩, ⟨3, _⟩ => (d46 hq).symm
  | ⟨5, _⟩, ⟨4, _⟩ => (d65 hq)
  | ⟨5, _⟩, ⟨5, _⟩ => absurd rfl hab
  | ⟨k + 6, h⟩, _ => absurd h (by omega)
  | _, ⟨k + 6, h⟩ => absurd h (by omega)


/-- The target triangle `A B C` of the layout. -/
noncomputable def tgt (n : ℕ) (hn : 2 ≤ n) : Tri :=
  triC (n : ℝ) (hq1n hn) pA (pB (n : ℝ)) (pC (n : ℝ)) (detT (hqn hn))

theorem hsub_all {n : ℕ} (hn : 2 ≤ n) : ∀ a : Fin 6, regionOf (n : ℝ) a ⊆ (tgt n hn).carrier := by
  have hc : (tgt n hn).carrier = Phi (n : ℝ) '' HT (n : ℝ) := carrier_triC _ _ _ _ _ _
  have hq := hqn hn
  intro a
  rw [hc]
  exact match a with
  | ⟨0, _⟩ => Set.image_mono (sub1 hq)
  | ⟨1, _⟩ => Set.image_mono (sub2 hq)
  | ⟨2, _⟩ => Set.image_mono (sub3 hq)
  | ⟨3, _⟩ => Set.image_mono (sub4 hq)
  | ⟨4, _⟩ => Set.image_mono (sub5 hq)
  | ⟨5, _⟩ => Set.image_mono (sub6 hq)
  | ⟨k + 6, h⟩ => absurd h (by omega)

theorem sum_cnt (n : ℕ) (hn : 2 ≤ n) : ∑ a, cnt n a = (2 * n ^ 2 - 1) * (3 * n ^ 2 - 1) := by
  rw [Fin.sum_univ_six]
  show n ^ 2 * n ^ 2 + n ^ 2 * n ^ 2 + n ^ 2 * n ^ 2 + n * n + (n ^ 2 - 1) * (n ^ 2 - 1)
    + 2 * (n ^ 3 - 2 * n) * n = _
  have h1 : 1 ≤ n ^ 2 := by nlinarith
  have h2 : 2 * n ≤ n ^ 3 := by nlinarith [Nat.mul_le_mul hn hn]
  have h3 : 1 ≤ 2 * n ^ 2 := by nlinarith
  have h4 : 1 ≤ 3 * n ^ 2 := by nlinarith
  zify [h1, h2, h3, h4]
  ring

theorem sum_cnt_real (n : ℕ) (hn : 2 ≤ n) :
    ((∑ a, cnt n a : ℕ) : ℝ) = (2 * (n : ℝ) ^ 2 - 1) * (3 * (n : ℝ) ^ 2 - 1) := by
  have h3 : 1 ≤ 2 * n ^ 2 := by nlinarith
  have h4 : 1 ≤ 3 * n ^ 2 := by nlinarith
  rw [sum_cnt n hn, Nat.cast_mul, Nat.cast_sub h3, Nat.cast_sub h4]
  push_cast; ring

open MeasureTheory in
theorem hvol_all (n : ℕ) (hn : 2 ≤ n) :
    ((∑ a, cnt n a : ℕ) : ENNReal) * volume (MF (n : ℝ) (hq1n hn)).carrier = volume (tgt n hn).carrier := by
  have hq := hqn hn
  have hq1 := hq1n hn
  have h0 := q_pos hq; have hb := b_pos hq; have h4 := q2_ge hq
  have h3 : 0 < 3 * (n : ℝ) ^ 2 - 1 := by nlinarith
  have h2 : 0 < 2 * (n : ℝ) ^ 2 - 1 := by nlinarith
  have hs := sD_pos hq1
  have hM : volume (MF (n : ℝ) hq1).carrier = ENNReal.ofReal (sD (n : ℝ) / (2 * (n : ℝ)) * (((n : ℝ) ^ 2 - 1) * (n : ℝ)))
      * volume Erdos634.AreaDet.stdCarrier := by
    unfold MF brickL
    rw [vol_triC]
    congr 2
    rw [← abs_of_pos (show 0 < sD (n : ℝ) / (2 * (n : ℝ)) * (((n : ℝ) ^ 2 - 1) * (n : ℝ)) by positivity)]
    congr 1; ring
  have hT : volume (tgt n hn).carrier = ENNReal.ofReal (sD (n : ℝ) / (2 * (n : ℝ)) *
      ((3 * (n : ℝ) ^ 2 - 1) * ((n : ℝ) ^ 2 - 1) * ((n : ℝ) * (2 * (n : ℝ) ^ 2 - 1))))
      * volume Erdos634.AreaDet.stdCarrier := by
    unfold tgt
    rw [vol_triC]
    congr 2
    rw [← abs_of_pos (show 0 < sD (n : ℝ) / (2 * (n : ℝ)) *
      ((3 * (n : ℝ) ^ 2 - 1) * ((n : ℝ) ^ 2 - 1) * ((n : ℝ) * (2 * (n : ℝ) ^ 2 - 1))) by positivity)]
    rw [← abs_neg]; congr 1
    simp only [pA, pB, pC]; ring
  rw [hM, hT, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    sum_cnt_real n hn]
  congr 2
  ring

/-- Side lengths of the model tile `MF q`: `(q²-1, q, q²)` on the edges `01, 12, 20`. -/
theorem MF_sides (n : ℕ) (hn : 2 ≤ n) :
    dist ((MF (n : ℝ) (hq1n hn)).pts 0) ((MF (n : ℝ) (hq1n hn)).pts 1) = (n : ℝ) ^ 2 - 1 ∧
    dist ((MF (n : ℝ) (hq1n hn)).pts 1) ((MF (n : ℝ) (hq1n hn)).pts 2) = (n : ℝ) ∧
    dist ((MF (n : ℝ) (hq1n hn)).pts 2) ((MF (n : ℝ) (hq1n hn)).pts 0) = (n : ℝ) ^ 2 := by
  have hq := hqn hn; have hq1 := hq1n hn
  have h0 := q_pos hq; have hb := b_pos hq
  have h0' : (n : ℝ) ≠ 0 := h0.ne'
  simp only [MF, brickL, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg hb.le).mp ?_
    rw [sq_Phi hq1]; ring
  · refine (sq_eq_sq₀ dist_nonneg h0.le).mp ?_
    rw [sq_Phi hq1]; simp only; ring
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi hq1]; simp only; field_simp; ring

/-- Side lengths of the target `tgt q`: `AB = (3q²-1)(q²-1)`, `AC = q⁴`, `BC = q²(2q²-1)`. -/
theorem tgt_sides (n : ℕ) (hn : 2 ≤ n) :
    dist ((tgt n hn).pts 0) ((tgt n hn).pts 1) = (3 * (n : ℝ) ^ 2 - 1) * ((n : ℝ) ^ 2 - 1) ∧
    dist ((tgt n hn).pts 0) ((tgt n hn).pts 2) = (n : ℝ) ^ 4 ∧
    dist ((tgt n hn).pts 1) ((tgt n hn).pts 2) = (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2 - 1) := by
  have hq := hqn hn; have hq1 := hq1n hn
  have h0 := q_pos hq; have hb := b_pos hq; have h4 := q2_ge hq
  have h3 : 0 < 3 * (n : ℝ) ^ 2 - 1 := by nlinarith
  have h2 : 0 < 2 * (n : ℝ) ^ 2 - 1 := by nlinarith
  have h0' : (n : ℝ) ≠ 0 := h0.ne'
  simp only [tgt, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi hq1]; simp only [pA, pB]; ring
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi hq1]; simp only [pA, pC]; field_simp; ring
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi hq1]; simp only [pB, pC]; field_simp; ring

/-- **The S2 family, p = 1** (Beeson III Thm 10 layout).  For every integer `q ≥ 2`
the triangle `tgt q` with sides `((3q²-1)(q²-1), q⁴, q²(2q²-1))` (see `tgt_sides`) is dissected into
`N = (2q²-1)(3q²-1)` copies of the tile `MF q` with sides `(q²-1, q, q²)` (see `MF_sides`). -/
theorem s2_family_model (q : ℕ) (hq : 2 ≤ q) :
    ∃ D : CongruentDissection ((2 * q ^ 2 - 1) * (3 * q ^ 2 - 1)),
      D.model = MF (q : ℝ) (hq1n hq) ∧ D.target = tgt q hq := by
  have := pack_exists (M := MF (q : ℝ) (hq1n hq)) (T := tgt q hq) (regionOf (q : ℝ)) (cnt q)
    (Rall q hq) (hS_all (hqn hq)) (hsub_all hq) (hvol_all q hq)
  rw [sum_cnt q hq] at this
  exact this

/-- **Statement requested:** `N = (2q²-1)(3q²-1)` is a tile count for every `q ≥ 2`. -/
theorem s2_family (q : ℕ) (hq : 2 ≤ q) : Nonempty (CongruentDissection ((2 * q ^ 2 - 1) * (3 * q ^ 2 - 1))) := by
  obtain ⟨D, -, -⟩ := s2_family_model q hq
  exact ⟨D⟩

/-! sanity: the first members (q = 2: N = 77 with tile (2,3,4); q = 3: N = 442 with tile (3,8,9); q = 4: N = 1457). -/
example : Nonempty (CongruentDissection 77) := by simpa using s2_family 2 le_rfl
example : Nonempty (CongruentDissection 442) := by simpa using s2_family 3 (by norm_num)
example : Nonempty (CongruentDissection 1457) := by simpa using s2_family 4 (by norm_num)

end Erdos634.Draft.S2L

#print axioms Erdos634.Draft.S2L.s2_family
#print axioms Erdos634.Draft.S2L.s2_family_model
#print axioms Erdos634.Draft.S2L.MF_sides
#print axioms Erdos634.Draft.S2L.tgt_sides
