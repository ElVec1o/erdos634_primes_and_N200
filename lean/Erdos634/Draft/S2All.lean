/-
Draft/S2All.lean — **the S2 family for ALL `0 < p < q`**: `N = (2q²−p²)(3q²−p²)` is a tile count (tile `(pq, q²−p², q²)`),
including `q² ≤ 2p²`.  The five-piece layout is due to **D. Paliy** (`github.com/DenisUkranian/erdos-634-tilings`,
his 897-tiling; decoded in `private/ROOM/S2/report.md`, `paliy_layout.py`, `piece_check.py`).  The construction is his; what is
added here is the symbolic (all `p,q`) proof, in Lean.

Layout (skew frame `Φ_f`, `f = q/p`, all coordinates multiplied by `q`, `q = p + t`, `b = q²−p² = t(2p+t)`,
`A = 2q²−p²`, `B = 3q²−p²`, `a = pq`, `c = q²`).  Five pieces meet at the origin `O`:
  `T1 = (V0,O,V1)` and `T2 = (V0,O,V2)`: scale `b` triangles (`b²` tiles each);  `T3 = (V1,O,V3)`: scale `a` (`a²` tiles);
  `T4 = (P2,V1,W)`: scale `A` (`A²` tiles);  `PG = O V2 W V3`: the parallelogram of `b × p²` cells (`2 b p²` tiles);
target `(V0,P2,W)`, sides `c², A c, B b` (times the frame scale).  Count `2b²+a²+A²+2bp² = AB`.
The parallelogram is tiled by the lattice machinery of `S2AllTheta` (general lattice vectors in the skew frame).
No sign condition on `q²−2p²`.  Separating lines (5 of them) and the containment barycentrics have nonnegative coefficients in
`(p,t)`, `t = q−p > 0`.

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.S2AllTheta
import Erdos634.Draft.TileCountFamilies

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd Sh_Rect)

namespace Erdos634.Draft.S2All
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.Draft.S2L (rect_subset tri_le tri_ge tri_fst_le tri_fst_ge tri_snd_le tri_snd_ge mem_hull3' pack_exists)
open Erdos634.Draft.WBrickF (interior_disj_lin)

macro "ppos_nn" : tactic => `(tactic| first
  | (rw [← sub_nonneg]; ring_nf; positivity)
  | (rw [← sub_nonneg]; ring_nf)
  | (rw [← sub_nonneg]; ring_nf; exact le_refl _))

/-! ### the layout -/
def vO : ℝ × ℝ := (0, 0)
def vV0 (p t : ℝ) : ℝ × ℝ := ((p + t) * (t * (2 * p + t)) ^ 2, 0)
def vV1 (p t : ℝ) : ℝ × ℝ := (-p ^ 2 * (p + t) * (t * (2 * p + t)), p * (p + t) ^ 2 * (t * (2 * p + t)))
def vV2 (p t : ℝ) : ℝ × ℝ := (0, -p * (p + t) ^ 2 * (t * (2 * p + t)))
def vV3 (p t : ℝ) : ℝ × ℝ := (-p ^ 2 * (p + t) * (t * (2 * p + t)), -p ^ 3 * (p + t) ^ 2)
def vW (p t : ℝ) : ℝ × ℝ := (-p ^ 2 * (p + t) * (t * (2 * p + t)), -p * (p + t) ^ 4)
def vP2 (p t : ℝ) : ℝ × ℝ :=
  (-2 * (p + t) ^ 3 * (t * (2 * p + t)), p * (t * (2 * p + t)) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2))
/-- lattice vectors of the parallelogram cell. -/
def uu (p t : ℝ) : ℝ × ℝ := (0, -p * (p + t) ^ 2)
def ww (p t : ℝ) : ℝ × ℝ := ((p + t) * (t * (2 * p + t)), p * (p + t) ^ 2)
/-- the frame parameter `f = q/p`. -/
noncomputable def fr (p t : ℝ) : ℝ := (p + t) / p

def H1 (p t : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {vV0 p t, vO, vV1 p t}
def H2 (p t : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {vV0 p t, vO, vV2 p t}
def H3 (p t : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {vV1 p t, vO, vV3 p t}
def H4 (p t : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {vP2 p t, vV1 p t, vW p t}
def H5 (p t : ℝ) : Set (ℝ × ℝ) := Lam (uu p t) (ww p t) '' Rect 0 (t * (2 * p + t)) (-p ^ 2) 0
def HT (p t : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {vV0 p t, vP2 p t, vW p t}

section geom
variable {p t : ℝ} (hp : 0 < p) (ht : 0 < t)
include hp ht

theorem hfr : 1 < 4 * (fr p t) ^ 2 := by
  have h : 1 < fr p t := by unfold fr; rw [lt_div_iff₀ hp]; linarith
  nlinarith

theorem hcc : 0 < (p + t) * (t * (2 * p + t)) := by positivity
theorem hbb : 0 < (p + t) * (p * (p + t)) := by positivity

/-- the model tile (scaled by `q`): legs `q b`, `q a` along the axes, hypotenuse `q c = q³`. -/
noncomputable def Mod : Tri := brickL (fr p t) (hfr hp ht) _ _ (hcc hp ht) (hbb hp ht)

theorem hab_id : ((p + t) * (t * (2 * p + t))) ^ 2 + ((p + t) * (p * (p + t))) ^ 2
    + ((p + t) * (t * (2 * p + t))) * ((p + t) * (p * (p + t))) / fr p t = ((p + t) ^ 3) ^ 2 := by
  have h1 : p ≠ 0 := hp.ne'
  have h2 : p + t ≠ 0 := by positivity
  unfold fr; field_simp; ring

/-! ### non-degeneracy -/
theorem det1 : ((vO).1 - (vV0 p t).1) * ((vV1 p t).2 - (vV0 p t).2) - ((vV1 p t).1 - (vV0 p t).1) * ((vO).2 - (vV0 p t).2) ≠ 0 := by
  have e : ((vO).1 - (vV0 p t).1) * ((vV1 p t).2 - (vV0 p t).2) - ((vV1 p t).1 - (vV0 p t).1) * ((vO).2 - (vV0 p t).2)
      = -(p * t ^ 3 * (p + t) ^ 3 * (2 * p + t) ^ 3) := by simp only [vO, vV0, vV1]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)
theorem det2 : ((vO).1 - (vV0 p t).1) * ((vV2 p t).2 - (vV0 p t).2) - ((vV2 p t).1 - (vV0 p t).1) * ((vO).2 - (vV0 p t).2) ≠ 0 := by
  have e : ((vO).1 - (vV0 p t).1) * ((vV2 p t).2 - (vV0 p t).2) - ((vV2 p t).1 - (vV0 p t).1) * ((vO).2 - (vV0 p t).2)
      = p * t ^ 3 * (p + t) ^ 3 * (2 * p + t) ^ 3 := by simp only [vO, vV0, vV2]; ring
  rw [e]; positivity
theorem det3 : ((vO).1 - (vV1 p t).1) * ((vV3 p t).2 - (vV1 p t).2) - ((vV3 p t).1 - (vV1 p t).1) * ((vO).2 - (vV1 p t).2) ≠ 0 := by
  have e : ((vO).1 - (vV1 p t).1) * ((vV3 p t).2 - (vV1 p t).2) - ((vV3 p t).1 - (vV1 p t).1) * ((vO).2 - (vV1 p t).2)
      = -(p ^ 3 * t * (p + t) ^ 5 * (2 * p + t)) := by simp only [vO, vV1, vV3]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)
theorem det4 : ((vV1 p t).1 - (vP2 p t).1) * ((vW p t).2 - (vP2 p t).2) - ((vW p t).1 - (vP2 p t).1) * ((vV1 p t).2 - (vP2 p t).2) ≠ 0 := by
  have e : ((vV1 p t).1 - (vP2 p t).1) * ((vW p t).2 - (vP2 p t).2) - ((vW p t).1 - (vP2 p t).1) * ((vV1 p t).2 - (vP2 p t).2)
      = -(p * t * (p + t) ^ 3 * (2 * p + t) * (p ^ 2 + 4 * p * t + 2 * t ^ 2) ^ 2) := by simp only [vV1, vP2, vW]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)
theorem detT : ((vP2 p t).1 - (vV0 p t).1) * ((vW p t).2 - (vV0 p t).2) - ((vW p t).1 - (vV0 p t).1) * ((vP2 p t).2 - (vV0 p t).2) ≠ 0 := by
  have e : ((vP2 p t).1 - (vV0 p t).1) * ((vW p t).2 - (vV0 p t).2) - ((vW p t).1 - (vV0 p t).1) * ((vP2 p t).2 - (vV0 p t).2)
      = p * t * (p + t) ^ 3 * (2 * p + t) * (p ^ 2 + 4 * p * t + 2 * t ^ 2) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2) := by
    simp only [vV0, vP2, vW]; ring
  rw [e]; positivity
theorem detL : (uu p t).1 * (ww p t).2 - (uu p t).2 * (ww p t).1 ≠ 0 := by
  have e : (uu p t).1 * (ww p t).2 - (uu p t).2 * (ww p t).1 = p * (p + t) ^ 3 * (t * (2 * p + t)) := by
    simp only [uu, ww]; ring
  rw [e]; positivity

/-! ### the four triangles -/
noncomputable def R1 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = t * (2 * p + t)) :
    RTiling (Phi (fr p t) '' H1 p t) (Mod hp ht) (k * k) :=
  scaledRT (fr p t) (hfr hp ht) (vV0 p t) vO (vV1 p t) k hk0 (det1 hp ht) _
    (baseTri_cong _ _ _ _ (((p + t) ^ 3) ^ 2) (hcc hp ht) (hbb hp ht) (hab_id hp ht) _ _ _ k hk0 _
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vO, vV0, vV1]; field_simp; ring)
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vO, vV0, vV1]; field_simp; ring)
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vO, vV0, vV1]; field_simp; ring))

noncomputable def R2 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = t * (2 * p + t)) :
    RTiling (Phi (fr p t) '' H2 p t) (Mod hp ht) (k * k) :=
  scaledRT (fr p t) (hfr hp ht) (vV0 p t) vO (vV2 p t) k hk0 (det2 hp ht) _
    (baseTri_cong _ _ _ _ (((p + t) ^ 3) ^ 2) (hcc hp ht) (hbb hp ht) (hab_id hp ht) _ _ _ k hk0 _
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vO, vV0, vV2]; field_simp; ring)
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vO, vV0, vV2]; field_simp; ring)
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vO, vV0, vV2]; field_simp; ring))

noncomputable def R3 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = p * (p + t)) :
    RTiling (Phi (fr p t) '' H3 p t) (Mod hp ht) (k * k) :=
  scaledRT (fr p t) (hfr hp ht) (vV1 p t) vO (vV3 p t) k hk0 (det3 hp ht) _
    (baseTri_cong _ _ _ _ (((p + t) ^ 3) ^ 2) (hcc hp ht) (hbb hp ht) (hab_id hp ht) _ _ _ k hk0 _
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vO, vV1, vV3]; field_simp; ring)
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vO, vV1, vV3]; field_simp; ring)
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vO, vV1, vV3]; field_simp; ring))

noncomputable def R4 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = p ^ 2 + 4 * p * t + 2 * t ^ 2) :
    RTiling (Phi (fr p t) '' H4 p t) (Mod hp ht) (k * k) :=
  scaledRT (fr p t) (hfr hp ht) (vP2 p t) (vV1 p t) (vW p t) k hk0 (det4 hp ht) _
    (baseTri_cong _ _ _ _ (((p + t) ^ 3) ^ 2) (hcc hp ht) (hbb hp ht) (hab_id hp ht) _ _ _ k hk0 _
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vP2, vV1, vW]; field_simp; ring)
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vP2, vV1, vW]; field_simp; ring)
      (by have h1 : p ≠ 0 := hp.ne'
          have h2 : p + t ≠ 0 := by positivity
          rw [hk]; simp only [fr, vP2, vV1, vW]; field_simp; ring))

/-! ### the parallelogram -/
theorem cong_TL : (TL (hfr hp ht) (uu p t) (ww p t) (detL hp ht)).Congruent (Mod hp ht) := by
  have h1 : p ≠ 0 := hp.ne'
  have h2 : p + t ≠ 0 := by positivity
  unfold TL Mod brickL
  refine triC_cong (hfr hp ht) _ _ _ _ _ _ _ _ ?_ ?_ ?_ <;>
    simp only [uu, ww, fr, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] <;> field_simp <;> ring

theorem cong_TU : (TU (hfr hp ht) (uu p t) (ww p t) (detL hp ht)).Congruent (Mod hp ht) := by
  have h1 : p ≠ 0 := hp.ne'
  have h2 : p + t ≠ 0 := by positivity
  unfold TU Mod brickL
  refine triC_cong (hfr hp ht) _ _ _ _ _ _ _ _ ?_ ?_ ?_ <;>
    simp only [uu, ww, fr, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] <;> field_simp <;> ring

/-- the `(k+1) × (l+1)` parallelogram of cells, `2 (k+1)(l+1)` tiles. -/
noncomputable def R5 (k l : ℕ) (hk : (k : ℝ) + 1 = t * (2 * p + t)) (hl : (l : ℝ) + 1 = p ^ 2) :
    RTiling (Phi (fr p t) '' H5 p t) (Mod hp ht) (2 * (k + 1) * (l + 1)) := by
  have G := gridT (ThH (hfr hp ht) (uu p t) (ww p t) (detL hp ht))
    (ThH_add (hfr hp ht) (uu p t) (ww p t) (detL hp ht)) (A := 1) (B := 1) one_pos one_pos
    (cellRT (hfr hp ht) (uu p t) (ww p t) (detL hp ht) (Mod hp ht) (cong_TL hp ht) (cong_TU hp ht)) k l
  have S := shift_rectT (ThH (hfr hp ht) (uu p t) (ww p t) (detL hp ht))
    (ThH_add (hfr hp ht) (uu p t) (ww p t) (detL hp ht)) G 0 (-p ^ 2) (t * (2 * p + t)) 0
    (by rw [← hk]; ring) (by rw [← hl]; ring)
  rw [ThH_image] at S
  exact RTiling.cast (by rfl) (RTiling.castN (by ring) S)


/-! ### separating functionals (5 lines) and containment -/
def xv (p t : ℝ) : ℝ := -p ^ 2 * (p + t) * (t * (2 * p + t))

macro "vchk" : tactic => `(tactic| (simp only [vO, vV0, vV1, vV2, vV3, vW, vP2, xv] <;> ppos_nn))

theorem T1_y : ∀ x ∈ H1 p t, 0 ≤ x.2 :=
  tri_snd_ge (A := vV0 p t) (B := vO) (C := vV1 p t) _ (by vchk) (by vchk) (by vchk)
theorem T2_y : ∀ x ∈ H2 p t, x.2 ≤ 0 :=
  tri_snd_le (A := vV0 p t) (B := vO) (C := vV2 p t) _ (by vchk) (by vchk) (by vchk)
theorem T1_l1 : ∀ x ∈ H1 p t, 0 ≤ (p + t) * x.1 + p * x.2 :=
  tri_ge (A := vV0 p t) (B := vO) (C := vV1 p t) _ _ _ (by vchk) (by vchk) (by vchk)
theorem T3_l1 : ∀ x ∈ H3 p t, (p + t) * x.1 + p * x.2 ≤ 0 :=
  tri_le (A := vV1 p t) (B := vO) (C := vV3 p t) _ _ _ (by vchk) (by vchk) (by vchk)
theorem T2_x : ∀ x ∈ H2 p t, 0 ≤ x.1 :=
  tri_fst_ge (A := vV0 p t) (B := vO) (C := vV2 p t) _ (by vchk) (by vchk) (by vchk)
theorem T3_x : ∀ x ∈ H3 p t, x.1 ≤ 0 :=
  tri_fst_le (A := vV1 p t) (B := vO) (C := vV3 p t) _ (by vchk) (by vchk) (by vchk)
theorem T4_x : ∀ x ∈ H4 p t, x.1 ≤ 0 :=
  tri_fst_le (A := vP2 p t) (B := vV1 p t) (C := vW p t) _ (by vchk) (by vchk) (by vchk)
theorem T4_xv : ∀ x ∈ H4 p t, x.1 ≤ xv p t :=
  tri_fst_le (A := vP2 p t) (B := vV1 p t) (C := vW p t) _ (by vchk) (by vchk) (by vchk)
theorem T3_xv : ∀ x ∈ H3 p t, xv p t ≤ x.1 :=
  tri_fst_ge (A := vV1 p t) (B := vO) (C := vV3 p t) _ (by vchk) (by vchk) (by vchk)
theorem T1_xv : ∀ x ∈ H1 p t, xv p t ≤ x.1 :=
  tri_fst_ge (A := vV0 p t) (B := vO) (C := vV1 p t) _ (by vchk) (by vchk) (by vchk)
theorem T3_l3 : ∀ x ∈ H3 p t, p * (p + t) * x.1 + (-(t * (2 * p + t))) * x.2 ≤ 0 :=
  tri_le (A := vV1 p t) (B := vO) (C := vV3 p t) _ _ _ (by vchk) (by vchk) (by vchk)

theorem PG_y : ∀ x ∈ H5 p t, x.2 ≤ 0 := by
  rintro _ ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
  have hc : 0 ≤ p * (p + t) ^ 2 := by positivity
  simp only [Lam, uu, ww, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  nlinarith [mul_nonneg hc h1, mul_nonneg hc (neg_nonneg.mpr h4)]
theorem PG_x : ∀ x ∈ H5 p t, x.1 ≤ 0 := by
  rintro _ ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
  have hc : 0 ≤ (p + t) * (t * (2 * p + t)) := by positivity
  simp only [Lam, uu, ww, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  nlinarith [mul_nonneg hc (neg_nonneg.mpr h4)]
theorem PG_xv : ∀ x ∈ H5 p t, xv p t ≤ x.1 := by
  rintro _ ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
  have hc : 0 ≤ (p + t) * (t * (2 * p + t)) := by positivity
  simp only [xv, Lam, uu, ww, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  nlinarith [mul_nonneg hc (by linarith : 0 ≤ z.2 + p ^ 2)]
theorem PG_l3 : ∀ x ∈ H5 p t, 0 ≤ p * (p + t) * x.1 + (-(t * (2 * p + t))) * x.2 := by
  rintro _ ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
  have hc : 0 ≤ p * (p + t) ^ 2 * (t * (2 * p + t)) := by positivity
  simp only [Lam, uu, ww, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  nlinarith [mul_nonneg hc h1]

variable {f : ℝ} (hf : 1 < 4 * f ^ 2)
include hf

theorem d12 : Disjoint (interior (Phi f '' H1 p t)) (interior (Phi f '' H2 p t)) :=
  disjoint_image' hf (interior_disj_snd 0 (T2_y hp ht) (T1_y hp ht)).symm
theorem d13 : Disjoint (interior (Phi f '' H1 p t)) (interior (Phi f '' H3 p t)) :=
  disjoint_image' hf (interior_disj_lin (p + t) p 0 (by positivity) (T3_l1 hp ht) (T1_l1 hp ht)).symm
theorem d14 : Disjoint (interior (Phi f '' H1 p t)) (interior (Phi f '' H4 p t)) :=
  disjoint_image' hf (interior_disj_fst (xv p t) (T4_xv hp ht) (T1_xv hp ht)).symm
theorem d15 : Disjoint (interior (Phi f '' H1 p t)) (interior (Phi f '' H5 p t)) :=
  disjoint_image' hf (interior_disj_snd 0 (PG_y hp ht) (T1_y hp ht)).symm
theorem d23 : Disjoint (interior (Phi f '' H2 p t)) (interior (Phi f '' H3 p t)) :=
  disjoint_image' hf (interior_disj_fst 0 (T3_x hp ht) (T2_x hp ht)).symm
theorem d24 : Disjoint (interior (Phi f '' H2 p t)) (interior (Phi f '' H4 p t)) :=
  disjoint_image' hf (interior_disj_fst 0 (T4_x hp ht) (T2_x hp ht)).symm
theorem d25 : Disjoint (interior (Phi f '' H2 p t)) (interior (Phi f '' H5 p t)) :=
  disjoint_image' hf (interior_disj_fst 0 (PG_x hp ht) (T2_x hp ht)).symm
theorem d34 : Disjoint (interior (Phi f '' H3 p t)) (interior (Phi f '' H4 p t)) :=
  disjoint_image' hf (interior_disj_fst (xv p t) (T4_xv hp ht) (T3_xv hp ht)).symm
theorem d35 : Disjoint (interior (Phi f '' H3 p t)) (interior (Phi f '' H5 p t)) :=
  disjoint_image' hf (interior_disj_lin (p * (p + t)) (-(t * (2 * p + t))) 0 (by positivity)
    (T3_l3 hp ht) (PG_l3 hp ht))
theorem d45 : Disjoint (interior (Phi f '' H4 p t)) (interior (Phi f '' H5 p t)) :=
  disjoint_image' hf (interior_disj_fst (xv p t) (T4_xv hp ht) (PG_xv hp ht))

omit hf

/-! ### containment in the target -/
theorem mem_O : vO ∈ HT p t :=
  mem_hull3' (A := vV0 p t) (B := vP2 p t) (C := vW p t)
    (p * t * (p + t) ^ 3 * (2 * p + t) * (p ^ 2 + 4 * p * t + 2 * t ^ 2) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2))
    (p * t * (p + t) * (2 * p + t) * (p ^ 2 + 4 * p * t + 2 * t ^ 2)
      * (2 * p ^ 4 + 8 * p ^ 3 * t + 8 * p ^ 2 * t ^ 2 + 4 * p * t ^ 3 + t ^ 4))
    (p * t ^ 2 * (p + t) ^ 5 * (2 * p + t) ^ 2)
    (p * t ^ 3 * (p + t) * (2 * p + t) ^ 3 * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2))
    (by positivity) (by positivity) (by positivity) (by positivity) (by ring) _
    (by simp only [vO, vV0, vP2, vW]; ring) (by simp only [vO, vV0, vP2, vW]; ring)

theorem mem_V1 : vV1 p t ∈ HT p t :=
  mem_hull3' (A := vV0 p t) (B := vP2 p t) (C := vW p t)
    (p * t * (p + t) ^ 3 * (2 * p + t) * (p ^ 2 + 4 * p * t + 2 * t ^ 2) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2))
    (p * t * (p + t) ^ 3 * (2 * p + t) * (p ^ 2 + 4 * p * t + 2 * t ^ 2) ^ 2)
    (p * t * (p + t) ^ 5 * (2 * p + t) * (p ^ 2 + 4 * p * t + 2 * t ^ 2))
    0
    (by positivity) (by positivity) (by positivity) (le_refl _) (by ring) _
    (by simp only [vV1, vV0, vP2, vW]; ring) (by simp only [vV1, vV0, vP2, vW]; ring)

theorem mem_V2 : vV2 p t ∈ HT p t :=
  mem_hull3' (A := vV0 p t) (B := vP2 p t) (C := vW p t)
    (p * t * (p + t) ^ 3 * (2 * p + t) * (p ^ 2 + 4 * p * t + 2 * t ^ 2) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2))
    (p ^ 3 * t * (p + t) * (2 * p + t) * (p ^ 2 + 4 * p * t + 2 * t ^ 2) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2))
    0
    (p * t ^ 2 * (p + t) * (2 * p + t) ^ 2 * (p ^ 2 + 4 * p * t + 2 * t ^ 2) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2))
    (by positivity) (by positivity) (le_refl _) (by positivity) (by ring) _
    (by simp only [vV2, vV0, vP2, vW]; ring) (by simp only [vV2, vV0, vP2, vW]; ring)

theorem mem_V3 : vV3 p t ∈ HT p t :=
  mem_hull3' (A := vV0 p t) (B := vP2 p t) (C := vW p t)
    (p * t * (p + t) ^ 3 * (2 * p + t) * (p ^ 2 + 4 * p * t + 2 * t ^ 2) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2))
    (p * t ^ 2 * (p + t) ^ 3 * (2 * p + t) ^ 2 * (p ^ 2 + 4 * p * t + 2 * t ^ 2))
    (p * t ^ 2 * (p + t) ^ 5 * (2 * p + t) ^ 2)
    (p * t * (p + t) ^ 5 * (2 * p + t) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2))
    (by positivity) (by positivity) (by positivity) (by positivity) (by ring) _
    (by simp only [vV3, vV0, vP2, vW]; ring) (by simp only [vV3, vV0, vP2, vW]; ring)

omit hp ht in
theorem mem_V0 : vV0 p t ∈ HT p t := subset_convexHull ℝ _ (by simp)
omit hp ht in
theorem mem_P2 : vP2 p t ∈ HT p t := subset_convexHull ℝ _ (by simp)
omit hp ht in
theorem mem_W : vW p t ∈ HT p t := subset_convexHull ℝ _ (by simp)

theorem sub_tri {a b c : ℝ × ℝ} (ha : a ∈ HT p t) (hb : b ∈ HT p t) (hc : c ∈ HT p t) :
    convexHull ℝ {a, b, c} ⊆ HT p t := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem sub1 : H1 p t ⊆ HT p t := sub_tri hp ht mem_V0 (mem_O hp ht) (mem_V1 hp ht)
theorem sub2 : H2 p t ⊆ HT p t := sub_tri hp ht mem_V0 (mem_O hp ht) (mem_V2 hp ht)
theorem sub3 : H3 p t ⊆ HT p t := sub_tri hp ht (mem_V1 hp ht) (mem_O hp ht) (mem_V3 hp ht)
theorem sub4 : H4 p t ⊆ HT p t := sub_tri hp ht mem_P2 (mem_V1 hp ht) mem_W
theorem sub5 : H5 p t ⊆ HT p t := by
  have hK : Convex ℝ {z : ℝ × ℝ | Lam (uu p t) (ww p t) z ∈ HT p t} :=
    (convex_convexHull ℝ ({vV0 p t, vP2 p t, vW p t} : Set (ℝ × ℝ))).linear_preimage (LamL (uu p t) (ww p t))
  have hm : (0 : ℝ) < t * (2 * p + t) := by positivity
  have hn : -p ^ 2 < (0 : ℝ) := by nlinarith
  have key := rect_subset hK hm hn
    (c00 := by
      show Lam (uu p t) (ww p t) (0, -p ^ 2) ∈ HT p t
      have e : Lam (uu p t) (ww p t) (0, -p ^ 2) = vV3 p t := by
        ext <;> simp only [Lam, uu, ww, vV3, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
      rw [e]; exact mem_V3 hp ht)
    (c10 := by
      show Lam (uu p t) (ww p t) (t * (2 * p + t), -p ^ 2) ∈ HT p t
      have e : Lam (uu p t) (ww p t) (t * (2 * p + t), -p ^ 2) = vW p t := by
        ext <;> simp only [Lam, uu, ww, vW, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
      rw [e]; exact mem_W)
    (c01 := by
      show Lam (uu p t) (ww p t) (0, 0) ∈ HT p t
      have e : Lam (uu p t) (ww p t) (0, 0) = vO := by
        ext <;> simp only [Lam, uu, ww, vO, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
      rw [e]; exact mem_O hp ht)
    (c11 := by
      show Lam (uu p t) (ww p t) (t * (2 * p + t), 0) ∈ HT p t
      have e : Lam (uu p t) (ww p t) (t * (2 * p + t), 0) = vV2 p t := by
        ext <;> simp only [Lam, uu, ww, vV2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
      rw [e]; exact mem_V2 hp ht)
  rintro _ ⟨z, hz, rfl⟩
  exact key hz

end geom

/-! ### assembly -/
noncomputable def regionOf (p t : ℝ) : Fin 5 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi (fr p t) '' H1 p t
  | ⟨1, _⟩ => Phi (fr p t) '' H2 p t
  | ⟨2, _⟩ => Phi (fr p t) '' H3 p t
  | ⟨3, _⟩ => Phi (fr p t) '' H4 p t
  | ⟨4, _⟩ => Phi (fr p t) '' H5 p t
  | ⟨k + 5, h⟩ => absurd h (by omega)

def cnt (kb ka kA np : ℕ) : Fin 5 → ℕ := fun i => match i with
  | ⟨0, _⟩ => kb * kb
  | ⟨1, _⟩ => kb * kb
  | ⟨2, _⟩ => ka * ka
  | ⟨3, _⟩ => kA * kA
  | ⟨4, _⟩ => 2 * kb * np
  | ⟨k + 5, h⟩ => absurd h (by omega)

section asm
variable {p t : ℝ} (hp : 0 < p) (ht : 0 < t)
include hp ht

/-- the target triangle `V0 P2 W`. -/
noncomputable def tgt : Tri := triC (fr p t) (hfr hp ht) (vV0 p t) (vP2 p t) (vW p t) (detT hp ht)

theorem hS_all : ∀ a b : Fin 5, a ≠ b →
    Disjoint (interior (regionOf p t a)) (interior (regionOf p t b)) := by
  have hf := hfr hp ht
  intro a b hab
  exact match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hab
  | ⟨0, _⟩, ⟨1, _⟩ => d12 hp ht hf
  | ⟨0, _⟩, ⟨2, _⟩ => d13 hp ht hf
  | ⟨0, _⟩, ⟨3, _⟩ => d14 hp ht hf
  | ⟨0, _⟩, ⟨4, _⟩ => d15 hp ht hf
  | ⟨1, _⟩, ⟨0, _⟩ => (d12 hp ht hf).symm
  | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hab
  | ⟨1, _⟩, ⟨2, _⟩ => d23 hp ht hf
  | ⟨1, _⟩, ⟨3, _⟩ => d24 hp ht hf
  | ⟨1, _⟩, ⟨4, _⟩ => d25 hp ht hf
  | ⟨2, _⟩, ⟨0, _⟩ => (d13 hp ht hf).symm
  | ⟨2, _⟩, ⟨1, _⟩ => (d23 hp ht hf).symm
  | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hab
  | ⟨2, _⟩, ⟨3, _⟩ => d34 hp ht hf
  | ⟨2, _⟩, ⟨4, _⟩ => d35 hp ht hf
  | ⟨3, _⟩, ⟨0, _⟩ => (d14 hp ht hf).symm
  | ⟨3, _⟩, ⟨1, _⟩ => (d24 hp ht hf).symm
  | ⟨3, _⟩, ⟨2, _⟩ => (d34 hp ht hf).symm
  | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hab
  | ⟨3, _⟩, ⟨4, _⟩ => d45 hp ht hf
  | ⟨4, _⟩, ⟨0, _⟩ => (d15 hp ht hf).symm
  | ⟨4, _⟩, ⟨1, _⟩ => (d25 hp ht hf).symm
  | ⟨4, _⟩, ⟨2, _⟩ => (d35 hp ht hf).symm
  | ⟨4, _⟩, ⟨3, _⟩ => (d45 hp ht hf).symm
  | ⟨4, _⟩, ⟨4, _⟩ => absurd rfl hab
  | ⟨k + 5, h⟩, _ => absurd h (by omega)
  | _, ⟨k + 5, h⟩ => absurd h (by omega)

theorem hsub_all : ∀ a : Fin 5, regionOf p t a ⊆ (tgt hp ht).carrier := by
  have hc : (tgt hp ht).carrier = Phi (fr p t) '' HT p t := carrier_triC _ _ _ _ _ _
  intro a
  rw [hc]
  exact match a with
  | ⟨0, _⟩ => Set.image_mono (sub1 hp ht)
  | ⟨1, _⟩ => Set.image_mono (sub2 hp ht)
  | ⟨2, _⟩ => Set.image_mono (sub3 hp ht)
  | ⟨3, _⟩ => Set.image_mono (sub4 hp ht)
  | ⟨4, _⟩ => Set.image_mono (sub5 hp ht)
  | ⟨k + 5, h⟩ => absurd h (by omega)

open MeasureTheory in
theorem volMod : volume (Mod hp ht).carrier
    = ENNReal.ofReal (|sD (fr p t) / (2 * fr p t)| * (((p + t) * (t * (2 * p + t))) * ((p + t) * (p * (p + t)))))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold Mod brickL
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have hX : 0 < ((p + t) * (t * (2 * p + t))) * ((p + t) * (p * (p + t))) := by positivity
  rw [← abs_of_pos hX]
  congr 1
  dsimp only
  ring

open MeasureTheory in
theorem volTgt : volume (tgt hp ht).carrier
    = ENNReal.ofReal (|sD (fr p t) / (2 * fr p t)| * (p * t * (p + t) ^ 3 * (2 * p + t)
        * (p ^ 2 + 4 * p * t + 2 * t ^ 2) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2)))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold tgt
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have hX : 0 < p * t * (p + t) ^ 3 * (2 * p + t)
        * (p ^ 2 + 4 * p * t + 2 * t ^ 2) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2) := by positivity
  rw [← abs_of_pos hX]
  congr 1
  simp only [vV0, vP2, vW]
  ring

open MeasureTheory in
theorem hvol_all (N : ℕ) (hN : (N : ℝ) = (p ^ 2 + 4 * p * t + 2 * t ^ 2) * (2 * p ^ 2 + 6 * p * t + 3 * t ^ 2)) :
    (N : ENNReal) * volume (Mod hp ht).carrier = volume (tgt hp ht).carrier := by
  rw [volMod hp ht, volTgt hp ht, ← mul_assoc, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 2
  rw [hN]; ring

/-- **The S2 layout, real parameters.** -/
theorem s2_real (kb ka kA np N : ℕ) (hNsum : ∑ a, cnt kb ka kA np a = N) (hkb0 : 0 < kb) (hka0 : 0 < ka) (hkA0 : 0 < kA) (hnp0 : 0 < np)
    (hkb : (kb : ℝ) = t * (2 * p + t)) (hka : (ka : ℝ) = p * (p + t))
    (hkA : (kA : ℝ) = p ^ 2 + 4 * p * t + 2 * t ^ 2) (hnp : (np : ℝ) = p ^ 2) :
    ∃ D : CongruentDissection N, D.model = Mod hp ht ∧ D.target = tgt hp ht := by
  subst hNsum
  have R : ∀ a : Fin 5, RTiling (regionOf p t a) (Mod hp ht) (cnt kb ka kA np a) := fun a => match a with
    | ⟨0, _⟩ => R1 hp ht kb hkb0 hkb
    | ⟨1, _⟩ => R2 hp ht kb hkb0 hkb
    | ⟨2, _⟩ => R3 hp ht ka hka0 hka
    | ⟨3, _⟩ => R4 hp ht kA hkA0 hkA
    | ⟨4, _⟩ => RTiling.castN (by
          show 2 * (kb - 1 + 1) * (np - 1 + 1) = 2 * kb * np
          rw [Nat.sub_add_cancel hkb0, Nat.sub_add_cancel hnp0])
        (R5 hp ht (kb - 1) (np - 1)
          (by have := Nat.sub_add_cancel hkb0; rw [← hkb]; exact_mod_cast this)
          (by have := Nat.sub_add_cancel hnp0; rw [← hnp]; exact_mod_cast this))
    | ⟨k + 5, h⟩ => absurd h (by omega)
  refine pack_exists (M := Mod hp ht) (T := tgt hp ht) (regionOf p t) (cnt kb ka kA np) R
    (hS_all hp ht) (hsub_all hp ht) (hvol_all hp ht _ ?_)
  rw [Fin.sum_univ_five]
  show (((kb * kb + kb * kb + ka * ka + kA * kA + 2 * kb * np : ℕ)) : ℝ) = _
  push_cast
  rw [hkb, hka, hkA, hnp]
  ring


/-! ### side lengths of the layout (frame scale `q`) -/
omit hp ht in
theorem s2all_eq_of_sq {d c : ℝ} (hd : 0 ≤ d) (hc : 0 ≤ c) (h : d ^ 2 = c ^ 2) : d = c :=
  Erdos634.Draft.SumTwoSquares.eqsq hd hc h

/-- Sides of the target `V0 P2 W` and of the model: `q·(B b, A c, c²)` and `q·(b, a, c)`. -/
theorem sides_real :
    dist ((tgt hp ht).pts 0) ((tgt hp ht).pts 1)
        = (p + t) * ((2 * p ^ 2 + 6 * p * t + 3 * t ^ 2) * (t * (2 * p + t))) ∧
    dist ((tgt hp ht).pts 1) ((tgt hp ht).pts 2)
        = (p + t) * ((p ^ 2 + 4 * p * t + 2 * t ^ 2) * (p + t) ^ 2) ∧
    dist ((tgt hp ht).pts 2) ((tgt hp ht).pts 0) = (p + t) * ((p + t) ^ 2) ^ 2 ∧
    dist ((Mod hp ht).pts 0) ((Mod hp ht).pts 1) = (p + t) * (t * (2 * p + t)) ∧
    dist ((Mod hp ht).pts 1) ((Mod hp ht).pts 2) = (p + t) * (p * (p + t)) ∧
    dist ((Mod hp ht).pts 2) ((Mod hp ht).pts 0) = (p + t) * (p + t) ^ 2 := by
  have h1 : p ≠ 0 := hp.ne'
  have h2 : p + t ≠ 0 := by positivity
  have hf := hfr hp ht
  have hx : ∀ a b c : ℝ × ℝ, ∀ r : ℝ, 0 ≤ r → ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 + (a.1 - b.1) * (a.2 - b.2) / fr p t = r ^ 2) →
      dist (Phi (fr p t) a) (Phi (fr p t) b) = r := fun a b c r hr h => by
    refine s2all_eq_of_sq dist_nonneg hr ?_
    rw [sq_Phi' hf]; exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tgt, triC_pts]
    exact hx _ _ (0, 0) _ (by positivity) (by simp only [fr, vV0, vP2]; field_simp; ring)
  · simp only [tgt, triC_pts]
    exact hx _ _ (0, 0) _ (by positivity) (by simp only [fr, vP2, vW]; field_simp; ring)
  · simp only [tgt, triC_pts]
    exact hx _ _ (0, 0) _ (by positivity) (by simp only [fr, vW, vV0]; field_simp; ring)
  · simp only [Mod, brickL, triC_pts]
    exact hx _ _ (0, 0) _ (by positivity) (by simp only [fr]; field_simp; ring)
  · simp only [Mod, brickL, triC_pts]
    exact hx _ _ (0, 0) _ (by positivity) (by simp only [fr]; field_simp; ring)
  · simp only [Mod, brickL, triC_pts]
    exact hx _ _ (0, 0) _ (by positivity) (by simp only [fr]; field_simp; ring)

end asm

/-! ### the theorems for natural `p < q` -/
theorem s2_family_all_dissection (p q : ℕ) (hp : 0 < p) (hpq : p < q) :
    Nonempty (CongruentDissection ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2))) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (p : ℝ) < q := by exact_mod_cast hpq
  have ht : (0 : ℝ) < (q : ℝ) - p := by linarith
  have h1 : p ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hpq.le 2
  have h2 : p ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hpq (by norm_num)
  have h3 : p ^ 2 ≤ 2 * q ^ 2 := by omega
  have h4 : p ^ 2 ≤ 3 * q ^ 2 := by omega
  have hpos : 0 < p ^ 2 := by positivity
  have hsum : ∑ a, cnt (q ^ 2 - p ^ 2) (p * q) (2 * q ^ 2 - p ^ 2) (p ^ 2) a
      = (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) := by
    rw [Fin.sum_univ_five]
    show (q ^ 2 - p ^ 2) * (q ^ 2 - p ^ 2) + (q ^ 2 - p ^ 2) * (q ^ 2 - p ^ 2) + (p * q) * (p * q)
      + (2 * q ^ 2 - p ^ 2) * (2 * q ^ 2 - p ^ 2) + 2 * (q ^ 2 - p ^ 2) * p ^ 2 = _
    zify [h1, h3, h4]
    ring
  obtain ⟨D, -, -⟩ := s2_real (p := (p : ℝ)) (t := (q : ℝ) - p) hp' ht (q ^ 2 - p ^ 2) (p * q) (2 * q ^ 2 - p ^ 2) (p ^ 2) _ hsum
    (by omega) (Nat.mul_pos hp (by omega)) (by omega) hpos
    (by rw [Nat.cast_sub h1]; push_cast; ring) (by push_cast; ring)
    (by rw [Nat.cast_sub h3]; push_cast; ring) (by push_cast; ring)
  exact ⟨D⟩

/-- **S2 for all `0 < p < q`** (layout of D. Paliy): `(2q²−p²)(3q²−p²)` is a tile count. -/
theorem s2_family_all (p q : ℕ) (hp : 0 < p) (hpq : p < q) :
    Erdos634.Draft.TileCountFamilies.TileCount ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)) :=
  s2_family_all_dissection p q hp hpq

/-- with the side lengths: the target has sides `q·(B b, A c, c²)` and the tile `q·(b, a, c)`
(`a = pq, b = q²−p², c = q², A = 2q²−p², B = 3q²−p²`). -/
theorem s2_family_all_sides (p q : ℕ) (hp : 0 < p) (hpq : p < q) :
    ∃ D : CongruentDissection ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)),
      dist (D.target.pts 0) (D.target.pts 1) = (q : ℝ) * ((3 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2) * ((q : ℝ) ^ 2 - (p : ℝ) ^ 2)) ∧
      dist (D.target.pts 1) (D.target.pts 2) = (q : ℝ) * ((2 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2) * (q : ℝ) ^ 2) ∧
      dist (D.target.pts 2) (D.target.pts 0) = (q : ℝ) * ((q : ℝ) ^ 2) ^ 2 ∧
      dist (D.model.pts 0) (D.model.pts 1) = (q : ℝ) * ((q : ℝ) ^ 2 - (p : ℝ) ^ 2) ∧
      dist (D.model.pts 1) (D.model.pts 2) = (q : ℝ) * ((p : ℝ) * q) ∧
      dist (D.model.pts 2) (D.model.pts 0) = (q : ℝ) * (q : ℝ) ^ 2 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (p : ℝ) < q := by exact_mod_cast hpq
  have ht : (0 : ℝ) < (q : ℝ) - p := by linarith
  have h1 : p ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hpq.le 2
  have h2 : p ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hpq (by norm_num)
  have h3 : p ^ 2 ≤ 2 * q ^ 2 := by omega
  have h4 : p ^ 2 ≤ 3 * q ^ 2 := by omega
  have hpos : 0 < p ^ 2 := by positivity
  have hsum : ∑ a, cnt (q ^ 2 - p ^ 2) (p * q) (2 * q ^ 2 - p ^ 2) (p ^ 2) a
      = (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) := by
    rw [Fin.sum_univ_five]
    show (q ^ 2 - p ^ 2) * (q ^ 2 - p ^ 2) + (q ^ 2 - p ^ 2) * (q ^ 2 - p ^ 2) + (p * q) * (p * q)
      + (2 * q ^ 2 - p ^ 2) * (2 * q ^ 2 - p ^ 2) + 2 * (q ^ 2 - p ^ 2) * p ^ 2 = _
    zify [h1, h3, h4]
    ring
  obtain ⟨D, hM, hT⟩ := s2_real (p := (p : ℝ)) (t := (q : ℝ) - p) hp' ht (q ^ 2 - p ^ 2) (p * q) (2 * q ^ 2 - p ^ 2) (p ^ 2) _ hsum
    (by omega) (Nat.mul_pos hp (by omega)) (by omega) hpos
    (by rw [Nat.cast_sub h1]; push_cast; ring) (by push_cast; ring)
    (by rw [Nat.cast_sub h3]; push_cast; ring) (by push_cast; ring)
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := sides_real (p := (p : ℝ)) (t := (q : ℝ) - p) hp' ht
  refine ⟨D, ?_⟩
  rw [hT, hM]
  have e : (p : ℝ) + ((q : ℝ) - p) = q := by ring
  rw [e] at s1 s2 s3 s4 s5 s6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s1]; ring
  · rw [s2]; ring
  · rw [s3]
  · rw [s4]; ring
  · rw [s5]
  · rw [s6]

end Erdos634.Draft.S2All

/-- witness: `p = 3, q = 4` gives `897` (Paliy's tiling; compare `Draft.N897.tileCount_897`, same shape scaled by 8:
here target `4·(273, 368, 256)`, tile `4·(7, 12, 16)`; there target `32·(273, 368, 256)`, tile `32·(7, 12, 16)`). -/
theorem Erdos634.Draft.S2All.tileCount_897_from_family :
    Erdos634.Draft.TileCountFamilies.TileCount 897 := by
  have := s2_family_all 3 4 (by norm_num) (by norm_num)
  norm_num at this
  exact this

#print axioms Erdos634.Draft.S2All.s2_family_all
#print axioms Erdos634.Draft.S2All.s2_family_all_sides
#print axioms Erdos634.Draft.S2All.tileCount_897_from_family
