-- Assembly and the theorem `s2_family_gen`.
-- For naturals p ≥ 1, q with 2p² < q²:  N = (2q²-p²)(3q²-p²) is a tile count (tile (pq, q²-p², q²)).
-- No sorry, no native_decide; axioms printed at the foot.
import Erdos634.Draft.S2GPieces

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.S2G
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.BrickGridF (shift_rect)
open Erdos634.Draft.S2L (pack_exists)

/-- `P = p²`, `g = q² - 2p²` (as a real, from the natural subtraction). -/
noncomputable def Pr (p : ℕ) : ℝ := (p : ℝ) ^ 2
noncomputable def gr (p q : ℕ) : ℝ := ((q ^ 2 - 2 * p ^ 2 : ℕ) : ℝ)

theorem cast_pred {n : ℕ} (h : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
  rw [Nat.cast_sub h]; push_cast; ring

theorem q2pos {p q : ℕ} (hp : 1 ≤ p) (hg : 2 * p ^ 2 < q ^ 2) : 0 < q ^ 2 := by omega

noncomputable def regionOf (p q : ℕ) : Fin 6 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi (ff (Pr p) (gr p q)) '' H1 (Pr p) (gr p q)
  | ⟨1, _⟩ => Phi (ff (Pr p) (gr p q)) '' H2 (Pr p) (gr p q)
  | ⟨2, _⟩ => Phi (ff (Pr p) (gr p q)) '' H3 (Pr p) (gr p q)
  | ⟨3, _⟩ => Phi (ff (Pr p) (gr p q)) '' H4 (Pr p) (gr p q)
  | ⟨4, _⟩ => Phi (ff (Pr p) (gr p q)) '' H5 (Pr p) (gr p q)
  | ⟨5, _⟩ => Phi (ff (Pr p) (gr p q)) '' H6 (Pr p) (gr p q)
  | ⟨k + 6, h⟩ => absurd h (by omega)


section nat
variable {p q : ℕ} (hp : 1 ≤ p) (hg : 2 * p ^ 2 < q ^ 2)
include hp hg

theorem hPp : 0 < Pr p := by
  unfold Pr; have : (1 : ℝ) ≤ p := by exact_mod_cast hp
  positivity

theorem hgp : 0 < gr p q := by
  unfold gr
  have : 0 < q ^ 2 - 2 * p ^ 2 := by omega
  exact_mod_cast this

theorem hcq : ((q ^ 2 : ℕ) : ℝ) = 2 * Pr p + gr p q := by
  unfold Pr gr; rw [Nat.cast_sub hg.le]; push_cast; ring

theorem hbq : ((q ^ 2 - p ^ 2 : ℕ) : ℝ) = Pr p + gr p q := by
  have h1 : p ^ 2 ≤ q ^ 2 := by omega
  unfold Pr gr; rw [Nat.cast_sub h1, Nat.cast_sub hg.le]; push_cast; ring

theorem hapq : (((p * q : ℕ) : ℝ)) ^ 2 = Pr p * (2 * Pr p + gr p q) := by
  rw [← hcq hp hg]; unfold Pr; push_cast; ring

/-- Piece 6: the strip `Rect (c²+b²) (bB) 0 (bc)`: `g` columns × `c` rows of cells, `2 g c` tiles. -/
noncomputable def R6 : RTiling (Phi (ff (Pr p) (gr p q)) '' H6 (Pr p) (gr p q))
    (Mod (hPp hp hg) (hgp hp hg)) (2 * (q ^ 2 - 2 * p ^ 2) * q ^ 2) := by
  have hg1 : 1 ≤ q ^ 2 - 2 * p ^ 2 := by omega
  have hq1 : 1 ≤ q ^ 2 := by omega
  have S := grid (hfr (hPp hp hg) (hgp hp hg)) (hcpos (hPp hp hg) (hgp hp hg)) (hbpos (hPp hp hg) (hgp hp hg))
    (cellRT (hPp hp hg) (hgp hp hg)) (q ^ 2 - 2 * p ^ 2 - 1) (q ^ 2 - 1)
  have e1 := cast_pred hg1
  have e2 := cast_pred hq1
  have hc := hcq hp hg
  have S2 := shift_rect S ((2 * Pr p + gr p q) ^ 2 + (Pr p + gr p q) ^ 2) 0
    ((Pr p + gr p q) * (5 * Pr p + 3 * gr p q)) ((Pr p + gr p q) * (2 * Pr p + gr p q))
    (by rw [e1]; unfold gr at *; ring) (by rw [e2, hc]; ring)
  refine RTiling.castN ?_ S2
  rw [Nat.sub_add_cancel hg1, Nat.sub_add_cancel hq1]

end nat

def cnt (p q : ℕ) : Fin 6 → ℕ := fun i => match i with
  | ⟨0, _⟩ => q ^ 2 * q ^ 2
  | ⟨1, _⟩ => q ^ 2 * q ^ 2
  | ⟨2, _⟩ => q ^ 2 * q ^ 2
  | ⟨3, _⟩ => (p * q) * (p * q)
  | ⟨4, _⟩ => (q ^ 2 - p ^ 2) * (q ^ 2 - p ^ 2)
  | ⟨5, _⟩ => 2 * (q ^ 2 - 2 * p ^ 2) * q ^ 2
  | ⟨k + 6, h⟩ => absurd h (by omega)

section nat2
variable {p q : ℕ} (hp : 1 ≤ p) (hg : 2 * p ^ 2 < q ^ 2)
include hp hg

noncomputable def Rall : ∀ a : Fin 6, RTiling (regionOf p q a)
    (Mod (hPp hp hg) (hgp hp hg)) (cnt p q a) := fun a => match a with
  | ⟨0, _⟩ => R1 (hPp hp hg) (hgp hp hg) (q ^ 2) (q2pos hp hg) (hcq hp hg)
  | ⟨1, _⟩ => R2 (hPp hp hg) (hgp hp hg) (q ^ 2) (q2pos hp hg) (hcq hp hg)
  | ⟨2, _⟩ => R3 (hPp hp hg) (hgp hp hg) (q ^ 2) (q2pos hp hg) (hcq hp hg)
  | ⟨3, _⟩ => R4 (hPp hp hg) (hgp hp hg) (p * q) (Nat.mul_pos hp (Nat.pos_of_ne_zero (by rintro rfl; simp at hg))) (hapq hp hg)
  | ⟨4, _⟩ => R5 (hPp hp hg) (hgp hp hg) (q ^ 2 - p ^ 2) (by omega) (hbq hp hg)
  | ⟨5, _⟩ => R6 hp hg
  | ⟨k + 6, h⟩ => absurd h (by omega)

theorem hS_all : ∀ a b : Fin 6, a ≠ b →
    Disjoint (interior (regionOf p q a))
      (interior (regionOf p q b)) := by
  have hP := hPp hp hg
  have hg' := hgp hp hg
  have hf := hfr hP hg'
  intro a b hab
  exact match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hab
  | ⟨0, _⟩, ⟨1, _⟩ => d12 hP hg' hf
  | ⟨0, _⟩, ⟨2, _⟩ => d13 hP hg' hf
  | ⟨0, _⟩, ⟨3, _⟩ => d14 hP hg' hf
  | ⟨0, _⟩, ⟨4, _⟩ => d15 hP hg' hf
  | ⟨0, _⟩, ⟨5, _⟩ => d16 hP hg' hf
  | ⟨1, _⟩, ⟨0, _⟩ => (d12 hP hg' hf).symm
  | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hab
  | ⟨1, _⟩, ⟨2, _⟩ => d23 hP hg' hf
  | ⟨1, _⟩, ⟨3, _⟩ => d24 hP hg' hf
  | ⟨1, _⟩, ⟨4, _⟩ => d25 hP hg' hf
  | ⟨1, _⟩, ⟨5, _⟩ => d26 hP hg' hf
  | ⟨2, _⟩, ⟨0, _⟩ => (d13 hP hg' hf).symm
  | ⟨2, _⟩, ⟨1, _⟩ => (d23 hP hg' hf).symm
  | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hab
  | ⟨2, _⟩, ⟨3, _⟩ => d34 hP hg' hf
  | ⟨2, _⟩, ⟨4, _⟩ => d35 hP hg' hf
  | ⟨2, _⟩, ⟨5, _⟩ => d36 hP hg' hf
  | ⟨3, _⟩, ⟨0, _⟩ => (d14 hP hg' hf).symm
  | ⟨3, _⟩, ⟨1, _⟩ => (d24 hP hg' hf).symm
  | ⟨3, _⟩, ⟨2, _⟩ => (d34 hP hg' hf).symm
  | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hab
  | ⟨3, _⟩, ⟨4, _⟩ => d45 hP hg' hf
  | ⟨3, _⟩, ⟨5, _⟩ => d46 hP hg' hf
  | ⟨4, _⟩, ⟨0, _⟩ => (d15 hP hg' hf).symm
  | ⟨4, _⟩, ⟨1, _⟩ => (d25 hP hg' hf).symm
  | ⟨4, _⟩, ⟨2, _⟩ => (d35 hP hg' hf).symm
  | ⟨4, _⟩, ⟨3, _⟩ => (d45 hP hg' hf).symm
  | ⟨4, _⟩, ⟨4, _⟩ => absurd rfl hab
  | ⟨4, _⟩, ⟨5, _⟩ => d56 hP hg' hf
  | ⟨5, _⟩, ⟨0, _⟩ => (d16 hP hg' hf).symm
  | ⟨5, _⟩, ⟨1, _⟩ => (d26 hP hg' hf).symm
  | ⟨5, _⟩, ⟨2, _⟩ => (d36 hP hg' hf).symm
  | ⟨5, _⟩, ⟨3, _⟩ => (d46 hP hg' hf).symm
  | ⟨5, _⟩, ⟨4, _⟩ => (d56 hP hg' hf).symm
  | ⟨5, _⟩, ⟨5, _⟩ => absurd rfl hab
  | ⟨k + 6, h⟩, _ => absurd h (by omega)
  | _, ⟨k + 6, h⟩ => absurd h (by omega)

/-- The target triangle `O B' C`. -/
noncomputable def tgt : Tri :=
  triC (ff (Pr p) (gr p q)) (hfr (hPp hp hg) (hgp hp hg)) pO (pB (Pr p) (gr p q)) (pC (Pr p) (gr p q))
    (detT (hPp hp hg) (hgp hp hg))

theorem hsub_all : ∀ a : Fin 6, regionOf p q a ⊆ (tgt hp hg).carrier := by
  have hP := hPp hp hg
  have hg' := hgp hp hg
  have hc : (tgt hp hg).carrier = Phi (ff (Pr p) (gr p q)) '' HT (Pr p) (gr p q) :=
    carrier_triC _ _ _ _ _ _
  intro a
  rw [hc]
  exact match a with
  | ⟨0, _⟩ => Set.image_mono (sub1 hP hg')
  | ⟨1, _⟩ => Set.image_mono (sub2 hP hg')
  | ⟨2, _⟩ => Set.image_mono (sub3 hP hg')
  | ⟨3, _⟩ => Set.image_mono (sub4 hP hg')
  | ⟨4, _⟩ => Set.image_mono (sub5 hP hg')
  | ⟨5, _⟩ => Set.image_mono (sub6 hP hg')
  | ⟨k + 6, h⟩ => absurd h (by omega)

end nat2

theorem sum_cnt (p q : ℕ) (hg : 2 * p ^ 2 < q ^ 2) :
    ∑ a, cnt p q a = (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) := by
  rw [Fin.sum_univ_six]
  show q ^ 2 * q ^ 2 + q ^ 2 * q ^ 2 + q ^ 2 * q ^ 2 + (p * q) * (p * q)
    + (q ^ 2 - p ^ 2) * (q ^ 2 - p ^ 2) + 2 * (q ^ 2 - 2 * p ^ 2) * q ^ 2 = _
  have h1 : p ^ 2 ≤ q ^ 2 := by omega
  have h2 : 2 * p ^ 2 ≤ q ^ 2 := hg.le
  have h3 : p ^ 2 ≤ 2 * q ^ 2 := by omega
  have h4 : p ^ 2 ≤ 3 * q ^ 2 := by omega
  zify [h1, h2, h3, h4]
  ring

theorem sum_cnt_real (p q : ℕ) (hg : 2 * p ^ 2 < q ^ 2) :
    ((∑ a, cnt p q a : ℕ) : ℝ) = (2 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2) * (3 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2) := by
  have h3 : p ^ 2 ≤ 2 * q ^ 2 := by omega
  have h4 : p ^ 2 ≤ 3 * q ^ 2 := by omega
  rw [sum_cnt p q hg, Nat.cast_mul, Nat.cast_sub h3, Nat.cast_sub h4]
  push_cast; ring

section real2
variable {P g : ℝ} (hP : 0 < P) (hg : 0 < g)
include hP hg

noncomputable def tgtR : Tri :=
  triC (ff P g) (hfr hP hg) pO (pB P g) (pC P g) (detT hP hg)

open MeasureTheory in
theorem volM : volume (Mod hP hg).carrier
    = ENNReal.ofReal (|sD (ff P g) / (2 * ff P g)| * ((2 * P + g) * (P + g)))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold Mod brickL
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have e : ((2 * P + g, (0 : ℝ)).1 - ((0 : ℝ), (0 : ℝ)).1) * ((2 * P + g, P + g).2 - ((0 : ℝ), (0 : ℝ)).2)
      - ((2 * P + g, P + g).1 - ((0 : ℝ), (0 : ℝ)).1) * ((2 * P + g, (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2)
      = (2 * P + g) * (P + g) := by ring
  rw [e, abs_of_pos (by positivity)]

open MeasureTheory in
theorem volT : volume (tgtR hP hg).carrier
    = ENNReal.ofReal (|sD (ff P g) / (2 * ff P g)| *
        ((P + g) * (2 * P + g) * (3 * P + 2 * g) * (5 * P + 3 * g)))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold tgtR
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have e : ((pB P g).1 - pO.1) * ((pC P g).2 - pO.2) - ((pC P g).1 - pO.1) * ((pB P g).2 - pO.2)
      = (P + g) * (2 * P + g) * (3 * P + 2 * g) * (5 * P + 3 * g) := by
    simp only [pO, pB, pC]; ring
  rw [e, abs_of_pos (by positivity)]
end real2

section nat3
variable {p q : ℕ} (hp : 1 ≤ p) (hg : 2 * p ^ 2 < q ^ 2)
include hp hg

open MeasureTheory in
theorem hvol_all :
    ((∑ a, cnt p q a : ℕ) : ENNReal) * volume (Mod (hPp hp hg) (hgp hp hg)).carrier
      = volume (tgt hp hg).carrier := by
  have hP := hPp hp hg
  have hg' := hgp hp hg
  have hc := hcq hp hg
  show _ = volume (tgtR hP hg').carrier
  rw [volM hP hg', volT hP hg', ← mul_assoc, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), sum_cnt_real p q hg]
  congr 2
  have hq2 : (q : ℝ) ^ 2 = 2 * Pr p + gr p q := by rw [← hc]; push_cast; ring
  have hp2 : (p : ℝ) ^ 2 = Pr p := rfl
  rw [hq2, hp2]
  ring

/-- **The S2 family, general p.** -/
theorem s2_family_gen_model :
    ∃ D : CongruentDissection ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)),
      D.model = Mod (hPp hp hg) (hgp hp hg) ∧ D.target = tgt hp hg := by
  have := pack_exists (M := Mod (hPp hp hg) (hgp hp hg)) (T := tgt hp hg)
    (regionOf p q) (cnt p q)
    (Rall hp hg) (hS_all hp hg) (hsub_all hp hg) (hvol_all hp hg)
  rw [sum_cnt p q hg] at this
  exact this

end nat3

theorem s2_family_gen (p q : ℕ) (hp : 1 ≤ p) (hg : 2 * p ^ 2 < q ^ 2) :
    Nonempty (CongruentDissection ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2))) := by
  obtain ⟨D, -, -⟩ := s2_family_gen_model hp hg
  exact ⟨D⟩

end Erdos634.Draft.S2G

#print axioms Erdos634.Draft.S2G.s2_family_gen
#print axioms Erdos634.Draft.S2G.s2_family_gen_model
