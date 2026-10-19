-- Draft/CollarFam.lean — the collar up-set of the base-α rows (1,4), (1,6), (2,5) from the layer step.  UNAUDITED.  No sorry, no native_decide.
--
-- RESULTS (Lean):  ∀ g ≥ 5, TileCount (465 g²)   [row (e,f)=(1,4), tile (4,15,16)];
--                  ∀ g ≥ 7, TileCount (2485 g²)  [row (1,6), tile (6,35,36)];
--                  ∀ g ≥ 25, TileCount (966 g²)  [row (2,5), tile (10,21,25)],
-- by induction with `CollarLayer.layer_core` (T_G ⇒ T_{G+1}) from the template tilings T11625, T121765, T603750.
-- CREDIT: formalization of Paliy's alpha-isosceles up-set (docs/eventual-rational-families.md, 2026-09-29; macrodissection of
-- Beeson Thm 24 + gluing; seeds 84, 189: Beeson v4 Figs 28–29, 189 credited to Harries) — an INDEPENDENT construction: the layer step
-- ((project working notes), our engine `bto`) is ours, as are the Lean proofs; the macro
-- dissection idea is Laczkovich's; skew frame S2L: Beeson–Roșu.
import Erdos634.Draft.CollarLayer
import Erdos634.Draft.T11625
import Erdos634.Draft.T121765
import Erdos634.Draft.T603750

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.CollarFam
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- **Nat-level layer step.**  Row `(e,f)`, `b = f²−e²` (`f*f = e*e + b`), `e f ≤ b`, frame `φ = f/e`. -/
theorem layer_step {φ : ℝ} (hφ : 1 < φ) (e f b N0 G : ℕ) (he : 0 < e) (hef : e < f) (hb : f * f = e * e + b)
    (hba : e * f ≤ b) (hφE : φ = (f : ℝ) / e) (hN0 : N0 = b * (b + f * f)) (hG : 1 ≤ G)
    (R : RTiling (TG φ (e : ℝ) (f : ℝ) (G : ℝ))
      (brickL φ hφ ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((e : ℝ) * f) (pos_facts (by exact_mod_cast he) (by exact_mod_cast hef)).1
        (pos_facts (by exact_mod_cast he) (by exact_mod_cast hef)).2.1) (N0 * G * G)) :
    Nonempty (RTiling (TG φ (e : ℝ) (f : ℝ) ((G : ℝ) + 1))
      (brickL φ hφ ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((e : ℝ) * f) (pos_facts (by exact_mod_cast he) (by exact_mod_cast hef)).1
        (pos_facts (by exact_mod_cast he) (by exact_mod_cast hef)).2.1) (N0 * (G + 1) * (G + 1))) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  have hbR : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : ((f * f : ℕ) : ℝ) = ((e * e + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; nlinarith
  have hbaR : (e : ℝ) * f ≤ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by rw [← hbR]; exact_mod_cast hba
  have hle : e * f ≤ (b + f * f) * G := by
    calc e * f ≤ b := hba
      _ ≤ b + f * f := Nat.le_add_right _ _
      _ = (b + f * f) * 1 := (Nat.mul_one _).symm
      _ ≤ (b + f * f) * G := Nat.mul_le_mul_left _ hG
  obtain ⟨apn, hapn⟩ := Nat.exists_eq_add_of_le hle
  have hapR : (apn : ℝ) = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2 + (f : ℝ) ^ 2) * G - (e : ℝ) * f := by
    have : (((b + f * f) * G : ℕ) : ℝ) = ((e * f + apn : ℕ) : ℝ) := by rw [hapn]
    push_cast at this
    rw [hbR] at this
    nlinarith
  refine layer_core hφ hφE hE hEF hbaR G hG (f * f) b (b - e * f) apn N0 (by push_cast; ring) hbR ?_ hapR ?_ R
  · have : ((b - e * f : ℕ) : ℝ) = (b : ℝ) - (e * f : ℕ) := Nat.cast_sub hba
    rw [this, hbR]; push_cast; ring
  · rw [hN0]; push_cast; rw [hbR]; ring

/-- The model tile of the row `(e,f)` in the frame `φ`: the brick `(f²−e²) × (e f)`. -/
def Mrow {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) : Tri :=
  brickL φ hφ ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((e : ℝ) * f) (pos_facts (by exact_mod_cast he) (by exact_mod_cast hef)).1
    (pos_facts (by exact_mod_cast he) (by exact_mod_cast hef)).2.1

/-- **Induction on the layer step.** -/
theorem up_rtiling {φ : ℝ} (hφ : 1 < φ) (e f b N0 g0 : ℕ) (he : 0 < e) (hef : e < f) (hb : f * f = e * e + b)
    (hba : e * f ≤ b) (hφE : φ = (f : ℝ) / e) (hN0 : N0 = b * (b + f * f)) (hg0 : 1 ≤ g0)
    (base : Nonempty (RTiling (TG φ (e : ℝ) (f : ℝ) (g0 : ℝ)) (Mrow hφ e f he hef) (N0 * g0 * g0))) :
    ∀ g, g0 ≤ g → Nonempty (RTiling (TG φ (e : ℝ) (f : ℝ) (g : ℝ)) (Mrow hφ e f he hef) (N0 * g * g)) := by
  intro g hg
  induction g, hg using Nat.le_induction with
  | base => exact base
  | succ n hn ih =>
    obtain ⟨R⟩ := ih
    have h := layer_step hφ e f b N0 n he hef hb hba hφE hN0 (le_trans hg0 hn) R
    have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc]
    exact h

theorem tileCount_of_rtiling {φ : ℝ} (hφ : 1 < φ) {E F : ℝ} (hE : 0 < E) (hEF : E < F) {g : ℝ} (hg : 0 < g)
    {M : Tri} {N : ℕ} (R : RTiling (TG φ E F g) M N) : TileCount N := by
  obtain ⟨hb, ha, hc⟩ := pos_facts hE hEF
  have hB0 : 0 < pB0 E F := by unfold pB0; positivity
  have hdetT : ((pB0 E F * g, (0 : ℝ)).1 - ((0 : ℝ), (0 : ℝ)).1) *
      (((F^2-E^2)^2 * g, E*F*(F^2-E^2) * g).2 - ((0 : ℝ), (0 : ℝ)).2) -
      (((F^2-E^2)^2 * g, E*F*(F^2-E^2) * g).1 - ((0 : ℝ), (0 : ℝ)).1) *
      ((pB0 E F * g, (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2) ≠ 0 := by
    have : ((pB0 E F * g, (0 : ℝ)).1 - ((0 : ℝ), (0 : ℝ)).1) *
      (((F^2-E^2)^2 * g, E*F*(F^2-E^2) * g).2 - ((0 : ℝ), (0 : ℝ)).2) -
      (((F^2-E^2)^2 * g, E*F*(F^2-E^2) * g).1 - ((0 : ℝ), (0 : ℝ)).1) *
      ((pB0 E F * g, (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2) = pB0 E F * g * (E*F*(F^2-E^2) * g) := by
      simp only []; ring
    rw [this]
    exact (mul_pos (mul_pos hB0 hg) (mul_pos (mul_pos ha hb) hg)).ne'
  have hcar := carrier_triC φ hφ ((0 : ℝ), (0 : ℝ)) (pB0 E F * g, 0) ((F^2-E^2)^2 * g, E*F*(F^2-E^2) * g) hdetT
  have R' : RTiling (triC φ hφ ((0 : ℝ), (0 : ℝ)) (pB0 E F * g, 0) ((F^2-E^2)^2 * g, E*F*(F^2-E^2) * g) hdetT).carrier M N := by
    rw [hcar]; exact R
  exact ⟨RegionTiling.toCD R'⟩

/-- A dissection whose target carrier is `S` is a region tiling of `S`. -/
theorem rtiling_of_dissection {N : ℕ} {M : Tri} {S : Set Plane} (D : CongruentDissection N) (hm : D.model = M)
    (ht : D.target.carrier = S) : Nonempty (RTiling S M N) :=
  ⟨{ tile := D.tile
     covers := D.covers.trans ht
     disj := D.interiors_disjoint
     cong := fun i => by have := D.tiles_congruent i; rwa [hm] at this }⟩

/-- Base of row (1,4): the template tiling `Erdos634.Draft.T11625` as a region tiling of `T_5`. -/
theorem base_465 : Nonempty (RTiling (TG 4 ((1:ℕ):ℝ) ((4:ℕ):ℝ) ((5:ℕ):ℝ)) (Mrow Erdos634.Draft.T11625.hf 1 4 (by norm_num) (by norm_num)) (465 * 5 * 5)) := by
  obtain ⟨D, hD, hT⟩ := Erdos634.Draft.LadderFam.pack_exists' (M := Erdos634.Draft.WBrickF.MF 4 Erdos634.Draft.T11625.hf) (T := Erdos634.Draft.T11625.tgt) Erdos634.Draft.T11625.regionOf Erdos634.Draft.T11625.cnt Erdos634.Draft.T11625.famAll Erdos634.Draft.T11625.hS_all Erdos634.Draft.T11625.hsub_all Erdos634.Draft.T11625.hvol_all
  have hMeq : Mrow Erdos634.Draft.T11625.hf 1 4 (by norm_num) (by norm_num) = Erdos634.Draft.WBrickF.MF 4 Erdos634.Draft.T11625.hf := by
    unfold Mrow; try unfold Erdos634.Draft.WBrickF.MF
    congr 1 <;> norm_num
  have hTeq : TG 4 ((1:ℕ):ℝ) ((4:ℕ):ℝ) ((5:ℕ):ℝ) = Erdos634.Draft.T11625.tgt.carrier := by
    rw [Erdos634.Draft.T11625.tgt_carrier]; unfold TG pB0 Erdos634.Draft.T11625.tA Erdos634.Draft.T11625.tB Erdos634.Draft.T11625.tC; push_cast; norm_num
  have key : ∀ N : ℕ, N = 465 * 5 * 5 → ∀ D : CongruentDissection N, D.model = Erdos634.Draft.WBrickF.MF 4 Erdos634.Draft.T11625.hf → D.target = Erdos634.Draft.T11625.tgt →
      Nonempty (RTiling (TG 4 ((1:ℕ):ℝ) ((4:ℕ):ℝ) ((5:ℕ):ℝ)) (Mrow Erdos634.Draft.T11625.hf 1 4 (by norm_num) (by norm_num)) (465 * 5 * 5)) := by
    rintro N rfl D hm ht
    exact rtiling_of_dissection D (hm.trans hMeq.symm) (by rw [ht, hTeq])
  exact key _ (Erdos634.Draft.T11625.sum_cnt) D hD hT

/-- **Collar up-set, row (1,4):** `465 g²` is a tile count for every `g ≥ 5`. -/
theorem tileCount_465_sq : ∀ g : ℕ, 5 ≤ g → TileCount (465 * g * g) := by
  intro g hg
  obtain ⟨R⟩ := up_rtiling Erdos634.Draft.T11625.hf 1 4 15 465 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) base_465 g hg
  exact tileCount_of_rtiling Erdos634.Draft.T11625.hf (by norm_num) (by norm_num) (by exact_mod_cast (show 0 < g by omega)) R

/-- Base of row (1,6): the template tiling `Erdos634.Draft.T121765` as a region tiling of `T_7`. -/
theorem base_2485 : Nonempty (RTiling (TG 6 ((1:ℕ):ℝ) ((6:ℕ):ℝ) ((7:ℕ):ℝ)) (Mrow Erdos634.Draft.T121765.hf 1 6 (by norm_num) (by norm_num)) (2485 * 7 * 7)) := by
  obtain ⟨D, hD, hT⟩ := Erdos634.Draft.LadderFam.pack_exists' (M := Erdos634.Draft.WBrickF.MF 6 Erdos634.Draft.T121765.hf) (T := Erdos634.Draft.T121765.tgt) Erdos634.Draft.T121765.regionOf Erdos634.Draft.T121765.cnt Erdos634.Draft.T121765.famAll Erdos634.Draft.T121765.hS_all Erdos634.Draft.T121765.hsub_all Erdos634.Draft.T121765.hvol_all
  have hMeq : Mrow Erdos634.Draft.T121765.hf 1 6 (by norm_num) (by norm_num) = Erdos634.Draft.WBrickF.MF 6 Erdos634.Draft.T121765.hf := by
    unfold Mrow; try unfold Erdos634.Draft.WBrickF.MF
    congr 1 <;> norm_num
  have hTeq : TG 6 ((1:ℕ):ℝ) ((6:ℕ):ℝ) ((7:ℕ):ℝ) = Erdos634.Draft.T121765.tgt.carrier := by
    rw [Erdos634.Draft.T121765.tgt_carrier]; unfold TG pB0 Erdos634.Draft.T121765.tA Erdos634.Draft.T121765.tB Erdos634.Draft.T121765.tC; push_cast; norm_num
  have key : ∀ N : ℕ, N = 2485 * 7 * 7 → ∀ D : CongruentDissection N, D.model = Erdos634.Draft.WBrickF.MF 6 Erdos634.Draft.T121765.hf → D.target = Erdos634.Draft.T121765.tgt →
      Nonempty (RTiling (TG 6 ((1:ℕ):ℝ) ((6:ℕ):ℝ) ((7:ℕ):ℝ)) (Mrow Erdos634.Draft.T121765.hf 1 6 (by norm_num) (by norm_num)) (2485 * 7 * 7)) := by
    rintro N rfl D hm ht
    exact rtiling_of_dissection D (hm.trans hMeq.symm) (by rw [ht, hTeq])
  exact key _ (Erdos634.Draft.T121765.sum_cnt) D hD hT

/-- **Collar up-set, row (1,6):** `2485 g²` is a tile count for every `g ≥ 7`. -/
theorem tileCount_2485_sq : ∀ g : ℕ, 7 ≤ g → TileCount (2485 * g * g) := by
  intro g hg
  obtain ⟨R⟩ := up_rtiling Erdos634.Draft.T121765.hf 1 6 35 2485 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) base_2485 g hg
  exact tileCount_of_rtiling Erdos634.Draft.T121765.hf (by norm_num) (by norm_num) (by exact_mod_cast (show 0 < g by omega)) R

/-- Base of row (2,5): the template tiling `Erdos634.Draft.T603750` as a region tiling of `T_25`. -/
theorem base_966 : Nonempty (RTiling (TG (5/2:ℝ) ((2:ℕ):ℝ) ((5:ℕ):ℝ) ((25:ℕ):ℝ)) (Mrow Erdos634.Draft.T603750.hf 2 5 (by norm_num) (by norm_num)) (966 * 25 * 25)) := by
  obtain ⟨D, hD, hT⟩ := Erdos634.Draft.LadderFam.pack_exists' (M := Erdos634.Draft.WBrickF.brickL (5/2:ℝ) Erdos634.Draft.T603750.hf (21:ℝ) (10:ℝ) (by norm_num) (by norm_num)) (T := Erdos634.Draft.T603750.tgt) Erdos634.Draft.T603750.regionOf Erdos634.Draft.T603750.cnt Erdos634.Draft.T603750.famAll Erdos634.Draft.T603750.hS_all Erdos634.Draft.T603750.hsub_all Erdos634.Draft.T603750.hvol_all
  have hMeq : Mrow Erdos634.Draft.T603750.hf 2 5 (by norm_num) (by norm_num) = Erdos634.Draft.WBrickF.brickL (5/2:ℝ) Erdos634.Draft.T603750.hf (21:ℝ) (10:ℝ) (by norm_num) (by norm_num) := by
    unfold Mrow; try unfold Erdos634.Draft.WBrickF.MF
    congr 1 <;> norm_num
  have hTeq : TG (5/2:ℝ) ((2:ℕ):ℝ) ((5:ℕ):ℝ) ((25:ℕ):ℝ) = Erdos634.Draft.T603750.tgt.carrier := by
    rw [Erdos634.Draft.T603750.tgt_carrier]; unfold TG pB0 Erdos634.Draft.T603750.tA Erdos634.Draft.T603750.tB Erdos634.Draft.T603750.tC; push_cast
    congr 2; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; norm_num
  have key : ∀ N : ℕ, N = 966 * 25 * 25 → ∀ D : CongruentDissection N, D.model = Erdos634.Draft.WBrickF.brickL (5/2:ℝ) Erdos634.Draft.T603750.hf (21:ℝ) (10:ℝ) (by norm_num) (by norm_num) → D.target = Erdos634.Draft.T603750.tgt →
      Nonempty (RTiling (TG (5/2:ℝ) ((2:ℕ):ℝ) ((5:ℕ):ℝ) ((25:ℕ):ℝ)) (Mrow Erdos634.Draft.T603750.hf 2 5 (by norm_num) (by norm_num)) (966 * 25 * 25)) := by
    rintro N rfl D hm ht
    exact rtiling_of_dissection D (hm.trans hMeq.symm) (by rw [ht, hTeq])
  exact key _ (Erdos634.Draft.T603750.sum_cnt) D hD hT

/-- **Collar up-set, row (2,5):** `966 g²` is a tile count for every `g ≥ 25`. -/
theorem tileCount_966_sq : ∀ g : ℕ, 25 ≤ g → TileCount (966 * g * g) := by
  intro g hg
  obtain ⟨R⟩ := up_rtiling Erdos634.Draft.T603750.hf 2 5 21 966 25 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) base_966 g hg
  exact tileCount_of_rtiling Erdos634.Draft.T603750.hf (by norm_num) (by norm_num) (by exact_mod_cast (show 0 < g by omega)) R

end
end Erdos634.Draft.CollarFam

#print axioms Erdos634.Draft.CollarFam.tileCount_465_sq
#print axioms Erdos634.Draft.CollarFam.tileCount_2485_sq
#print axioms Erdos634.Draft.CollarFam.tileCount_966_sq
#print axioms Erdos634.Draft.CollarLayer.layer_core
