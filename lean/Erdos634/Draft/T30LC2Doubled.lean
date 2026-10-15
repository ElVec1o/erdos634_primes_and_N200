import Mathlib.Tactic
import Erdos634.Draft.T30LC2Corner

/-!
# (C2) at the doubled corner, both ends, with side lengths

`SideTile D P u a b`: there is a tile `K` with a vertex of angle `π/3` at `P` and one of its two edges at `P` runs along the ray `ℝ≥0 u`, with length `a` or `b`.
`c2_config` / `c2_doubled_corner`: for the corner tile `T` (π/3 at the target corner `O`, edges along the sides ending at `P`, `Q`, neither a target vertex),
`SideTile D P (side direction through P)` and `SideTile D Q (side direction through Q)`: the second supported tile on each side starts with `π/3`, and its edge on the
side has length `a` or `b` (never `c`).  `backward_mem`: the backward point `P − ε(P−O)` is in the corner tile (so the direction in `sep_not_mem` matters).
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6 Erdos634.ChordFar Erdos634.Pi3Corner Erdos634.SectorFill

def SideTile {N : ℕ} (D : CongruentDissection N) (P u : Plane) (a b : ℝ) : Prop :=
  ∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = P ∧ (D.tile K).angleAt l = Real.pi / 3 ∧
    ((SameRay ℝ u ((D.tile K).pts (l + 1) - P) ∧
        (dist P ((D.tile K).pts (l + 1)) = a ∨ dist P ((D.tile K).pts (l + 1)) = b)) ∨
      (SameRay ℝ u ((D.tile K).pts (l + 2) - P) ∧
        (dist P ((D.tile K).pts (l + 2)) = a ∨ dist P ((D.tile K).pts (l + 2)) = b)))

theorem pi3_edge_ab {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c) (K : Fin N) (l : Fin 3)
    (hang : (D.tile K).angleAt l = Real.pi / 3) :
    (dist ((D.tile K).pts l) ((D.tile K).pts (l + 1)) = a ∨ dist ((D.tile K).pts l) ((D.tile K).pts (l + 1)) = b) ∧
    (dist ((D.tile K).pts l) ((D.tile K).pts (l + 2)) = a ∨ dist ((D.tile K).pts l) ((D.tile K).pts (l + 2)) = b) := by
  have hU := tile_sixty D hS K
  have hopp := opp_c_of_pi3 hirr hU l hang
  have hor := tri_two_orient hU hac hbc l hopp
  have e3 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e4 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e5 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have e6 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  simp only [Tri.oppLen, e3, e4, e5, e6] at hor
  constructor
  · rcases hor with ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩
    · exact Or.inr h1
    · exact Or.inl h1
  · rw [dist_comm]
    rcases hor with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
    · exact Or.inl h1
    · exact Or.inr h1

theorem sideTile_of {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c) {P u : Plane}
    (h : ∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = P ∧ (D.tile K).angleAt l = Real.pi / 3 ∧
      (SameRay ℝ u ((D.tile K).pts (l + 1) - P) ∨ SameRay ℝ u ((D.tile K).pts (l + 2) - P))) :
    SideTile D P u a b := by
  obtain ⟨K, l, hl, hang, hray⟩ := h
  obtain ⟨h1, h2⟩ := pi3_edge_ab D hirr hS hac hbc K l hang
  rw [hl] at h1 h2
  exact ⟨K, l, hl, hang, hray.elim (fun h => Or.inl ⟨h, h1⟩) (fun h => Or.inr ⟨h, h2⟩)⟩

/-- **Control** for `sep_not_mem`: the BACKWARD points `P − ε(P − O)` (`0 < ε ≤ 1`) lie on the segment `[O,P]`, hence in the tile. -/
theorem backward_mem (O P Q : Plane) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    P + (-ε) • (P - O) ∈ convexHull ℝ {O, P, Q} := by
  have hO : O ∈ convexHull ℝ ({O, P, Q} : Set Plane) := subset_convexHull ℝ _ (by simp)
  have hP : P ∈ convexHull ℝ ({O, P, Q} : Set Plane) := subset_convexHull ℝ _ (by simp)
  have := (convex_convexHull ℝ ({O, P, Q} : Set Plane)).add_smul_sub_mem hP hO (t := ε) ⟨h0.le, h1⟩
  have e : P + ε • (O - P) = P + (-ε) • (P - O) := by
    rw [neg_smul, ← smul_neg, neg_sub]
  rwa [e] at this

set_option maxHeartbeats 800000 in
theorem c2_config {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x + y + z = 1)
    (i : Fin N) (j : Fin 3) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hjv : (D.tile i).pts j = D.target.pts v) (hang : (D.tile i).angleAt j = Real.pi / 3)
    {p r : ℝ} (hp0 : 0 < p) (hr0 : 0 < r)
    (hP : (D.tile i).pts (j + 1) - D.target.pts v = p • (D.target.pts w - D.target.pts v))
    (hQ : (D.tile i).pts (j + 2) - D.target.pts v = r • (D.target.pts z - D.target.pts v))
    (hPA : (D.tile i).pts (j + 1) ≠ D.target.pts w) (hQB : (D.tile i).pts (j + 2) ≠ D.target.pts z) :
    SideTile D ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 1) - D.target.pts v) a b ∧
    SideTile D ((D.tile i).pts (j + 2)) ((D.tile i).pts (j + 2) - D.target.pts v) a b := by
  obtain ⟨j', hj', hcar2, hangs, hl1, hl2⟩ := aux_reflection_ex D hirr hS hac hbc hword i j v w z hvw hvz hwz
    hjv hang hp0 hr0 hP hQ hPA hQB
  set T := D.target with hT
  set P := (D.tile i).pts (j + 1) with hPdef
  set Q := (D.tile i).pts (j + 2) with hQdef
  set O := T.pts v with hO
  rw [hjv] at hcar2
  have hPform : P = (1 - p) • T.pts v + p • T.pts w := by
    have : P = T.pts v + p • (T.pts w - T.pts v) := by rw [← hP]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hQform : Q = (1 - r) • T.pts v + r • T.pts z := by
    have : Q = T.pts v + r • (T.pts z - T.pts v) := by rw [← hQ]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hcd : ∀ (m n : Fin 3), T.basis.coord m (T.pts n) = if m = n then 1 else 0 :=
    fun m n => AffineBasis.coord_apply T.basis m n
  have hPmem : P ∈ T.carrier := Erdos634.BaseSelection.tile_subset_target D.toDissection i
    (subset_convexHull ℝ _ ⟨j + 1, rfl⟩)
  have hQmem : Q ∈ T.carrier := Erdos634.BaseSelection.tile_subset_target D.toDissection i
    (subset_convexHull ℝ _ ⟨j + 2, rfl⟩)
  have hp1 : p < 1 := by
    have hmem' := hPmem
    rw [T.carrier_eq_nonneg_coord] at hmem'
    have hnn : 0 ≤ T.basis.coord v P := hmem' v
    rw [hPform, aff_comb _ _ _ _ _ (by ring), hcd, hcd] at hnn
    simp [hvw] at hnn
    rcases lt_or_eq_of_le (by linarith : p ≤ 1) with h | h
    · exact h
    · exfalso; apply hPA; rw [hPform, h]; simp
  have hr1 : r < 1 := by
    have hmem' := hQmem
    rw [T.carrier_eq_nonneg_coord] at hmem'
    have hnn : 0 ≤ T.basis.coord v Q := hmem' v
    rw [hQform, aff_comb _ _ _ _ _ (by ring), hcd, hcd] at hnn
    simp [hvz] at hnn
    rcases lt_or_eq_of_le (by linarith : r ≤ 1) with h | h
    · exact h
    · exfalso; apply hQB; rw [hQform, h]; simp
  obtain ⟨-, -, -, hfr, hnv, -, -⟩ := clamps T v w z hvw hvz hwz hp0 hp1 hr0 hr1
  obtain ⟨-, -, -, hfr', hnv', -, -⟩ := clamps T v z w hvz hvw hwz.symm hr0 hr1 hp0 hp1
  have hPfr : P ∈ frontier T.carrier := by rw [hPform]; exact hfr
  have hPnv : P ∉ Set.range T.pts := by rw [hPform]; exact hnv
  have hQfr : Q ∈ frontier T.carrier := by rw [hQform]; exact hfr'
  have hQnv : Q ∉ Set.range T.pts := by rw [hQform]; exact hnv'
  obtain ⟨g, cg, hg0, hgle, hgv, hgw, hgz⟩ := supp_pair T v w z hvw hvz hwz
  obtain ⟨h, ch, hh0, hhle, hhv, hhz, hhw⟩ := supp_pair T v z w hvz hvw hwz.symm
  have hgP : g P = cg := by rw [hPform, lin_comb, hgv, hgw]; ring
  have hhQ : h Q = ch := by rw [hQform, lin_comb, hhv, hhz]; ring
  -- the corner is a genuine corner: `P - O`, `Q - O` at angle `π/3`
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have hj1 : P - O ≠ 0 := by
    rw [sub_ne_zero, ← hjv]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
  have hj2 : Q - O ≠ 0 := by
    rw [sub_ne_zero, ← hjv]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
  have hang' : InnerProductGeometry.angle (P - O) (Q - O) = Real.pi / 3 := by
    have := hang
    unfold Tri.angleAt cornerAngle EuclideanGeometry.angle at this
    simp only [vsub_eq_sub] at this
    rw [hjv] at this
    exact this
  have hind := cross_ne_of_angle hj1 hj2 hang'
  have hind' : (Q - O) 0 * (P - O) 1 - (Q - O) 1 * (P - O) 0 ≠ 0 := fun h => hind (by linarith)
  -- carriers
  have hTc : (D.tile i).carrier = convexHull ℝ {O, P, Q} := by
    unfold Tri.carrier; rw [range_pts_eq _ j, hjv]
  have hTc' : (D.tile i).carrier = convexHull ℝ {O, Q, P} := by rw [hTc, Set.pair_comm]
  have hcar2' : (D.tile j').carrier = convexHull ℝ {Q, P, Q + P - O} := by
    rw [hcar2]
    congr 1
    rw [Set.insert_comm, add_comm P Q]
  -- forward points stay in the target
  have hconv : Convex ℝ T.carrier := convex_convexHull ℝ _
  have hOmem : O ∈ T.carrier := subset_convexHull ℝ _ ⟨v, rfl⟩
  have hwmem : T.pts w ∈ T.carrier := subset_convexHull ℝ _ ⟨w, rfl⟩
  have hzmem : T.pts z ∈ T.carrier := subset_convexHull ℝ _ ⟨z, rfl⟩
  have hinP : ∀ ε : ℝ, 0 < ε → ε ≤ (1 - p) / p → P + ε • (P - O) ∈ T.carrier := by
    intro ε hε hεle
    have hεp : ε * p ≤ 1 - p := (le_div_iff₀ hp0).mp hεle
    have e : P + ε • (P - O) = O + ((1 + ε) * p) • (T.pts w - O) := by
      have h1 : P + ε • (P - O) = O + (1 + ε) • (P - O) := by rw [add_smul, one_smul]; abel
      rw [h1, hP, smul_smul]
    rw [e]
    exact hconv.add_smul_sub_mem hOmem hwmem ⟨by positivity, by nlinarith⟩
  have hinQ : ∀ ε : ℝ, 0 < ε → ε ≤ (1 - r) / r → Q + ε • (Q - O) ∈ T.carrier := by
    intro ε hε hεle
    have hεp : ε * r ≤ 1 - r := (le_div_iff₀ hr0).mp hεle
    have e : Q + ε • (Q - O) = O + ((1 + ε) * r) • (T.pts z - O) := by
      have h1 : Q + ε • (Q - O) = O + (1 + ε) • (Q - O) := by rw [add_smul, one_smul]; abel
      rw [h1, hQ, smul_smul]
    rw [e]
    exact hconv.add_smul_sub_mem hOmem hzmem ⟨by positivity, by nlinarith⟩
  have hpos1 : 0 < (1 - p) / p := div_pos (by linarith) hp0
  have hpos2 : 0 < (1 - r) / r := div_pos (by linarith) hr0
  -- angles
  have hAB := hangs
  have hA' := hl1
  have hB' := hl2
  refine ⟨sideTile_of D hirr hS hac hbc ?_, sideTile_of D hirr hS hac hbc ?_⟩
  · refine c2_at_end D hirr hS hind hPfr hPnv g hg0 cg hgle hgP hgv hpos1 hinP i j' hTc hcar2 ?_
    rcases hAB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by rw [hA', h2]⟩
    · exact Or.inr ⟨h1, by rw [hA', h2]⟩
  · refine c2_at_end D hirr hS hind' hQfr hQnv h hh0 ch hhle hhQ hhv hpos2 hinQ i j' hTc' hcar2' ?_
    rcases hAB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, by rw [hB', h1]⟩
    · exact Or.inl ⟨h2, by rw [hB', h1]⟩

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.c2_config
#print axioms Erdos634.C2Forward.backward_mem
