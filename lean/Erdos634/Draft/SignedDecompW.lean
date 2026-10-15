/-
Draft/SignedDecompW.lean  Part of `AllThreshold`.

Signed decomposition for `W_M(e, f)`, used for `prop:layerall` (a).  The statement: the triangle `ABQ` is a copy of `W_M(e, f)`, and `ABQ ∪ Q'QZ = ABQ' ∪ AQ'Z`.  So `T_M(e, f)` together with one copy of the tile at scale `Me` is
three copies of the tile at scale `fM`, and `W_M(e, f)` together with that copy is two.  The triangle `ABQ` has the angles `2α`, `α + β`, `β` at `A`, `Q`, `B` and the sides `|AQ| = Mfb`, `|QB| = Me(2f² − e²)`, `|AB| = Mf³`.
The numbers of tiles agree: `3f²M² − e²M² = M²(3f² − e²)` and `2f²M² − e²M² = M²(2f² − e²)`.

Contents, in the frame of `SignedDecompE1` (`Phi F`, `F = f / e`, `t = M e³`, the points `A = (0, v)`, `B = (u, 0)`, `Q = (u, v)`, `Q' = (u, k)`, `Z = (u + e, v)`; `ptQ` is `Q`):
* `regABQ`, `hull_regABQ`: the triangle `ABQ` as the region `{x ≤ u, y ≤ v, v x + u y ≥ u v}`;
* `frame_union_W`: `ABQ ∪ Q'QZ = ABQ' ∪ AQ'Z`; `disj_ABQ_Q1QZ`: the line `x = u` separates `ABQ` from `Q'QZ` (the other disjointness is `SignedDecompE1.disj_ABQ1_AQ1Z`);
* `d_BQ`, `nd_ABQ`, `triABQ`, `carrier_triABQ`, `sides_ABQ`: `ABQ` is a `Tri` with the sides `|AQ| = F (F² − 1) t`, `|QB| = (2F² − 1) t`, `|AB| = F³ t`;
* `WSignedDecomp`, `signed_decomposition_real_W`: the union identity, the two disjointness statements and the five side statements, for real `F > 1`, `t > 0`;
* `signed_decomposition_member_W`: for every member `1 ≤ e < f` and every `M ≥ 1`: `WSignedDecomp (f / e) (M e³)` and the side lengths in the form of `WTilable` and `ebelow_a`: `ABQ` has the sides `M f (f² − e²)`, `M e (2f² − e²)`, `M f³`
  (`W_M(e, f)`), `Q'QZ` has `(Me) a, (Me) c, (Me) b`, and `ABQ'`, `AQ'Z` have `(fM) a, (fM) c, (fM) b` (the tile at the scales `Me` and `fM`);
* `count_T`, `count_W`: the arithmetic identities `3 (fM)² − (Me)² = M² (3f² − e²)`, `2 (fM)² − (Me)² = M² (2f² − e²)` (in `ℕ`).
The angles of `ABQ` (`2α`, `α + β`, `β`) are not stated: the library defines `W_M` by its three side lengths (`CollarG.WTilable`, `ebelow_a`), and `SideRunGThickCount.W_corners_of_sides` gives the angles from the sides.  The `T` half of `prop:layerall` (a) is `SignedDecompG.signed_decomposition_member`.

No sorry, no native_decide.
-/
import Erdos634.Draft.SignedDecompG

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.SignedDecompW
open Erdos634.Draft.SignedDecompE1 Erdos634.Draft.WFrameF Erdos634.Draft.WBrickF Erdos634.Draft.WtoDeltaF
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)

/-! ## 1. The triangle `ABQ` and the union identity in frame coordinates -/

/-- `ABQ`: `x ≤ u`, `y ≤ v`, above `AB` (`A = (0, v)`, `B = (u, 0)`, `Q = (u, v)`). -/
def regABQ (u v : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ u ∧ p.2 ≤ v ∧ u * v ≤ v * p.1 + u * p.2}

theorem hull_regABQ {u v : ℝ} (hu : 0 < u) (hv0 : 0 < v) :
    convexHull ℝ ({((0 : ℝ), v), (u, (0 : ℝ)), (u, v)} : Set (ℝ × ℝ)) = regABQ u v := by
  have huv := mul_pos hu hv0
  apply Set.Subset.antisymm
  · intro p hp
    have h1 := tri_le' 1 0 u (by linarith) (by linarith) (by linarith) p hp
    have h2 := tri_le' 0 1 v (by linarith) (by linarith) (by linarith) p hp
    have h3 := tri_ge' v u (u * v) (by nlinarith) (by nlinarith) (by nlinarith) p hp
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro p ⟨h1, h2, h3⟩
    exact mem3 (u * v) (v * (u - p.1)) (u * (v - p.2)) (v * p.1 + u * p.2 - u * v)
      huv (mul_nonneg hv0.le (by linarith)) (mul_nonneg hu.le (by linarith)) (by linarith)
      (by ring) p (by ring) (by ring)

/-- **`ABQ ∪ Q'QZ = ABQ' ∪ AQ'Z`** in frame coordinates -/
theorem frame_union_W {u v k e : ℝ} (hu : 0 < u) (hk : 0 < k) (hv : k < v) (he : 0 < e) :
    regABQ u v ∪ regQ1QZ u v k e = regABQ1 u v k ∪ regAQ1Z u v k e := by
  have hv0 : 0 < v := by linarith
  have hvk : 0 < v - k := by linarith
  ext p
  simp only [Set.mem_union]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · -- a point of `ABQ`
      by_cases hl : (v - k) * p.1 + u * p.2 ≤ u * v
      · exact Or.inl ⟨h1, h3, hl⟩
      · rw [not_le] at hl
        have hyk : k ≤ p.2 := by
          by_contra hc
          rw [not_le] at hc
          nlinarith [mul_pos hu (sub_pos.2 hc), mul_nonneg hvk.le (sub_nonneg.2 h1)]
        refine Or.inr ⟨h2, hl.le, ?_⟩
        nlinarith [mul_nonneg hvk.le (sub_nonneg.2 h1), mul_nonneg he.le (sub_nonneg.2 hyk)]
    · -- a point of `Q'QZ`
      have hyk : k ≤ p.2 := by
        by_contra hc
        rw [not_le] at hc
        nlinarith [mul_pos he (sub_pos.2 hc), mul_nonneg hvk.le (sub_nonneg.2 h1)]
      refine Or.inr ⟨h2, ?_, h3⟩
      nlinarith [mul_nonneg hvk.le (sub_nonneg.2 h1), mul_nonneg hu.le (sub_nonneg.2 hyk)]
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · -- a point of `ABQ'`
      exact Or.inl ⟨h1, regABQ1_snd_le hu hk hv ⟨h1, h2, h3⟩, h2⟩
    · -- a point of `AQ'Z`
      by_cases hx : p.1 ≤ u
      · have hx0 : 0 ≤ p.1 := by
          by_contra hc
          rw [not_le] at hc
          nlinarith [mul_pos hvk (neg_pos.2 hc), mul_le_mul_of_nonneg_left h1 hu.le]
        exact Or.inl ⟨hx, h1, by nlinarith [mul_nonneg hk.le hx0]⟩
      · rw [not_le] at hx
        exact Or.inr ⟨hx.le, h1, h3⟩

/-- the base line `x = u` separates `ABQ` from `Q'QZ` -/
theorem disj_ABQ_Q1QZ (u v k e : ℝ) :
    Disjoint (interior (regABQ u v)) (interior (regQ1QZ u v k e)) :=
  interior_disj_fst u (fun p hp => hp.1) (fun p hp => hp.1)

/-! ## 2. The triangle `ABQ` as a `Tri` -/

theorem hull_ABQ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    convexHull ℝ ({ptA F t, ptB F t, ptQ F t} : Set (ℝ × ℝ)) = regABQ (sdU F t) (sdV F t) := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  exact hull_regABQ hu (by linarith)

/-- `|BQ| = (2 F² − 1) t` (the side `QB` of `W`) -/
theorem d_BQ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptB F t)) (Phi F (ptQ F t)) = (2 * F ^ 2 - 1) * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos hB ht).le ?_
  simp only [ptB, ptQ, sdU, sdV]
  ring1

theorem nd_ABQ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    ((ptB F t).1 - (ptA F t).1) * ((ptQ F t).2 - (ptA F t).2) -
      ((ptQ F t).1 - (ptA F t).1) * ((ptB F t).2 - (ptA F t).2) ≠ 0 := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  have e : ((ptB F t).1 - (ptA F t).1) * ((ptQ F t).2 - (ptA F t).2) -
      ((ptQ F t).1 - (ptA F t).1) * ((ptB F t).2 - (ptA F t).2) = sdU F t * sdV F t := by
    simp only [ptA, ptB, ptQ]; ring
  rw [e]
  exact (mul_pos hu (by linarith)).ne'

/-- `ABQ` (vertices in the order `A, B, Q`) -/
noncomputable def triABQ (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) : Erdos634.Geometry.Tri :=
  triC F hF1 (ptA F t) (ptB F t) (ptQ F t) (nd_ABQ F t hF1 ht)

theorem carrier_triABQ (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    (triABQ F hF1 t ht).carrier = Phi F '' convexHull ℝ ({ptA F t, ptB F t, ptQ F t} : Set (ℝ × ℝ)) :=
  carrier_triC F hF1 _ _ _ _

/-- `ABQ` has the sides `|AQ| = F (F² − 1) t`, `|QB| = (2F² − 1) t`, `|AB| = F³ t`: the sides of `W_M(e, f)` -/
theorem sides_ABQ (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    HasSides (triABQ F hF1 t ht) (F * (F ^ 2 - 1) * t) ((2 * F ^ 2 - 1) * t) (F ^ 3 * t) := by
  have base : HasSides (triABQ F hF1 t ht) ((2 * F ^ 2 - 1) * t) (F * (F ^ 2 - 1) * t) (F ^ 3 * t) :=
    hasSides_triC F hF1 (ptA F t) (ptB F t) (ptQ F t) (nd_ABQ F t hF1 ht) _ _ _
      (d_BQ F t hF1 ht) ((dist_comm _ _).trans (d_AQ F t hF1 ht)) (d_AB F t hF1 ht)
  exact hasSides_swap base

/-! ## 3. The decomposition of `W` -/

/-- **The signed decomposition of `W`** at the real parameters `F > 1`, `t > 0`: `ABQ ∪ Q'QZ = ABQ' ∪ AQ'Z`, the two disjointness statements, and the sides of the four triangles. -/
def WSignedDecomp (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) : Prop :=
  ((triABQ F hF1 t ht).carrier ∪ (triQ1QZ F hF1 t ht).carrier =
      (triABQ1 F hF1 t ht).carrier ∪ (triAQ1Z F hF1 t ht).carrier) ∧
    Disjoint (interior (triABQ F hF1 t ht).carrier) (interior (triQ1QZ F hF1 t ht).carrier) ∧
    Disjoint (interior (triABQ1 F hF1 t ht).carrier) (interior (triAQ1Z F hF1 t ht).carrier) ∧
    HasSides (triABQ F hF1 t ht) (F * (F ^ 2 - 1) * t) ((2 * F ^ 2 - 1) * t) (F ^ 3 * t) ∧
    HasSides (triQ1QZ F hF1 t ht) (t * F) (t * F ^ 2) (t * (F ^ 2 - 1)) ∧
    HasSides (triABQ1 F hF1 t ht) (t * F * F) (t * F * F ^ 2) (t * F * (F ^ 2 - 1)) ∧
    HasSides (triAQ1Z F hF1 t ht) (t * F * F) (t * F * F ^ 2) (t * F * (F ^ 2 - 1))

theorem signed_decomposition_real_W (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    WSignedDecomp F hF1 t ht := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  unfold WSignedDecomp
  refine ⟨?_, ?_, ?_, sides_ABQ F hF1 t ht, sides_Q1QZ F hF1 t ht, sides_ABQ1 F hF1 t ht,
    sides_AQ1Z F hF1 t ht⟩
  · rw [carrier_triABQ, carrier_triQ1QZ, carrier_triABQ1, carrier_triAQ1Z, hull_ABQ F t hF1 ht,
      hull_Q1QZ F t hF1 ht, hull_ABQ1 F t hF1 ht, hull_AQ1Z F t hF1 ht]
    simp only [← Set.image_union]
    rw [frame_union_W hu hk hv he]
  · rw [carrier_triABQ, carrier_triQ1QZ, hull_ABQ F t hF1 ht, hull_Q1QZ F t hF1 ht]
    exact disjoint_image hF1 (disj_ABQ_Q1QZ _ _ _ _)
  · rw [carrier_triABQ1, carrier_triAQ1Z]
    exact disjoint_ABQ1_AQ1Z F t hF1 ht

/-! ## 4. The member `(e, f)` at the scale `M` -/

open Erdos634.Draft.SignedDecompG (member_F_gt member_t_pos cast_sub_sq)

/-- **The `W` half of `prop:layerall` (a), for every member `(e, f)` at every scale `M`**: with `F = f / e`, `t = M e³` the triangle `ABQ` has the sides `M f (f² − e²)`, `M e (2f² − e²)`, `M f³` (it is `W_M(e, f)`), `Q'QZ` is the tile at the scale `M e`,
`ABQ'` and `AQ'Z` are the tile at the scale `f M`, and `ABQ ∪ Q'QZ = ABQ' ∪ AQ'Z`, with disjoint interiors on each side.  The side lengths are in the form of `CollarG.WTilable` and `SideRunGMain.ebelow_a`. -/
theorem signed_decomposition_member_W (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hM : 1 ≤ M) :
    WSignedDecomp ((f : ℝ) / e) (member_F_gt he hef) ((M : ℝ) * (e : ℝ) ^ 3) (member_t_pos he hM) ∧
    HasSides (triABQ ((f : ℝ) / e) (member_F_gt he hef) ((M : ℝ) * (e : ℝ) ^ 3) (member_t_pos he hM))
      ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3) ∧
    HasSides (Erdos634.Draft.SignedDecompE1.triQ1QZ ((f : ℝ) / e) (member_F_gt he hef)
        ((M : ℝ) * (e : ℝ) ^ 3) (member_t_pos he hM))
      ((M * e * (e * f) : ℕ) : ℝ) ((M * e * f ^ 2 : ℕ) : ℝ) ((M * e * (f ^ 2 - e ^ 2) : ℕ) : ℝ) ∧
    HasSides (Erdos634.Draft.SignedDecompE1.triABQ1 ((f : ℝ) / e) (member_F_gt he hef)
        ((M : ℝ) * (e : ℝ) ^ 3) (member_t_pos he hM))
      ((f * M * (e * f) : ℕ) : ℝ) ((f * M * f ^ 2 : ℕ) : ℝ) ((f * M * (f ^ 2 - e ^ 2) : ℕ) : ℝ) ∧
    HasSides (Erdos634.Draft.SignedDecompE1.triAQ1Z ((f : ℝ) / e) (member_F_gt he hef)
        ((M : ℝ) * (e : ℝ) ^ 3) (member_t_pos he hM))
      ((f * M * (e * f) : ℕ) : ℝ) ((f * M * f ^ 2 : ℕ) : ℝ) ((f * M * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
  have he0 : (e : ℝ) ≠ 0 := (natpos he).ne'
  have hsd := signed_decomposition_real_W ((f : ℝ) / e) (member_F_gt he hef) ((M : ℝ) * (e : ℝ) ^ 3)
    (member_t_pos he hM)
  have hsd2 := hsd
  unfold WSignedDecomp at hsd2
  obtain ⟨-, -, -, sABQ, sQ, sABQ1, sAQZ⟩ := hsd2
  obtain ⟨b, hbN, hbR⟩ : ∃ b : ℕ, f ^ 2 - e ^ 2 = b ∧ (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 :=
    ⟨_, rfl, cast_sub_sq hef⟩
  rw [hbN]
  refine ⟨hsd, ?_, ?_, ?_, ?_⟩
  · refine hasSides_eq sABQ ?_ ?_ ?_ <;>
      (first | (field_simp; ring1) | field_simp | ring1)
  · refine hasSides_eq sQ ?_ ?_ ?_ <;>
      (push_cast; (try rw [hbR]); first | (field_simp; ring1) | field_simp | ring1)
  · refine hasSides_eq sABQ1 ?_ ?_ ?_ <;>
      (push_cast; (try rw [hbR]); first | (field_simp; ring1) | field_simp | ring1)
  · refine hasSides_eq sAQZ ?_ ?_ ?_ <;>
      (push_cast; (try rw [hbR]); first | (field_simp; ring1) | field_simp | ring1)

/-- the numbers of tiles of `prop:layerall` (a): `3 (f M)² − (M e)² = M² (3 f² − e²)` -/
theorem count_T (e f M : ℕ) (hef : e < f) :
    3 * (f * M) ^ 2 - (M * e) ^ 2 = M ^ 2 * (3 * f ^ 2 - e ^ 2) := by
  have h1 : e ^ 2 ≤ 3 * f ^ 2 := by
    have := Nat.pow_le_pow_left hef.le 2
    omega
  have h2 : (M * e) ^ 2 ≤ 3 * (f * M) ^ 2 := by
    have := Nat.mul_le_mul_left (M ^ 2) (Nat.pow_le_pow_left hef.le 2)
    nlinarith [this, Nat.zero_le (M ^ 2 * f ^ 2)]
  zify [h1, h2]
  ring

/-- the numbers of tiles of `prop:layerall` (a): `2 (f M)² − (M e)² = M² (2 f² − e²)` -/
theorem count_W (e f M : ℕ) (hef : e < f) :
    2 * (f * M) ^ 2 - (M * e) ^ 2 = M ^ 2 * (2 * f ^ 2 - e ^ 2) := by
  have h1 : e ^ 2 ≤ 2 * f ^ 2 := by
    have := Nat.pow_le_pow_left hef.le 2
    omega
  have h2 : (M * e) ^ 2 ≤ 2 * (f * M) ^ 2 := by
    have := Nat.mul_le_mul_left (M ^ 2) (Nat.pow_le_pow_left hef.le 2)
    nlinarith [this, Nat.zero_le (M ^ 2 * f ^ 2)]
  zify [h1, h2]
  ring

end Erdos634.Draft.SignedDecompW

#print axioms Erdos634.Draft.SignedDecompW.hull_regABQ
#print axioms Erdos634.Draft.SignedDecompW.frame_union_W
#print axioms Erdos634.Draft.SignedDecompW.sides_ABQ
#print axioms Erdos634.Draft.SignedDecompW.signed_decomposition_real_W
#print axioms Erdos634.Draft.SignedDecompW.signed_decomposition_member_W
#print axioms Erdos634.Draft.SignedDecompW.count_T
#print axioms Erdos634.Draft.SignedDecompW.count_W
