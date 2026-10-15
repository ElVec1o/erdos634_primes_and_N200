import Mathlib.Tactic
import Erdos634.Draft.GLCCorner
import Erdos634.Draft.GLCForward

/-!
# G1 in full at an `α`-corner: the second tile on each side starts with `α`

`corner_G1`: at a target corner of angle `α` (tile `γ = 2α`, word lemma for `a`, adjacent side lengths not in `{b, c}`), with `T` the corner tile
(`P, Q` its other vertices, on the two target sides, `PQ` the `a`-edge) and `T2` the point reflection of `T` through the midpoint of `PQ`
(`GLCCorner.corner_far_reflection_2a`, here re-run inside the proof so that its clamp data is in scope), there are tiles `K_P, K_Q` with a vertex of
angle `α` at `P` (resp. `Q`) and an edge there running along the side (`SameRay` with `P − O`, resp. `Q − O`, forward from the corner).
This is (G1): "the second tile on each of the two sides starts with `α` at its end next to `T`; `T` and its point reflection `T2`
share the corner chord".  Uses `forward_tile_2a` (the fan at `P` is `(α,β,γ)` because `T`, `T2` present `β,γ` there and the forward points lie in neither).
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Pi3Cone Erdos634.Pi3F6 Erdos634.Pi3Tile Erdos634.ChordFar

variable {N : ℕ}

theorem coord_lin (U : Tri) (m : Fin 3) (x y z : Plane) (t : ℝ) :
    U.basis.coord m (x + t • (y - z)) = U.basis.coord m x + t * (U.basis.coord m y - U.basis.coord m z) := by
  have h1 : x + t • (y - z) = (t • (y - z)) +ᵥ x := by rw [vadd_eq_add]; abel
  have h2 : (U.basis.coord m).linear (y - z) = U.basis.coord m y - U.basis.coord m z := by
    rw [← vsub_eq_sub, AffineMap.linearMap_vsub]; rfl
  rw [h1, AffineMap.map_vadd, map_smul, h2]
  simp [vadd_eq_add, smul_eq_mul, add_comm]

/-- A point `U.pts n + ε (U.pts r - U.pts m)` with `ε > 0` and `m ≠ n, r` lies outside the triangle (barycentric coordinate at `m` is `-ε`). -/
theorem fwd_not_mem (U : Tri) (m n r : Fin 3) (hmn : m ≠ n) (hmr : m ≠ r) {ε : ℝ} (hε : 0 < ε) :
    U.pts n + ε • (U.pts r - U.pts m) ∉ U.carrier := by
  intro h
  rw [U.carrier_eq_nonneg_coord] at h
  have := h m
  have hcd : ∀ (m n : Fin 3), U.basis.coord m (U.pts n) = if m = n then 1 else 0 :=
    fun m n => AffineBasis.coord_apply U.basis m n
  simp only [coord_lin, hcd, if_neg hmn, if_neg hmr, if_true] at this
  linarith

set_option maxHeartbeats 3200000 in
theorem aux_G1 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1)
    (i : Fin N) (j : Fin 3) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hjv : (D.tile i).pts j = D.target.pts v)
    (hlen : dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = a)
    {p r : ℝ} (hp0 : 0 < p) (hr0 : 0 < r)
    (hP : (D.tile i).pts (j + 1) - D.target.pts v = p • (D.target.pts w - D.target.pts v))
    (hQ : (D.tile i).pts (j + 2) - D.target.pts v = r • (D.target.pts z - D.target.pts v))
    (hPA : (D.tile i).pts (j + 1) ≠ D.target.pts w) (hQB : (D.tile i).pts (j + 2) ≠ D.target.pts z) :
    ∃ j' : Fin N, j' ≠ i ∧ ∃ X : Plane,
      (D.tile i).carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2), X} ∧
      (D.tile j').carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2),
        (D.tile i).pts (j + 1) + (D.tile i).pts (j + 2) - X}
      ∧ (∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts (j + 1) ∧ (D.tile K).angleAt l = α ∧
          (SameRay ℝ ((D.tile i).pts (j + 1) - D.target.pts v) ((D.tile K).pts (l + 1) - (D.tile i).pts (j + 1)) ∨
           SameRay ℝ ((D.tile i).pts (j + 1) - D.target.pts v) ((D.tile K).pts (l + 2) - (D.tile i).pts (j + 1))))
      ∧ (∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts (j + 2) ∧ (D.tile K).angleAt l = α ∧
          (SameRay ℝ ((D.tile i).pts (j + 2) - D.target.pts v) ((D.tile K).pts (l + 1) - (D.tile i).pts (j + 2)) ∨
           SameRay ℝ ((D.tile i).pts (j + 2) - D.target.pts v) ((D.tile K).pts (l + 2) - (D.tile i).pts (j + 2)))) := by
  set T := D.target with hT
  set P := (D.tile i).pts (j + 1) with hPdef
  set Q := (D.tile i).pts (j + 2) with hQdef
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
  obtain ⟨⟨g, cg, hg, hgP, hgQ, hg0⟩, ⟨h, ch, hh, hhQ, hhP, hh0⟩, hint, hfr, hnv, -, -⟩ :=
    clamps T v w z hvw hvz hwz hp0 hp1 hr0 hr1
  obtain ⟨f, c0, hf, hfle, hf1, hf2, hf3⟩ := exists_supporting (D.tile i) (j + 1)
  have hfle' : ∀ m, f ((D.tile i).pts m) ≤ c0 := fun m => hfle _ (subset_convexHull ℝ _ ⟨m, rfl⟩)
  have e11 : j + 1 + 1 = j + 2 := (by decide : ∀ j : Fin 3, j + 1 + 1 = j + 2) j
  rw [e11] at hf2
  have hinjT : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have hj1' : (D.tile i).pts (j + 1) - (D.tile i).pts j ≠ 0 := by
    rw [sub_ne_zero]; exact (hinjT _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
  have hj2' : (D.tile i).pts (j + 2) - (D.tile i).pts j ≠ 0 := by
    rw [sub_ne_zero]; exact (hinjT _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
  obtain ⟨j', hj', X, hXf, hcar1, hcar2, hfar, hXeq, ⟨k2, hk2, hZ⟩, hangs⟩ := corner_chord_reflection_2a D hα hS hab hac hword i (j + 1)
    (P := P) (Q := Q) rfl (by rw [e11]) hlen f hf c0 hfle' hf1 hf2 g cg hg (by rw [hPform]; exact hgP)
    (by rw [hQform]; exact hgQ)
    h ch hh (by rw [hQform]; exact hhQ) (by rw [hPform]; exact hhP)
    (by rw [hPform, hQform]; exact hint) (by rw [hPform]; exact hfr) (by rw [hPform]; exact hnv)
  refine ⟨j', hj', X, hcar1, hcar2, ?_⟩
  -- clamp facts at the corner `O = T.pts v`
  have hgP' : g P = cg := by rw [hPform]; exact hgP
  have hhQ' : h Q = ch := by rw [hQform]; exact hhQ
  have hXO : X = T.pts v := by
    rw [hXeq, (by decide : ∀ x : Fin 3, x + 1 + 2 = x) j]; exact hjv
  have hgO : g (T.pts v) = cg := by
    have h1 : g (T.pts v) ≤ cg := hg _ (subset_convexHull ℝ _ ⟨v, rfl⟩)
    have h2 : g (T.pts w) ≤ cg := hg _ (subset_convexHull ℝ _ ⟨w, rfl⟩)
    have h3 : g P = (1 - p) * g (T.pts v) + p * g (T.pts w) := by
      rw [hPform, map_add, map_smul, map_smul]; simp only [smul_eq_mul]
    by_contra hne
    have : g (T.pts v) < cg := lt_of_le_of_ne h1 hne
    nlinarith [mul_nonneg hp0.le (sub_nonneg.2 h2), mul_pos (sub_pos.2 hp1) (sub_pos.2 this)]
  have hhO : h (T.pts v) = ch := by
    have h1 : h (T.pts v) ≤ ch := hh _ (subset_convexHull ℝ _ ⟨v, rfl⟩)
    have h2 : h (T.pts z) ≤ ch := hh _ (subset_convexHull ℝ _ ⟨z, rfl⟩)
    have h3 : h Q = (1 - r) * h (T.pts v) + r * h (T.pts z) := by
      rw [hQform, map_add, map_smul, map_smul]; simp only [smul_eq_mul]
    by_contra hne
    have : h (T.pts v) < ch := lt_of_le_of_ne h1 hne
    nlinarith [mul_nonneg hr0.le (sub_nonneg.2 h2), mul_pos (sub_pos.2 hr1) (sub_pos.2 this)]
  have hconv : Convex ℝ T.carrier := by unfold Tri.carrier; exact convex_convexHull ℝ _
  have hinP : ∀ ε : ℝ, 0 < ε → ε ≤ (1 - p) / p → P + ε • (P - T.pts v) ∈ T.carrier := by
    intro ε hε hεle
    have hpe : p * ε ≤ 1 - p := by rwa [le_div_iff₀ hp0, mul_comm] at hεle
    have key := hconv.add_smul_sub_mem (subset_convexHull ℝ _ ⟨v, rfl⟩ : T.pts v ∈ T.carrier)
      (subset_convexHull ℝ _ ⟨w, rfl⟩ : T.pts w ∈ T.carrier) (t := p * (1 + ε))
      ⟨by positivity, by nlinarith⟩
    convert key using 1
    rw [show P + ε • (P - T.pts v) = T.pts v + (P - T.pts v) + ε • (P - T.pts v) by abel, hP]
    module
  have hinQ : ∀ ε : ℝ, 0 < ε → ε ≤ (1 - r) / r → Q + ε • (Q - T.pts v) ∈ T.carrier := by
    intro ε hε hεle
    have hre : r * ε ≤ 1 - r := by rwa [le_div_iff₀ hr0, mul_comm] at hεle
    have key := hconv.add_smul_sub_mem (subset_convexHull ℝ _ ⟨v, rfl⟩ : T.pts v ∈ T.carrier)
      (subset_convexHull ℝ _ ⟨z, rfl⟩ : T.pts z ∈ T.carrier) (t := r * (1 + ε))
      ⟨by positivity, by nlinarith⟩
    convert key using 1
    rw [show Q + ε • (Q - T.pts v) = T.pts v + (Q - T.pts v) + ε • (Q - T.pts v) by abel, hQ]
    module
  have hu1 : P - T.pts v ≠ 0 := by rw [← hjv]; exact hj1'
  have hu2 : Q - T.pts v ≠ 0 := by rw [← hjv]; exact hj2'
  -- forward points are not in the corner tile `T`
  have hnT_P : ∀ ε : ℝ, 0 < ε → P + ε • (P - T.pts v) ∉ (D.tile i).carrier := by
    intro ε hε
    have := fwd_not_mem (D.tile i) j (j + 1) (j + 1) ((by decide : ∀ x : Fin 3, x ≠ x + 1) j) ((by decide : ∀ x : Fin 3, x ≠ x + 1) j) hε
    rwa [hjv] at this
  have hnT_Q : ∀ ε : ℝ, 0 < ε → Q + ε • (Q - T.pts v) ∉ (D.tile i).carrier := by
    intro ε hε
    have := fwd_not_mem (D.tile i) j (j + 2) (j + 2) ((by decide : ∀ x : Fin 3, x ≠ x + 2) j) ((by decide : ∀ x : Fin 3, x ≠ x + 2) j) hε
    rwa [hjv] at this
  -- ... and not in the reflected tile `T2`
  have hZP : (D.tile j').pts (k2 + 2) - Q = P - T.pts v := by rw [hZ, hXO]; abel
  have hZQ : (D.tile j').pts (k2 + 2) - P = Q - T.pts v := by rw [hZ, hXO]; abel
  have n01 : ∀ x : Fin 3, x ≠ x + 1 := by decide
  have n02 : ∀ x : Fin 3, x ≠ x + 2 := by decide
  have n12 : ∀ x : Fin 3, x + 1 ≠ x + 2 := by decide
  have hnT2_P : ∀ ε : ℝ, 0 < ε → P + ε • (P - T.pts v) ∉ (D.tile j').carrier := by
    intro ε hε
    rcases hk2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have := fwd_not_mem (D.tile j') (k2 + 1) k2 (k2 + 2) ((n01 k2).symm) ((n12 k2)) hε
      rwa [e1, e2, hZP] at this
    · have := fwd_not_mem (D.tile j') k2 (k2 + 1) (k2 + 2) (n01 k2) (n02 k2) hε
      rwa [e1, e2, hZP] at this
  have hnT2_Q : ∀ ε : ℝ, 0 < ε → Q + ε • (Q - T.pts v) ∉ (D.tile j').carrier := by
    intro ε hε
    rcases hk2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have := fwd_not_mem (D.tile j') k2 (k2 + 1) (k2 + 2) (n01 k2) (n02 k2) hε
      rwa [e1, e2, hZQ] at this
    · have := fwd_not_mem (D.tile j') (k2 + 1) k2 (k2 + 2) ((n01 k2).symm) ((n12 k2)) hε
      rwa [e1, e2, hZQ] at this
  have hPfr' : P ∈ frontier T.carrier := by rw [hPform]; exact hfr
  have hPnv' : P ∉ Set.range T.pts := by rw [hPform]; exact hnv
  obtain ⟨-, -, -, hfrQ, hnvQ, -, -⟩ :=
    clamps T v z w hvz hvw hwz.symm hr0 hr1 hp0 hp1
  have hQfr' : Q ∈ frontier T.carrier := by rw [hQform]; exact hfrQ
  have hQnv' : Q ∉ Set.range T.pts := by rw [hQform]; exact hnvQ
  have hgu : g (P - T.pts v) = 0 := by rw [map_sub, hgP', hgO]; ring
  have hhu : h (Q - T.pts v) = 0 := by rw [map_sub, hhQ', hhO]; ring
  have hε0P : 0 < (1 - p) / p := div_pos (by linarith) hp0
  have hε0Q : 0 < (1 - r) / r := div_pos (by linarith) hr0
  rcases hangs with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
  · exact ⟨forward_tile_2a D hα hS hPfr' hPnv' hu1 g hg0 cg hg hgP' hgu hε0P hinP i j' a1 a2
      (fun ε hε _ => hnT_P ε hε) (fun ε hε _ => hnT2_P ε hε),
      forward_tile_2a D hα hS hQfr' hQnv' hu2 h hh0 ch hh hhQ' hhu hε0Q hinQ j' i a4 a3
      (fun ε hε _ => hnT2_Q ε hε) (fun ε hε _ => hnT_Q ε hε)⟩
  · exact ⟨forward_tile_2a D hα hS hPfr' hPnv' hu1 g hg0 cg hg hgP' hgu hε0P hinP j' i a2 a1
      (fun ε hε _ => hnT2_P ε hε) (fun ε hε _ => hnT_P ε hε),
      forward_tile_2a D hα hS hQfr' hQnv' hu2 h hh0 ch hh hhQ' hhu hε0Q hinQ i j' a3 a4
      (fun ε hε _ => hnT_Q ε hε) (fun ε hε _ => hnT2_Q ε hε)⟩

/-- **G1 at an `α`-corner: the corner tile and its point reflection share the corner chord (the `a`-edge).** -/
theorem corner_G1 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1)
    (k : Fin 3) (hk : D.target.angleAt k = α)
    (hA1 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ b)
    (hA2 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ c)
    (hB1 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ b)
    (hB2 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ c) :
    ∃ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts k ∧ (D.tile i).angleAt j = α ∧
      ((SameRay ℝ (D.target.pts (k + 1) - D.target.pts k) ((D.tile i).pts (j + 1) - D.target.pts k) ∧
        SameRay ℝ (D.target.pts (k + 2) - D.target.pts k) ((D.tile i).pts (j + 2) - D.target.pts k)) ∨
       (SameRay ℝ (D.target.pts (k + 2) - D.target.pts k) ((D.tile i).pts (j + 1) - D.target.pts k) ∧
        SameRay ℝ (D.target.pts (k + 1) - D.target.pts k) ((D.tile i).pts (j + 2) - D.target.pts k))) ∧
      dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = a ∧
      ∃ j' : Fin N, j' ≠ i ∧ ∃ X : Plane,
        (D.tile i).carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2), X} ∧
        (D.tile j').carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2),
          (D.tile i).pts (j + 1) + (D.tile i).pts (j + 2) - X} ∧
      (∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts (j + 1) ∧ (D.tile K).angleAt l = α ∧
          (SameRay ℝ ((D.tile i).pts (j + 1) - D.target.pts k) ((D.tile K).pts (l + 1) - (D.tile i).pts (j + 1)) ∨
           SameRay ℝ ((D.tile i).pts (j + 1) - D.target.pts k) ((D.tile K).pts (l + 2) - (D.tile i).pts (j + 1)))) ∧
      (∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts (j + 2) ∧ (D.tile K).angleAt l = α ∧
          (SameRay ℝ ((D.tile i).pts (j + 2) - D.target.pts k) ((D.tile K).pts (l + 1) - (D.tile i).pts (j + 2)) ∨
           SameRay ℝ ((D.tile i).pts (j + 2) - D.target.pts k) ((D.tile K).pts (l + 2) - (D.tile i).pts (j + 2)))) := by
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D hS
  have hpi := Real.pi_pos
  obtain ⟨hc1, -, -, -, -⟩ := corner_has_alpha_tile D hα hS hk
  obtain ⟨i, hi⟩ : ∃ i : Fin N, (D.tile i).localAngle (D.target.pts k) = α := by
    have : 0 < cntA D (D.target.pts k) α := by omega
    unfold cntA at this
    obtain ⟨i, hi⟩ := Finset.card_pos.mp this
    exact ⟨i, by simpa using hi⟩
  obtain ⟨j, hj, hang, hcase⟩ := corner_tile_on_sides_gen D hα0 (by linarith) k hk i hi
  have hU := tile_twoalpha D hS i
  have hopp := opp_a_of_alpha hα hU j hang
  have hor := tri_orient_a hU hab hac j hopp
  have e3 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e4 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e5 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have e6 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  have hlen : dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = a := hopp
  simp only [Tri.oppLen, e3, e4, e5, e6] at hor
  have hlOQ : dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = b ∨
      dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = c := by
    rcases hor with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hlOP : dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = b ∨
      dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = c := by
    rcases hor with ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩
    · exact Or.inr h1
    · exact Or.inl h1
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have hj1 : (D.tile i).pts (j + 1) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero, ← hj]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
  have hj2 : (D.tile i).pts (j + 2) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero, ← hj]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
  have hAne : D.target.pts (k + 1) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero]; intro h
    exact (by decide : ∀ x : Fin 3, x + 1 ≠ x) k (D.target.indep.injective h)
  have hBne : D.target.pts (k + 2) - D.target.pts k ≠ 0 := by
    rw [sub_ne_zero]; intro h
    exact (by decide : ∀ x : Fin 3, x + 2 ≠ x) k (D.target.indep.injective h)
  have vk1 : k ≠ k + 1 := (by decide : ∀ x : Fin 3, x ≠ x + 1) k
  have vk2 : k ≠ k + 2 := (by decide : ∀ x : Fin 3, x ≠ x + 2) k
  have v12 : k + 1 ≠ k + 2 := (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k
  refine ⟨i, j, hj, hang, hcase, hlen, ?_⟩
  rcases hcase with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
  · obtain ⟨p, hp0, hp⟩ := Erdos634.Pi3F6.rayparam hAne hj1 hr1
    obtain ⟨r, hr0, hr⟩ := Erdos634.Pi3F6.rayparam hBne hj2 hr2
    refine aux_G1 D hα hS hab hac hword i j k (k + 1) (k + 2) vk1 vk2 v12 hj hlen hp0 hr0
      hp hr ?_ ?_
    · intro h
      rcases hlOP with h' | h'
      · apply hA1; rw [← h', hj, h]
      · apply hA2; rw [← h', hj, h]
    · intro h
      rcases hlOQ with h' | h'
      · apply hB1; rw [← dist_comm, ← h', hj, h]
      · apply hB2; rw [← dist_comm, ← h', hj, h]
  · obtain ⟨p, hp0, hp⟩ := Erdos634.Pi3F6.rayparam hBne hj1 hr1
    obtain ⟨r, hr0, hr⟩ := Erdos634.Pi3F6.rayparam hAne hj2 hr2
    refine aux_G1 D hα hS hab hac hword i j k (k + 2) (k + 1) vk2 vk1 v12.symm hj hlen hp0 hr0
      hp hr ?_ ?_
    · intro h
      rcases hlOP with h' | h'
      · apply hB1; rw [← h', hj, h]
      · apply hB2; rw [← h', hj, h]
    · intro h
      rcases hlOQ with h' | h'
      · apply hA1; rw [← dist_comm, ← h', hj, h]
      · apply hA2; rw [← dist_comm, ← h', hj, h]

end Erdos634.GLC

#print axioms Erdos634.GLC.corner_G1
