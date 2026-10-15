import Mathlib.Tactic
import Erdos634.Draft.T30LL4Tri
import Erdos634.Draft.T30LC2Strong
import Erdos634.Draft.T30LL3Corner

/-!
# (L4): the corner of type `(b,a)` is impossible (`b < a`)

Setting as `l3_corner`: corner tile `T = {O,P,Q}` (`π/3` at the target corner `O`, `|OP| = a`, `|OQ| = b`, `b < a`).  Type `(b,a)`: the second tile on the `P`-side has a side edge of length `b`
(`SideTileLen D P (P-O) b`), the second tile on the `Q`-side a side edge of length `a`.  Conclusion `False`, for a dissection whose words satisfy `x a + y b + z c = a → y = 0` (and the `c`-word lemma).
Chain: `side_tile_full` on rescaled directions gives `T₃ ∋ P, P+(b/a)(P-O), P+(a/b)(Q-O)` and `T₄ ∋ Q, Q+(b/a)(P-O), Q+(a/b)(Q-O)`; `corner_chord_reflection_ex` gives `T₂ = {P,Q,Z}`, `Z = P+Q-O`, so `(Q,Z)`
is a wall; the line `QZ` past `Z` runs into the interior of `T₃`; `chain_sum_open_end` + `word_of_sum_with`: the chain edges on `[Q,Z]` (containing `T₄`'s `b`-edge) give `x a + y b + z c = a`, `y ≥ 1`.
-/

namespace Erdos634.C2Forward

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.Pi3F6 Erdos634.ChordFar Erdos634.SectorFill

theorem stl_scale {N : ℕ} {D : CongruentDissection N} {X u : Plane} {x k : ℝ} (h : SideTileLen D X u x)
    (hk : 0 < k) : SideTileLen D X (k • u) x := by
  obtain ⟨K, l, hl, hang, hc⟩ := h
  refine ⟨K, l, hl, hang, ?_⟩
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨(SameRay.sameRay_pos_smul_left u hk).trans h1 (fun h => Or.inl (by rw [h, smul_zero])), h2⟩
  · exact Or.inr ⟨(SameRay.sameRay_pos_smul_left u hk).trans h1 (fun h => Or.inl (by rw [h, smul_zero])), h2⟩

theorem coord_lin3 (φ : Plane →ᵃ[ℝ] ℝ) (O A B : Plane) (s t : ℝ) :
    φ (O + s • (A - O) + t • (B - O)) = φ O + s * (φ A - φ O) + t * (φ B - φ O) := by
  have hd : ∀ x, φ x = φ.linear x + φ 0 := fun x => by simpa using congrFun (AffineMap.decomp φ) x
  rw [hd, hd O, hd A, hd B]
  simp only [map_add, map_smul, map_sub, smul_eq_mul]
  ring

set_option maxHeartbeats 3200000 in
theorem l4_corner {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hac : a ≠ c) (hbc : b ≠ c) (hab : a ≠ b) (hba : b < a)
    (hword1 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → y = 0)
    (hwordc : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x + y + z = 1)
    (i : Fin N) (j : Fin 3) (v w z : Fin 3) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hjv : (D.tile i).pts j = D.target.pts v) (hang : (D.tile i).angleAt j = Real.pi / 3)
    {p r : ℝ} (hp0 : 0 < p) (hr0 : 0 < r)
    (hP : (D.tile i).pts (j + 1) - D.target.pts v = p • (D.target.pts w - D.target.pts v))
    (hQ : (D.tile i).pts (j + 2) - D.target.pts v = r • (D.target.pts z - D.target.pts v))
    (hOP : dist (D.target.pts v) ((D.tile i).pts (j + 1)) = a)
    (hOQ : dist (D.target.pts v) ((D.tile i).pts (j + 2)) = b)
    (hK3 : SideTileLen D ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 1) - D.target.pts v) b)
    (hK4 : SideTileLen D ((D.tile i).pts (j + 2)) ((D.tile i).pts (j + 2) - D.target.pts v) a) :
    False := by
  classical
  have hpi := Real.pi_pos
  set T := D.target with hT
  set P := (D.tile i).pts (j + 1) with hPdef
  set Q := (D.tile i).pts (j + 2) with hQdef
  set O := T.pts v with hO
  have hPform : P = (1 - p) • T.pts v + p • T.pts w := by
    have : P = T.pts v + p • (T.pts w - T.pts v) := by rw [← hP]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hQform : Q = (1 - r) • T.pts v + r • T.pts z := by
    have : Q = T.pts v + r • (T.pts z - T.pts v) := by rw [← hQ]; abel
    rw [this]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hcd : ∀ (m n : Fin 3), T.basis.coord m (T.pts n) = if m = n then 1 else 0 :=
    fun m n => AffineBasis.coord_apply T.basis m n
  have hinj : ∀ m n : Fin 3, m ≠ n → (D.tile i).pts m ≠ (D.tile i).pts n :=
    fun m n h hh => h ((D.tile i).indep.injective hh)
  have hu : P - O ≠ 0 := by
    rw [sub_ne_zero, ← hjv]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 1) j)).symm
  have hq : Q - O ≠ 0 := by
    rw [sub_ne_zero, ← hjv]; exact (hinj _ _ ((by decide : ∀ x : Fin 3, x ≠ x + 2) j)).symm
  have hang' : InnerProductGeometry.angle (P - O) (Q - O) = Real.pi / 3 := by
    have := hang
    unfold Tri.angleAt cornerAngle EuclideanGeometry.angle at this
    simp only [vsub_eq_sub] at this
    rw [hjv] at this
    exact this
  have hnu : ‖P - O‖ = a := by rw [← dist_eq_norm, dist_comm]; exact hOP
  have hnq : ‖Q - O‖ = b := by rw [← dist_eq_norm, dist_comm]; exact hOQ
  have hPQc : dist P Q = c := by
    have := opp_c_of_pi3 hirr (tile_sixty D hS i) j hang
    unfold Tri.oppLen at this
    exact this
  -- supporting functionals of the two sides
  obtain ⟨g, cg, hg0, hgle, hgv, hgw, hgz⟩ := supp_pair T v w z hvw hvz hwz
  obtain ⟨h, ch, hh0, hhle, hhv, hhz, hhw⟩ := supp_pair T v z w hvz hvw hwz.symm
  have hgP : g P = cg := by rw [hPform, lin_comb, hgv, hgw]; ring
  have hgQ : g Q < cg := by
    rw [hQform, lin_comb, hgv]; nlinarith [mul_pos hr0 (sub_pos.mpr hgz)]
  have hhQ : h Q = ch := by rw [hQform, lin_comb, hhv, hhz]; ring
  have hhP : h P < ch := by
    rw [hPform, lin_comb, hhv]; nlinarith [mul_pos hp0 (sub_pos.mpr hhw)]
  have hgu : g (P - O) = 0 := by rw [map_sub, hgP, hgv]; ring
  have hgq : g (Q - O) < 0 := by rw [map_sub, hgv]; linarith
  have hhq : h (Q - O) = 0 := by rw [map_sub, hhQ, hhv]; ring
  have hhp : h (P - O) < 0 := by rw [map_sub, hhv]; linarith
  have hapos : 0 < a := by rw [← hnu]; exact norm_pos_iff.mpr hu
  have hbpos : 0 < b := by rw [← hnq]; exact norm_pos_iff.mpr hq
  have hab0 : 0 < b / a := div_pos hbpos hapos
  have hba0 : 0 < a / b := div_pos hapos hbpos
  obtain ⟨K3, m3, hK3m, hK3v, -⟩ := side_tile_full D hirr hS hac hbc hab
    (u := (b / a) • (P - O)) (q := (a / b) • (Q - O)) (X := P)
    (smul_ne_zero hab0.ne' hu) (Or.inr ⟨by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hab0, hnu]; field_simp,
      by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hba0, hnq]; field_simp⟩)
    (by rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hab0, InnerProductGeometry.angle_smul_right_of_pos _ _ hba0]; exact hang')
    g (by rw [map_smul, hgu, smul_zero]) (by rw [map_smul]; exact mul_neg_of_pos_of_neg hba0 hgq)
    (fun y hy => by rw [hgP]; exact hgle y hy)
    (by
      have := stl_scale hK3 hab0
      rwa [show ‖(b / a) • (P - O)‖ = b by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hab0, hnu]; field_simp])
  obtain ⟨K4, m4, hK4m, hK4v, -⟩ := side_tile_full D hirr hS hac hbc hab
    (u := (a / b) • (Q - O)) (q := (b / a) • (P - O)) (X := Q)
    (smul_ne_zero hba0.ne' hq) (Or.inl ⟨by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hba0, hnq]; field_simp,
      by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hab0, hnu]; field_simp⟩)
    (by rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hba0, InnerProductGeometry.angle_smul_right_of_pos _ _ hab0,
      InnerProductGeometry.angle_comm]; exact hang')
    h (by rw [map_smul, hhq, smul_zero]) (by rw [map_smul]; exact mul_neg_of_pos_of_neg hab0 hhp)
    (fun y hy => by rw [hhQ]; exact hhle y hy)
    (by
      have := stl_scale hK4 hba0
      rwa [show ‖(a / b) • (Q - O)‖ = a by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hba0, hnq]; field_simp])
  -- the point just past `Z` on the line `QZ` is interior to `T₃`
  set s0 : ℝ := b * (a - b) / (2 * a ^ 2) with hs0
  have hs0pos : 0 < s0 := by rw [hs0]; apply div_pos (mul_pos hbpos (by linarith)) (by positivity)
  have hββ : (b / a) * (a / b) = 1 := by field_simp
  have hover : ∀ s : ℝ, 0 < s → s ≤ s0 →
      (P + (Q - O)) + s • (P - O) ∈ interior (D.tile K3).carrier := by
    intro s hs hsle
    have hlam : 0 < 1 - b / a - s * (a / b) := by
      have h1 : s * (a / b) ≤ s0 * (a / b) := mul_le_mul_of_nonneg_right hsle hba0.le
      have h2 : s0 * (a / b) = (a - b) / (2 * a) := by rw [hs0]; field_simp
      have h3 : 1 - b / a = (a - b) / a := by field_simp
      have h4 : (a - b) / (2 * a) < (a - b) / a := by
        apply div_lt_div_of_pos_left (by linarith) hapos (by linarith)
      linarith
    have hsum1 : (s * (a / b)) + (1 - b / a - s * (a / b)) + b / a = 1 := by ring
    have hsum2 : (s * (a / b)) + (b / a) + (1 - b / a - s * (a / b)) = 1 := by ring
    have hvec : ∀ x0 x1 x2 : ℝ, x0 = s * (a / b) → x2 = b / a → x1 = 1 - b / a - s * (a / b) →
        x0 • (P + (b / a) • (P - O)) + x1 • P + x2 • (P + (a / b) • (Q - O)) = (P + (Q - O)) + s • (P - O) := by
      intro x0 x1 x2 h0 h1 h2
      subst h0 h1 h2
      rw [← sub_eq_zero]
      have : (s * (a / b)) • (P + (b / a) • (P - O)) + (1 - b / a - s * (a / b)) • P + (b / a) • (P + (a / b) • (Q - O))
          - ((P + (Q - O)) + s • (P - O)) = ((s * (a / b)) * (b / a) - s) • (P - O) + ((b / a) * (a / b) - 1) • (Q - O) := by
        module
      rw [this]
      have e1 : (s * (a / b)) * (b / a) - s = 0 := by field_simp; ring
      have e2 : (b / a) * (a / b) - 1 = 0 := by rw [hββ]; ring
      rw [e1, e2]; simp
    rcases hK3v with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have := interior_of_three (D.tile K3) m3 (s * (a / b)) (1 - b / a - s * (a / b)) (b / a)
        (mul_pos hs hba0) hlam hab0 hsum1
      rw [hK3m, e1, e2] at this
      rwa [hvec _ _ _ rfl rfl rfl] at this
    · have := interior_of_three (D.tile K3) m3 (s * (a / b)) (b / a) (1 - b / a - s * (a / b))
        (mul_pos hs hba0) hab0 hlam hsum2
      rw [hK3m, e1, e2] at this
      have h5 := hvec (s * (a / b)) (1 - b / a - s * (a / b)) (b / a) rfl rfl rfl
      rw [← h5]
      convert this using 1
      abel
  -- `p + r < 1`: the hover point lies in the target
  have hyform : (P + (Q - O)) + s0 • (P - O) = O + (p * (1 + s0)) • (T.pts w - O) + r • (T.pts z - O) := by
    have e : (P + (Q - O)) + s0 • (P - O) = O + (1 + s0) • (P - O) + (Q - O) := by module
    rw [e, hP, hQ, smul_smul, mul_comm]
  have hprlt : p + r < 1 := by
    have hmem := Erdos634.BaseSelection.tile_subset_target D.toDissection K3
      (interior_subset (hover s0 hs0pos le_rfl))
    rw [T.carrier_eq_nonneg_coord] at hmem
    have hnn : 0 ≤ T.basis.coord v ((P + (Q - O)) + s0 • (P - O)) := hmem v
    rw [hyform, coord_lin3, hcd, hcd, hcd] at hnn
    simp [hvw, hvz] at hnn
    nlinarith [mul_pos hp0 hs0pos]
  have hp1 : p < 1 := by linarith
  have hr1 : r < 1 := by linarith
  -- the open chord `QZ` is inside the target
  have hintQZ : openSegment ℝ Q (P + (Q - O)) ⊆ interior T.carrier := by
    have hint : interior T.carrier = {x | ∀ i, 0 < T.basis.coord i x} := by
      have : T.carrier = convexHull ℝ (Set.range (T.basis : Fin 3 → Plane)) := rfl
      rw [this]
      exact AffineBasis.interior_convexHull T.basis
    rw [hint]
    rintro y ⟨s', t', hs', ht', hst, rfl⟩ i
    have e : s' • Q + t' • (P + (Q - O)) = O + (t' * p) • (T.pts w - O) + r • (T.pts z - O) := by
      have e1 : s' • Q + t' • (P + (Q - O)) = O + t' • (P - O) + (Q - O) := by
        have : s' = 1 - t' := by linarith
        subst this; module
      rw [e1, hP, hQ, smul_smul]
    have cO : ∀ i, T.basis.coord i O = if i = v then 1 else 0 := fun i => hcd i v
    have cA : ∀ i, T.basis.coord i (T.pts w) = if i = w then 1 else 0 := fun i => hcd i w
    have cB : ∀ i, T.basis.coord i (T.pts z) = if i = z then 1 else 0 := fun i => hcd i z
    have ht1 : t' * p < p := by nlinarith [mul_pos hs' hp0]
    rw [e, coord_lin3, cO, cA, cB]
    rcases cover3 v w z i hvw hvz hwz with h' | h' | h'
    · rw [h']; simp [hvw, hvz]; nlinarith
    · rw [h']; simp [hvw.symm, hwz]; exact mul_pos ht' hp0
    · rw [h']; simp [hvz.symm, hwz.symm]; exact hr0
  -- `T₂ = {P, Q, Z}`: the point reflection of `T` across the chord `PQ`
  obtain ⟨-, -, hint0, hfr0, hnv0, -, -⟩ := clamps T v w z hvw hvz hwz hp0 hp1 hr0 hr1
  have hintPQ : openSegment ℝ P Q ⊆ interior T.carrier := by rw [hPform, hQform]; exact hint0
  have hPfr : P ∈ frontier T.carrier := by rw [hPform]; exact hfr0
  have hPnv : P ∉ Set.range T.pts := by rw [hPform]; exact hnv0
  have e1 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e2 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  obtain ⟨f, c0, hf0, hfle, hfP, hfQ, hfO⟩ := exists_supporting (D.tile i) (j + 1)
  rw [e1] at hfQ
  rw [e2] at hfO
  obtain ⟨j', -, X, hX, -, -, hcar2, -⟩ := corner_chord_reflection_ex D hirr hS hac hbc hwordc i (j + 1)
    (P := P) (Q := Q) rfl (by rw [e1]) hPQc f hf0 c0
    (fun t => hfle _ (subset_convexHull ℝ _ ⟨t, rfl⟩)) hfP hfQ g cg hgle hgP hgQ h ch hhle hhQ hhP
    hintPQ hPfr hPnv
  rw [e2, hjv] at hX
  rw [hX] at hcar2
  have hZeq : P + Q - O = P + (Q - O) := by abel
  rw [hZeq] at hcar2
  have hgZ : g (P + (Q - O)) = g Q := by
    rw [map_add, map_sub, hgP]
    have : g O = cg := hgv
    rw [this]; ring
  have hwall : ∀ y ∈ openSegment ℝ Q (P + (Q - O)), ∀ i', y ∉ interior (D.tile i').carrier :=
    wall_of_hull_func D.toDissection j' hcar2 g hg0 (g Q) rfl hgZ (by linarith)
  -- the chain
  have hhZ : h (P + (Q - O)) < ch := by
    rw [map_add, hhq]
    linarith
  have hQZ : Q ≠ P + (Q - O) := by
    intro he
    apply hu
    have : P - O = 0 := by
      have h2 : (P + (Q - O)) - Q = P - O := by abel
      rw [← h2, ← he, sub_self]
    exact this
  have hlineMap : ∀ τ : ℝ, AffineMap.lineMap Q (P + (Q - O)) τ = Q + τ • (P - O) := by
    intro τ
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    have : (P + (Q - O)) - Q = P - O := by abel
    rw [this, add_comm]
  obtain ⟨-, hsum⟩ := chain_sum_open_end D.toDissection g hg0 (g Q) hQZ rfl hgZ h ch hhle hhQ hhZ hintQZ hwall
    ⟨s0, hs0pos, fun s hs hsle => ⟨K3, by
      rw [hlineMap]
      have := hover s hs hsle
      have e : (P + (Q - O)) + s • (P - O) = Q + (1 + s) • (P - O) := by module
      rwa [e] at this⟩⟩
  -- the `b`-edge of `T₄` on the chord
  have hdPZ : dist Q (P + (Q - O)) = a := by
    rw [dist_eq_norm]
    have : Q - (P + (Q - O)) = -(P - O) := by abel
    rw [this, norm_neg, hnu]
  have hgW : g (Q + (b / a) • (P - O)) = g Q := by rw [map_add, map_smul, hgu, smul_zero, add_zero]
  have hdW : dist Q (Q + (b / a) • (P - O)) = b := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hab0, hnu]; field_simp
  have hWseg : Q + (b / a) • (P - O) ∈ segment ℝ Q (P + (Q - O)) := by
    refine ⟨1 - b / a, b / a, ?_, hab0.le, by ring, by module⟩
    have : b / a < 1 := (div_lt_one hapos).mpr hba
    linarith
  have hQseg : Q ∈ segment ℝ Q (P + (Q - O)) := left_mem_segment ℝ _ _
  have hgV4 : g (Q + (a / b) • (Q - O)) ≤ g Q := by
    rw [map_add, map_smul, smul_eq_mul]
    have := mul_neg_of_pos_of_neg hba0 hgq
    linarith
  have hcov : ∀ m t : Fin 3, t = m ∨ t = m + 1 ∨ t = m + 2 := by decide
  have hchain : ((K4, m4 + 1) : Fin N × Fin 3) ∈ D.lineChain g (g Q) := by
    rw [Dissection.mem_lineChain]
    have hle : ∀ t : Fin 3, g ((D.tile K4).pts t) ≤ g Q := by
      intro t
      rcases hcov m4 t with rfl | rfl | rfl
      · rw [hK4m]; exact hgV4
      · rcases hK4v with ⟨x1, x2⟩ | ⟨x1, x2⟩
        · rw [x1]
        · rw [x1, hgW]
      · rcases hK4v with ⟨x1, x2⟩ | ⟨x1, x2⟩
        · rw [x2, hgW]
        · rw [x2]
    refine ⟨?_, ?_, hle⟩
    · rcases hK4v with ⟨x1, x2⟩ | ⟨x1, x2⟩
      · exact (congrArg g x1)
      · exact x1 ▸ hgW
    · show g ((D.tile K4).pts (m4 + 1 + 1)) = g Q
      rw [e1]
      rcases hK4v with ⟨x1, x2⟩ | ⟨x1, x2⟩
      · rw [x2, hgW]
      · rw [x2]
  have hsub : (D.tile K4).edge (m4 + 1) ⊆ segment ℝ Q (P + (Q - O)) := by
    unfold Tri.edge
    rw [e1]
    rcases hK4v with ⟨x1, x2⟩ | ⟨x1, x2⟩
    · rw [x1, x2]; exact (convex_segment _ _).segment_subset hQseg hWseg
    · rw [x1, x2]; exact (convex_segment _ _).segment_subset hWseg hQseg
  have hb0 : dist ((D.tile K4).pts (m4 + 1)) ((D.tile K4).pts (m4 + 1 + 1)) = b := by
    rw [e1]
    rcases hK4v with ⟨x1, x2⟩ | ⟨x1, x2⟩
    · rw [x1, x2]; exact hdW
    · rw [x1, x2, dist_comm]; exact hdW
  obtain ⟨x, y, z, hy, hxyz⟩ := word_of_sum_with D hS hab hac hbc _ (dist Q (P + (Q - O))) dist_nonneg hsum
    (K4, m4 + 1) (Finset.mem_filter.mpr ⟨hchain, hsub⟩) hb0
  rw [hdPZ] at hxyz
  exact absurd (hword1 x y z hxyz) (by omega)

end Erdos634.C2Forward

#print axioms Erdos634.C2Forward.l4_corner
