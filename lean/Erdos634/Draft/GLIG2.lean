import Mathlib.Tactic
import Erdos634.Draft.GLICorner
import Erdos634.Draft.GLCG2k

/-!
# `G*` from `corner_G2_k`

`forward_next`: a tile with a vertex at the east end of chain edge `E m` and an edge going forward along the wall gives `E (m+1)`.
`double_not_vertex`: if `2·|OP| < |side|`, the point `P + (P - O)` is not a target vertex.
`corner_G2_side`: at an `α` corner with both walls' chains, if the corner tile's edge on wall `wa` is `c`, its second chain edge is `c`
(the `(c,c)` configuration), and `2c`, `2b` are shorter than the sides, then the third chain edge of `wa` starts with `α`
(the model's `G*`).
-/

namespace Erdos634.GLI

open Erdos634.Geometry Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.GLG
  Erdos634.BaseChain

variable {N : ℕ}

theorem forward_next {D : Dissection N} {w : Wall D} {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain w E n)
    {m : ℕ} (hm : m < n) {v : Plane} {r0 : ℝ} (hr0 : 0 < r0) (hv : v = r0 • (w.b - w.a))
    {K : Fin N} {l : Fin 3} (hU : (D.tile K).pts l = edgeEast D w.dir (E m))
    (hr : SameRay ℝ v ((D.tile K).pts (l + 1) - (D.tile K).pts l) ∨
      SameRay ℝ v ((D.tile K).pts (l + 2) - (D.tile K).pts l)) :
    m + 1 < n ∧ (E (m + 1)).1 = K ∧ edgeWest D w.dir (E (m + 1)) = (D.tile K).pts l ∧
      ∃ Q : Plane, (Q = (D.tile K).pts (l + 1) ∨ Q = (D.tile K).pts (l + 2)) ∧
        SameRay ℝ v (Q - (D.tile K).pts l) ∧ D.eLen (E (m + 1)) = dist ((D.tile K).pts l) Q ∧
        edgeEast D w.dir (E (m + 1)) = Q := by
  have hab : w.b - w.a ≠ 0 := sub_ne_zero.mpr w.hab.symm
  have hv0 : v ≠ 0 := by rw [hv]; exact smul_ne_zero hr0.ne' hab
  have hgU : w.g ((D.tile K).pts l) = 0 := by rw [hU]; exact C.edgeEast_on_wall trivial hm
  have step : ∀ (x' : Fin 3) (Q : Plane), Q ≠ (D.tile K).pts l → SameRay ℝ v (Q - (D.tile K).pts l) →
      (((D.tile K).pts x' = (D.tile K).pts l ∧ (D.tile K).pts (x' + 1) = Q) ∨
        ((D.tile K).pts x' = Q ∧ (D.tile K).pts (x' + 1) = (D.tile K).pts l)) →
      m + 1 < n ∧ (K, x') = E (m + 1) ∧ D.eLen (E (m + 1)) = dist ((D.tile K).pts l) Q ∧
        edgeEast D w.dir (E (m + 1)) = Q := by
    intro x' Q hQP hQr hQe
    obtain ⟨r1, hr1, hQ1⟩ := sameRay_vec hQr hv0 (sub_ne_zero.mpr hQP)
    have hQ : Q = (D.tile K).pts l + (r1 * r0) • (w.b - w.a) := by
      have : Q - (D.tile K).pts l = (r1 * r0) • (w.b - w.a) := by rw [hQ1, hv, smul_smul]
      rw [← this]; abel
    obtain ⟨h1n, hE1⟩ := C.next_of_edge (mul_pos hr1 hr0) hgU hQ hQe hm hU
    obtain ⟨-, -, hEa', -, -⟩ := edge_ends_of_vec w (mul_pos hr1 hr0) hgU hQ hQe
    refine ⟨h1n, hE1, ?_, ?_⟩
    · rw [← hE1]
      show dist ((D.tile K).pts x') ((D.tile K).pts (x' + 1)) = dist ((D.tile K).pts l) Q
      rcases hQe with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2]; exact dist_comm _ _
    · rw [← hE1]; exact hEa'
  have hKP1 : (D.tile K).pts (l + 1) ≠ (D.tile K).pts l := fun h' =>
    Erdos634.TilePlacement.pts_ne (D.tile K) ((by decide : ∀ y : Fin 3, y ≠ y + 1) l) h'.symm
  have hKP2 : (D.tile K).pts (l + 2) ≠ (D.tile K).pts l := fun h' =>
    Erdos634.TilePlacement.pts_ne (D.tile K) ((by decide : ∀ y : Fin 3, y ≠ y + 2) l) h'.symm
  have hjn := C.junc m
  rcases hr with hr | hr
  · obtain ⟨h1n, hE1, hd, he⟩ := step l _ hKP1 hr (Or.inl ⟨rfl, rfl⟩)
    exact ⟨h1n, (congrArg Prod.fst hE1).symm, (hjn h1n).symm.trans hU.symm, _, Or.inl rfl, hr, hd, he⟩
  · obtain ⟨h1n, hE1, hd, he⟩ := step (l + 2) _ hKP2 hr
      (Or.inr ⟨rfl, by rw [(by decide : ∀ y : Fin 3, y + 2 + 1 = y) l]⟩)
    exact ⟨h1n, (congrArg Prod.fst hE1).symm, (hjn h1n).symm.trans hU.symm, _, Or.inr rfl, hr, hd, he⟩

theorem double_not_vertex {D : Dissection N} (w : Wall D) {O P : Plane} (hO : O = w.a)
    (hP : SameRay ℝ (w.b - w.a) (P - O)) (hPO : P ≠ O) (hlt : 2 * dist O P < dist w.a w.b) :
    ∀ v : Fin 3, D.target.pts v ≠ P + (P - O) := by
  have hab : w.b - w.a ≠ 0 := sub_ne_zero.mpr w.hab.symm
  obtain ⟨r0, hr0, hP0⟩ := sameRay_vec hP hab (sub_ne_zero.mpr hPO)
  have hd1 : dist O P = r0 * ‖w.b - w.a‖ := by
    rw [dist_comm, dist_eq_norm, hP0, norm_smul, Real.norm_of_nonneg hr0.le]
  have hd2 : dist w.a w.b = ‖w.b - w.a‖ := by rw [dist_comm, dist_eq_norm]
  have hn : 0 < ‖w.b - w.a‖ := norm_pos_iff.mpr hab
  rw [hd1, hd2] at hlt
  have h2r : 2 * r0 < 1 := by nlinarith
  have hX : P + (P - O) = O + (2 * r0) • (w.b - w.a) := by
    have : P = O + r0 • (w.b - w.a) := by rw [← hP0]; abel
    rw [this]
    module
  have hgO : w.g O = 0 := by rw [hO]; exact w.hline _ (left_mem_segment ℝ _ _)
  obtain ⟨hgX, -⟩ := wall_dir_of_vec w (by linarith : 0 < 2 * r0) hgO hX
  intro v hv
  rw [hX] at hv
  have hgv : w.g (D.target.pts v) = 0 := by rw [hv, ← hX]; exact hgX
  rcases w.hvert v hgv with h | h
  · rw [h, hO] at hv
    have h0 : w.a + 0 = w.a + (2 * r0) • (w.b - w.a) := by rw [add_zero]; exact hv
    have : (2 * r0) • (w.b - w.a) = 0 := (add_left_cancel h0).symm
    rcases smul_eq_zero.mp this with h' | h'
    · linarith
    · exact hab h'
  · rw [h, hO] at hv
    have hX' : (2 * r0) • (w.b - w.a) = w.b - w.a := by
      calc (2 * r0) • (w.b - w.a) = (w.a + (2 * r0) • (w.b - w.a)) - w.a := by abel
        _ = w.b - w.a := by rw [← hv]
    have : (2 * r0 - 1) • (w.b - w.a) = 0 := by rw [sub_smul, one_smul, hX']; abel
    rcases smul_eq_zero.mp this with h' | h'
    · linarith
    · exact hab h'

theorem eLen_c (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoAlphaData α a b c) {e : Fin N × Fin 3} (he : tyE D.toDissection a b e = TT.c) :
    D.eLen e = c := by
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  rcases Row4.eLen_abc D h e with h1 | h1 | h1
  · simp [tyE, h1] at he
  · simp [tyE, h1, hab.symm] at he
  · exact h1

theorem eLen_b (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoAlphaData α a b c) {e : Fin N × Fin 3} (he : tyE D.toDissection a b e = TT.b) :
    D.eLen e = b := by
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  rcases Row4.eLen_abc D h e with h1 | h1 | h1
  · simp [tyE, h1] at he
  · exact h1
  · simp [tyE, h1, hac.symm, hbc.symm] at he

theorem corner_G2_core (D : CongruentDissection N) {α a b c s : ℝ} (k : ℕ) (hk2 : 2 ≤ k) (hs : 0 < s)
    (ha : a = s * (k : ℝ) ^ 2) (hb : b = s * (2 * k + 1)) (hc : c = s * (k * (k + 1)))
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (κ : Fin 3) (hκ : D.target.angleAt κ = α)
    (hA1 : dist (D.target.pts κ) (D.target.pts (κ + 1)) ≠ b)
    (hA2 : dist (D.target.pts κ) (D.target.pts (κ + 1)) ≠ c)
    (hB1 : dist (D.target.pts κ) (D.target.pts (κ + 2)) ≠ b)
    (hB2 : dist (D.target.pts κ) (D.target.pts (κ + 2)) ≠ c)
    {wa wb : Wall D.toDissection} {Ea Eb : ℕ → Fin N × Fin 3} {na nb : ℕ}
    (Ca : IsChain wa Ea na) (Cb : IsChain wb Eb nb)
    {i : Fin N} {j : Fin 3} {Pa Pb : Plane} (hij : (D.tile i).pts j = D.target.pts κ)
    (hjα : (D.tile i).angleAt j = α)
    (SA : SideAt D α wa Ea na i j Pa) (SB : SideAt D α wb Eb nb i j Pb)
    (hPab : (Pa = (D.tile i).pts (j + 1) ∧ Pb = (D.tile i).pts (j + 2)) ∨
      (Pa = (D.tile i).pts (j + 2) ∧ Pb = (D.tile i).pts (j + 1)))
    (htc : tyE D.toDissection a b (Ea 0) = TT.c) (htb : tyE D.toDissection a b (Eb 0) = TT.b)
    (hLa : 2 * c < dist wa.a wa.b) (hLb : 2 * b < dist wb.a wb.b)
    (h11 : tyE D.toDissection a b (Ea 1) = TT.c) :
    2 < na ∧ wAng D.toDissection wa.dir (Ea 2) = α := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨i', j', hi'p, hi'a, hG⟩ := GLC.corner_G2_k D k hk2 hs ha hb hc hα h κ hκ hA1 hA2 hB1 hB2
  have hcnt := (GLC.corner_has_alpha_tile D hα h hκ).1
  unfold GLC.cntA at hcnt
  have hloc : ∀ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts κ →
      (D.tile i).angleAt j = α → (D.tile i).localAngle (D.target.pts κ) = α := by
    intro i j hp ha'; rw [← hp, Tri.localAngle_vertex]; exact ha'
  have hii : i' = i := by
    have hle := Finset.card_le_one.mp (le_of_eq hcnt)
    exact hle i' (by simp [hloc i' j' hi'p hi'a]) i (by simp [hloc i j hij hjα])
  rw [hii] at hi'p hi'a hG
  have hjj : j' = j := (D.tile i).indep.injective (hi'p.trans hij.symm)
  rw [hjj] at hG
  obtain ⟨m1, m2, hm, hm1, hm2⟩ : ∃ m1 m2 : Fin 3, ((m1 = j + 1 ∧ m2 = j + 2) ∨ (m1 = j + 2 ∧ m2 = j + 1)) ∧
      (D.tile i).pts m1 = Pa ∧ (D.tile i).pts m2 = Pb := by
    rcases hPab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨j + 1, j + 2, Or.inl ⟨rfl, rfl⟩, h1.symm, h2.symm⟩
    · exact ⟨j + 2, j + 1, Or.inr ⟨rfl, rfl⟩, h1.symm, h2.symm⟩
  have hdc' : dist ((D.tile i).pts j) Pa = c := by rw [← SA.len0]; exact eLen_c D hα h htc
  have hdb' : dist ((D.tile i).pts j) Pb = b := by rw [← SB.len0]; exact eLen_b D hα h htb
  have hdc : dist (D.target.pts κ) ((D.tile i).pts m1) = c := by rw [hm1, ← hij]; exact hdc'
  have hdb : dist (D.target.pts κ) ((D.tile i).pts m2) = b := by rw [hm2, ← hij]; exact hdb'
  have hnv1 : ∀ v' : Fin 3, D.target.pts v' ≠ (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts κ) := by
    intro v'
    rw [hm1, ← hij]
    exact double_not_vertex wa SA.wa_eq.symm SA.ray SA.ne_O (by rw [hdc']; exact hLa) v'
  have hnv2 : ∀ v' : Fin 3, D.target.pts v' ≠ (D.tile i).pts m2 + ((D.tile i).pts m2 - D.target.pts κ) := by
    intro v'
    rw [hm2, ← hij]
    exact double_not_vertex wb SB.wa_eq.symm SB.ray SB.ne_O (by rw [hdb']; exact hLb) v'
  obtain ⟨K, l, hK1, hKl, hKa, Q, hQ, hQr, hd, he⟩ := SA.second
  have hdc2 : dist Pa Q = c := hd.symm.trans (eLen_c D hα h h11)
  have hKcond : (SameRay ℝ ((D.tile i).pts m1 - D.target.pts κ)
        ((D.tile K).pts (l + 1) - (D.tile i).pts m1) ∧
        dist ((D.tile i).pts m1) ((D.tile K).pts (l + 1)) = c) ∨
      (SameRay ℝ ((D.tile i).pts m1 - D.target.pts κ) ((D.tile K).pts (l + 2) - (D.tile i).pts m1) ∧
        dist ((D.tile i).pts m1) ((D.tile K).pts (l + 2)) = c) := by
    rcases hQ with hQ | hQ
    · rw [hQ] at hQr hdc2
      exact Or.inl ⟨by rw [hm1, ← hij]; exact hQr, by rw [hm1]; exact hdc2⟩
    · rw [hQ] at hQr hdc2
      exact Or.inr ⟨by rw [hm1, ← hij]; exact hQr, by rw [hm1]; exact hdc2⟩
  obtain ⟨-, K', l'', hK'p, hK'a, hK'r⟩ :=
    hG m1 m2 hm hdc hdb hnv1 hnv2 K l (hKl.trans hm1.symm) hKa hKcond
  rw [hm1, ← hij] at hK'p hK'r
  -- Q = Pa + (Pa - O)
  have hPO' : Pa - (D.tile i).pts j ≠ 0 := sub_ne_zero.mpr SA.ne_O
  have hQP : Q - Pa ≠ 0 := by
    intro h0
    have : Q = Pa := sub_eq_zero.mp h0
    rw [this, dist_self] at hdc2
    linarith
  obtain ⟨r1, hr1, hQ1⟩ := sameRay_vec hQr hPO' hQP
  have hn1 : ‖Pa - (D.tile i).pts j‖ = c := by rw [← hdc', dist_comm, dist_eq_norm]
  have hn2 : ‖Q - Pa‖ = c := by rw [← hdc2, dist_comm, dist_eq_norm]
  have hr1' : r1 = 1 := by
    rw [hQ1, norm_smul, Real.norm_of_nonneg hr1.le, hn1] at hn2
    exact mul_right_cancel₀ hc0.ne' (hn2.trans (one_mul c).symm)
  have hQeq : Q = Pa + (Pa - (D.tile i).pts j) := by
    rw [hr1', one_smul] at hQ1
    rw [← hQ1]; abel
  obtain ⟨r0, hr0, hP0⟩ := sameRay_vec SA.ray (sub_ne_zero.mpr wa.hab.symm) hPO'
  have hU : (D.tile K').pts l'' = edgeEast D.toDissection wa.dir (Ea 1) := by
    rw [hK'p, he, hQeq]
  obtain ⟨h2n, hK2, hW2, -⟩ := forward_next Ca (m := 1) SA.one_lt hr0 hP0 hU (by
    rcases hK'r with hr | hr
    · left; rw [hK'p]; exact hr
    · right; rw [hK'p]; exact hr)
  exact ⟨h2n, by rw [wAng_eq wa.dir hK2 hW2]; exact hK'a⟩

end Erdos634.GLI

#print axioms Erdos634.GLI.corner_G2_core
