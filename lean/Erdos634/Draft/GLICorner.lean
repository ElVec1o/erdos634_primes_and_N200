import Mathlib.Tactic
import Erdos634.Draft.GLISum
import Erdos634.Draft.GLCG1
import Erdos634.Draft.GLCArith

/-!
# Corners: `K` coupling and `C2` from `corner_G1`

`corner_both`: at a target corner `O = pts k` of angle `α` with two oriented walls `wa`, `wb` starting at `O` (ending at `pts (k+1)`, `pts (k+2)`) and
their chains, `GLC.corner_G1` gives the corner tile `T = tile i` (vertex `j` at `O`); its two edges at `O` are the first chain edges `Ea 0`, `Eb 0`
(`SideAt.start`), of types `{b, c}` (the coupling `K`), with `α` at the corner (`sa 0 = α`), and each wall's SECOND chain edge starts with `α`
(`C2`, via the tile `K` of `corner_G1` and `next_of_edge`).
-/

namespace Erdos634.GLI

open Erdos634.Geometry Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.GLG
  Erdos634.BaseChain

variable {N : ℕ}

theorem sameRay_vec {x y : Plane} (h : SameRay ℝ x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ y = r • x := by
  obtain ⟨r, hr, e⟩ := h.exists_pos_left hx hy
  exact ⟨r, hr, e.symm⟩

theorem wAng_eq {D : Dissection N} (dir : Plane →ₗ[ℝ] ℝ) {e : Fin N × Fin 3} {K : Fin N} (hK : e.1 = K)
    {l : Fin 3} (hl : edgeWest D dir e = (D.tile K).pts l) : wAng D dir e = (D.tile K).angleAt l := by
  subst hK
  have h1 := pts_west D dir e
  rw [hl] at h1
  have := (D.tile e.1).indep.injective h1
  unfold wAng; rw [this]

theorem eAng_eq {D : Dissection N} (dir : Plane →ₗ[ℝ] ℝ) {e : Fin N × Fin 3} {K : Fin N} (hK : e.1 = K)
    {l : Fin 3} (hl : edgeEast D dir e = (D.tile K).pts l) : eAng D dir e = (D.tile K).angleAt l := by
  subst hK
  have h1 := pts_east D dir e
  rw [hl] at h1
  have := (D.tile e.1).indep.injective h1
  unfold eAng; rw [this]

/-- The data of one side at a corner: the first chain edge is an edge of the corner tile, the second chain edge starts with `α`. -/
structure SideAt (D : CongruentDissection N) (α : ℝ) (w : Wall D.toDissection) (E : ℕ → Fin N × Fin 3)
    (n : ℕ) (i : Fin N) (j : Fin 3) (P : Plane) : Prop where
  first_tile : (E 0).1 = i
  wa_eq : w.a = (D.tile i).pts j
  ray : SameRay ℝ (w.b - w.a) (P - (D.tile i).pts j)
  ne_O : P ≠ (D.tile i).pts j
  len0 : D.eLen (E 0) = dist ((D.tile i).pts j) P
  west0 : edgeWest D.toDissection w.dir (E 0) = (D.tile i).pts j
  east0 : edgeEast D.toDissection w.dir (E 0) = P
  ang0 : wAng D.toDissection w.dir (E 0) = α
  one_lt : 1 < n
  ang1 : wAng D.toDissection w.dir (E 1) = α
  second : ∃ (K : Fin N) (l : Fin 3), (E 1).1 = K ∧ (D.tile K).pts l = P ∧ (D.tile K).angleAt l = α ∧
    ∃ Q : Plane, (Q = (D.tile K).pts (l + 1) ∨ Q = (D.tile K).pts (l + 2)) ∧
      SameRay ℝ (P - (D.tile i).pts j) (Q - P) ∧ D.eLen (E 1) = dist P Q ∧
      edgeEast D.toDissection w.dir (E 1) = Q

theorem corner_side_west (D : CongruentDissection N) {α : ℝ} {w : Wall D.toDissection}
    {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain w E n) {i : Fin N} {j x : Fin 3} {P : Plane}
    (hO : (D.tile i).pts j = w.a) (hja : (D.tile i).angleAt j = α)
    (hP : SameRay ℝ (w.b - w.a) (P - (D.tile i).pts j)) (hPO : P ≠ (D.tile i).pts j)
    (hends : ((D.tile i).pts x = (D.tile i).pts j ∧ (D.tile i).pts (x + 1) = P) ∨
      ((D.tile i).pts x = P ∧ (D.tile i).pts (x + 1) = (D.tile i).pts j))
    {K : Fin N} {l : Fin 3} (hKl : (D.tile K).pts l = P) (hKa : (D.tile K).angleAt l = α)
    (hKr : SameRay ℝ (P - (D.tile i).pts j) ((D.tile K).pts (l + 1) - P) ∨
      SameRay ℝ (P - (D.tile i).pts j) ((D.tile K).pts (l + 2) - P)) :
    (i, x) = E 0 ∧ SideAt D α w E n i j P := by
  set O := (D.tile i).pts j with hOdef
  have hab : w.b - w.a ≠ 0 := sub_ne_zero.mpr w.hab.symm
  have hPO' : P - O ≠ 0 := sub_ne_zero.mpr hPO
  obtain ⟨r0, hr0, hP0⟩ := sameRay_vec hP hab hPO'
  have hVP : P = O + r0 • (w.b - w.a) := by rw [← hP0]; abel
  have hgO : w.g O = 0 := by rw [hO]; exact w.hline _ (left_mem_segment ℝ _ _)
  have hE0 : (i, x) = E 0 := C.first_of_edge hr0 hgO hVP hends hO
  obtain ⟨-, hW, hEa, -, -⟩ := edge_ends_of_vec w hr0 hgO hVP hends
  have hW0 : edgeWest D.toDissection w.dir (E 0) = O := by rw [← hE0]; exact hW
  have hEast0 : edgeEast D.toDissection w.dir (E 0) = P := by rw [← hE0]; exact hEa
  have hgP : w.g P = 0 := (wall_dir_of_vec w hr0 hgO hVP).1
  have step : ∀ (x' : Fin 3) (Q : Plane), Q ≠ P → SameRay ℝ (P - O) (Q - P) →
      (((D.tile K).pts x' = P ∧ (D.tile K).pts (x' + 1) = Q) ∨
        ((D.tile K).pts x' = Q ∧ (D.tile K).pts (x' + 1) = P)) →
      1 < n ∧ (K, x') = E 1 ∧ D.eLen (E 1) = dist P Q ∧ edgeEast D.toDissection w.dir (E 1) = Q := by
    intro x' Q hQP hQr hQe
    obtain ⟨r1, hr1, hQ1⟩ := sameRay_vec hQr hPO' (sub_ne_zero.mpr hQP)
    have hQ : Q = P + (r1 * r0) • (w.b - w.a) := by
      have : Q - P = (r1 * r0) • (w.b - w.a) := by rw [hQ1, hP0, smul_smul]
      rw [← this]; abel
    obtain ⟨h1n, hE1⟩ := C.next_of_edge (mul_pos hr1 hr0) hgP hQ hQe C.n_pos hEast0.symm
    obtain ⟨-, -, hEa', -, -⟩ := edge_ends_of_vec w (mul_pos hr1 hr0) hgP hQ hQe
    refine ⟨by omega, hE1, ?_, ?_⟩
    · rw [← hE1]
      show dist ((D.tile K).pts x') ((D.tile K).pts (x' + 1)) = dist P Q
      rcases hQe with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2]; exact dist_comm _ _
    · rw [← hE1]; exact hEa'
  have hKP1 : (D.tile K).pts (l + 1) ≠ P := fun h' =>
    Erdos634.TilePlacement.pts_ne (D.tile K) ((by decide : ∀ y : Fin 3, y ≠ y + 1) l) (hKl.trans h'.symm)
  have hKP2 : (D.tile K).pts (l + 2) ≠ P := fun h' =>
    Erdos634.TilePlacement.pts_ne (D.tile K) ((by decide : ∀ y : Fin 3, y ≠ y + 2) l) (hKl.trans h'.symm)
  have hk : ∃ Q : Plane, (Q = (D.tile K).pts (l + 1) ∨ Q = (D.tile K).pts (l + 2)) ∧
      SameRay ℝ (P - O) (Q - P) ∧ 1 < n ∧ (E 1).1 = K ∧
      D.eLen (E 1) = dist P Q ∧ edgeEast D.toDissection w.dir (E 1) = Q := by
    rcases hKr with hr | hr
    · obtain ⟨h1n, hE1, hd, he⟩ := step l _ hKP1 hr (Or.inl ⟨hKl, rfl⟩)
      exact ⟨_, Or.inl rfl, hr, h1n, (congrArg Prod.fst hE1).symm, hd, he⟩
    · obtain ⟨h1n, hE1, hd, he⟩ := step (l + 2) _ hKP2 hr
        (Or.inr ⟨rfl, by rw [(by decide : ∀ y : Fin 3, y + 2 + 1 = y) l]; exact hKl⟩)
      exact ⟨_, Or.inr rfl, hr, h1n, (congrArg Prod.fst hE1).symm, hd, he⟩
  obtain ⟨Q, hQ, hQr, h1n, hK1, hd, he⟩ := hk
  have hjn := C.junc 0 (by omega : 0 + 1 < n)
  have hW1 : edgeWest D.toDissection w.dir (E 1) = (D.tile K).pts l :=
    (hjn.symm.trans hEast0).trans hKl.symm
  have hlen0 : D.eLen (E 0) = dist O P := by
    rw [← hE0]
    show dist ((D.tile i).pts x) ((D.tile i).pts (x + 1)) = dist O P
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; exact dist_comm _ _
  refine ⟨hE0, ⟨(congrArg Prod.fst hE0).symm, hO.symm, hP, hPO, hlen0, hW0, hEast0, ?_, h1n, ?_,
    ⟨K, l, hK1, hKl, hKa, Q, hQ, hQr, hd, he⟩⟩⟩
  · rw [wAng_eq w.dir (congrArg Prod.fst hE0).symm hW0]; exact hja
  · rw [wAng_eq w.dir hK1 hW1]; exact hKa

theorem corner_types (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoAlphaData α a b c) (i : Fin N) (j : Fin 3) (hj : (D.tile i).angleAt j = α) :
    (tyE D.toDissection a b (i, j) = TT.b ∧ tyE D.toDissection a b (i, j + 2) = TT.c) ∨
    (tyE D.toDissection a b (i, j) = TT.c ∧ tyE D.toDissection a b (i, j + 2) = TT.b) := by
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  have n01 := Row4.tile_angles_ne D hα h i ((by decide : ∀ y : Fin 3, y ≠ y + 1) j)
  have n02 := Row4.tile_angles_ne D hα h i ((by decide : ∀ y : Fin 3, y ≠ y + 2) j)
  have n12 := Row4.tile_angles_ne D hα h i ((by decide : ∀ y : Fin 3, y + 1 ≠ y + 2) j)
  have t1 := edge_triple D h (i, j)
  have t2 := edge_triple D h (i, j + 2)
  dsimp only at t1 t2
  rw [(by decide : ∀ y : Fin 3, y + 2 + 2 = y + 1) j] at t2
  have tb : ∀ e : Fin N × Fin 3, D.eLen e = b → tyE D.toDissection a b e = TT.b := fun e he => by
    simp [tyE, he, hab.symm]
  have tc : ∀ e : Fin N × Fin 3, D.eLen e = c → tyE D.toDissection a b e = TT.c := fun e he => by
    simp [tyE, he, hac.symm, hbc.symm]
  rw [hj] at n01 n02
  rcases t1 with ⟨e1, l1⟩ | ⟨e1, l1⟩ | ⟨e1, l1⟩ <;> rcases t2 with ⟨e2, l2⟩ | ⟨e2, l2⟩ | ⟨e2, l2⟩
  all_goals first
    | exact absurd e1 (Ne.symm n02)
    | exact absurd e2 (Ne.symm n01)
    | exact absurd (e1.trans e2.symm) n12.symm
    | exact absurd (e1.trans e2.symm) n12
    | exact Or.inl ⟨tb _ l1, tc _ l2⟩
    | exact Or.inr ⟨tc _ l1, tb _ l2⟩

theorem corner_both (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1)
    (k : Fin 3) (hk : D.target.angleAt k = α)
    (hA1 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ b)
    (hA2 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ c)
    (hB1 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ b)
    (hB2 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ c)
    {wa wb : Wall D.toDissection} {Ea Eb : ℕ → Fin N × Fin 3} {na nb : ℕ}
    (Ca : IsChain wa Ea na) (Cb : IsChain wb Eb nb)
    (haa : wa.a = D.target.pts k) (hab' : wa.b = D.target.pts (k + 1))
    (hba : wb.a = D.target.pts k) (hbb : wb.b = D.target.pts (k + 2)) :
    ∃ (i : Fin N) (j : Fin 3) (Pa Pb : Plane), (D.tile i).pts j = D.target.pts k ∧
      (D.tile i).angleAt j = α ∧ SideAt D α wa Ea na i j Pa ∧ SideAt D α wb Eb nb i j Pb ∧
      ((tyE D.toDissection a b (Ea 0) = TT.b ∧ tyE D.toDissection a b (Eb 0) = TT.c) ∨
       (tyE D.toDissection a b (Ea 0) = TT.c ∧ tyE D.toDissection a b (Eb 0) = TT.b)) ∧
      ((Pa = (D.tile i).pts (j + 1) ∧ Pb = (D.tile i).pts (j + 2)) ∨
       (Pa = (D.tile i).pts (j + 2) ∧ Pb = (D.tile i).pts (j + 1))) := by
  obtain ⟨i, j, hij, hjα, hrays, hlen, j', hj'i, X, hc1, hc2, ⟨K1, l1, h1p, h1a, h1r⟩,
    ⟨K2, l2, h2p, h2a, h2r⟩⟩ := GLC.corner_G1 D hα h hab hac hword k hk hA1 hA2 hB1 hB2
  have hP1 : (D.tile i).pts (j + 1) ≠ (D.tile i).pts j :=
    (Erdos634.TilePlacement.pts_ne (D.tile i) ((by decide : ∀ y : Fin 3, y ≠ y + 1) j)).symm
  have hP2 : (D.tile i).pts (j + 2) ≠ (D.tile i).pts j :=
    (Erdos634.TilePlacement.pts_ne (D.tile i) ((by decide : ∀ y : Fin 3, y ≠ y + 2) j)).symm
  have e21 : (D.tile i).pts (j + 2 + 1) = (D.tile i).pts j := by
    rw [(by decide : ∀ y : Fin 3, y + 2 + 1 = y) j]
  have hty := corner_types D hα h i j hjα
  have hOa : (D.tile i).pts j = wa.a := hij.trans haa.symm
  have hOb : (D.tile i).pts j = wb.a := hij.trans hba.symm
  have h1r' : SameRay ℝ ((D.tile i).pts (j + 1) - (D.tile i).pts j) ((D.tile K1).pts (l1 + 1) - (D.tile i).pts (j + 1)) ∨
      SameRay ℝ ((D.tile i).pts (j + 1) - (D.tile i).pts j) ((D.tile K1).pts (l1 + 2) - (D.tile i).pts (j + 1)) := by
    rw [hij]; exact h1r
  have h2r' : SameRay ℝ ((D.tile i).pts (j + 2) - (D.tile i).pts j) ((D.tile K2).pts (l2 + 1) - (D.tile i).pts (j + 2)) ∨
      SameRay ℝ ((D.tile i).pts (j + 2) - (D.tile i).pts j) ((D.tile K2).pts (l2 + 2) - (D.tile i).pts (j + 2)) := by
    rw [hij]; exact h2r
  rcases hrays with ⟨r1, r2⟩ | ⟨r1, r2⟩
  · obtain ⟨hEa, SA⟩ := corner_side_west D Ca hOa hjα (by rw [haa, hab', hij]; exact r1) hP1
      (Or.inl ⟨rfl, rfl⟩) h1p h1a h1r'
    obtain ⟨hEb, SB⟩ := corner_side_west D Cb hOb hjα (by rw [hba, hbb, hij]; exact r2) hP2
      (Or.inr ⟨rfl, e21⟩) h2p h2a h2r'
    refine ⟨i, j, _, _, hij, hjα, SA, SB, ?_, Or.inl ⟨rfl, rfl⟩⟩
    rw [← hEa, ← hEb]; exact hty
  · obtain ⟨hEa, SA⟩ := corner_side_west D Ca hOa hjα (by rw [haa, hab', hij]; exact r2) hP2
      (Or.inr ⟨rfl, e21⟩) h2p h2a h2r'
    obtain ⟨hEb, SB⟩ := corner_side_west D Cb hOb hjα (by rw [hba, hbb, hij]; exact r1) hP1
      (Or.inl ⟨rfl, rfl⟩) h1p h1a h1r'
    refine ⟨i, j, _, _, hij, hjα, SA, SB, ?_, Or.inr ⟨rfl, rfl⟩⟩
    rw [← hEa, ← hEb]
    rcases hty with ⟨x1, x2⟩ | ⟨x1, x2⟩
    · exact Or.inr ⟨x2, x1⟩
    · exact Or.inl ⟨x2, x1⟩

end Erdos634.GLI

#print axioms Erdos634.GLI.corner_both
#print axioms Erdos634.GLI.corner_types
