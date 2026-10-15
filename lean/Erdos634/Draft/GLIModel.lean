import Mathlib.Tactic
import Erdos634.Draft.GLIWall
import Erdos634.Draft.GLGMain
import Erdos634.Draft.GLCFan

/-!
# A real side chain as a `GLG.Side`

For a `CongruentDissection` with `TwoAlphaData α a b c`, `α ∉ ℚπ`, and an ordered chain `E 0 … E (n-1)` of tile edges on a wall,
`sideOf` is the `GLG.Side` with `ty m` = the edge's type by length (`a,b,c`), `fl m` the orientation, such that
`sa m = cls (angle of tile (E m) at its west end)`, `na m = cls (angle at its east end)` (`sa_eq`, `na_eq`).
`sideOf_V`: the vertex rule `V` (at most one `β`, one `γ` at an interior junction), from `GLC.angles_differ_2alpha`
and distinct tiles at distinct chain indices.  `sum_lenK`: `s · ∑ lenK(ty) = |ab|` when `a,b,c = s·(k²,2k+1,k(k+1))`.
-/

namespace Erdos634.GLI

open Erdos634.Geometry Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.GLG

variable {N : ℕ}

noncomputable def clsA (α θ : ℝ) : Ang :=
  if θ = α then Ang.al else if θ = Real.pi - 3 * α then Ang.be else Ang.ga

noncomputable def tyE (D : Dissection N) (a b : ℝ) (e : Fin N × Fin 3) : TT :=
  if D.eLen e = a then TT.a else if D.eLen e = b then TT.b else TT.c

noncomputable def westIdx (dir : Plane →ₗ[ℝ] ℝ) (T : Tri) (x : Fin 3) : Fin 3 :=
  open Classical in if dir (T.pts x) ≤ dir (T.pts (x + 1)) then x else x + 1

noncomputable def eastIdx (dir : Plane →ₗ[ℝ] ℝ) (T : Tri) (x : Fin 3) : Fin 3 :=
  open Classical in if dir (T.pts x) ≤ dir (T.pts (x + 1)) then x + 1 else x

theorem pts_west (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3) :
    (D.tile e.1).pts (westIdx dir (D.tile e.1) e.2) = edgeWest D dir e := by
  unfold westIdx edgeWest; split_ifs <;> rfl

theorem pts_east (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3) :
    (D.tile e.1).pts (eastIdx dir (D.tile e.1) e.2) = edgeEast D dir e := by
  unfold eastIdx edgeEast; split_ifs <;> rfl

theorem west_east_cases (dir : Plane →ₗ[ℝ] ℝ) (T : Tri) (x : Fin 3) :
    (westIdx dir T x = x ∧ eastIdx dir T x = x + 1) ∨ (westIdx dir T x = x + 1 ∧ eastIdx dir T x = x) := by
  unfold westIdx eastIdx; split_ifs
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

noncomputable def wAng (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3) : ℝ :=
  (D.tile e.1).angleAt (westIdx dir (D.tile e.1) e.2)

noncomputable def eAng (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3) : ℝ :=
  (D.tile e.1).angleAt (eastIdx dir (D.tile e.1) e.2)

theorem ends_ne (t : TT) : (ends t).1 ≠ (ends t).2 := by cases t <;> simp [ends]

theorem edge_triple (D : CongruentDissection N) {α a b c : ℝ} (h : D.model.TwoAlphaData α a b c)
    (e : Fin N × Fin 3) :
    ((D.tile e.1).angleAt (e.2 + 2) = α ∧ D.eLen e = a) ∨
    ((D.tile e.1).angleAt (e.2 + 2) = Real.pi - 3 * α ∧ D.eLen e = b) ∨
    ((D.tile e.1).angleAt (e.2 + 2) = 2 * α ∧ D.eLen e = c) := by
  obtain ⟨σ', hσ'⟩ := (D.tiles_congruent e.1).exists_perm
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have hopp : (D.tile e.1).oppLen (e.2 + 2) = D.eLen e := by
    unfold Tri.oppLen Dissection.eLen
    rw [(by decide : ∀ x : Fin 3, x + 2 + 1 = x) e.2, (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) e.2]
  obtain ⟨m, hm⟩ := σ.surjective (σ' (e.2 + 2))
  have hm3 : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hm3 with rfl | rfl | rfl
  · exact Or.inl ⟨by rw [(hσ' _).1, ← hm, h0], by rw [← hopp, (hσ' _).2, ← hm, o0]⟩
  · exact Or.inr (Or.inl ⟨by rw [(hσ' _).1, ← hm, h1], by rw [← hopp, (hσ' _).2, ← hm, o1]⟩)
  · exact Or.inr (Or.inr ⟨by rw [(hσ' _).1, ← hm, h2], by rw [← hopp, (hσ' _).2, ← hm, o2]⟩)

theorem pair_core {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (x y z : ℝ)
    (hx : x = α ∨ x = Real.pi - 3 * α ∨ x = 2 * α) (hy : y = α ∨ y = Real.pi - 3 * α ∨ y = 2 * α)
    (hz : z = α ∨ z = Real.pi - 3 * α ∨ z = 2 * α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (t : TT) (ht : (z = α ∧ t = TT.a) ∨ (z = Real.pi - 3 * α ∧ t = TT.b) ∨ (z = 2 * α ∧ t = TT.c)) :
    (clsA α x, clsA α y) = ends t ∨ (clsA α y, clsA α x) = ends t := by
  have hπ := Real.pi_pos
  have d1 : α ≠ Real.pi - 3 * α := fun e => hα ⟨1 / 4, by push_cast; linarith⟩
  have d6 : Real.pi - 3 * α ≠ 2 * α := fun e => hα ⟨1 / 5, by push_cast; linarith⟩
  have d2 : α ≠ 2 * α := by intro e; linarith
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
    rcases ht with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  all_goals first
    | exact absurd rfl hxy | exact absurd rfl hxz | exact absurd rfl hyz
    | exact absurd h1 d1 | exact absurd h1.symm d1 | exact absurd h1 d6 | exact absurd h1.symm d6
    | exact absurd h1 d2 | exact absurd h1.symm d2
    | (left; simp [clsA, ends, d1, d1.symm, d6, d6.symm, d2, d2.symm]; done)
    | (right; simp [clsA, ends, d1, d1.symm, d6, d6.symm, d2, d2.symm]; done)

theorem pair_cls (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoAlphaData α a b c) (dir : Plane →ₗ[ℝ] ℝ) (e : Fin N × Fin 3) :
    (clsA α (wAng D.toDissection dir e), clsA α (eAng D.toDissection dir e))
        = ends (tyE D.toDissection a b e) ∨
      (clsA α (eAng D.toDissection dir e), clsA α (wAng D.toDissection dir e))
        = ends (tyE D.toDissection a b e) := by
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  obtain ⟨hα0, -, -⟩ := Row4.model_sides D h
  have hne01 : e.2 ≠ e.2 + 1 := (by decide : ∀ x : Fin 3, x ≠ x + 1) e.2
  have hne02 : e.2 ≠ e.2 + 2 := (by decide : ∀ x : Fin 3, x ≠ x + 2) e.2
  have hne12 : e.2 + 1 ≠ e.2 + 2 := (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) e.2
  have a01 := Row4.tile_angles_ne D hα h e.1 hne01
  have a02 := Row4.tile_angles_ne D hα h e.1 hne02
  have a12 := Row4.tile_angles_ne D hα h e.1 hne12
  have m0 := Row4.tile_angle_mem D h e.1 e.2
  have m1 := Row4.tile_angle_mem D h e.1 (e.2 + 1)
  have m2 := Row4.tile_angle_mem D h e.1 (e.2 + 2)
  have trip := edge_triple D h e
  have hty : ((D.tile e.1).angleAt (e.2 + 2) = α ∧ tyE D.toDissection a b e = TT.a) ∨
      ((D.tile e.1).angleAt (e.2 + 2) = Real.pi - 3 * α ∧ tyE D.toDissection a b e = TT.b) ∨
      ((D.tile e.1).angleAt (e.2 + 2) = 2 * α ∧ tyE D.toDissection a b e = TT.c) := by
    rcases trip with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by simp [tyE, h2]⟩
    · exact Or.inr (Or.inl ⟨h1, by simp [tyE, h2, hab.symm]⟩)
    · exact Or.inr (Or.inr ⟨h1, by simp [tyE, h2, hac.symm, hbc.symm]⟩)
  have core := pair_core hα hα0 _ _ _ m0 m1 m2 a01 a02 a12 _ hty
  rcases west_east_cases dir (D.tile e.1) e.2 with ⟨hw, he⟩ | ⟨hw, he⟩
  · unfold wAng eAng; rw [hw, he]; exact core
  · unfold wAng eAng; rw [hw, he]; exact core.symm

/-- The side model of a chain. -/
noncomputable def sideOf (D : CongruentDissection N) (α a b : ℝ) (dir : Plane →ₗ[ℝ] ℝ)
    (E : ℕ → Fin N × Fin 3) (n : ℕ) : Side where
  n := n
  ty := fun m => tyE D.toDissection a b (E m)
  fl := fun m => open Classical in
    decide (clsA α (wAng D.toDissection dir (E m)) ≠ (ends (tyE D.toDissection a b (E m))).1)

theorem sa_na (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoAlphaData α a b c) (dir : Plane →ₗ[ℝ] ℝ) (E : ℕ → Fin N × Fin 3) (n m : ℕ) :
    (sideOf D α a b dir E n).sa m = clsA α (wAng D.toDissection dir (E m)) ∧
    (sideOf D α a b dir E n).na m = clsA α (eAng D.toDissection dir (E m)) := by
  have hp := pair_cls D hα h dir (E m)
  set t := tyE D.toDissection a b (E m) with ht
  set cw := clsA α (wAng D.toDissection dir (E m)) with hcw
  set ce := clsA α (eAng D.toDissection dir (E m)) with hce
  have hfl : (sideOf D α a b dir E n).fl m = decide (cw ≠ (ends t).1) := rfl
  show sAng t ((sideOf D α a b dir E n).fl m) = cw ∧ nAng t ((sideOf D α a b dir E n).fl m) = ce
  rw [hfl]
  rcases hp with hp | hp
  · have e1 : (ends t).1 = cw := congrArg Prod.fst hp.symm
    have e2 : (ends t).2 = ce := congrArg Prod.snd hp.symm
    simp [sAng, nAng, e1, e2]
  · have e1 : (ends t).1 = ce := congrArg Prod.fst hp.symm
    have e2 : (ends t).2 = cw := congrArg Prod.snd hp.symm
    have hn' : cw ≠ ce := by rw [← e2, ← e1]; exact (ends_ne t).symm
    simp [sAng, nAng, e1, e2, hn']

theorem sa_eq (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoAlphaData α a b c) (dir : Plane →ₗ[ℝ] ℝ) (E : ℕ → Fin N × Fin 3) (n m : ℕ) :
    (sideOf D α a b dir E n).sa m = clsA α (wAng D.toDissection dir (E m)) :=
  (sa_na D hα h dir E n m).1

theorem na_eq (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoAlphaData α a b c) (dir : Plane →ₗ[ℝ] ℝ) (E : ℕ → Fin N × Fin 3) (n m : ℕ) :
    (sideOf D α a b dir E n).na m = clsA α (eAng D.toDissection dir (E m)) :=
  (sa_na D hα h dir E n m).2

theorem cls_ga {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) {θ : ℝ}
    (hθ : θ = α ∨ θ = Real.pi - 3 * α ∨ θ = 2 * α) (h : clsA α θ = Ang.ga) : θ = 2 * α := by
  have hπ := Real.pi_pos
  have d1 : α ≠ Real.pi - 3 * α := fun e => hα ⟨1 / 4, by push_cast; linarith⟩
  rcases hθ with rfl | rfl | rfl
  · simp [clsA] at h
  · simp [clsA, d1.symm] at h
  · rfl

theorem cls_be {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) {θ : ℝ}
    (hθ : θ = α ∨ θ = Real.pi - 3 * α ∨ θ = 2 * α) (h : clsA α θ = Ang.be) : θ = Real.pi - 3 * α := by
  have hπ := Real.pi_pos
  have d1 : α ≠ Real.pi - 3 * α := fun e => hα ⟨1 / 4, by push_cast; linarith⟩
  have d6 : Real.pi - 3 * α ≠ 2 * α := fun e => hα ⟨1 / 5, by push_cast; linarith⟩
  have h2 : (2:ℝ) * α ≠ α := by intro e; linarith
  rcases hθ with rfl | rfl | rfl
  · simp [clsA] at h
  · rfl
  · simp [clsA, d6.symm, h2] at h

theorem cls_al {α : ℝ} {θ : ℝ} (h : clsA α θ = Ang.al) : θ = α := by
  by_contra hne
  simp [clsA, hne] at h
  split_ifs at h

theorem al_cls {α : ℝ} : clsA α α = Ang.al := by simp [clsA]

/-- **Vertex rule `V`** (interface lemma I2): at an interior junction of a side chain at most one `β` and one `γ`. -/
theorem sideOf_V (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoAlphaData α a b c) {w : Wall D.toDissection} {E : ℕ → Fin N × Fin 3} {n : ℕ}
    (C : IsChain w E n) : (sideOf D α a b w.dir E n).V := by
  obtain ⟨hα0, -, -⟩ := Row4.model_sides D h
  have hjn : ∀ i, i + 1 < n →
      (D.tile (E i).1).localAngle (edgeEast D.toDissection w.dir (E i)) = eAng D.toDissection w.dir (E i) ∧
      (D.tile (E (i + 1)).1).localAngle (edgeEast D.toDissection w.dir (E i))
        = wAng D.toDissection w.dir (E (i + 1)) := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [← pts_east, Tri.localAngle_vertex]; rfl
    · rw [C.junc i hi, ← pts_west, Tri.localAngle_vertex]; rfl
  have key : ∀ i, i + 1 < n → ∀ θ, (θ = Real.pi - 3 * α ∨ θ = 2 * α) →
      eAng D.toDissection w.dir (E i) = θ → wAng D.toDissection w.dir (E (i + 1)) = θ → False := by
    intro i hi θ hθ h1 h2
    obtain ⟨j1, j2⟩ := hjn i hi
    obtain ⟨hv, hnv⟩ := C.junction_boundary hi
    have hne := C.tile_ne (by omega : i < n) hi (by omega : i ≠ i + 1)
    have := GLC.angles_differ_2alpha D hα h hv hnv hne (by rw [j1, h1]; exact hθ)
    rw [j1, j2, h1, h2] at this
    exact this rfl
  constructor
  · intro i hi ⟨h1, h2⟩
    rw [na_eq D hα h] at h1
    rw [sa_eq D hα h] at h2
    have e1 := cls_ga hα (by exact (Row4.tile_angle_mem D h _ _)) h1
    have e2 := cls_ga hα (by exact (Row4.tile_angle_mem D h _ _)) h2
    exact key i hi _ (Or.inr rfl) e1 e2
  · intro i hi ⟨h1, h2⟩
    rw [na_eq D hα h] at h1
    rw [sa_eq D hα h] at h2
    have e1 := cls_be hα hα0 (by exact (Row4.tile_angle_mem D h _ _)) h1
    have e2 := cls_be hα hα0 (by exact (Row4.tile_angle_mem D h _ _)) h2
    exact key i hi _ (Or.inl rfl) e1 e2

end Erdos634.GLI

#print axioms Erdos634.GLI.sideOf_V
#print axioms Erdos634.GLI.sa_na
