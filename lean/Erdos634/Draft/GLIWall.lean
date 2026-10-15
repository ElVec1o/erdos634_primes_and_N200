import Mathlib.Tactic
import Erdos634.WallEndpoints
import Erdos634.WallDir
import Erdos634.WallThird
import Erdos634.BaseWalkGeneral
import Erdos634.Draft.ApexLegWord

/-!
# Oriented wall of a target side and its ordered edge chain

`Wall D` packages the data `WallEndpoints.chain_endpoints` needs for ONE target side, oriented from a vertex `a`
to a vertex `b`: `Wall.fwd D k` (side `k`, `a = pts k`) and `Wall.bwd D k` (reversed).  `exists_wall`: for any two
distinct target vertices `u ≠ v` there is a `Wall` with `a = pts u`, `b = pts v`.
`Wall.exists_chain`: the ordered chain `E 0, …, E (n-1)` of tile edges on the wall (`IsChain`), and its consequences:
lengths, strictly increasing positions, uniqueness of a wall edge by its west position, the telescoping length sum,
junction facts (a junction is a boundary non-vertex point), and distinct tiles at distinct chain indices.
-/

namespace Erdos634.GLI

open Erdos634.Geometry Erdos634.Placement Erdos634.WallEndpoints Erdos634.OrientBridge
  Erdos634.ChainInstance Erdos634.SideWall Erdos634.BaseChain Erdos634.Geometry.Dissection

variable {N : ℕ}

/-- The data of one oriented target side. -/
structure Wall (D : Dissection N) where
  g : Plane →ᵃ[ℝ] ℝ
  dir : Plane →ₗ[ℝ] ℝ
  a : Plane
  b : Plane
  hab : a ≠ b
  hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0
  hne : g.linear ≠ 0
  hwall : ∀ y ∈ D.target.carrier, g y ≤ 0
  hbase : segment ℝ a b ⊆ frontier D.target.carrier
  hline : ∀ y ∈ segment ℝ a b, g y = 0
  hface : ∀ y ∈ D.target.carrier, g y = 0 → y ∈ segment ℝ a b
  hiso : ∀ p q : Plane, g p = 0 → g q = 0 → dist p q = |dir p - dir q|
  hdirab : dir a ≤ dir b
  hvert : ∀ j : Fin 3, g (D.target.pts j) = 0 → D.target.pts j = a ∨ D.target.pts j = b

theorem wall_vert (T : Tri) (k : Fin 3) (j : Fin 3) (h : wallFun T k (T.pts j) = 0) :
    T.pts j = T.pts k ∨ T.pts j = T.pts (k + 1) := by
  have hj : j ≠ k + 2 := by
    intro e; subst e
    have h' : -(T.basis.coord (k + 2) (T.pts (k + 2))) = 0 := h
    rw [Erdos634.Draft.NearBaseVertex.coord_self] at h'
    norm_num at h'
  have key : ∀ k j : Fin 3, j ≠ k + 2 → j = k ∨ j = k + 1 := by decide
  rcases key k j hj with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

noncomputable def Wall.fwd (D : Dissection N) (k : Fin 3) : Wall D where
  g := wallFun D.target k
  dir := (dirFun D.target k).linear
  a := D.target.pts k
  b := D.target.pts (k + 1)
  hab := Erdos634.TilePlacement.pts_ne D.target (by fin_cases k <;> decide)
  hker := hker_wallFun D.target k
  hne := wallFun_linear_ne_zero D.target k
  hwall := fun y hy => wallFun_le D.target k hy
  hbase := edge_subset_frontier D.target k
  hline := fun y hy => wallFun_eq_zero D.target k hy
  hface := hface_wallFun D.target k
  hiso := hiso_wallFun' D.target k
  hdirab := Erdos634.Draft.ApexLegWord.hdirab_dirFun D.target k
  hvert := fun j h => wall_vert D.target k j h

noncomputable def Wall.bwd (D : Dissection N) (k : Fin 3) : Wall D where
  g := wallFun D.target k
  dir := -(dirFun D.target k).linear
  a := D.target.pts (k + 1)
  b := D.target.pts k
  hab := (Erdos634.TilePlacement.pts_ne D.target (by fin_cases k <;> decide)).symm
  hker := fun v h1 h2 => hker_wallFun D.target k v h1 (by simpa using h2)
  hne := wallFun_linear_ne_zero D.target k
  hwall := fun y hy => wallFun_le D.target k hy
  hbase := by rw [segment_symm]; exact edge_subset_frontier D.target k
  hline := fun y hy => wallFun_eq_zero D.target k (by rw [segment_symm] at hy; exact hy)
  hface := fun y hy h0 => by rw [segment_symm]; exact hface_wallFun D.target k y hy h0
  hiso := fun p q hp hq => by
    rw [hiso_wallFun' D.target k p q hp hq]
    simp only [LinearMap.neg_apply]
    rw [show -(dirFun D.target k).linear p - -(dirFun D.target k).linear q
      = -((dirFun D.target k).linear p - (dirFun D.target k).linear q) by ring, abs_neg]
  hdirab := by
    simp only [LinearMap.neg_apply]
    exact neg_le_neg (Erdos634.Draft.ApexLegWord.hdirab_dirFun D.target k)
  hvert := fun j h => (wall_vert D.target k j h).symm

/-- Every ordered pair of distinct target vertices is the endpoint pair of a `Wall`. -/
theorem exists_wall (D : Dissection N) (u v : Fin 3) (huv : u ≠ v) :
    ∃ w : Wall D, w.a = D.target.pts u ∧ w.b = D.target.pts v := by
  have h : v = u + 1 ∨ u = v + 1 := by revert huv; revert v; revert u; decide
  rcases h with rfl | rfl
  · exact ⟨Wall.fwd D u, rfl, rfl⟩
  · exact ⟨Wall.bwd D v, rfl, rfl⟩

namespace Wall

variable {D : Dissection N} (w : Wall D)

theorem dir_lt : w.dir w.a < w.dir w.b := by
  have h := w.hiso w.a w.b (w.hline _ (left_mem_segment ℝ _ _)) (w.hline _ (right_mem_segment ℝ _ _))
  have hp : 0 < dist w.a w.b := dist_pos.mpr w.hab
  rw [h] at hp
  rcases lt_or_eq_of_le w.hdirab with h1 | h1
  · exact h1
  · rw [h1] at hp; simp at hp

theorem hthird : ∀ p ∈ wallList D w.g 0, w.g ((D.tile p.1).pts (p.2 + 2)) < 0 :=
  hthird_general D w.g 0 w.hne w.hwall

end Wall

/-- The chain of tile edges along a wall, in order (the output of `WallEndpoints.chain_endpoints`). -/
structure IsChain {D : Dissection N} (w : Wall D) (E : ℕ → Fin N × Fin 3) (n : ℕ) : Prop where
  n_eq : n = (wallList D w.g 0).length
  n_pos : 0 < n
  west0 : edgeWest D w.dir (E 0) = w.a
  east_last : edgeEast D w.dir (E (n - 1)) = w.b
  junc : ∀ m, m + 1 < n → edgeEast D w.dir (E m) = edgeWest D w.dir (E (m + 1))
  mem : ∀ m, m < n → E m ∈ wallList D w.g 0
  inj : ∀ m1 m2, m1 < n → m2 < n → E m1 = E m2 → m1 = m2
  lb : ∀ m, 0 < m → m < n → w.dir w.a < edgePos D w.dir (E m)
  ub : ∀ m, m + 1 < n → edgeEnd D w.dir (E m) < w.dir w.b
  nondeg : ∀ m, m < n → edgePos D w.dir (E m) < edgeEnd D w.dir (E m)
  surj : ∀ x ∈ wallList D w.g 0, ∃ i < n, E i = x

theorem Wall.exists_chain {D : Dissection N} (w : Wall D) (hN : 0 < N) :
    ∃ (E : ℕ → Fin N × Fin 3) (n : ℕ), IsChain w E n := by
  obtain ⟨E, n, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    chain_endpoints hN D w.g 0 w.dir w.hker w.hwall w.a w.b w.hab w.hdirab w.hbase w.hline
      w.hface w.hthird
  exact ⟨E, n, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩⟩

namespace IsChain

variable {D : Dissection N} {w : Wall D} {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain w E n)
include C

theorem edgePos_next {m : ℕ} (hm : m + 1 < n) :
    edgePos D w.dir (E (m + 1)) = edgeEnd D w.dir (E m) := by
  have := congrArg w.dir (C.junc m hm)
  rw [dir_edgeEast, dir_edgeWest] at this
  exact this.symm

theorem pos_mono : ∀ d m, m + d + 1 < n → edgePos D w.dir (E m) < edgePos D w.dir (E (m + d + 1)) := by
  intro d
  induction d with
  | zero =>
    intro m hm
    rw [show m + 0 + 1 = m + 1 from rfl, C.edgePos_next hm]
    exact C.nondeg m (by omega)
  | succ d ih =>
    intro m hm
    have h1 := ih m (by omega)
    have h2 : edgePos D w.dir (E (m + d + 1 + 1)) = edgeEnd D w.dir (E (m + d + 1)) :=
      C.edgePos_next (by omega)
    have h3 := C.nondeg (m + d + 1) (by omega)
    rw [show m + (d + 1) + 1 = m + d + 1 + 1 by ring, h2]
    linarith

theorem pos_lt {m m' : ℕ} (h : m < m') (h' : m' < n) :
    edgePos D w.dir (E m) < edgePos D w.dir (E m') := by
  obtain ⟨d, rfl⟩ : ∃ d, m' = m + d + 1 := ⟨m' - m - 1, by omega⟩
  exact C.pos_mono d m h'

/-- A wall edge is determined by its west position. -/
theorem unique_by_pos {p : Fin N × Fin 3} (hp : p ∈ wallList D w.g 0) {m : ℕ} (hm : m < n)
    (h : edgePos D w.dir p = edgePos D w.dir (E m)) : p = E m := by
  obtain ⟨m', hm', rfl⟩ := C.surj p hp
  rcases lt_trichotomy m' m with h1 | h1 | h1
  · have := C.pos_lt h1 hm; linarith
  · rw [h1]
  · have := C.pos_lt h1 hm'; linarith

theorem dist_eq {m : ℕ} (hm : m < n) :
    dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1))
      = edgeEnd D w.dir (E m) - edgePos D w.dir (E m) := by
  have hwm := (mem_wallList D w.g 0 (E m)).mp (C.mem m hm)
  rw [w.hiso _ _ hwm.1 hwm.2]
  show |w.dir ((D.tile (E m).1).pts (E m).2) - w.dir ((D.tile (E m).1).pts ((E m).2 + 1))|
    = max (w.dir ((D.tile (E m).1).pts (E m).2)) (w.dir ((D.tile (E m).1).pts ((E m).2 + 1)))
      - min (w.dir ((D.tile (E m).1).pts (E m).2)) (w.dir ((D.tile (E m).1).pts ((E m).2 + 1)))
  rcases le_total (w.dir ((D.tile (E m).1).pts (E m).2))
      (w.dir ((D.tile (E m).1).pts ((E m).2 + 1))) with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]

/-- The telescoping length sum. -/
theorem sum_len :
    ∑ m ∈ Finset.range n, (edgeEnd D w.dir (E m) - edgePos D w.dir (E m))
      = w.dir w.b - w.dir w.a := by
  have key : ∀ j, j < n → ∑ m ∈ Finset.range (j + 1), (edgeEnd D w.dir (E m) - edgePos D w.dir (E m))
      = edgeEnd D w.dir (E j) - edgePos D w.dir (E 0) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [Finset.sum_range_succ, ih (by omega), C.edgePos_next hj]; ring
  have h := key (n - 1) (by have := C.n_pos; omega)
  rw [show n - 1 + 1 = n by have := C.n_pos; omega] at h
  rw [h, ← dir_edgeEast, C.east_last, ← dir_edgeWest, C.west0]

/-- The junction point after the `m`-th chain edge. -/
theorem junction_dir {m : ℕ} (hm : m + 1 < n) :
    w.dir w.a < w.dir (edgeEast D w.dir (E m)) ∧ w.dir (edgeEast D w.dir (E m)) < w.dir w.b := by
  rw [dir_edgeEast]
  refine ⟨?_, C.ub m hm⟩
  rw [← C.edgePos_next hm]
  exact C.lb (m + 1) (by omega) hm

theorem edgeEast_on_wall (hN : True) {m : ℕ} (hm : m < n) : w.g (edgeEast D w.dir (E m)) = 0 := by
  have hwm := (mem_wallList D w.g 0 (E m)).mp (C.mem m hm)
  unfold edgeEast
  split_ifs
  · exact hwm.2
  · exact hwm.1

theorem edgeWest_on_wall {m : ℕ} (hm : m < n) : w.g (edgeWest D w.dir (E m)) = 0 := by
  have hwm := (mem_wallList D w.g 0 (E m)).mp (C.mem m hm)
  unfold edgeWest
  split_ifs
  · exact hwm.1
  · exact hwm.2

/-- A junction is a boundary point of the target that is not a target vertex. -/
theorem junction_boundary {m : ℕ} (hm : m + 1 < n) :
    edgeEast D w.dir (E m) ∈ frontier D.target.carrier ∧
      edgeEast D w.dir (E m) ∉ Set.range D.target.pts := by
  have h0 := C.edgeEast_on_wall trivial (by omega : m < n)
  have hdir := C.junction_dir hm
  have hcar : edgeEast D w.dir (E m) ∈ D.target.carrier := by
    have hwm := (mem_wallList D w.g 0 (E m)).mp (C.mem m (by omega))
    have : edgeEast D w.dir (E m) ∈ (D.tile (E m).1).carrier := by
      unfold edgeEast; split_ifs
      · exact subset_convexHull ℝ _ (Set.mem_range_self _)
      · exact subset_convexHull ℝ _ (Set.mem_range_self _)
    exact tile_subset_target D _ this
  refine ⟨w.hbase (w.hface _ hcar h0), ?_⟩
  rintro ⟨j, hj⟩
  have hjg : w.g (D.target.pts j) = 0 := by rw [hj]; exact h0
  rcases w.hvert j hjg with h | h
  · have := hdir.1; rw [← hj, h] at this; exact lt_irrefl _ this
  · have := hdir.2; rw [← hj, h] at this; exact lt_irrefl _ this

/-- Distinct chain indices carry distinct tiles. -/
theorem tile_ne {m m' : ℕ} (hm : m < n) (hm' : m' < n) (hne : m ≠ m') : (E m).1 ≠ (E m').1 := by
  intro h1
  have hE : (E m).2 ≠ (E m').2 := by
    intro h2
    exact hne (C.inj m m' hm hm' (Prod.ext h1 h2))
  have hwm := (mem_wallList D w.g 0 (E m)).mp (C.mem m hm)
  have hwm' := (mem_wallList D w.g 0 (E m')).mp (C.mem m' hm')
  have hth := w.hthird (E m) (C.mem m hm)
  obtain ⟨q0, q1⟩ := hwm'
  rw [← h1] at q0 q1
  have hc : ∀ k k' : Fin 3, k ≠ k' → k' = k + 1 ∨ k' = k + 2 := by decide
  rcases hc _ _ hE with h | h
  · rw [h, show ∀ x : Fin 3, x + 1 + 1 = x + 2 from by decide] at q1
    linarith
  · rw [h] at q0
    linarith

end IsChain

end Erdos634.GLI

#print axioms Erdos634.GLI.Wall.exists_chain
#print axioms Erdos634.GLI.exists_wall
#print axioms Erdos634.GLI.IsChain.junction_boundary
#print axioms Erdos634.GLI.IsChain.tile_ne
#print axioms Erdos634.GLI.IsChain.sum_len
