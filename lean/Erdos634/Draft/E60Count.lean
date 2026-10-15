/-
Draft/E60Count.lean: the degree count: a tile with an angle `π/3` and an irrational angle that tiles an
equilateral triangle satisfies a relation `j a = p b + q c`.

`sixty_has_a_relation`: for a `CongruentDissection` with an equilateral target whose model has `Tri.SixtyData α a b c`
and `α ∉ ℚπ`, there are integers `j ≥ 1`, `p, q ≥ 0` with `j a = p b + q c` (`a` the side opposite `α`).

Prior work.  The statement is part of Laczkovich's theorem that such a tile has commensurable sides (M. Laczkovich,
Tilings of convex polygons with congruent triangles, Discrete Comput. Geom. 48 (2012), Theorem 3.3).  The proof
formalized here is the degree count of M. Beeson and Y. X. Zhang (Rationality of certain triangle tilings,
arXiv:2604.01314, Lemma 3.5, written there for the tile with an angle `2π/3`), transposed to the angle `π/3`.

The count.  Vertex figures `(#α, #β, #γ)` with `β = 2π/3 − α`, `γ = π/3` (`interior_fan`, and
`Pi3Tile.boundary_fan_real`, `Pi3Tile.corner_fan_real`): a target corner is `(0,0,1)`; a point on a target side or
strictly inside an edge of a tile is `(1,1,1)` or `(0,0,3)`; a full interior vertex is `(3,3,0)`, `(2,2,2)`,
`(1,1,4)` or `(0,0,6)`.

* Every tile has one corner of each kind, so `Σ_p (#γ(p) − #α(p)) = 0` over the vertex points (`sum_cnt`); the
  pointwise bound `pointwise` turns this into `3·|O| ≥ |corners| + 3·|T3|`, where `O` is the set of full vertices of
  type `(3,3,0)` or `(1,1,4)` and `T3` the set of interior points of type `(0,0,3)` with a tile through them.
* In the graph of mismatched `a`-edges (`E60Graph`, `E60Heads`): every point of `O` is the start of a mismatched
  edge (`odd_vertex_out`), every head of type `(1,1,1)` is too (`simple_head_out`), heads are pairwise distinct
  (`head_inj`), and a head that is not of type `(1,1,1)` is in `T3`.  Hence `|O| ≤ |T3|` (`graph_ineq`).
The two inequalities contradict each other.  No sorry, no native_decide.
-/
import Erdos634.Draft.E60Heads

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.E60Second Erdos634.Pi3Tile Erdos634.VertexFigureReal

namespace Erdos634.Draft.E60Graph

section count

variable {N : ℕ}

theorem cnt_one {D : Dissection N} {p : Plane} {θ : ℝ} (h : cnt D p θ = 1) :
    (∃ i, (D.tile i).localAngle p = θ) ∧
      ∀ i i', (D.tile i).localAngle p = θ → (D.tile i').localAngle p = θ → i = i' := by
  unfold cnt at h
  obtain ⟨i₀, h0⟩ := Finset.card_eq_one.mp h
  have hmem : ∀ i, (D.tile i).localAngle p = θ ↔ i = i₀ := by
    intro i
    have h1 : i ∈ ({i | (D.tile i).localAngle p = θ} : Finset (Fin N)) ↔ i ∈ ({i₀} : Finset (Fin N)) := by
      rw [h0]
    simpa using h1
  exact ⟨⟨i₀, (hmem i₀).mpr rfl⟩, fun i i' hi hi' => ((hmem i).mp hi).trans ((hmem i').mp hi').symm⟩

theorem cnt_zero {D : Dissection N} {p : Plane} {θ : ℝ} (h : cnt D p θ = 0) (i : Fin N) :
    (D.tile i).localAngle p ≠ θ := by
  unfold cnt at h
  intro hi
  have : i ∈ ({i | (D.tile i).localAngle p = θ} : Finset (Fin N)) := by simp [hi]
  rw [Finset.card_eq_zero.mp h] at this
  exact absurd this (Finset.notMem_empty i)

theorem cnt_pos {D : Dissection N} {p : Plane} {θ : ℝ} {i : Fin N} (h : (D.tile i).localAngle p = θ) :
    1 ≤ cnt D p θ := by
  unfold cnt
  exact Finset.card_pos.mpr ⟨i, by simp [h]⟩

theorem card_filter_or (D : Dissection N) (p : Plane) {θ₁ θ₂ : ℝ} (hne : θ₁ ≠ θ₂) :
    (Finset.univ.filter (fun i : Fin N => (D.tile i).localAngle p = θ₁ ∨
      (D.tile i).localAngle p = θ₂)).card = cnt D p θ₁ + cnt D p θ₂ := by
  unfold cnt
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro i _ h1 h2
  exact hne (h1.symm.trans h2)

theorem target_vertex_not_interior (T : Tri) (k : Fin 3) : T.pts k ∉ interior T.carrier := by
  intro h
  have h1 := T.localAngle_interior h
  have h2 := localAngle_vertex_bounds T k
  linarith [Real.pi_pos]

variable {D : CongruentDissection N} {α a b c : ℝ}

/-- the three angles of the model sit at three different vertices -/
theorem model_dist (hirr : Irr α) (hS : D.model.SixtyData α a b c) (k l : Fin 3)
    (h : cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
       = cornerAngle (D.model.pts (l + 1)) (D.model.pts l) (D.model.pts (l + 2))) : k = l := by
  obtain ⟨τ, h0, -, h1, -, h2, -⟩ := hS
  have h' : D.model.angleAt k = D.model.angleAt l := h
  obtain ⟨m, rfl⟩ := τ.surjective k
  obtain ⟨m', rfl⟩ := τ.surjective l
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  have hm' : m' = 0 ∨ m' = 1 ∨ m' = 2 := by fin_cases m' <;> simp
  rcases hm with rfl | rfl | rfl <;> rcases hm' with rfl | rfl | rfl
  · rfl
  · rw [h0, h1] at h'; exact absurd h' (d_ab hirr)
  · rw [h0, h2] at h'; exact absurd h' (d_ag hirr)
  · rw [h1, h0] at h'; exact absurd h'.symm (d_ab hirr)
  · rfl
  · rw [h1, h2] at h'; exact absurd h' (d_bg hirr)
  · rw [h2, h0] at h'; exact absurd h'.symm (d_ag hirr)
  · rw [h2, h1] at h'; exact absurd h'.symm (d_bg hirr)
  · rfl

/-- **The corner balance**: over the vertex points, the tiles presenting `α` number `N`, and so do the tiles
presenting `π/3`. -/
theorem sum_cnt (hirr : Irr α) (hS : D.model.SixtyData α a b c) :
    ∑ v ∈ cornerPts D.toDissection, cnt D.toDissection v α = N ∧
    ∑ v ∈ cornerPts D.toDissection, cnt D.toDissection v (Real.pi / 3) = N := by
  have hS' := hS
  obtain ⟨τ, h0, -, h1, -, h2, -⟩ := hS
  have hpi := Real.pi_pos
  have e0 : cornerAngle (D.model.pts (τ 0 + 1)) (D.model.pts (τ 0)) (D.model.pts (τ 0 + 2)) = α := h0
  have e2 : cornerAngle (D.model.pts (τ 2 + 1)) (D.model.pts (τ 2)) (D.model.pts (τ 2 + 2)) = Real.pi / 3 := h2
  constructor
  · have hb := congruentDissection_corner_balance D (model_dist hirr hS') (τ 0)
      (by rw [e0]; exact d_a0 hirr) (by rw [e0]; exact d_ap hirr)
      (by rw [e0]; exact fun e => hirr ⟨2, by push_cast; linarith⟩)
    rw [e0] at hb
    exact hb
  · have hb := congruentDissection_corner_balance D (model_dist hirr hS') (τ 2)
      (by rw [e2]; exact d_g0) (by rw [e2]; exact d_gp) (by rw [e2]; exact gamma_ne_two_pi)
    rw [e2] at hb
    exact hb

/-- **The figure at an interior vertex point.** -/
theorem interior_fan (hirr : Irr α) (hS : D.model.SixtyData α a b c) {p : Plane}
    (hp : p ∈ interior D.target.carrier) (hv : p ∈ cornerPts D.toDissection) :
    (cnt D.toDissection p Real.pi = 1 ∧
      ((cnt D.toDissection p α = 1 ∧ cnt D.toDissection p (2 * Real.pi / 3 - α) = 1 ∧
          cnt D.toDissection p (Real.pi / 3) = 1) ∨
       (cnt D.toDissection p α = 0 ∧ cnt D.toDissection p (2 * Real.pi / 3 - α) = 0 ∧
          cnt D.toDissection p (Real.pi / 3) = 3))) ∨
    (cnt D.toDissection p Real.pi = 0 ∧
      ((cnt D.toDissection p α = 3 ∧ cnt D.toDissection p (2 * Real.pi / 3 - α) = 3 ∧
          cnt D.toDissection p (Real.pi / 3) = 0) ∨
       (cnt D.toDissection p α = 2 ∧ cnt D.toDissection p (2 * Real.pi / 3 - α) = 2 ∧
          cnt D.toDissection p (Real.pi / 3) = 2) ∨
       (cnt D.toDissection p α = 1 ∧ cnt D.toDissection p (2 * Real.pi / 3 - α) = 1 ∧
          cnt D.toDissection p (Real.pi / 3) = 4) ∨
       (cnt D.toDissection p α = 0 ∧ cnt D.toDissection p (2 * Real.pi / 3 - α) = 0 ∧
          cnt D.toDissection p (Real.pi / 3) = 6))) := by
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hj
  have hjv := localAngle_vertex_bounds (D.tile j) m
  rw [hm] at hjv
  have hs := Erdos634.PinPlumbing.pin_angle_sum_interior D.toDissection hp
  have hpi := Real.pi_pos
  have hvals : ∀ i, (D.tile i).localAngle p
      ∈ ({α, 2 * Real.pi / 3 - α, Real.pi / 3, Real.pi, 0} : Finset ℝ) := by
    intro i
    rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) p with ⟨k, _, hval⟩ | h2 | hpi' | h0
    · have := corner_mem D hS i k
      rw [hval]
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto
    · exfalso
      have hij : i ≠ j := by
        intro h; rw [h] at h2; linarith [hjv.2]
      have h1 : ({i, j} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
      have h3 : ∑ m ∈ ({i, j} : Finset (Fin N)), (D.tile m).localAngle p
          ≤ ∑ m, (D.tile m).localAngle p :=
        Finset.sum_le_sum_of_subset_of_nonneg h1 (fun m _ _ => (D.tile m).localAngle_nonneg p)
      rw [Finset.sum_pair hij, h2, hs] at h3
      linarith [hjv.1]
    · rw [hpi']; simp
    · rw [h0]; simp
  have hc := cards_eq D.toDissection α _ _ (d_ab hirr) (d_ag hirr) (d_ap hirr) (d_a0 hirr)
    (d_bg hirr) (d_bp hirr) (d_b0 hirr) d_gp d_g0 d_p0 hvals hs
  have hc' : (cnt D.toDissection p α : ℝ) * α
      + (cnt D.toDissection p (2 * Real.pi / 3 - α) : ℝ) * (2 * Real.pi / 3 - α)
      + (cnt D.toDissection p (Real.pi / 3) : ℝ) * (Real.pi / 3)
      + (cnt D.toDissection p Real.pi : ℝ) * Real.pi = ((6 : ℕ) : ℝ) * (Real.pi / 3) := by
    rw [show ((6 : ℕ) : ℝ) * (Real.pi / 3) = 2 * Real.pi by push_cast; ring]
    exact hc
  obtain ⟨hxy, hsum⟩ := fan_eq hirr _ _ _ _ 6 hc'
  have hpos : 1 ≤ cnt D.toDissection p α + cnt D.toDissection p (2 * Real.pi / 3 - α)
      + cnt D.toDissection p (Real.pi / 3) := by
    have hjm := corner_mem D hS j m
    have hjl : (D.tile j).localAngle p
        = cornerAngle ((D.tile j).pts (m + 1)) ((D.tile j).pts m) ((D.tile j).pts (m + 2)) := by
      rw [← hm, Tri.localAngle_vertex]
    rw [← hjl] at hjm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjm
    rcases hjm with h | h | h
    · have := cnt_pos (D := D.toDissection) h
      omega
    · have := cnt_pos (D := D.toDissection) h
      omega
    · have := cnt_pos (D := D.toDissection) h
      omega
  omega

/-- a full interior vertex of type `(3,3,0)` or `(1,1,4)` -/
def IsO (D : CongruentDissection N) (α : ℝ) (p : Plane) : Prop :=
  p ∈ interior D.target.carrier ∧ cnt D.toDissection p Real.pi = 0 ∧
    Odd (cnt D.toDissection p (2 * Real.pi / 3 - α) + cnt D.toDissection p (Real.pi / 3))

/-- an interior point with a tile through it and three tiles presenting `π/3` -/
def IsT3 (D : CongruentDissection N) (p : Plane) : Prop :=
  p ∈ interior D.target.carrier ∧ cnt D.toDissection p Real.pi = 1 ∧
    cnt D.toDissection p (Real.pi / 3) = 3

/-- **The pointwise bound.** -/
theorem pointwise (hirr : Irr α) (hS : D.model.SixtyData α a b c)
    (hE : ∀ k, D.target.angleAt k = Real.pi / 3) {p : Plane} (hv : p ∈ cornerPts D.toDissection) :
    (if p ∈ Set.range D.target.pts then (1 : ℤ) else 0) + 3 * (if IsT3 D p then (1 : ℤ) else 0)
        - 3 * (if IsO D α p then (1 : ℤ) else 0)
      ≤ (cnt D.toDissection p (Real.pi / 3) : ℤ) - (cnt D.toDissection p α : ℤ) := by
  rcases cornerPts_trichotomy D.toDissection hv with ⟨k, rfl⟩ | ⟨hfr, hnv⟩ | hint
  · obtain ⟨h1, -, h3, -⟩ := corner_fan_real D hirr hS k (hE k)
    have hnint := target_vertex_not_interior D.target k
    rw [if_pos ⟨k, rfl⟩, if_neg (fun h => hnint h.1), if_neg (fun h => hnint h.1), h1, h3]
    norm_num
  · have hb := boundary_fan_real D hirr hS hfr hnv
    dsimp only at hb
    rw [if_neg hnv, if_neg (fun h => hfr.2 h.1), if_neg (fun h => hfr.2 h.1)]
    rcases hb with ⟨h1, -, h3, -⟩ | ⟨h1, -, h3, -⟩ | ⟨h1, -, h3, -⟩ <;> rw [h1, h3] <;> norm_num
  · have hnc : p ∉ Set.range D.target.pts := by
      rintro ⟨k, rfl⟩
      exact target_vertex_not_interior D.target k hint
    rw [if_neg hnc]
    rcases interior_fan hirr hS hint hv with ⟨hπ, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ |
      ⟨hπ, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
    · rw [if_neg (fun h : IsT3 D p => by have := h.2.2; omega),
        if_neg (fun h : IsO D α p => by have := h.2.1; omega), h1, h3]
      norm_num
    · have hT : IsT3 D p := ⟨hint, hπ, h3⟩
      rw [if_pos hT, if_neg (fun h : IsO D α p => by have := h.2.1; omega), h1, h3]
      norm_num
    · have hOo : IsO D α p := ⟨hint, hπ, by rw [h2, h3]; decide⟩
      rw [if_neg (fun h : IsT3 D p => by have := h.2.1; omega), if_pos hOo, h1, h3]
      norm_num
    · rw [if_neg (fun h : IsT3 D p => by have := h.2.1; omega),
        if_neg (fun h : IsO D α p => by have := h.2.2; rw [h2, h3] at this; exact absurd this (by decide)),
        h1, h3]
      norm_num
    · have hOo : IsO D α p := ⟨hint, hπ, by rw [h2, h3]; decide⟩
      rw [if_neg (fun h : IsT3 D p => by have := h.2.1; omega), if_pos hOo, h1, h3]
      norm_num
    · rw [if_neg (fun h : IsT3 D p => by have := h.2.1; omega),
        if_neg (fun h : IsO D α p => by have := h.2.2; rw [h2, h3] at this; exact absurd this (by decide)),
        h1, h3]
      norm_num

/-- **The graph inequality.**  Without a relation `j a = p b + q c`, the full vertices of type `(3,3,0)` or
`(1,1,4)` are at most as many as the interior points of type `(0,0,3)` with a tile through them. -/
theorem graph_ineq (hirr : Irr α) (hS : D.model.SixtyData α a b c)
    (hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c) :
    ((cornerPts D.toDissection).filter (IsO D α)).card ≤ ((cornerPts D.toDissection).filter (IsT3 D)).card := by
  obtain ⟨M, hMdef⟩ : ∃ M : Finset (DE N), M = Finset.univ.filter (Mis D a) := ⟨_, rfl⟩
  obtain ⟨Hd, hHd⟩ : ∃ Hd : Finset Plane,
      Hd = (cornerPts D.toDissection).filter (fun p => ∃ e, Mis D a e ∧ Head D a e p) := ⟨_, rfl⟩
  obtain ⟨Hs, hHs⟩ : ∃ Hs : Finset Plane,
      Hs = Hd.filter (fun p => cnt D.toDissection p (Real.pi / 3) = 1) := ⟨_, rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : Finset Plane, O = (cornerPts D.toDissection).filter (IsO D α) := ⟨_, rfl⟩
  obtain ⟨T3, hT3⟩ : ∃ T3 : Finset Plane, T3 = (cornerPts D.toDissection).filter (IsT3 D) := ⟨_, rfl⟩
  rw [← hO, ← hT3]
  have hmemM : ∀ e, e ∈ M ↔ Mis D a e := by
    intro e; rw [hMdef]; simp
  -- every head is a vertex point, interior, with a tile through it
  have hhead : ∀ p, p ∈ Hd → p ∈ cornerPts D.toDissection ∧ p ∈ interior D.target.carrier ∧
      1 ≤ cnt D.toDissection p Real.pi := by
    intro p hp
    rw [hHd] at hp
    obtain ⟨hpV, e, hM, hH⟩ := Finset.mem_filter.mp hp
    obtain ⟨hint, ⟨j, hj⟩, -⟩ := head_through hS hrel hM hH
    exact ⟨hpV, hint, cnt_pos hj⟩
  have h1 : M.card ≤ Hd.card := by
    refine Finset.card_le_card_of_forall_subsingleton (fun e p => Head D a e p) ?_ ?_
    · intro e he
      have hM := (hmemM e).mp he
      obtain ⟨H, hH⟩ := head_exists hS hrel hM
      obtain ⟨-, -, j, k, hk⟩ := head_through hS hrel hM hH
      refine ⟨H, ?_, hH⟩
      rw [hHd]
      exact Finset.mem_filter.mpr ⟨hk ▸ mem_cornerPts D.toDissection j k, e, hM, hH⟩
    · intro p _ e he e' he'
      obtain ⟨he1, he2⟩ := he
      obtain ⟨he1', he2'⟩ := he'
      exact head_inj hS hrel ((hmemM e).mp he1) ((hmemM e').mp he1') he2 he2'
  have h2 : (M.image (src D)).card ≤ M.card := Finset.card_image_le
  have h3 : O ∪ Hs ⊆ M.image (src D) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rw [hO] at hp
      obtain ⟨-, hint, hπ0, hodd⟩ := Finset.mem_filter.mp hp
      have hodd' : Odd ((Finset.univ.filter (fun i : Fin N =>
          (D.tile i).localAngle p = 2 * Real.pi / 3 - α ∨ (D.tile i).localAngle p = Real.pi / 3)).card) := by
        rw [card_filter_or D.toDissection p (d_bg hirr)]; exact hodd
      obtain ⟨e, hM, hsrc⟩ := odd_vertex_out hirr hS hrel hint (cnt_zero hπ0) hodd'
      exact Finset.mem_image.mpr ⟨e, (hmemM e).mpr hM, hsrc⟩
    · rw [hHs] at hp
      obtain ⟨hpHd, hγ1⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpV, hint, hπ1⟩ := hhead p hpHd
      rw [hHd] at hpHd
      obtain ⟨-, e, hM, hH⟩ := Finset.mem_filter.mp hpHd
      have hβ1 : cnt D.toDissection p (2 * Real.pi / 3 - α) = 1 := by
        rcases interior_fan hirr hS hint hpV with ⟨-, ⟨-, h, -⟩ | ⟨-, -, h⟩⟩ |
          ⟨hπ, -⟩
        · exact h
        · omega
        · omega
      obtain ⟨hβex, hβu⟩ := cnt_one hβ1
      obtain ⟨hγex, hγu⟩ := cnt_one hγ1
      obtain ⟨e₂, hM₂, hsrc₂⟩ := simple_head_out hirr hS hrel hM hH hβu hγu hβex hγex
      exact Finset.mem_image.mpr ⟨e₂, (hmemM e₂).mpr hM₂, hsrc₂⟩
  have h4 : Disjoint O Hs := by
    rw [Finset.disjoint_left]
    intro p hpO hpHs
    rw [hO] at hpO
    obtain ⟨-, -, hπ0, -⟩ := Finset.mem_filter.mp hpO
    rw [hHs] at hpHs
    obtain ⟨-, -, hπ1⟩ := hhead p (Finset.mem_filter.mp hpHs).1
    omega
  have h5 : (Hd.filter (fun p => ¬ cnt D.toDissection p (Real.pi / 3) = 1)) ⊆ T3 := by
    intro p hp
    obtain ⟨hpHd, hγ⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpV, hint, hπ1⟩ := hhead p hpHd
    rw [hT3]
    refine Finset.mem_filter.mpr ⟨hpV, hint, ?_⟩
    rcases interior_fan hirr hS hint hpV with ⟨hπ, ⟨-, -, h⟩ | ⟨-, -, h⟩⟩ | ⟨hπ, -⟩
    · exact absurd h hγ
    · exact ⟨hπ, h⟩
    · omega
  have h6 := Finset.card_filter_add_card_filter_not (s := Hd)
    (fun p => cnt D.toDissection p (Real.pi / 3) = 1)
  rw [← hHs] at h6
  have h7 := Finset.card_le_card h5
  have h8 := Finset.card_le_card h3
  rw [Finset.card_union_of_disjoint h4] at h8
  omega

/-- **Laczkovich's relation.**  A tile with an angle `π/3` and an irrational angle `α` that tiles an equilateral
triangle satisfies `j a = p b + q c` for some integers `j ≥ 1`, `p, q ≥ 0`, where `a` is the side opposite `α`,
`c` the side opposite `π/3`. -/
theorem sixty_has_a_relation (D : CongruentDissection N) {α a b c : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α a b c) (hE : ∀ k, D.target.angleAt k = Real.pi / 3) :
    ∃ j p q : ℕ, 0 < j ∧ (j : ℝ) * a = p * b + q * c := by
  by_contra hcon
  have hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c := by
    intro j p q hj h
    exact hcon ⟨j, p, q, hj, h⟩
  have hg := graph_ineq hirr hS hrel
  obtain ⟨hsα, hsγ⟩ := sum_cnt hirr hS
  have hsum := Finset.sum_le_sum (fun p (hv : p ∈ cornerPts D.toDissection) => pointwise hirr hS hE hv)
  have hR : ∑ p ∈ cornerPts D.toDissection,
      ((cnt D.toDissection p (Real.pi / 3) : ℤ) - (cnt D.toDissection p α : ℤ)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, hsα, hsγ]
    simp
  rw [hR, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_boole, Finset.sum_boole] at hsum
  -- a target corner is a vertex point
  have hC : 1 ≤ ((cornerPts D.toDissection).filter (fun p => p ∈ Set.range D.target.pts)).card := by
    obtain ⟨-, -, h3, -⟩ := corner_fan_real D hirr hS 0 (hE 0)
    obtain ⟨⟨i, hi⟩, -⟩ := cnt_one h3
    obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile i) hi d_g0 d_gp gamma_ne_two_pi
    exact Finset.card_pos.mpr ⟨D.target.pts 0, Finset.mem_filter.mpr
      ⟨hm ▸ mem_cornerPts D.toDissection i m, ⟨0, rfl⟩⟩⟩
  have hC' : (1 : ℤ) ≤ (((cornerPts D.toDissection).filter (fun p => p ∈ Set.range D.target.pts)).card : ℤ) := by
    exact_mod_cast hC
  have hg' : ((((cornerPts D.toDissection).filter (IsO D α)).card : ℕ) : ℤ)
      ≤ ((((cornerPts D.toDissection).filter (IsT3 D)).card : ℕ) : ℤ) := by exact_mod_cast hg
  linarith

end count

end Erdos634.Draft.E60Graph

#print axioms Erdos634.Draft.E60Graph.sixty_has_a_relation
