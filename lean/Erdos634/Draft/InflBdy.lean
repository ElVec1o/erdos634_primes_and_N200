import Erdos634.Draft.GLIWall
import Erdos634.Draft.S5PinA
import Erdos634.GammaTrapLt
import Erdos634.SideNoB
import Erdos634.ChainWalk
import Erdos634.CornerBaseEdgesReal
import Erdos634.EdgeType
import Erdos634.TileAt
import Erdos634.Inflation
import Erdos634.BADAngles
import Erdos634.Draft.WtoDeltaF

/-!
# The boundary of a dissection of the inflated tile

The statement concerns a dissection, into
congruent copies of the tile `(a, b, c) = (ef, f² − e², f²)`, of a triangle with the angles
`α, β, γ` of the tile whose side between the `α`-corner and the `β`-corner (its `c`-side) has
length `f·c = f³`: the tile inflated by `f`.  It is proved here for a real
`CongruentDissection`, with the ordered edge chains of `GLI.Wall`:

* `side_no_b` : the `c`-side carries no `b`-edge (general `γ`-trap `GammaTrapLt` for the
  `c`-edge, then `SideNoB.side_no_b_uncond`); its word satisfies `P·a + R·c = f·c` with `R ≥ 1`;
* `alpha_corner` : at the `α`-corner a single tile has a nonzero angle; it presents `α`, it lays
  `c` on the `c`-side and `b` on the `b`-side;
* `beta_corner` : at the `β`-corner a single tile has a nonzero angle; it presents `β`, and it lays
  either `c` on the `c`-side and `a` on the `a`-side (direct), or `a` on the `c`-side and `c` on
  the `a`-side (transverse);
* `inflbdy` : the three together.

Target vertex `k` is the `α`-corner, `k + 1` the `β`-corner, `k + 2` the `γ`-corner.  No
assumption is made at the `γ`-corner.  Standard axioms, no `sorry`.
-/

open scoped Classical
open Erdos634 Erdos634.Geometry Erdos634.TilePlacement Erdos634.Placement Erdos634.GLI
  Erdos634.BaseChain Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.SideWall
  Erdos634.Geometry.Dissection

namespace Erdos634.Draft.InflBdy

variable {N : ℕ}

/-- The length of the tile edge `p`. -/
noncomputable def len (D : CongruentDissection N) (p : Fin N × Fin 3) : ℝ :=
  dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1))

/-- The angles of the model tile, with the standing hypotheses of the base-`β` branch. -/
structure Ang (D : CongruentDissection N) (α β γ : ℝ) : Prop where
  hαβ : α ≠ β
  hαγ : α ≠ γ
  hαπ : α ≠ Real.pi
  hα0 : α ≠ 0
  hβγ : β ≠ γ
  hβπ : β ≠ Real.pi
  hβ0 : β ≠ 0
  hγπ : γ ≠ Real.pi
  hγ0 : γ ≠ 0
  hγdef : γ = 2 * α + β
  hrel : 3 * α + 2 * β = Real.pi
  hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi
  hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m'
  hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α
  hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β
  hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ

/-! ## Multisets of three -/

theorem ms3_rot (a b c : ℝ) : ({a, b, c} : Multiset ℝ) = {b, c, a} := by
  show a ::ₘ b ::ₘ {c} = b ::ₘ c ::ₘ {a}
  rw [Multiset.cons_swap]
  congr 1
  exact Multiset.pair_comm a c

theorem ms3_rot2 (a b c : ℝ) : ({a, b, c} : Multiset ℝ) = {c, a, b} :=
  (ms3_rot a b c).trans (ms3_rot b c a)

/-! ## A vertex of a tile -/

theorem sideOpp_ne_zero (T : Tri) (m : Fin 3) : sideOpp T m ≠ 0 := by
  have hne : T.pts (m + 1) ≠ T.pts (m + 2) := pts_ne T (by fin_cases m <;> decide)
  exact (dist_pos.mpr hne).ne'

/-- **The data of a vertex of a tile**: its angle is the model's angle at some vertex `m`, and its
two edges at the vertex have the lengths of the two model sides other than `sideOpp m`. -/
theorem vertex_data (D : CongruentDissection N) (i : Fin N) (j : Fin 3) :
    ∃ m : Fin 3,
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        = cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2)) ∧
      ((dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = sideOpp D.model (m + 1) ∧
        dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = sideOpp D.model (m + 2)) ∨
       (dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = sideOpp D.model (m + 2) ∧
        dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = sideOpp D.model (m + 1))) := by
  obtain ⟨m, hang, hside⟩ :=
    Erdos634.CornerBaseEdgesReal.congruent_opposite_side (D.tiles_congruent i).symm j
  refine ⟨m, hang, ?_⟩
  have hopp : dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = sideOpp D.model m := by
    rw [← hside]; rfl
  have hmulti := (D.tiles_congruent i).sideMultiset_eq
  have hshift := Tri.sideMultiset_shift (D.tile i) j
  have hmodel : ({dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
      dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ)
      = {sideOpp D.model (m + 1), sideOpp D.model m, sideOpp D.model (m + 2)} := by
    fin_cases m
    · show ({sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} : Multiset ℝ)
        = {sideOpp D.model 1, sideOpp D.model 0, sideOpp D.model 2}
      exact ms3_rot _ _ _
    · show ({sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} : Multiset ℝ)
        = {sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0}
      rfl
    · show ({sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} : Multiset ℝ)
        = {sideOpp D.model 0, sideOpp D.model 2, sideOpp D.model 1}
      exact ms3_rot2 _ _ _
  exact corner_tile_edges (D.tile i) j _ _ _ (sideOpp_ne_zero D.model m) hopp
    (by rw [hshift, hmulti, hmodel])

/-- The local angle of a tile at one of its vertices, by the model index of that vertex. -/
theorem localAngle_by_index {D : CongruentDissection N} {α β γ : ℝ} (A : Ang D α β γ)
    (i : Fin N) (j m : Fin 3)
    (hang : cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        = cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2))) :
    (m = 0 ∧ (D.tile i).localAngle ((D.tile i).pts j) = α) ∨
    (m = 1 ∧ (D.tile i).localAngle ((D.tile i).pts j) = β) ∨
    (m = 2 ∧ (D.tile i).localAngle ((D.tile i).pts j) = γ) := by
  rw [Tri.localAngle_vertex, hang]
  fin_cases m
  · exact Or.inl ⟨rfl, A.hα'⟩
  · exact Or.inr (Or.inl ⟨rfl, A.hβ'⟩)
  · exact Or.inr (Or.inr ⟨rfl, A.hγ'⟩)

/-! ## The corner counts -/

/-- A corner of angle `α` holds a single `α`: the solution of `pα + qβ + rγ + sπ = α`. -/
theorem alpha_corner_single {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = α) :
    p = 1 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((1 - 3 * (s : ℤ) : ℤ) : ℝ) * α + ((-2 * (s : ℤ) : ℤ) : ℝ) * β := by
    push_cast; linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The counts at an `α`-corner of the target.** -/
theorem alpha_corner_counts (D : CongruentDissection N) {α β γ : ℝ} (A : Ang D α β γ) (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem D α β γ A.hα' A.hβ' A.hγ' k i
  have h := corner_multiplicities D.toDissection α β γ A.hαβ A.hαγ A.hαπ A.hα0 A.hβγ A.hβπ A.hβ0
    A.hγπ A.hγ0 Real.pi_ne_zero k hvals
  rw [hcorner] at h
  exact alpha_corner_single A.hγdef A.hrel A.hirr _ _ _ _ h

/-- **The counts at a `β`-corner of the target.** -/
theorem beta_corner_counts (D : CongruentDissection N) {α β γ : ℝ} (A : Ang D α β γ) (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 :=
  congruentDissection_base_corner_counts D α β γ A.hαβ A.hαγ A.hαπ A.hα0 A.hβγ A.hβπ A.hβ0
    A.hγπ A.hγ0 Real.pi_ne_zero A.hγdef A.hrel A.hirr A.hα' A.hβ' A.hγ' k hcorner

theorem not_of_card_zero {p : Plane} {D : CongruentDissection N} {v : ℝ}
    (h : ({i | (D.tile i).localAngle p = v} : Finset (Fin N)).card = 0) (i : Fin N) :
    (D.tile i).localAngle p ≠ v := by
  intro heq
  have hmem : i ∈ ({j : Fin N | (D.tile j).localAngle p = v} : Finset (Fin N)) := by
    simpa using heq
  rw [Finset.card_eq_zero.mp h] at hmem
  exact absurd hmem (Finset.notMem_empty i)

theorem eq_of_card_one {p : Plane} {D : CongruentDissection N} {v : ℝ}
    (h : ({i | (D.tile i).localAngle p = v} : Finset (Fin N)).card = 1) {i i' : Fin N}
    (hi : (D.tile i).localAngle p = v) (hi' : (D.tile i').localAngle p = v) : i = i' := by
  obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp h
  have h1 : i ∈ ({j : Fin N | (D.tile j).localAngle p = v} : Finset (Fin N)) := by simpa using hi
  have h2 : i' ∈ ({j : Fin N | (D.tile j).localAngle p = v} : Finset (Fin N)) := by simpa using hi'
  rw [hi0] at h1 h2
  rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2]

/-! ## The ends of a wall chain -/

theorem fin3_add (x : Fin 3) : x + 1 + 2 = x := by fin_cases x <;> rfl

/-- **The first edge of a wall chain**: its tile has a vertex `j` at the start of the wall; the edge
joins `j` to another vertex `o` of the tile, which also lies on the wall. -/
theorem first_edge {D : Dissection N} {w : Wall D} {E : ℕ → Fin N × Fin 3} {n : ℕ}
    (C : IsChain w E n) :
    ∃ j o : Fin 3, (o = j + 1 ∨ o = j + 2) ∧ (D.tile (E 0).1).pts j = w.a ∧
      w.g ((D.tile (E 0).1).pts o) = 0 ∧
      dist ((D.tile (E 0).1).pts (E 0).2) ((D.tile (E 0).1).pts ((E 0).2 + 1))
        = dist ((D.tile (E 0).1).pts j) ((D.tile (E 0).1).pts o) := by
  have hwm := (mem_wallList D w.g 0 (E 0)).mp (C.mem 0 C.n_pos)
  have h := C.west0
  unfold edgeWest at h
  split_ifs at h
  · exact ⟨(E 0).2, (E 0).2 + 1, Or.inl rfl, h, hwm.2, rfl⟩
  · refine ⟨(E 0).2 + 1, (E 0).2, Or.inr (fin3_add _).symm, h, hwm.1, ?_⟩
    rw [dist_comm]

/-- **The last edge of a wall chain**, likewise at the end of the wall. -/
theorem last_edge {D : Dissection N} {w : Wall D} {E : ℕ → Fin N × Fin 3} {n : ℕ}
    (C : IsChain w E n) :
    ∃ j o : Fin 3, (o = j + 1 ∨ o = j + 2) ∧ (D.tile (E (n - 1)).1).pts j = w.b ∧
      w.g ((D.tile (E (n - 1)).1).pts o) = 0 ∧
      dist ((D.tile (E (n - 1)).1).pts (E (n - 1)).2) ((D.tile (E (n - 1)).1).pts ((E (n - 1)).2 + 1))
        = dist ((D.tile (E (n - 1)).1).pts j) ((D.tile (E (n - 1)).1).pts o) := by
  have hn : n - 1 < n := by have := C.n_pos; omega
  have hwm := (mem_wallList D w.g 0 (E (n - 1))).mp (C.mem (n - 1) hn)
  have h := C.east_last
  unfold edgeEast at h
  split_ifs at h
  · refine ⟨(E (n - 1)).2 + 1, (E (n - 1)).2, Or.inr (fin3_add _).symm, h, hwm.1, ?_⟩
    rw [dist_comm]
  · exact ⟨(E (n - 1)).2, (E (n - 1)).2 + 1, Or.inl rfl, h, hwm.2, rfl⟩

theorem fin3_other (k j : Fin 3) (hj : j ≠ k) : j = k + 2 ∨ j = k + 2 + 2 := by
  revert k j; decide

theorem fin3_other' (k j : Fin 3) (hj : j ≠ k + 1) : j = k + 2 ∨ j = k + 1 + 2 := by
  revert k j; decide

/-- A point on the walls of the sides `k` and `k + 2` of a triangle is the vertex `k`. -/
theorem two_walls (T : Tri) (k : Fin 3) {x : Plane} (h1 : wallFun T k x = 0)
    (h2 : wallFun T (k + 2) x = 0) : x = T.pts k := by
  have c1 : T.basis.coord (k + 2) x = 0 := by
    have : -(T.basis.coord (k + 2) x) = 0 := h1
    linarith
  have c2 : T.basis.coord (k + 2 + 2) x = 0 := by
    have : -(T.basis.coord (k + 2 + 2) x) = 0 := h2
    linarith
  apply Erdos634.Draft.S5Pin.eq_vertex_of_coords T x k
  intro j hj
  rcases fin3_other k j hj with rfl | rfl
  · exact c1
  · exact c2

/-- A point on the walls of the sides `k` and `k + 1` of a triangle is the vertex `k + 1`. -/
theorem two_walls' (T : Tri) (k : Fin 3) {x : Plane} (h1 : wallFun T k x = 0)
    (h2 : wallFun T (k + 1) x = 0) : x = T.pts (k + 1) := by
  have c1 : T.basis.coord (k + 2) x = 0 := by
    have : -(T.basis.coord (k + 2) x) = 0 := h1
    linarith
  have c2 : T.basis.coord (k + 1 + 2) x = 0 := by
    have : -(T.basis.coord (k + 1 + 2) x) = 0 := h2
    linarith
  apply Erdos634.Draft.S5Pin.eq_vertex_of_coords T x (k + 1)
  intro j hj
  rcases fin3_other' k j hj with rfl | rfl
  · exact c1
  · exact c2

/-! ## The word of a side -/

/-- The number of edges of length `x` in the chain `E 0, …, E (n-1)`. -/
noncomputable def cnt (D : CongruentDissection N) (E : ℕ → Fin N × Fin 3) (n : ℕ) (x : ℝ) : ℕ :=
  ((Finset.range n).filter (fun m => len D (E m) = x)).card

theorem len_cases (D : CongruentDissection N) (p : Fin N × Fin 3) :
    len D p = sideOpp D.model 0 ∨ len D p = sideOpp D.model 1 ∨ len D p = sideOpp D.model 2 := by
  obtain ⟨j, hj⟩ := exists_matching_side D p.1 p.2
  unfold len; rw [hj]
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem cnt_pos {D : CongruentDissection N} {E : ℕ → Fin N × Fin 3} {n : ℕ} {x : ℝ} {m : ℕ}
    (hm : m < n) (h : len D (E m) = x) : 1 ≤ cnt D E n x :=
  Finset.card_pos.mpr ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, h⟩⟩

theorem ne_of_cnt_zero {D : CongruentDissection N} {E : ℕ → Fin N × Fin 3} {n : ℕ} {x : ℝ}
    (h0 : cnt D E n x = 0) {m : ℕ} (hm : m < n) : len D (E m) ≠ x := by
  intro h
  have := cnt_pos hm h
  omega

/-- **The walk equation of a side**: the length of the side is the sum of the lengths of the edges
of its chain, counted by type. -/
theorem chain_walk_eq (D : CongruentDissection N) {α β γ : ℝ} (A : Ang D α β γ)
    {w : Wall D.toDissection} {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain w E n) :
    dist w.a w.b = cnt D E n (sideOpp D.model 0) * sideOpp D.model 0
      + cnt D E n (sideOpp D.model 1) * sideOpp D.model 1
      + cnt D E n (sideOpp D.model 2) * sideOpp D.model 2 := by
  set L : ℕ → ℝ := fun m => edgePos D.toDissection w.dir (E m) with hL
  set R : ℕ → ℝ := fun m => edgeEnd D.toDissection w.dir (E m) with hR
  have hRL : ∀ m, m < n → R m - L m = len D (E m) := fun m hm => (C.dist_eq hm).symm
  have hAB := A.hscalene 0 1 (by decide)
  have hAC := A.hscalene 0 2 (by decide)
  have hBC := A.hscalene 1 2 (by decide)
  have hcw := Erdos634.ChainWalk.chain_walk n C.n_pos L R (sideOpp D.model 0) (sideOpp D.model 1)
    (sideOpp D.model 2) hAB hAC hBC
    (fun j hj => (C.edgePos_next hj).symm)
    (fun m hm => by
      rw [Finset.mem_range] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [hRL m hm]; exact len_cases D (E m))
  have hfilt : ∀ x : ℝ, ((Finset.range n).filter (fun j => R j - L j = x)).card = cnt D E n x := by
    intro x
    unfold cnt
    congr 1
    apply Finset.filter_congr
    intro m hm
    rw [hRL m (Finset.mem_range.mp hm)]
  rw [hfilt, hfilt, hfilt] at hcw
  have hRb : R (n - 1) = w.dir w.b := by
    show edgeEnd D.toDissection w.dir (E (n - 1)) = w.dir w.b
    rw [← dir_edgeEast, C.east_last]
  have hL0 : L 0 = w.dir w.a := by
    show edgePos D.toDissection w.dir (E 0) = w.dir w.a
    rw [← dir_edgeWest, C.west0]
  have hdist : dist w.a w.b = w.dir w.b - w.dir w.a := by
    rw [w.hiso w.a w.b (w.hline _ (left_mem_segment ℝ _ _)) (w.hline _ (right_mem_segment ℝ _ _))]
    rw [abs_of_nonpos (by linarith [w.dir_lt])]; ring
  rw [hdist, ← hRb, ← hL0]
  exact hcw

/-! ## The `c`-side carries no `b`-edge -/

/-- **The side between two corners smaller than `γ`, of length `f·c = f³`, carries no `b`-edge**:
every edge of its chain has length `a` or `c`, and the numbers `P`, `R` of the two satisfy
`P·a + R·c = f·c` with `R ≥ 1`. -/
theorem side_no_b (D : CongruentDissection N) {α β γ : ℝ} (A : Ang D α β γ) (k : Fin 3)
    (hc1 : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) < γ)
    (hc2 : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) < γ)
    {e f : ℕ} (hco : Nat.Coprime e f) (hef : e < f)
    (hA : sideOpp D.model 0 = (e : ℝ) * f) (hB : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hC : sideOpp D.model 2 = (f : ℝ) ^ 2)
    (hLen : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3)
    {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain (Wall.fwd D.toDissection k) E n) :
    (∀ m, m < n → len D (E m) = sideOpp D.model 0 ∨ len D (E m) = sideOpp D.model 2) ∧
    1 ≤ cnt D E n (sideOpp D.model 2) ∧
    cnt D E n (sideOpp D.model 0) * (e * f) + cnt D E n (sideOpp D.model 2) * (f * f)
      = f * f * f := by
  have hN : 0 < N := D.toDissection.pos
  have heq0 := chain_walk_eq D A C
  have heq : (f : ℝ) ^ 3 = cnt D E n (sideOpp D.model 0) * sideOpp D.model 0
      + cnt D E n (sideOpp D.model 1) * sideOpp D.model 1
      + cnt D E n (sideOpp D.model 2) * sideOpp D.model 2 := by
    rw [← hLen]; exact heq0
  set w := Wall.fwd D.toDissection k with hw
  obtain ⟨p0, hp0, hp0len⟩ := congruentDissection_gammatrap_lt hN D α β γ A.hαβ A.hαγ A.hαπ A.hα0
    A.hβγ A.hβπ A.hβ0 A.hγπ A.hγ0 Real.pi_ne_zero A.hγdef A.hrel A.hirr A.hscalene A.hα' A.hβ' A.hγ'
    k w.dir w.hker w.hdirab w.hthird hc1 hc2
  have hR1 : 1 ≤ cnt D E n (sideOpp D.model 2) := by
    obtain ⟨ic, hic, hEic⟩ := C.surj p0 hp0
    refine cnt_pos hic ?_
    rw [hEic]; exact hp0len
  set Pc := cnt D E n (sideOpp D.model 0) with hPc
  set Qc := cnt D E n (sideOpp D.model 1) with hQc
  set Rc := cnt D E n (sideOpp D.model 2) with hRc
  have hee : e * e ≤ f * f := Nat.mul_le_mul hef.le hef.le
  set b : ℕ := f * f - e * e with hb
  have hbe : b + e * e = f * f := Nat.sub_add_cancel hee
  have hbR : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : ((b + e * e : ℕ) : ℝ) = ((f * f : ℕ) : ℝ) := by rw [hbe]
    push_cast at this; linarith
  have hwalk : Pc * (e * f) + Qc * b + Rc * (f * f) = f * f * f := by
    have h : ((Pc * (e * f) + Qc * b + Rc * (f * f) : ℕ) : ℝ) = ((f * f * f : ℕ) : ℝ) := by
      push_cast
      rw [hbR]
      rw [hA, hB, hC] at heq
      linear_combination (-1 : ℝ) * heq
    exact_mod_cast h
  have hQ0 : Qc = 0 := Erdos634.SideNoB.side_no_b_uncond hco hef hbe hwalk hR1
  refine ⟨?_, hR1, ?_⟩
  · intro m hm
    rcases len_cases D (E m) with h | h | h
    · exact Or.inl h
    · exact absurd h (ne_of_cnt_zero hQ0 hm)
    · exact Or.inr h
  · rw [hQ0] at hwalk; simpa using hwalk

/-! ## The tile at a corner -/

/-- A tile with a vertex at an `α`-corner of the target presents `α` there, and its two edges at
that vertex have lengths `b` and `c`. -/
theorem corner_tile_alpha (D : CongruentDissection N) {α β γ : ℝ} (A : Ang D α β γ) (k : Fin 3)
    (hcα : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α)
    (i : Fin N) (j : Fin 3) (hj : (D.tile i).pts j = D.target.pts k) :
    (D.tile i).localAngle (D.target.pts k) = α ∧
    ((dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = sideOpp D.model 1 ∧
      dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = sideOpp D.model 2) ∨
     (dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = sideOpp D.model 2 ∧
      dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = sideOpp D.model 1)) := by
  obtain ⟨hα1, hβ0, hγ0, -⟩ := alpha_corner_counts D A k hcα
  obtain ⟨m, hang, hedges⟩ := vertex_data D i j
  rcases localAngle_by_index A i j m hang with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [hj] at h
    exact ⟨h, hedges⟩
  · rw [hj] at h; exact absurd h (not_of_card_zero hβ0 i)
  · rw [hj] at h; exact absurd h (not_of_card_zero hγ0 i)

/-- A tile with a vertex at a `β`-corner of the target presents `β` there, and its two edges at
that vertex have lengths `c` and `a`. -/
theorem corner_tile_beta (D : CongruentDissection N) {α β γ : ℝ} (A : Ang D α β γ) (k : Fin 3)
    (hcβ : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β)
    (i : Fin N) (j : Fin 3) (hj : (D.tile i).pts j = D.target.pts k) :
    (D.tile i).localAngle (D.target.pts k) = β ∧
    ((dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = sideOpp D.model 2 ∧
      dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = sideOpp D.model 0) ∨
     (dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = sideOpp D.model 0 ∧
      dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = sideOpp D.model 2)) := by
  obtain ⟨hα0, hβ1, hγ0, -⟩ := beta_corner_counts D A k hcβ
  obtain ⟨m, hang, hedges⟩ := vertex_data D i j
  rcases localAngle_by_index A i j m hang with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [hj] at h; exact absurd h (not_of_card_zero hα0 i)
  · rw [hj] at h
    exact ⟨h, hedges⟩
  · rw [hj] at h; exact absurd h (not_of_card_zero hγ0 i)

/-- At a corner where exactly one tile presents the value `v` and none presents the three other
nonzero values, every tile with a nonzero angle there is that tile. -/
theorem single_tile (D : CongruentDissection N) {α β γ : ℝ} (A : Ang D α β γ) (k : Fin 3) {v : ℝ}
    (hv1 : ({i | (D.tile i).localAngle (D.target.pts k) = v} : Finset (Fin N)).card = 1)
    (hrest : ∀ u ∈ ({α, β, γ, Real.pi} : Finset ℝ), u ≠ v →
      ({i | (D.tile i).localAngle (D.target.pts k) = u} : Finset (Fin N)).card = 0)
    {i i' : Fin N} (hi : (D.tile i).localAngle (D.target.pts k) ≠ 0)
    (hi' : (D.tile i').localAngle (D.target.pts k) = v) : i = i' := by
  have hval := congruentDissection_localAngle_mem D α β γ A.hα' A.hβ' A.hγ' k i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hval
  have key : ∀ u ∈ ({α, β, γ, Real.pi} : Finset ℝ), (D.tile i).localAngle (D.target.pts k) = u →
      (D.tile i).localAngle (D.target.pts k) = v := by
    intro u hu hiu
    by_contra hne
    have huv : u ≠ v := fun h => hne (hiu.trans h)
    exact not_of_card_zero (hrest u hu huv) i hiu
  have hiv : (D.tile i).localAngle (D.target.pts k) = v := by
    rcases hval with h | h | h | h | h
    · exact key α (by simp) h
    · exact key β (by simp) h
    · exact key γ (by simp) h
    · exact key Real.pi (by simp) h
    · exact absurd h hi
  exact eq_of_card_one hv1 hiv hi'

/-! ## The two corners of the `c`-side -/

theorem fin3_ne (x : Fin 3) : x + 1 ≠ x ∧ x + 2 ≠ x ∧ x + 1 ≠ x + 2 := by
  revert x; decide

theorem fin3_add' (x : Fin 3) : x + 2 + 1 = x := by
  revert x; decide

theorem angles_lt {D : CongruentDissection N} {α β γ : ℝ} (A : Ang D α β γ) : α < γ ∧ β < γ := by
  have hαpos : 0 < α :=
    lt_of_le_of_ne (by rw [← A.hα']; exact EuclideanGeometry.angle_nonneg _ _ _) (Ne.symm A.hα0)
  have hβpos : 0 < β :=
    lt_of_le_of_ne (by rw [← A.hβ']; exact EuclideanGeometry.angle_nonneg _ _ _) (Ne.symm A.hβ0)
  constructor <;> rw [A.hγdef] <;> linarith

/-- **The `α`-corner.**  The first edge of the `c`-side and the first edge of the `b`-side at the
`α`-corner belong to one tile, the only tile with a nonzero angle at the corner; it presents `α`,
its edge on the `c`-side has length `c` and its edge on the `b`-side has length `b`. -/
theorem alpha_corner (D : CongruentDissection N) {α β γ : ℝ} (A : Ang D α β γ) (k : Fin 3)
    (hcα : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α)
    (hcβ : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = β)
    {e f : ℕ} (hco : Nat.Coprime e f) (hef : e < f)
    (hA : sideOpp D.model 0 = (e : ℝ) * f) (hB : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hC : sideOpp D.model 2 = (f : ℝ) ^ 2)
    (hLen : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3)
    {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain (Wall.fwd D.toDissection k) E n)
    {E' : ℕ → Fin N × Fin 3} {n' : ℕ} (C' : IsChain (Wall.bwd D.toDissection (k + 2)) E' n') :
    (D.tile (E 0).1).localAngle (D.target.pts k) = α ∧
    (∀ i, (D.tile i).localAngle (D.target.pts k) ≠ 0 → i = (E 0).1) ∧
    (E' 0).1 = (E 0).1 ∧
    len D (E 0) = sideOpp D.model 2 ∧ len D (E' 0) = sideOpp D.model 1 := by
  obtain ⟨hαγ, hβγ⟩ := angles_lt A
  obtain ⟨hnob, -⟩ := side_no_b D A k (by rw [hcα]; exact hαγ) (by rw [hcβ]; exact hβγ) hco hef
    hA hB hC hLen C
  obtain ⟨hα1, hβ0, hγ0, hπ0⟩ := alpha_corner_counts D A k hcα
  have hAB := A.hscalene 0 1 (by decide)
  have hBC := A.hscalene 1 2 (by decide)
  have h0 := hnob 0 C.n_pos
  -- the `c`-side
  obtain ⟨j, o, ho, hja, hgo, hlen⟩ := first_edge C
  have hja' : (D.tile (E 0).1).pts j = D.target.pts k := hja
  have hgo' : wallFun D.target k ((D.tile (E 0).1).pts o) = 0 := hgo
  obtain ⟨hang, hedges⟩ := corner_tile_alpha D A k hcα (E 0).1 j hja'
  have hlenE : len D (E 0) = dist ((D.tile (E 0).1).pts j) ((D.tile (E 0).1).pts o) := hlen
  -- the `b`-side
  obtain ⟨j2, o2, ho2, hja2, hgo2, hlen2⟩ := first_edge C'
  have hk3 : D.target.pts (k + 2 + 1) = D.target.pts k := by rw [fin3_add']
  have hja2' : (D.tile (E' 0).1).pts j2 = D.target.pts k := Eq.trans hja2 hk3
  have hgo2' : wallFun D.target (k + 2) ((D.tile (E' 0).1).pts o2) = 0 := hgo2
  obtain ⟨hang2, -⟩ := corner_tile_alpha D A k hcα (E' 0).1 j2 hja2'
  have hsame : (E' 0).1 = (E 0).1 := eq_of_card_one hα1 hang2 hang
  have hlenE' : len D (E' 0) = dist ((D.tile (E' 0).1).pts j2) ((D.tile (E' 0).1).pts o2) := hlen2
  rw [hsame] at hja2' hgo2' hlenE'
  have hj2 : j2 = j := (D.tile (E 0).1).indep.injective (hja2'.trans hja'.symm)
  subst hj2
  obtain ⟨hn1, hn2, hn12⟩ := fin3_ne j2
  have hoo : o2 ≠ o := by
    intro h
    rw [h] at hgo2'
    have hx := two_walls D.target k hgo' hgo2'
    have hoj : o = j2 := (D.tile (E 0).1).indep.injective (hx.trans hja'.symm)
    rcases ho with h1 | h1
    · exact hn1 (h1.symm.trans hoj)
    · exact hn2 (h1.symm.trans hoj)
  have hsingle : ∀ i, (D.tile i).localAngle (D.target.pts k) ≠ 0 → i = (E 0).1 := by
    intro i hi
    refine single_tile D A k hα1 ?_ hi hang
    intro u hu hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact hβ0
    · exact hγ0
    · exact hπ0
  refine ⟨hang, hsingle, hsame, ?_⟩
  rcases ho with rfl | rfl <;> rcases ho2 with rfl | rfl
  · exact absurd rfl hoo
  · -- `o = j+1`, `o2 = j+2`
    rw [dist_comm] at hlenE'
    rcases hedges with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      rw [hlenE, h1] at h0
      rcases h0 with h | h
      · exact hAB h.symm
      · exact hBC h
    · exact ⟨by rw [hlenE, h1], by rw [hlenE', h2]⟩
  · -- `o = j+2`, `o2 = j+1`
    rw [dist_comm] at hlenE
    rcases hedges with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by rw [hlenE, h2], by rw [hlenE', h1]⟩
    · exfalso
      rw [hlenE, h2] at h0
      rcases h0 with h | h
      · exact hAB h.symm
      · exact hBC h
  · exact absurd rfl hoo

/-- **The `β`-corner.**  The last edge of the `c`-side and the first edge of the `a`-side at the
`β`-corner belong to one tile, the only tile with a nonzero angle at the corner; it presents `β`,
and it lays either `c` on the `c`-side and `a` on the `a`-side, or `a` on the `c`-side and `c` on
the `a`-side. -/
theorem beta_corner (D : CongruentDissection N) {α β γ : ℝ} (A : Ang D α β γ) (k : Fin 3)
    (hcβ : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = β)
    {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain (Wall.fwd D.toDissection k) E n)
    {E'' : ℕ → Fin N × Fin 3} {n'' : ℕ} (C'' : IsChain (Wall.fwd D.toDissection (k + 1)) E'' n'') :
    (D.tile (E (n - 1)).1).localAngle (D.target.pts (k + 1)) = β ∧
    (∀ i, (D.tile i).localAngle (D.target.pts (k + 1)) ≠ 0 → i = (E (n - 1)).1) ∧
    (E'' 0).1 = (E (n - 1)).1 ∧
    ((len D (E (n - 1)) = sideOpp D.model 2 ∧ len D (E'' 0) = sideOpp D.model 0) ∨
     (len D (E (n - 1)) = sideOpp D.model 0 ∧ len D (E'' 0) = sideOpp D.model 2)) := by
  obtain ⟨hα0, hβ1, hγ0, hπ0⟩ := beta_corner_counts D A (k + 1) hcβ
  -- the `c`-side
  obtain ⟨j, o, ho, hjb, hgo, hlen⟩ := last_edge C
  have hjb' : (D.tile (E (n - 1)).1).pts j = D.target.pts (k + 1) := hjb
  have hgo' : wallFun D.target k ((D.tile (E (n - 1)).1).pts o) = 0 := hgo
  obtain ⟨hang, hedges⟩ := corner_tile_beta D A (k + 1) hcβ (E (n - 1)).1 j hjb'
  have hlenE : len D (E (n - 1))
      = dist ((D.tile (E (n - 1)).1).pts j) ((D.tile (E (n - 1)).1).pts o) := hlen
  -- the `a`-side
  obtain ⟨j2, o2, ho2, hja2, hgo2, hlen2⟩ := first_edge C''
  have hja2' : (D.tile (E'' 0).1).pts j2 = D.target.pts (k + 1) := hja2
  have hgo2' : wallFun D.target (k + 1) ((D.tile (E'' 0).1).pts o2) = 0 := hgo2
  obtain ⟨hang2, -⟩ := corner_tile_beta D A (k + 1) hcβ (E'' 0).1 j2 hja2'
  have hsame : (E'' 0).1 = (E (n - 1)).1 := eq_of_card_one hβ1 hang2 hang
  have hlenE' : len D (E'' 0) = dist ((D.tile (E'' 0).1).pts j2) ((D.tile (E'' 0).1).pts o2) := hlen2
  rw [hsame] at hja2' hgo2' hlenE'
  have hj2 : j2 = j := (D.tile (E (n - 1)).1).indep.injective (hja2'.trans hjb'.symm)
  subst hj2
  obtain ⟨hn1, hn2, hn12⟩ := fin3_ne j2
  have hoo : o2 ≠ o := by
    intro h
    rw [h] at hgo2'
    have hx := two_walls' D.target k hgo' hgo2'
    have hoj : o = j2 := (D.tile (E (n - 1)).1).indep.injective (hx.trans hjb'.symm)
    rcases ho with h1 | h1
    · exact hn1 (h1.symm.trans hoj)
    · exact hn2 (h1.symm.trans hoj)
  have hsingle : ∀ i, (D.tile i).localAngle (D.target.pts (k + 1)) ≠ 0 → i = (E (n - 1)).1 := by
    intro i hi
    refine single_tile D A (k + 1) hβ1 ?_ hi hang
    intro u hu hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hα0
    · exact absurd rfl hne
    · exact hγ0
    · exact hπ0
  refine ⟨hang, hsingle, hsame, ?_⟩
  rcases ho with rfl | rfl <;> rcases ho2 with rfl | rfl
  · exact absurd rfl hoo
  · rw [dist_comm] at hlenE'
    rcases hedges with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [hlenE, h1], by rw [hlenE', h2]⟩
    · exact Or.inr ⟨by rw [hlenE, h1], by rw [hlenE', h2]⟩
  · rw [dist_comm] at hlenE
    rcases hedges with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨by rw [hlenE, h2], by rw [hlenE', h1]⟩
    · exact Or.inl ⟨by rw [hlenE, h2], by rw [hlenE', h1]⟩
  · exact absurd rfl hoo

/-- **The conclusion of `prop:inflbdy`**, for the target vertices `k` (the `α`-corner), `k + 1`
(the `β`-corner), `k + 2`: there are ordered chains of the tile edges on the three sides such that

* at the `α`-corner one tile has a nonzero angle; it presents `α` and lays `c` on the `c`-side and
  `b` on the `b`-side;
* at the `β`-corner one tile has a nonzero angle; it presents `β` and lays `c` on the `c`-side and
  `a` on the `a`-side, or `a` on the `c`-side and `c` on the `a`-side;
* every edge on the `c`-side has length `a` or `c`, and with `q f` edges `a` and `R` edges `c`
  one has `R ≥ 1` and `q e + R = f`. -/
def Statement (D : CongruentDissection N) (k : Fin 3) (α β : ℝ) (e f : ℕ) : Prop :=
  ∃ (E : ℕ → Fin N × Fin 3) (n : ℕ) (E' : ℕ → Fin N × Fin 3) (n' : ℕ)
      (E'' : ℕ → Fin N × Fin 3) (n'' : ℕ),
      IsChain (Wall.fwd D.toDissection k) E n ∧
      IsChain (Wall.bwd D.toDissection (k + 2)) E' n' ∧
      IsChain (Wall.fwd D.toDissection (k + 1)) E'' n'' ∧
      -- the `α`-corner
      ((D.tile (E 0).1).localAngle (D.target.pts k) = α ∧
        (∀ i, (D.tile i).localAngle (D.target.pts k) ≠ 0 → i = (E 0).1) ∧
        (E' 0).1 = (E 0).1 ∧
        len D (E 0) = sideOpp D.model 2 ∧ len D (E' 0) = sideOpp D.model 1) ∧
      -- the `β`-corner
      ((D.tile (E (n - 1)).1).localAngle (D.target.pts (k + 1)) = β ∧
        (∀ i, (D.tile i).localAngle (D.target.pts (k + 1)) ≠ 0 → i = (E (n - 1)).1) ∧
        (E'' 0).1 = (E (n - 1)).1 ∧
        ((len D (E (n - 1)) = sideOpp D.model 2 ∧ len D (E'' 0) = sideOpp D.model 0) ∨
         (len D (E (n - 1)) = sideOpp D.model 0 ∧ len D (E'' 0) = sideOpp D.model 2))) ∧
      -- the word of the `c`-side
      (∀ m, m < n → len D (E m) = sideOpp D.model 0 ∨ len D (E m) = sideOpp D.model 2) ∧
      ∃ q : ℕ, cnt D E n (sideOpp D.model 0) = q * f ∧ 1 ≤ cnt D E n (sideOpp D.model 2) ∧
        q * e + cnt D E n (sideOpp D.model 2) = f

/-- **`prop:inflbdy`**, with the angles as hypotheses.  For a dissection, into copies of the tile
`(ef, f² − e², f²)`, of a triangle with the angles `α`, `β` at the vertices `k`, `k + 1` whose side
from `k` to `k + 1` has length `f³`.  Nothing is assumed at the third corner. -/
theorem inflbdy (D : CongruentDissection N) {α β γ : ℝ} (A : Ang D α β γ) (k : Fin 3)
    (hcα : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α)
    (hcβ : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = β)
    {e f : ℕ} (he : 1 ≤ e) (hco : Nat.Coprime e f) (hef : e < f)
    (hA : sideOpp D.model 0 = (e : ℝ) * f) (hB : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hC : sideOpp D.model 2 = (f : ℝ) ^ 2)
    (hLen : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3) :
    Statement D k α β e f := by
  have hN : 0 < N := D.toDissection.pos
  obtain ⟨E, n, C⟩ := (Wall.fwd D.toDissection k).exists_chain hN
  obtain ⟨E', n', C'⟩ := (Wall.bwd D.toDissection (k + 2)).exists_chain hN
  obtain ⟨E'', n'', C''⟩ := (Wall.fwd D.toDissection (k + 1)).exists_chain hN
  obtain ⟨hαγ, hβγ⟩ := angles_lt A
  obtain ⟨hnob, hR1, hwalk⟩ := side_no_b D A k (by rw [hcα]; exact hαγ)
    (by rw [hcβ]; exact hβγ) hco hef hA hB hC hLen C
  refine ⟨E, n, E', n', E'', n'', C, C', C'',
    alpha_corner D A k hcα hcβ hco hef hA hB hC hLen C C', beta_corner D A k hcβ C C'', hnob, ?_⟩
  have hw : cnt D E n (sideOpp D.model 0) * (e * f) + cnt D E n (sideOpp D.model 2) * f ^ 2
      = f * f ^ 2 := by
    have h3 : f * (f * f) = f * f * f := by ring
    rw [pow_two, h3]; exact hwalk
  obtain ⟨q, hq, hqe⟩ := Erdos634.Inflation.c_side_words_scale e f f _ _ he hef hco hw
  exact ⟨q, hq, hR1, hqe⟩

/-! ## From the side lengths alone -/

/-- **The angle hypotheses hold for every tile with sides `(ef, f² − e², f²)`**, `1 ≤ e < f`
coprime: the angles are those of the model at its vertices `0, 1, 2`. -/
theorem ang_of_sides (D : CongruentDissection N) {e f : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hco : Nat.Coprime e f)
    (hA : sideOpp D.model 0 = (e : ℝ) * f) (hB : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hC : sideOpp D.model 2 = (f : ℝ) ^ 2) :
    Ang D (cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
      (cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0))
      (cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)) := by
  have hl0 : D.model.oppLen ((Equiv.refl (Fin 3)) 0) = ((e : ℤ) : ℝ) * ((f : ℤ) : ℝ) := by
    rw [Int.cast_natCast, Int.cast_natCast]; exact hA
  have hl1 : D.model.oppLen ((Equiv.refl (Fin 3)) 1) = (((f : ℤ) : ℝ)) ^ 2 - (((e : ℤ) : ℝ)) ^ 2 := by
    rw [Int.cast_natCast, Int.cast_natCast]; exact hB
  have hl2 : D.model.oppLen ((Equiv.refl (Fin 3)) 2) = (((f : ℤ) : ℝ)) ^ 2 := by
    rw [Int.cast_natCast]; exact hC
  obtain ⟨-, hrel, hγ, hirr⟩ := Erdos634.BADL2.tile_angles D.model (Equiv.refl _) (e : ℤ) (f : ℤ)
    (by exact_mod_cast he) (by exact_mod_cast hef) hl0 hl1 hl2
  set α := cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) with hα
  set β := cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) with hβ
  set γ := cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) with hγ'
  have hrel' : 3 * α + 2 * β = Real.pi := hrel
  have hγ2 : γ = Real.pi - α - β := hγ
  have hirr' : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi := hirr
  have hγdef : γ = 2 * α + β := by linarith
  have rat : ∀ r : ℚ, α ≠ (r : ℝ) * Real.pi := fun r h => hirr' ⟨r, h⟩
  have hpi := Real.pi_pos
  -- the sides are pairwise distinct
  have hfe : (e : ℝ) < f := by exact_mod_cast hef
  have he0 : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have s02 : sideOpp D.model 0 ≠ sideOpp D.model 2 := by
    rw [hA, hC]; intro h; nlinarith
  have s12 : sideOpp D.model 1 ≠ sideOpp D.model 2 := by
    rw [hB, hC]; intro h; nlinarith
  have s01 : sideOpp D.model 0 ≠ sideOpp D.model 1 := by
    rw [hA, hB]; intro h
    have hnat : e * (e + f) = f * f := by
      have : ((e * (e + f) : ℕ) : ℝ) = ((f * f : ℕ) : ℝ) := by push_cast; nlinarith
      exact_mod_cast this
    have h1 : e ∣ f * f := ⟨e + f, hnat.symm⟩
    have h2 : e ∣ f := Nat.Coprime.dvd_of_dvd_mul_left hco h1
    have h3 : e ∣ Nat.gcd e f := Nat.dvd_gcd dvd_rfl h2
    rw [hco] at h3
    have he1 : e = 1 := Nat.dvd_one.mp h3
    subst he1
    nlinarith
  refine
    { hαβ := fun h => rat (1 / 5) (by push_cast; linarith)
      hαγ := fun h => rat 1 (by push_cast; linarith)
      hαπ := fun h => rat 1 (by push_cast; linarith)
      hα0 := fun h => rat 0 (by push_cast; linarith)
      hβγ := fun h => rat 0 (by push_cast; linarith)
      hβπ := fun h => rat (-1 / 3) (by push_cast; linarith)
      hβ0 := fun h => rat (1 / 3) (by push_cast; linarith)
      hγπ := fun h => rat 1 (by push_cast; linarith)
      hγ0 := fun h => rat (-1) (by push_cast; linarith)
      hγdef := hγdef
      hrel := hrel'
      hirr := hirr'
      hscalene := ?_
      hα' := rfl
      hβ' := rfl
      hγ' := rfl }
  intro m m' hmm
  fin_cases m <;> fin_cases m' <;>
    first
      | exact absurd rfl hmm
      | exact s01
      | exact s01.symm
      | exact s02
      | exact s02.symm
      | exact s12
      | exact s12.symm

/-- Equal side ratios give equal angles. -/
theorem cornerAngle_scaled (p q r p' q' r' : Plane) (t : ℝ) (ht : 0 < t)
    (h1 : dist p q = t * dist p' q') (h2 : dist r q = t * dist r' q')
    (h3 : dist p r = t * dist p' r') (hne1 : dist p' q' ≠ 0) (hne2 : dist r' q' ≠ 0) :
    cornerAngle p q r = cornerAngle p' q' r' := by
  have hmem : ∀ X Y Z : Plane, cornerAngle X Y Z ∈ Set.Icc (0 : ℝ) Real.pi := fun X Y Z =>
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  apply Real.injOn_cos (hmem _ _ _) (hmem _ _ _)
  rw [Erdos634.AngleThreshold.cos_of_sides p q r (by rw [h1]; positivity) (by rw [h2]; positivity),
    Erdos634.AngleThreshold.cos_of_sides p' q' r' hne1 hne2, h1, h2, h3]
  field_simp

/-- The corner angles of the inflated triangle are those of the tile. -/
theorem target_corners (D : CongruentDissection N) (k : Fin 3) {f : ℕ} (hf : 0 < f)
    (hT01 : dist (D.target.pts k) (D.target.pts (k + 1)) = f * sideOpp D.model 2)
    (hT12 : dist (D.target.pts (k + 1)) (D.target.pts (k + 2)) = f * sideOpp D.model 0)
    (hT20 : dist (D.target.pts (k + 2)) (D.target.pts k) = f * sideOpp D.model 1) :
    cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) ∧
    cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1)) (D.target.pts (k + 1 + 2))
      = cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) := by
  have hf0 : (0 : ℝ) < f := by exact_mod_cast hf
  have m0 := sideOpp_ne_zero D.model 0
  have m1 := sideOpp_ne_zero D.model 1
  have m2 := sideOpp_ne_zero D.model 2
  have d01 : dist (D.model.pts 0) (D.model.pts 1) = sideOpp D.model 2 := rfl
  have d12 : dist (D.model.pts 1) (D.model.pts 2) = sideOpp D.model 0 := rfl
  have d20 : dist (D.model.pts 2) (D.model.pts 0) = sideOpp D.model 1 := rfl
  have hk1 : k + 1 + 1 = k + 2 := by rw [add_assoc]; rfl
  have hk2 : k + 1 + 2 = k := fin3_add k
  constructor
  · refine cornerAngle_scaled _ _ _ _ _ _ (f : ℝ) hf0 ?_ ?_ ?_ ?_ ?_
    · rw [dist_comm, hT01, dist_comm (D.model.pts 1), d01]
    · rw [hT20, d20]
    · rw [hT12, d12]
    · rw [dist_comm, d01]; exact m2
    · rw [d20]; exact m1
  · rw [hk1, hk2]
    refine cornerAngle_scaled _ _ _ _ _ _ (f : ℝ) hf0 ?_ ?_ ?_ ?_ ?_
    · rw [dist_comm, hT12, dist_comm (D.model.pts 2), d12]
    · rw [hT01, d01]
    · rw [hT20, d20]
    · rw [dist_comm, d12]; exact m0
    · rw [d01]; exact m2

/-- **`prop:inflbdy`**, from the side lengths alone: the tile has sides `(ef, f² − e², f²)`, and the
target has sides `f·c`, `f·a`, `f·b` between its vertices `k, k+1`, then `k+1, k+2`, then
`k+2, k` (the tile inflated by `f`). -/
theorem inflbdy_of_sides (D : CongruentDissection N) (k : Fin 3)
    {e f : ℕ} (he : 1 ≤ e) (hco : Nat.Coprime e f) (hef : e < f)
    (hA : sideOpp D.model 0 = (e : ℝ) * f) (hB : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hC : sideOpp D.model 2 = (f : ℝ) ^ 2)
    (hT01 : dist (D.target.pts k) (D.target.pts (k + 1)) = f * sideOpp D.model 2)
    (hT12 : dist (D.target.pts (k + 1)) (D.target.pts (k + 2)) = f * sideOpp D.model 0)
    (hT20 : dist (D.target.pts (k + 2)) (D.target.pts k) = f * sideOpp D.model 1) :
    Statement D k (cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
      (cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)) e f := by
  have A := ang_of_sides D he hef hco hA hB hC
  obtain ⟨hcα, hcβ⟩ := target_corners D k (by omega) hT01 hT12 hT20
  have hLen : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3 := by
    rw [hT01, hC]; ring
  exact inflbdy D A k hcα hcβ he hco hef hA hB hC hLen

/-! ## The direct placement, and the table at `(1,3)` and `(3,7)` -/

/-- A real walk equation with natural side lengths is an equation between natural numbers. -/
theorem walk_nat {P Q R : ℕ} {sA sB sC : ℝ} {a b c t : ℕ} (hA : sA = a) (hB : sB = b) (hC : sC = c)
    (h : (t : ℝ) = P * sA + Q * sB + R * sC) : P * a + Q * b + R * c = t := by
  rw [hA, hB, hC] at h
  exact_mod_cast h.symm

theorem len_eq_dist_ends (D : CongruentDissection N) (dir : Plane →ₗ[ℝ] ℝ) (p : Fin N × Fin 3) :
    len D p = dist (edgeWest D.toDissection dir p) (edgeEast D.toDissection dir p) := by
  unfold len edgeWest edgeEast
  split_ifs
  · rfl
  · rw [dist_comm]

/-- **The direct placement.**  If the tile at the `β`-corner lays `c` on the `c`-side and `a` on the
`a`-side, then the `c`-side has at least two `c`-edges (its two end edges), and the `b`-side and
the `a`-side satisfy their walk equations with a first edge `b`, resp. `a`. -/
theorem direct_sides (D : CongruentDissection N) {α β γ : ℝ} (A : Ang D α β γ) (k : Fin 3)
    {f : ℕ} (hf : 2 ≤ f)
    (hT01 : dist (D.target.pts k) (D.target.pts (k + 1)) = f * sideOpp D.model 2)
    (hT12 : dist (D.target.pts (k + 1)) (D.target.pts (k + 2)) = f * sideOpp D.model 0)
    (hT20 : dist (D.target.pts (k + 2)) (D.target.pts k) = f * sideOpp D.model 1)
    {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain (Wall.fwd D.toDissection k) E n)
    {E' : ℕ → Fin N × Fin 3} {n' : ℕ} (C' : IsChain (Wall.bwd D.toDissection (k + 2)) E' n')
    {E'' : ℕ → Fin N × Fin 3} {n'' : ℕ} (C'' : IsChain (Wall.fwd D.toDissection (k + 1)) E'' n'')
    (hα : len D (E 0) = sideOpp D.model 2) (hαb : len D (E' 0) = sideOpp D.model 1)
    (hdir : len D (E (n - 1)) = sideOpp D.model 2 ∧ len D (E'' 0) = sideOpp D.model 0) :
    2 ≤ cnt D E n (sideOpp D.model 2) ∧
    (1 ≤ cnt D E' n' (sideOpp D.model 1) ∧
      (f : ℝ) * sideOpp D.model 1 = cnt D E' n' (sideOpp D.model 0) * sideOpp D.model 0
        + cnt D E' n' (sideOpp D.model 1) * sideOpp D.model 1
        + cnt D E' n' (sideOpp D.model 2) * sideOpp D.model 2) ∧
    (1 ≤ cnt D E'' n'' (sideOpp D.model 0) ∧
      (f : ℝ) * sideOpp D.model 0 = cnt D E'' n'' (sideOpp D.model 0) * sideOpp D.model 0
        + cnt D E'' n'' (sideOpp D.model 1) * sideOpp D.model 1
        + cnt D E'' n'' (sideOpp D.model 2) * sideOpp D.model 2) := by
  refine ⟨?_, ⟨cnt_pos C'.n_pos hαb, ?_⟩, ⟨cnt_pos C''.n_pos hdir.2, ?_⟩⟩
  · -- the two end edges are different edges
    have hn : n ≠ 1 := by
      intro h1
      subst h1
      have h := len_eq_dist_ends D (Wall.fwd D.toDissection k).dir (E 0)
      have he : edgeEast D.toDissection (Wall.fwd D.toDissection k).dir (E 0)
          = (Wall.fwd D.toDissection k).b := C.east_last
      rw [C.west0, he] at h
      have hab : dist (Wall.fwd D.toDissection k).a (Wall.fwd D.toDissection k).b
          = f * sideOpp D.model 2 := hT01
      rw [hab, hα] at h
      have hpos : 0 < sideOpp D.model 2 :=
        lt_of_le_of_ne dist_nonneg (Ne.symm (sideOpp_ne_zero D.model 2))
      have hf' : (2 : ℝ) ≤ f := by exact_mod_cast hf
      nlinarith
    have hn2 : 2 ≤ n := by have := C.n_pos; omega
    unfold cnt
    apply Finset.one_lt_card.mpr
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hα⟩, n - 1,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hdir.1⟩, by omega⟩
  · have h := chain_walk_eq D A C'
    have hab : dist (Wall.bwd D.toDissection (k + 2)).a (Wall.bwd D.toDissection (k + 2)).b
        = f * sideOpp D.model 1 := by
      show dist (D.target.pts (k + 2 + 1)) (D.target.pts (k + 2)) = _
      rw [fin3_add', dist_comm]; exact hT20
    rw [hab] at h; exact h
  · have h := chain_walk_eq D A C''
    have hab : dist (Wall.fwd D.toDissection (k + 1)).a (Wall.fwd D.toDissection (k + 1)).b
        = f * sideOpp D.model 0 := by
      show dist (D.target.pts (k + 1)) (D.target.pts (k + 1 + 1)) = _
      have hk1 : k + 1 + 1 = k + 2 := by rw [add_assoc]; rfl
      rw [hk1]; exact hT12
    rw [hab] at h; exact h

/-- **The table of `prop:inflbdy`**: at `(e, f) = (1, 3)` and `(3, 7)`, in the direct placement the
`a`-side consists of `a`-edges only, the `b`-side of `b`-edges only, and the `c`-side has either
no `a`-edge and `f` edges `c`, or `f` edges `a` and `f − e` edges `c`. -/
theorem direct_table (D : CongruentDissection N) (k : Fin 3) {e f : ℕ}
    (hnum : (e = 1 ∧ f = 3) ∨ (e = 3 ∧ f = 7))
    (hA : sideOpp D.model 0 = (e : ℝ) * f) (hB : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hC : sideOpp D.model 2 = (f : ℝ) ^ 2)
    (hT01 : dist (D.target.pts k) (D.target.pts (k + 1)) = f * sideOpp D.model 2)
    (hT12 : dist (D.target.pts (k + 1)) (D.target.pts (k + 2)) = f * sideOpp D.model 0)
    (hT20 : dist (D.target.pts (k + 2)) (D.target.pts k) = f * sideOpp D.model 1)
    {E : ℕ → Fin N × Fin 3} {n : ℕ} (C : IsChain (Wall.fwd D.toDissection k) E n)
    {E' : ℕ → Fin N × Fin 3} {n' : ℕ} (C' : IsChain (Wall.bwd D.toDissection (k + 2)) E' n')
    {E'' : ℕ → Fin N × Fin 3} {n'' : ℕ} (C'' : IsChain (Wall.fwd D.toDissection (k + 1)) E'' n'')
    (hα : len D (E 0) = sideOpp D.model 2) (hαb : len D (E' 0) = sideOpp D.model 1)
    (hdir : len D (E (n - 1)) = sideOpp D.model 2 ∧ len D (E'' 0) = sideOpp D.model 0) :
    (∀ m, m < n'' → len D (E'' m) = sideOpp D.model 0) ∧
    (∀ m, m < n' → len D (E' m) = sideOpp D.model 1) ∧
    ((cnt D E n (sideOpp D.model 0) = 0 ∧ cnt D E n (sideOpp D.model 2) = f) ∨
     (cnt D E n (sideOpp D.model 0) = f ∧ cnt D E n (sideOpp D.model 2) = f - e)) := by
  have he : 1 ≤ e := by rcases hnum with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hef : e < f := by rcases hnum with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hco : Nat.Coprime e f := by
    rcases hnum with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> decide
  have A := ang_of_sides D he hef hco hA hB hC
  obtain ⟨hcα, hcβ⟩ := target_corners D k (by omega) hT01 hT12 hT20
  obtain ⟨hαγ, hβγ⟩ := angles_lt A
  have hLen : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3 := by
    rw [hT01, hC]; ring
  obtain ⟨-, -, hwalk⟩ := side_no_b D A k (by rw [hcα]; exact hαγ) (by rw [hcβ]; exact hβγ)
    hco hef hA hB hC hLen C
  obtain ⟨hc2, ⟨hb1, hbeq⟩, ⟨ha1, haeq⟩⟩ := direct_sides D A k (by omega) hT01 hT12 hT20 C C' C''
    hα hαb hdir
  rcases hnum with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
  · -- (1, 3): a = 3, b = 8, c = 9
    have sA : sideOpp D.model 0 = ((3 : ℕ) : ℝ) := by rw [hA]; norm_num
    have sB : sideOpp D.model 1 = ((8 : ℕ) : ℝ) := by rw [hB]; norm_num
    have sC : sideOpp D.model 2 = ((9 : ℕ) : ℝ) := by rw [hC]; norm_num
    have hb24 : ((24 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) * sideOpp D.model 1 := by rw [sB]; norm_num
    have ha9 : ((9 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) * sideOpp D.model 0 := by rw [sA]; norm_num
    have hbN := walk_nat sA sB sC (hb24.trans hbeq)
    have haN := walk_nat sA sB sC (ha9.trans haeq)
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      have hQ : cnt D E'' n'' (sideOpp D.model 1) = 0 := by omega
      have hR : cnt D E'' n'' (sideOpp D.model 2) = 0 := by omega
      rcases len_cases D (E'' m) with h | h | h
      · exact h
      · exact absurd h (ne_of_cnt_zero hQ hm)
      · exact absurd h (ne_of_cnt_zero hR hm)
    · intro m hm
      have hP : cnt D E' n' (sideOpp D.model 0) = 0 := by omega
      have hR : cnt D E' n' (sideOpp D.model 2) = 0 := by omega
      rcases len_cases D (E' m) with h | h | h
      · exact absurd h (ne_of_cnt_zero hP hm)
      · exact h
      · exact absurd h (ne_of_cnt_zero hR hm)
    · omega
  · -- (3, 7): a = 21, b = 40, c = 49
    have sA : sideOpp D.model 0 = ((21 : ℕ) : ℝ) := by rw [hA]; norm_num
    have sB : sideOpp D.model 1 = ((40 : ℕ) : ℝ) := by rw [hB]; norm_num
    have sC : sideOpp D.model 2 = ((49 : ℕ) : ℝ) := by rw [hC]; norm_num
    have hb280 : ((280 : ℕ) : ℝ) = ((7 : ℕ) : ℝ) * sideOpp D.model 1 := by rw [sB]; norm_num
    have ha147 : ((147 : ℕ) : ℝ) = ((7 : ℕ) : ℝ) * sideOpp D.model 0 := by rw [sA]; norm_num
    have hbN := walk_nat sA sB sC (hb280.trans hbeq)
    have haN := walk_nat sA sB sC (ha147.trans haeq)
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      have hQ : cnt D E'' n'' (sideOpp D.model 1) = 0 := by omega
      have hR : cnt D E'' n'' (sideOpp D.model 2) = 0 := by omega
      rcases len_cases D (E'' m) with h | h | h
      · exact h
      · exact absurd h (ne_of_cnt_zero hQ hm)
      · exact absurd h (ne_of_cnt_zero hR hm)
    · intro m hm
      have hP : cnt D E' n' (sideOpp D.model 0) = 0 := by omega
      have hR : cnt D E' n' (sideOpp D.model 2) = 0 := by omega
      rcases len_cases D (E' m) with h | h | h
      · exact absurd h (ne_of_cnt_zero hP hm)
      · exact h
      · exact absurd h (ne_of_cnt_zero hR hm)
    · omega

/-- **The hypotheses are satisfiable**: for every tile `M` with sides `(ef, f² − e², f²)` the
standard subdivision of `M` inflated by `f` into `f²` copies (`WtoDeltaF.ladderCD`) is a dissection
to which `inflbdy_of_sides` applies, with `k = 0`. -/
theorem inflbdy_ladder (M : Tri) {e f : ℕ} (he : 1 ≤ e) (hco : Nat.Coprime e f) (hef : e < f)
    (hA : sideOpp M 0 = (e : ℝ) * f) (hB : sideOpp M 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hC : sideOpp M 2 = (f : ℝ) ^ 2) :
    Statement (Erdos634.Draft.WtoDeltaF.ladderCD M f (by omega)) 0
      (cornerAngle (M.pts 1) (M.pts 0) (M.pts 2)) (cornerAngle (M.pts 2) (M.pts 1) (M.pts 0))
      e f := by
  have hf : 0 < f := by omega
  exact inflbdy_of_sides (Erdos634.Draft.WtoDeltaF.ladderCD M f hf) 0 he hco hef hA hB hC
    (Erdos634.Draft.WtoDeltaF.big_d01 (M.pts 0) (M.pts 1) (M.pts 2)
      (Erdos634.Draft.WtoDeltaF.indep_eta M) f hf)
    (Erdos634.Draft.WtoDeltaF.big_d12 (M.pts 0) (M.pts 1) (M.pts 2)
      (Erdos634.Draft.WtoDeltaF.indep_eta M) f hf)
    (Erdos634.Draft.WtoDeltaF.big_d20 (M.pts 0) (M.pts 1) (M.pts 2)
      (Erdos634.Draft.WtoDeltaF.indep_eta M) f hf)

end Erdos634.Draft.InflBdy
