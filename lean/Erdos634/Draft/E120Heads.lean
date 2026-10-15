/-
Draft/E120Heads.lean -- the graph `Γ_a` of `Draft/E120Graph.lean`: in-degree at most one, and two out-degree lemmas.

MECHANICAL PORT of `Draft/E60Heads.lean` to the tile with an angle `2π/3` (`β = π/3 − α`, `γ = 2π/3`): the tiles
with an `a`-edge at a point are those presenting `β` or `γ` there, as for the `π/3` tile.

* `head_inj` (in-degree ≤ 1): two mismatched edges with the same head are equal.
* `simple_head_out`: if the head carries exactly one tile with the angle `π/3 − α` and one with `2π/3`, a mismatched
  edge starts at the head.
* `odd_vertex_out`: at an interior point through which no tile passes, if the number of tiles presenting `π/3 − α`
  or `2π/3` is odd (a center `(0,0,3)` or a `γ`-star `(4,4,1)`), a mismatched edge starts there. not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.E120Graph

open Erdos634.Geometry Erdos634.Draft.E60Second Erdos634.TwoPi3Tile
open Erdos634.Pi3Tile (Irr irr_split cards_eq cnt)

namespace Erdos634.Draft.E120Graph

/-- a finite set with a fixed-point-free "partner" relation whose partner of a partner is the element itself has
even cardinality -/
theorem even_card_of_matching {ι : Type*} [DecidableEq ι] (s : Finset ι) (R : ι → ι → Prop)
    (hex : ∀ x ∈ s, ∃ y ∈ s, R x y) (hne : ∀ x y, R x y → x ≠ y)
    (hback : ∀ x y z, R x y → R y z → z = x) : Even s.card := by
  classical
  choose! g hg using hex
  have hsum : ∑ _x ∈ s, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun x _ => g x) ?_ ?_ ?_ ?_
    · intro x _; decide
    · intro x hx _ h
      exact hne x (g x) (hg x hx).2 h.symm
    · intro x hx; exact (hg x hx).1
    · intro x hx
      exact hback x (g x) (g (g x)) (hg x hx).2 (hg (g x) (hg x hx).1).2
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hsum

theorem fin3_same : ∀ m k l k₂ l₂ : Fin 3, m ≠ k → m ≠ l → k ≠ l → m ≠ k₂ → m ≠ l₂ → k₂ ≠ l₂ →
    (k₂ = k ∧ l₂ = l) ∨ (k₂ = l ∧ l₂ = k) := by decide

/-- a point strictly inside two edges of a triangle: the same edge -/
theorem same_edge (T : Tri) {k l k₂ l₂ : Fin 3} (hkl : k ≠ l) (hkl₂ : k₂ ≠ l₂) {θ θ₂ : ℝ} (h0 : 0 < θ)
    (h1 : θ < 1) (h0' : 0 < θ₂) (h1' : θ₂ < 1)
    (h : T.pts k + θ • (T.pts l - T.pts k) = T.pts k₂ + θ₂ • (T.pts l₂ - T.pts k₂)) :
    (k₂ = k ∧ l₂ = l) ∨ (k₂ = l ∧ l₂ = k) := by
  obtain ⟨m, hmk, hml, hm0, hmpos⟩ := onEdge_of_edge T hkl h0 h1
  obtain ⟨m₂, hmk₂, hml₂, hm0₂, hmpos₂⟩ := onEdge_of_edge T hkl₂ h0' h1'
  rw [← h] at hm0₂ hmpos₂
  have hmm : m₂ = m := by
    by_contra hne
    have := hmpos₂ m (Ne.symm hne)
    rw [hm0] at this
    exact lt_irrefl 0 this
  rw [hmm] at hmk₂ hml₂
  exact fin3_same m k l k₂ l₂ hmk hml hkl hmk₂ hml₂ hkl₂

section heads

variable {N : ℕ} {D : CongruentDissection N}

/-- the tile `j` has an edge on the line `p + ℝ w` containing the points `p + t w` for small `t > 0` -/
def Covers (D : CongruentDissection N) (j : Fin N) (p w : Plane) : Prop :=
  ∃ k l : Fin 3, k ≠ l ∧ ∃ t₀ t₁ : ℝ, t₀ ≤ 0 ∧ 0 < t₁ ∧
    (D.tile j).pts k = p + t₀ • w ∧ (D.tile j).pts l = p + t₁ • w

/-- the tile `j` has an edge on the line `p + ℝ w` with `p` strictly inside -/
def Through (D : CongruentDissection N) (j : Fin N) (p w : Plane) : Prop :=
  ∃ k l : Fin 3, k ≠ l ∧ ∃ t₀ t₁ : ℝ, t₀ < 0 ∧ 0 < t₁ ∧
    (D.tile j).pts k = p + t₀ • w ∧ (D.tile j).pts l = p + t₁ • w

theorem Covers.pi {j : Fin N} {p w : Plane} (h : Covers D j p w) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → (D.tile j).localAngle (p + t • w) = Real.pi := by
  obtain ⟨k, l, hkl, t₀, t₁, ht₀, ht₁, hk, hl⟩ := h
  refine ⟨t₁, ht₁, ?_⟩
  intro t ht0 ht
  have hd : 0 < t₁ - t₀ := by linarith
  have hθ0 : 0 < (t - t₀) / (t₁ - t₀) := div_pos (by linarith) hd
  have hθ1 : (t - t₀) / (t₁ - t₀) < 1 := by rw [div_lt_one hd]; linarith
  have hmul : (t - t₀) / (t₁ - t₀) * (t₁ - t₀) = t - t₀ := by field_simp
  have key : p + t • w
      = (D.tile j).pts k + ((t - t₀) / (t₁ - t₀)) • ((D.tile j).pts l - (D.tile j).pts k) := by
    rw [hk, hl, show p + t₁ • w - (p + t₀ • w) = (t₁ - t₀) • w by module, smul_smul, hmul]
    module
  rw [key]
  exact localAngle_pi_on_edge (D.tile j) hkl hθ0 hθ1

/-- **At most two tiles along a ray.** -/
theorem no_three_covers {i₁ i₂ i₃ : Fin N} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) {p w : Plane}
    (h1 : Covers D i₁ p w) (h2 : Covers D i₂ p w) (h3 : Covers D i₃ p w) : False := by
  obtain ⟨ε₁, hε₁, hp1⟩ := h1.pi
  obtain ⟨ε₂, hε₂, hp2⟩ := h2.pi
  obtain ⟨ε₃, hε₃, hp3⟩ := h3.pi
  have hm : 0 < min ε₁ (min ε₂ ε₃) := lt_min hε₁ (lt_min hε₂ hε₃)
  have hm1 : min ε₁ (min ε₂ ε₃) ≤ ε₁ := min_le_left _ _
  have hm2 : min ε₁ (min ε₂ ε₃) ≤ ε₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm3 : min ε₁ (min ε₂ ε₃) ≤ ε₃ := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min ε₁ (min ε₂ ε₃) / 2 := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; linarith
  have e1 := hp1 t ht0 (by rw [ht]; linarith)
  have e2 := hp2 t ht0 (by rw [ht]; linarith)
  have e3 := hp3 t ht0 (by rw [ht]; linarith)
  have hint := interior_of_through_and_vertex D.toDissection h12 e1 (by rw [e2]; exact Real.pi_pos)
  exact Erdos634.PinPlumbing.at_most_two_through D.toDissection hint i₁ i₂ i₃ h12 h13 h23 e1 e2 e3

theorem EdgeAlong.covers {j : Fin N} {p w : Plane} {x : ℝ} (h : EdgeAlong D j p w x) : Covers D j p w := by
  obtain ⟨k, l, hkl, hk, ⟨s, hs, hE⟩, -⟩ := h
  refine ⟨k, l, hkl, 0, s, le_refl 0, hs, by rw [hk]; module, ?_⟩
  have : (D.tile j).pts l = (D.tile j).pts k + s • w := by rw [← hE]; abel
  rw [this, hk]

theorem EdgeAlong.angle {j : Fin N} {p w : Plane} {x : ℝ} (h : EdgeAlong D j p w x) :
    0 < (D.tile j).localAngle p ∧ (D.tile j).localAngle p < Real.pi := by
  obtain ⟨k, l, hkl, hk, -, -⟩ := h
  rw [← hk]; exact localAngle_vertex_bounds (D.tile j) k

/-- the same edge seen along a positive multiple of the direction -/
theorem EdgeAlong.rescale {j : Fin N} {p w w' : Plane} {x c : ℝ} (h : EdgeAlong D j p w' x) (hc : 0 < c)
    (hw : w' = c • w) : EdgeAlong D j p w x := by
  obtain ⟨k, l, hkl, hk, ⟨s, hs, hE⟩, hd⟩ := h
  exact ⟨k, l, hkl, hk, ⟨s * c, mul_pos hs hc, by rw [hE, hw, smul_smul]⟩, hd⟩

/-- **A tile has at most one edge from a vertex along a ray.** -/
theorem edgeAlong_unique {j : Fin N} {p w : Plane} {x x' : ℝ} (h : EdgeAlong D j p w x)
    (h' : EdgeAlong D j p w x') : x = x' := by
  obtain ⟨k, l, hkl, hk, ⟨s, hs, hE⟩, hd⟩ := h
  obtain ⟨k₂, l₂, hkl₂, hk₂, ⟨s₂, hs₂, hE₂⟩, hd₂⟩ := h'
  have hkk : k₂ = k := (D.tile j).indep.injective (hk₂.trans hk.symm)
  rw [hkk] at hkl₂ hE₂ hd₂
  by_cases hll : l₂ = l
  · rw [hll] at hd₂; exact hd.symm.trans hd₂
  · exfalso
    have h1 : (D.tile j).pts l₂
        = (D.tile j).pts k + (s₂ / s) • ((D.tile j).pts l - (D.tile j).pts k) := by
      have h2 : (D.tile j).pts l₂ = (D.tile j).pts k + s₂ • w := by rw [← hE₂]; abel
      rw [h2, hE, smul_smul, div_mul_cancel₀ _ hs.ne']
    have h3 := coord_on_edge (D.tile j) hkl (s₂ / s) l₂
    rw [← h1, if_neg hll, if_neg (Ne.symm hkl₂)] at h3
    have h4 : (D.tile j).basis.coord l₂ ((D.tile j).pts l₂) = 1 := (D.tile j).basis.coord_apply_eq l₂
    rw [h4] at h3
    norm_num at h3

theorem Through.covers {j : Fin N} {p w : Plane} (h : Through D j p w) : Covers D j p w := by
  obtain ⟨k, l, hkl, t₀, t₁, ht₀, ht₁, hk, hl⟩ := h
  exact ⟨k, l, hkl, t₀, t₁, ht₀.le, ht₁, hk, hl⟩

theorem Through.neg {j : Fin N} {p w : Plane} (h : Through D j p w) : Through D j p (-w) := by
  obtain ⟨k, l, hkl, t₀, t₁, ht₀, ht₁, hk, hl⟩ := h
  exact ⟨l, k, Ne.symm hkl, -t₁, -t₀, by linarith, by linarith, by rw [hl]; module, by rw [hk]; module⟩

/-- the position of `p` on the edge -/
theorem Through.param {j : Fin N} {p w : Plane} (h : Through D j p w) :
    ∃ k l : Fin 3, k ≠ l ∧ ∃ t₀ t₁ θ : ℝ, t₀ < 0 ∧ 0 < t₁ ∧ 0 < θ ∧ θ < 1 ∧
      (D.tile j).pts k = p + t₀ • w ∧ (D.tile j).pts l = p + t₁ • w ∧
      p = (D.tile j).pts k + θ • ((D.tile j).pts l - (D.tile j).pts k) := by
  obtain ⟨k, l, hkl, t₀, t₁, ht₀, ht₁, hk, hl⟩ := h
  have hd : 0 < t₁ - t₀ := by linarith
  have hθ0 : 0 < (-t₀) / (t₁ - t₀) := div_pos (by linarith) hd
  have hθ1 : (-t₀) / (t₁ - t₀) < 1 := by rw [div_lt_one hd]; linarith
  have hmul : (-t₀) / (t₁ - t₀) * (t₁ - t₀) = -t₀ := by field_simp
  refine ⟨k, l, hkl, t₀, t₁, (-t₀) / (t₁ - t₀), ht₀, ht₁, hθ0, hθ1, hk, hl, ?_⟩
  rw [hk, hl, show p + t₁ • w - (p + t₀ • w) = (t₁ - t₀) • w by module, smul_smul, hmul]
  module

theorem Through.pi {j : Fin N} {p w : Plane} (h : Through D j p w) : (D.tile j).localAngle p = Real.pi := by
  obtain ⟨k, l, hkl, t₀, t₁, θ, -, -, hθ0, hθ1, -, -, hp⟩ := h.param
  rw [hp]
  exact localAngle_pi_on_edge (D.tile j) hkl hθ0 hθ1

/-- **A tile passes through a point along one line only.** -/
theorem through_parallel {j : Fin N} {p w w' : Plane} {a : ℝ} (ha : 0 < a) (hw : ‖w‖ = a) (hw' : ‖w'‖ = a)
    (h : Through D j p w) (h' : Through D j p w') : w' = w ∨ w' = -w := by
  obtain ⟨k, l, hkl, t₀, t₁, θ, ht₀, ht₁, hθ0, hθ1, hk, hl, hp⟩ := h.param
  obtain ⟨k₂, l₂, hkl₂, u₀, u₁, θ₂, hu₀, hu₁, hθ0', hθ1', hk₂, hl₂, hp₂⟩ := h'.param
  have hd : 0 < t₁ - t₀ := by linarith
  have hd' : 0 < u₁ - u₀ := by linarith
  have a1 : (D.tile j).pts l - (D.tile j).pts k = (t₁ - t₀) • w := by rw [hk, hl]; module
  have a2 : (D.tile j).pts l₂ - (D.tile j).pts k₂ = (u₁ - u₀) • w' := by rw [hk₂, hl₂]; module
  have hn1 : ‖(t₁ - t₀) • w‖ = (t₁ - t₀) * a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd, hw]
  have hn2 : ‖(u₁ - u₀) • w'‖ = (u₁ - u₀) * a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd', hw']
  rcases same_edge (D.tile j) hkl hkl₂ hθ0 hθ1 hθ0' hθ1' (hp.symm.trans hp₂) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left
    rw [e1, e2, a1] at a2
    have h3 : t₁ - t₀ = u₁ - u₀ := by
      have h4 := congrArg norm a2
      rw [hn1, hn2] at h4
      exact mul_right_cancel₀ ha.ne' h4
    rw [h3] at a2
    exact (smul_right_injective Plane hd'.ne' a2).symm
  · right
    rw [e1, e2] at a2
    have a3 : (t₁ - t₀) • w = (u₁ - u₀) • (-w') := by
      rw [← a1, smul_neg, ← a2]; abel
    have h3 : t₁ - t₀ = u₁ - u₀ := by
      have h4 := congrArg norm a3
      rw [hn1, norm_smul, Real.norm_eq_abs, abs_of_pos hd', norm_neg, hw'] at h4
      exact mul_right_cancel₀ ha.ne' h4
    rw [h3] at a3
    have h5 : w = -w' := smul_right_injective Plane hd'.ne' a3
    rw [h5, neg_neg]

variable {α a b c : ℝ}

theorem beta_ne_two_pi (hirr : Irr α) : Real.pi / 3 - α ≠ 2 * Real.pi := fun e =>
  hirr ⟨-5 / 3, by push_cast; linarith⟩

theorem gamma_ne_two_pi : 2 * Real.pi / 3 ≠ 2 * Real.pi := by
  have := Real.pi_pos
  intro e; linarith

/-- a tile presenting `π/3 − α` or `2π/3` at `p` has an `a`-edge from `p` -/
theorem adart_of_angle (hirr : Irr α) (hS : D.model.TwoPiThreeData α a b c) {j : Fin N} {p : Plane}
    (h : (D.tile j).localAngle p = Real.pi / 3 - α ∨ (D.tile j).localAngle p = 2 * Real.pi / 3) :
    ∃ k l : Fin 3, k ≠ l ∧ (D.tile j).pts k = p ∧ dist ((D.tile j).pts k) ((D.tile j).pts l) = a := by
  obtain ⟨L⟩ := lab_exists D hS j
  rcases h with h | h
  · obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile j) h (d_b0 hirr) (d_bp hirr) (beta_ne_two_pi hirr)
    rw [← hm] at h
    rcases L.cases m with e | e | e
    · rw [e] at h; exact absurd (L.angA.symm.trans h) (d_ab hirr)
    · rw [e] at hm; exact ⟨L.vB, L.vC, L.hBC, hm, L.lenA⟩
    · rw [e] at h; exact absurd (h.symm.trans L.angC) (d_bg hirr)
  · obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile j) h d_g0 d_gp gamma_ne_two_pi
    rw [← hm] at h
    rcases L.cases m with e | e | e
    · rw [e] at h; exact absurd (L.angA.symm.trans h) (d_ag hirr)
    · rw [e] at h; exact absurd (L.angB.symm.trans h) (d_bg hirr)
    · rw [e] at hm; exact ⟨L.vC, L.vB, Ne.symm L.hBC, hm, by rw [dist_comm]; exact L.lenA⟩

/-- the start of an `a`-edge is a vertex of angle `π/3 − α` or `2π/3` -/
theorem angle_of_adart (hS : D.model.TwoPiThreeData α a b c) (hab : a ≠ b) (hac : a ≠ c) {j : Fin N}
    {k l : Fin 3} (hkl : k ≠ l) (h : dist ((D.tile j).pts k) ((D.tile j).pts l) = a) :
    (D.tile j).localAngle ((D.tile j).pts k) = Real.pi / 3 - α ∨
      (D.tile j).localAngle ((D.tile j).pts k) = 2 * Real.pi / 3 := by
  obtain ⟨L⟩ := lab_exists D hS j
  rcases L.a_edge hab hac hkl h with ⟨e, -⟩ | ⟨e, -⟩
  · rw [e]; exact Or.inl L.angB
  · rw [e]; exact Or.inr L.angC

/-- the `a`-edge from a vertex of a tile is unique -/
theorem adart_unique (hS : D.model.TwoPiThreeData α a b c) (hab : a ≠ b) (hac : a ≠ c) {j : Fin N}
    {k l k₂ l₂ : Fin 3} (hkl : k ≠ l) (hkl₂ : k₂ ≠ l₂) (h : dist ((D.tile j).pts k) ((D.tile j).pts l) = a)
    (h₂ : dist ((D.tile j).pts k₂) ((D.tile j).pts l₂) = a) (hk : k₂ = k) : l₂ = l := by
  obtain ⟨L⟩ := lab_exists D hS j
  rcases L.a_edge hab hac hkl h with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rcases L.a_edge hab hac hkl₂ h₂ with ⟨f1, f2⟩ | ⟨f1, f2⟩
  · rw [e2, f2]
  · exact absurd (f1.symm.trans (hk.trans e1)) (Ne.symm L.hBC)
  · exact absurd (f1.symm.trans (hk.trans e1)) L.hBC
  · rw [e2, f2]

/-- two `a`-edges of the same tile from the same point: the same edge, so one direction -/
theorem adart_dir (hS : D.model.TwoPiThreeData α a b c) (hab : a ≠ b) (hac : a ≠ c) (ha : 0 < a) {j : Fin N}
    {p w w' : Plane} (hw : ‖w‖ = a) (hw' : ‖w'‖ = a) (h : EdgeAlong D j p w a)
    (h' : EdgeAlong D j p w' a) : w' = w := by
  obtain ⟨k, l, hkl, hk, ⟨s, hs, hE⟩, hd⟩ := h
  obtain ⟨k₂, l₂, hkl₂, hk₂, ⟨s₂, hs₂, hE₂⟩, hd₂⟩ := h'
  have hkk : k₂ = k := (D.tile j).indep.injective (hk₂.trans hk.symm)
  have hll : l₂ = l := adart_unique hS hab hac hkl hkl₂ hd hd₂ hkk
  rw [hkk, hll, hE] at hE₂
  have h1 : s = 1 := by
    have h2 := len_along hw hs hE
    rw [hd] at h2
    exact (mul_right_cancel₀ ha.ne' (by linarith : s * a = 1 * a))
  have h3 : s₂ = 1 := by
    have h2 := len_along hw' hs₂ (hE.trans hE₂)
    rw [hd] at h2
    exact (mul_right_cancel₀ ha.ne' (by linarith : s₂ * a = 1 * a))
  rw [h1, h3, one_smul, one_smul] at hE₂
  exact hE₂.symm

/-! ## The head of a mismatched edge -/

/-- **The three tiles at a head.** -/
theorem head_data (hS : D.model.TwoPiThreeData α a b c)
    (hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c) {e : DE N} (hM : Mis D a e) {H : Plane}
    (hH : Head D a e H) :
    ∃ n : ℕ, 1 ≤ n ∧ Chain D a e n ∧ H = src D e + (n : ℝ) • (dst D e - src D e) ∧
      (∃ jA, EdgeAlong D jA H (-(dst D e - src D e)) a) ∧
      (∃ jB, Through D jB H (dst D e - src D e)) ∧
      (∃ jC x, x ≠ a ∧ EdgeAlong D jC H (dst D e - src D e) x) := by
  obtain ⟨n, hn, hC, hHe, hcont⟩ := hH
  refine ⟨n, hn, hC, hHe, ?_, ?_, hcont⟩
  · obtain ⟨e', hA', hs', hd'⟩ := hC (n - 1) (by omega)
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hn]; push_cast; ring
    rw [hcast] at hd'
    have h3 : (D.tile e'.1).pts e'.2.1 = src D e + ((n - 1 : ℕ) : ℝ) • (dst D e - src D e) := hs'
    have h4 : (D.tile e'.1).pts e'.2.2 = src D e + (n : ℝ) • (dst D e - src D e) := hd'
    refine ⟨e'.1, e'.2.2, e'.2.1, Ne.symm hA'.1, ?_, ⟨1, one_pos, ?_⟩, ?_⟩
    · rw [hHe]; exact hd'
    · rw [h3, h4, Nat.cast_sub hn]
      push_cast
      module
    · rw [dist_comm]; exact hA'.2
  · obtain ⟨jB, k', l', hkl', t₀, t₁, ht₀, ht₁, hB0, hB1⟩ := pass hS hrel hM hC hn (le_refl n)
    refine ⟨jB, k', l', hkl', t₀ - n, t₁ - n, by linarith, by linarith, ?_, ?_⟩
    · rw [hB0, hHe]; module
    · rw [hB1, hHe]; module

theorem head_inj_aux (hS : D.model.TwoPiThreeData α a b c)
    (hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c) {e e' : DE N} (hM : Mis D a e)
    (hM' : Mis D a e') {n n' : ℕ} (hC' : Chain D a e' n') {V V' w : Plane} (hV : src D e = V)
    (hV' : src D e' = V') (hw : dst D e - src D e = w) (hw' : dst D e' - src D e' = w)
    (hH : V + (n : ℝ) • w = V' + (n' : ℝ) • w) (hle : n ≤ n') : e = e' := by
  obtain ⟨hA, j₀, hj₀, x₀, hx₀, hE₀⟩ := hM
  have hself : EdgeAlong D e.1 V w a := by
    rw [← hV, ← hw]
    exact ⟨e.2.1, e.2.2, hA.1, rfl, ⟨1, one_pos, by rw [one_smul]; rfl⟩, hA.2⟩
  rw [hw, hV] at hE₀
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have hVV : V = V' + ((n' - n : ℕ) : ℝ) • w := by
      rw [Nat.cast_sub hle]
      exact (eq_sub_of_add_eq hH).trans (by module)
    obtain ⟨jP, k', l', hkl', t₀, t₁, ht₀, ht₁, hP0, hP1⟩ :=
      pass hS hrel hM' hC' (k := n' - n) (by omega) (by omega)
    rw [hw', hV'] at hP0 hP1
    have hthr : Through D jP V w :=
      ⟨k', l', hkl', t₀ - ((n' - n : ℕ) : ℝ), t₁ - ((n' - n : ℕ) : ℝ), by linarith, by linarith,
        by rw [hP0, hVV]; module, by rw [hP1, hVV]; module⟩
    have h1 : jP ≠ e.1 := by
      intro h
      have := hself.angle
      rw [← h, hthr.pi] at this
      exact lt_irrefl _ this.2
    have h2 : jP ≠ j₀ := by
      intro h
      have := hE₀.angle
      rw [← h, hthr.pi] at this
      exact lt_irrefl _ this.2
    exact no_three_covers h1 h2 (Ne.symm hj₀) hthr.covers hself.covers hE₀.covers
  · rw [heq] at hH
    have hVeq : V = V' := add_right_cancel hH
    have hself' : EdgeAlong D e'.1 V w a := by
      rw [hVeq, ← hV', ← hw']
      exact ⟨e'.2.1, e'.2.2, hM'.1.1, rfl, ⟨1, one_pos, by rw [one_smul]; rfl⟩, hM'.1.2⟩
    by_cases h1 : e.1 = e'.1
    · have hs : (D.tile e.1).pts e.2.1 = (D.tile e'.1).pts e'.2.1 := by
        show src D e = src D e'
        rw [hV, hV', hVeq]
      have hd : (D.tile e.1).pts e.2.2 = (D.tile e'.1).pts e'.2.2 := by
        have e1 : dst D e = src D e + w := by rw [← hw]; abel
        have e2 : dst D e' = src D e' + w := by rw [← hw']; abel
        show dst D e = dst D e'
        rw [e1, e2, hV, hV', hVeq]
      rw [← h1] at hs hd
      exact Prod.ext h1 (Prod.ext ((D.tile e.1).indep.injective hs) ((D.tile e.1).indep.injective hd))
    · exfalso
      have h2 : j₀ ≠ e'.1 := by
        intro h
        rw [h] at hE₀
        exact hx₀ (edgeAlong_unique hE₀ hself')
      exact no_three_covers h1 (Ne.symm hj₀) (Ne.symm h2) hself.covers hself'.covers hE₀.covers

/-- **In-degree at most one.**  Two mismatched edges with the same head are equal. -/
theorem head_inj (hS : D.model.TwoPiThreeData α a b c)
    (hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c) {e e' : DE N} (hM : Mis D a e)
    (hM' : Mis D a e') {H : Plane} (hH : Head D a e H) (hH' : Head D a e' H) : e = e' := by
  obtain ⟨n, hn, hC, hHe, ⟨jA, hjA⟩, ⟨jB, hjB⟩, ⟨jC, x, hx, hjC⟩⟩ := head_data hS hrel hM hH
  obtain ⟨n', hn', hC', hHe', ⟨jA', hjA'⟩, ⟨jB', hjB'⟩, ⟨jC', x', hx', hjC'⟩⟩ :=
    head_data hS hrel hM' hH'
  obtain ⟨w, hw⟩ : ∃ w : Plane, dst D e - src D e = w := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : Plane, dst D e' - src D e' = w' := ⟨_, rfl⟩
  rw [hw] at hHe hjA hjB hjC
  rw [hw'] at hHe' hjA' hjB' hjC'
  have hapos := hM.1.pos
  have hwn : ‖w‖ = a := by rw [← hw]; exact hM.1.norm
  have hwn' : ‖w'‖ = a := by rw [← hw']; exact hM'.1.norm
  have hAang := hjA.angle
  have hBA : jB ≠ jA := by
    intro h
    rw [← h, hjB.pi] at hAang
    exact lt_irrefl _ hAang.2
  have hint : H ∈ interior D.target.carrier :=
    interior_of_through_and_vertex D.toDissection hBA hjB.pi hAang.1
  have hBB : jB' = jB := by
    by_contra hne
    have hBA' : jB' ≠ jA := by
      intro h
      rw [← h, hjB'.pi] at hAang
      exact lt_irrefl _ hAang.2
    exact Erdos634.RouteOne.two_through_excludes_third D.toDissection hint jB jB' jA (Ne.symm hne) hBA hBA'
      hjB.pi hjB'.pi hAang.1.ne'
  rw [hBB] at hjB'
  rcases through_parallel hapos hwn hwn' hjB hjB' with hww | hww
  · rw [hww] at hw' hHe'
    rcases le_total n n' with hle | hle
    · exact head_inj_aux hS hrel hM hM' hC' rfl rfl hw hw' (hHe.symm.trans hHe') hle
    · exact (head_inj_aux hS hrel hM' hM hC rfl rfl hw' hw (hHe'.symm.trans hHe) hle).symm
  · exfalso
    rw [hww, neg_neg] at hjA'
    have hCB : jC ≠ jB := by
      intro h
      have := hjC.angle
      rw [h, hjB.pi] at this
      exact lt_irrefl _ this.2
    have hA'B : jA' ≠ jB := by
      intro h
      have := hjA'.angle
      rw [h, hjB.pi] at this
      exact lt_irrefl _ this.2
    have hCA' : jC ≠ jA' := by
      intro h
      rw [h] at hjC
      exact hx (edgeAlong_unique hjC hjA')
    exact no_three_covers hCA' hCB hA'B hjC.covers hjA'.covers hjB.covers

/-- the head of a mismatched edge is interior to the target and a tile passes through it -/
theorem head_through (hS : D.model.TwoPiThreeData α a b c)
    (hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c) {e : DE N} (hM : Mis D a e) {H : Plane}
    (hH : Head D a e H) :
    H ∈ interior D.target.carrier ∧ (∃ j, (D.tile j).localAngle H = Real.pi) ∧
      ∃ j : Fin N, ∃ k : Fin 3, (D.tile j).pts k = H := by
  obtain ⟨n, hn, hC, hHe, ⟨jA, hjA⟩, ⟨jB, hjB⟩, -⟩ := head_data hS hrel hM hH
  have hAang := hjA.angle
  have hBA : jB ≠ jA := by
    intro h
    rw [← h, hjB.pi] at hAang
    exact lt_irrefl _ hAang.2
  refine ⟨interior_of_through_and_vertex D.toDissection hBA hjB.pi hAang.1, ⟨jB, hjB.pi⟩, ?_⟩
  obtain ⟨k, l, -, hk, -, -⟩ := hjA
  exact ⟨jA, k, hk⟩

/-- **Out-degree at a simple head.**  If exactly one tile presents `π/3 − α` and exactly one presents `2π/3` at
the head of a mismatched edge, a mismatched edge starts there. -/
theorem simple_head_out (hirr : Irr α) (hS : D.model.TwoPiThreeData α a b c)
    (hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c) {e : DE N} (hM : Mis D a e) {H : Plane}
    (hH : Head D a e H)
    (hβ : ∀ i i' : Fin N, (D.tile i).localAngle H = Real.pi / 3 - α →
      (D.tile i').localAngle H = Real.pi / 3 - α → i = i')
    (hγ : ∀ i i' : Fin N, (D.tile i).localAngle H = 2 * Real.pi / 3 →
      (D.tile i').localAngle H = 2 * Real.pi / 3 → i = i')
    (hβex : ∃ i : Fin N, (D.tile i).localAngle H = Real.pi / 3 - α)
    (hγex : ∃ i : Fin N, (D.tile i).localAngle H = 2 * Real.pi / 3) :
    ∃ e₂ : DE N, Mis D a e₂ ∧ src D e₂ = H := by
  have hab : a ≠ b := by
    intro h; exact hrel 1 1 0 one_pos (by push_cast; linarith)
  have hac : a ≠ c := by
    intro h; exact hrel 1 0 1 one_pos (by push_cast; linarith)
  obtain ⟨n, hn, hC, hHe, ⟨jA, hjA⟩, ⟨jB, hjB⟩, ⟨jC, x, hx, hjC⟩⟩ := head_data hS hrel hM hH
  obtain ⟨w, hw⟩ : ∃ w : Plane, dst D e - src D e = w := ⟨_, rfl⟩
  rw [hw] at hHe hjA hjB hjC
  have hapos := hM.1.pos
  have hwn : ‖w‖ = a := by rw [← hw]; exact hM.1.norm
  have hAang := hjA.angle
  have hBA : jB ≠ jA := by
    intro h
    rw [← h, hjB.pi] at hAang
    exact lt_irrefl _ hAang.2
  have hint : H ∈ interior D.target.carrier :=
    interior_of_through_and_vertex D.toDissection hBA hjB.pi hAang.1
  -- the angle of the arrival tile at `H`
  have hAβγ : (D.tile jA).localAngle H = Real.pi / 3 - α ∨ (D.tile jA).localAngle H = 2 * Real.pi / 3 := by
    obtain ⟨k, l, hkl, hk, -, hd⟩ := hjA
    have := angle_of_adart hS hab hac hkl hd
    rwa [hk] at this
  -- the other tile with an `a`-edge at `H`
  obtain ⟨T₂, hT₂, hT₂A, hall⟩ : ∃ T₂ : Fin N,
      ((D.tile T₂).localAngle H = Real.pi / 3 - α ∨ (D.tile T₂).localAngle H = 2 * Real.pi / 3) ∧
      T₂ ≠ jA ∧ ∀ j : Fin N, ((D.tile j).localAngle H = Real.pi / 3 - α ∨
        (D.tile j).localAngle H = 2 * Real.pi / 3) → j = jA ∨ j = T₂ := by
    obtain ⟨iβ, hiβ⟩ := hβex
    obtain ⟨iγ, hiγ⟩ := hγex
    rcases hAβγ with hA | hA
    · refine ⟨iγ, Or.inr hiγ, ?_, ?_⟩
      · intro h; rw [h, hA] at hiγ; exact d_bg hirr hiγ
      · intro j hj
        rcases hj with hj | hj
        · exact Or.inl (hβ j jA hj hA)
        · exact Or.inr (hγ j iγ hj hiγ)
    · refine ⟨iβ, Or.inl hiβ, ?_, ?_⟩
      · intro h; rw [h, hA] at hiβ; exact d_bg hirr hiβ.symm
      · intro j hj
        rcases hj with hj | hj
        · exact Or.inr (hβ j iβ hj hiβ)
        · exact Or.inl (hγ j jA hj hA)
  obtain ⟨k₂, l₂, hkl₂, hk₂, hd₂⟩ := adart_of_angle hirr hS hT₂
  obtain ⟨w₂, hw₂⟩ : ∃ w₂ : Plane, (D.tile T₂).pts l₂ - (D.tile T₂).pts k₂ = w₂ := ⟨_, rfl⟩
  have hwn₂ : ‖w₂‖ = a := by rw [← hw₂, ← dist_eq_norm, dist_comm]; exact hd₂
  have hself₂ : EdgeAlong D T₂ H w₂ a := ⟨k₂, l₂, hkl₂, hk₂, ⟨1, one_pos, by rw [one_smul, hw₂]⟩, hd₂⟩
  have hT₂B : T₂ ≠ jB := by
    intro h
    have := hself₂.angle
    rw [h, hjB.pi] at this
    exact lt_irrefl _ this.2
  have hCB : jC ≠ jB := by
    intro h
    have := hjC.angle
    rw [h, hjB.pi] at this
    exact lt_irrefl _ this.2
  -- the direction of the second `a`-edge is not along the line of the head
  have hnotpar : w₂ ≠ w ∧ w₂ ≠ -w := by
    constructor
    · intro h
      rw [h] at hself₂
      by_cases hC2 : jC = T₂
      · rw [hC2] at hjC
        exact hx (edgeAlong_unique hjC hself₂)
      · exact no_three_covers hC2 hCB hT₂B hjC.covers hself₂.covers hjB.covers
    · intro h
      rw [h] at hself₂
      exact no_three_covers hT₂A hT₂B (Ne.symm hBA) hself₂.covers hjA.covers hjB.neg.covers
  obtain ⟨ε, hε, hray⟩ := interior_ray hint w₂
  have hint' : ∀ t : ℝ, 0 < t → t < ε → H + ((0 : ℝ) + t) • w₂ ∈ interior D.target.carrier := by
    intro t ht0 ht
    rw [zero_add]; exact hray t ht0 ht
  obtain ⟨j, hj, k, l, hkl, s, hs, hE, hcase⟩ :=
    second_along D.toDissection T₂ hkl₂ hk₂ hw₂ (le_refl 0) one_pos hε hint'
  rw [zero_smul, add_zero] at hcase
  rcases hcase with hk | ⟨ν, hν0, hν1, hν⟩
  · -- an edge of `j` from `H` along `w₂`
    by_cases hxa : dist ((D.tile j).pts k) ((D.tile j).pts l) = a
    · exfalso
      have hjβγ := angle_of_adart hS hab hac hkl hxa
      rw [hk] at hjβγ
      have hjA' : j = jA := by
        rcases hall j hjβγ with h | h
        · exact h
        · exact absurd h hj
      have hE₂ : EdgeAlong D jA H w₂ a := by
        rw [← hjA']; exact ⟨k, l, hkl, hk, ⟨s, hs, hE⟩, hxa⟩
      have hdir : -w = w₂ := adart_dir hS hab hac hapos hwn₂ (by rw [norm_neg]; exact hwn) hE₂ hjA
      exact hnotpar.2 hdir.symm
    · refine ⟨(T₂, k₂, l₂), ⟨⟨hkl₂, hd₂⟩, j, hj, _, hxa, ?_⟩, hk₂⟩
      show EdgeAlong D j ((D.tile T₂).pts k₂) ((D.tile T₂).pts l₂ - (D.tile T₂).pts k₂) _
      rw [hw₂, hk₂]
      exact ⟨k, l, hkl, hk, ⟨s, hs, hE⟩, rfl⟩
  · -- a tile through `H` along `w₂`: it is `jB`, so `w₂ = ± w`
    exfalso
    have hthr : Through D j H w₂ := by
      refine ⟨k, l, hkl, -(ν * s), (1 - ν) * s, by nlinarith, by nlinarith, ?_, ?_⟩
      · rw [hν, smul_smul]; module
      · have : (D.tile j).pts l = (D.tile j).pts k + s • w₂ := by rw [← hE]; abel
        rw [this, hν, smul_smul]; module
    have hjB' : j = jB := by
      by_contra hne
      exact Erdos634.RouteOne.two_through_excludes_third D.toDissection hint jB j T₂ (Ne.symm hne)
        (Ne.symm hT₂B) hj hjB.pi hthr.pi hself₂.angle.1.ne'
    rw [hjB'] at hthr
    rcases through_parallel hapos hwn hwn₂ hjB hthr with h | h
    · exact hnotpar.1 h
    · exact hnotpar.2 h

/-- **Out-degree at an odd full vertex.**  `p` is interior to the target, no tile passes through `p`, and the
number of tiles presenting `π/3 − α` or `2π/3` at `p` is odd: a mismatched edge starts at `p`. -/
theorem odd_vertex_out (hirr : Irr α) (hS : D.model.TwoPiThreeData α a b c)
    (hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c) {p : Plane}
    (hp : p ∈ interior D.target.carrier) (hπ : ∀ i : Fin N, (D.tile i).localAngle p ≠ Real.pi)
    (hodd : Odd ((Finset.univ.filter (fun i : Fin N => (D.tile i).localAngle p = Real.pi / 3 - α ∨
      (D.tile i).localAngle p = 2 * Real.pi / 3)).card)) :
    ∃ e : DE N, Mis D a e ∧ src D e = p := by
  classical
  have hab : a ≠ b := by
    intro h; exact hrel 1 1 0 one_pos (by push_cast; linarith)
  have hac : a ≠ c := by
    intro h; exact hrel 1 0 1 one_pos (by push_cast; linarith)
  by_contra hno
  push Not at hno
  apply (Nat.not_even_iff_odd.mpr hodd)
  refine even_card_of_matching _
    (fun i i' => i ≠ i' ∧ ∃ w : Plane, ‖w‖ = a ∧ EdgeAlong D i p w a ∧ EdgeAlong D i' p w a) ?_ ?_ ?_
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    obtain ⟨k, l, hkl, hk, hd⟩ := adart_of_angle hirr hS hi'
    obtain ⟨w, hw⟩ : ∃ w : Plane, (D.tile i).pts l - (D.tile i).pts k = w := ⟨_, rfl⟩
    have hwn : ‖w‖ = a := by rw [← hw, ← dist_eq_norm, dist_comm]; exact hd
    have hself : EdgeAlong D i p w a := ⟨k, l, hkl, hk, ⟨1, one_pos, by rw [one_smul, hw]⟩, hd⟩
    obtain ⟨ε, hε, hray⟩ := interior_ray hp w
    have hint' : ∀ t : ℝ, 0 < t → t < ε → p + ((0 : ℝ) + t) • w ∈ interior D.target.carrier := by
      intro t ht0 ht
      rw [zero_add]; exact hray t ht0 ht
    obtain ⟨j, hj, k', l', hkl', s, hs, hE, hcase⟩ :=
      second_along D.toDissection i hkl hk hw (le_refl 0) one_pos hε hint'
    rw [zero_smul, add_zero] at hcase
    rcases hcase with hk' | ⟨ν, hν0, hν1, hν⟩
    · by_cases hxa : dist ((D.tile j).pts k') ((D.tile j).pts l') = a
      · have hjβγ := angle_of_adart hS hab hac hkl' hxa
        rw [hk'] at hjβγ
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjβγ⟩, Ne.symm hj, w, hwn, hself,
          ⟨k', l', hkl', hk', ⟨s, hs, hE⟩, hxa⟩⟩
      · exfalso
        refine hno (i, k, l) ⟨⟨hkl, hd⟩, j, hj, _, hxa, ?_⟩ hk
        show EdgeAlong D j ((D.tile i).pts k) ((D.tile i).pts l - (D.tile i).pts k) _
        rw [hw, hk]
        exact ⟨k', l', hkl', hk', ⟨s, hs, hE⟩, rfl⟩
    · exfalso
      apply hπ j
      rw [hν, ← hE]
      exact localAngle_pi_on_edge (D.tile j) hkl' hν0 hν1
  · intro x y h; exact h.1
  · rintro x y z ⟨hxy, w, hwn, hxw, hyw⟩ ⟨hyz, w', hwn', hyw', hzw'⟩
    have hapos : 0 < a := by
      obtain ⟨L⟩ := lab_exists D hS x
      exact L.a_pos
    have hww : w' = w := adart_dir hS hab hac hapos hwn hwn' hyw hyw'
    rw [hww] at hzw'
    by_contra hzx
    exact no_three_covers hxy (Ne.symm hzx) hyz hxw.covers hyw.covers hzw'.covers

end heads

end Erdos634.Draft.E120Graph

#print axioms Erdos634.Draft.E120Graph.head_inj
#print axioms Erdos634.Draft.E120Graph.simple_head_out
#print axioms Erdos634.Draft.E120Graph.odd_vertex_out
