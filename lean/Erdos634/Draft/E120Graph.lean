/-
Draft/E120Graph.lean -- Laczkovich's graph `Γ_a` on a tiling by a tile with an angle `2π/3`: links and their heads.

MECHANICAL PORT of `Draft/E60Graph.lean` (the tile with an angle `π/3`) to `Tri.TwoPiThreeData α a b c`: angles `α`,
`π/3 − α`, `2π/3` opposite the sides `a`, `b`, `c`.  The edge of length `a` again joins the vertices of the second
and the third angle, which is all the proofs use; they are the proofs of `E60Graph` with the two constants exchanged.
Declarations live in the namespace `E120Graph` (same names as in `E60Graph`).

Setting: no relation `j a = p b + q c` holds with integers `j ≥ 1`, `p, q ≥ 0` (`hrel`).  A directed tile edge of
length `a` is MISMATCHED (`Mis`) if another tile has an edge from the same point along the same ray of a different
length; `Chain`, `Head`, `pass`, `chain_next`, `head_exists` as in `E60Graph`.

The method is Laczkovich's (Discrete Comput. Geom. 48 (2012)); for the `2π/3` tile the degree count is Lemma 3.5 of
Beeson and Zhang, arXiv:2604.01314. not prime-case work.
No sorry, no native_decide.
-/
import Erdos634.Draft.E60Second
import Erdos634.Draft.E120Fan
import Erdos634.Draft.CompositeE5Gen

open Erdos634.Geometry Erdos634.Draft.E60Second

namespace Erdos634.Draft.E120Graph

theorem fin3_other : ∀ x y z k : Fin 3, x ≠ y → x ≠ z → y ≠ z → k = x ∨ k = y ∨ k = z := by decide

theorem fin3_opp : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
    (x + 1 = y ∧ x + 2 = z) ∨ (x + 1 = z ∧ x + 2 = y) := by decide

theorem oppLen_eq_dist (T : Tri) {x y z : Fin 3} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    T.oppLen x = dist (T.pts y) (T.pts z) := by
  unfold Tri.oppLen
  rcases fin3_opp x y z hxy hxz hyz with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
  · rw [e1, e2, dist_comm]

/-! ## The labelled vertices of a tile -/

/-- the vertices of a tile with angles `α`, `π/3 − α`, `2π/3` (opposite the sides `a`, `b`, `c`) -/
structure Lab (T : Tri) (α a b c : ℝ) where
  vA : Fin 3
  vB : Fin 3
  vC : Fin 3
  hAB : vA ≠ vB
  hAC : vA ≠ vC
  hBC : vB ≠ vC
  angA : T.localAngle (T.pts vA) = α
  angB : T.localAngle (T.pts vB) = Real.pi / 3 - α
  angC : T.localAngle (T.pts vC) = 2 * Real.pi / 3
  lenA : dist (T.pts vB) (T.pts vC) = a
  lenB : dist (T.pts vA) (T.pts vC) = b
  lenC : dist (T.pts vA) (T.pts vB) = c

theorem lab_exists {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hS : D.model.TwoPiThreeData α a b c)
    (i : Fin N) : Nonempty (Lab (D.tile i) α a b c) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
  obtain ⟨τ, h0, o0, h1, o1, h2, o2⟩ := hS
  have key : ∀ m : Fin 3, (D.tile i).angleAt (σ.symm (τ m)) = D.model.angleAt (τ m) ∧
      (D.tile i).oppLen (σ.symm (τ m)) = D.model.oppLen (τ m) := by
    intro m
    have := hσ (σ.symm (τ m))
    rwa [Equiv.apply_symm_apply] at this
  have hinj : ∀ m m' : Fin 3, m ≠ m' → σ.symm (τ m) ≠ σ.symm (τ m') :=
    fun m m' h e => h (τ.injective (σ.symm.injective e))
  have h01 := hinj 0 1 (by decide)
  have h02 := hinj 0 2 (by decide)
  have h12 := hinj 1 2 (by decide)
  refine ⟨⟨σ.symm (τ 0), σ.symm (τ 1), σ.symm (τ 2), h01, h02, h12, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Tri.localAngle_vertex]; exact (key 0).1.trans h0
  · rw [Tri.localAngle_vertex]; exact (key 1).1.trans h1
  · rw [Tri.localAngle_vertex]; exact (key 2).1.trans h2
  · rw [← oppLen_eq_dist (D.tile i) h01 h02 h12]; exact (key 0).2.trans o0
  · rw [← oppLen_eq_dist (D.tile i) (Ne.symm h01) h12 h02]; exact (key 1).2.trans o1
  · rw [← oppLen_eq_dist (D.tile i) (Ne.symm h02) (Ne.symm h12) h01]; exact (key 2).2.trans o2

namespace Lab

variable {T : Tri} {α a b c : ℝ}

theorem cases (L : Lab T α a b c) (k : Fin 3) : k = L.vA ∨ k = L.vB ∨ k = L.vC := fin3_other _ _ _ k L.hAB L.hAC L.hBC

/-- every edge has length `a`, `b` or `c` -/
theorem len (L : Lab T α a b c) {k l : Fin 3} (hkl : k ≠ l) :
    dist (T.pts k) (T.pts l) = a ∨ dist (T.pts k) (T.pts l) = b ∨ dist (T.pts k) (T.pts l) = c := by
  rcases L.cases k with rfl | rfl | rfl <;> rcases L.cases l with rfl | rfl | rfl
  · exact absurd rfl hkl
  · exact Or.inr (Or.inr L.lenC)
  · exact Or.inr (Or.inl L.lenB)
  · exact Or.inr (Or.inr (by rw [dist_comm]; exact L.lenC))
  · exact absurd rfl hkl
  · exact Or.inl L.lenA
  · exact Or.inr (Or.inl (by rw [dist_comm]; exact L.lenB))
  · exact Or.inl (by rw [dist_comm]; exact L.lenA)
  · exact absurd rfl hkl

/-- the edge of length `a` joins the vertices of angles `π/3 − α` and `2π/3` -/
theorem a_edge (L : Lab T α a b c) (hab : a ≠ b) (hac : a ≠ c) {k l : Fin 3} (hkl : k ≠ l) (h : dist (T.pts k) (T.pts l) = a) :
    (k = L.vB ∧ l = L.vC) ∨ (k = L.vC ∧ l = L.vB) := by
  rcases L.cases k with rfl | rfl | rfl <;> rcases L.cases l with rfl | rfl | rfl
  · exact absurd rfl hkl
  · exact absurd (h.symm.trans L.lenC) hac
  · exact absurd (h.symm.trans L.lenB) hab
  · exact absurd (h.symm.trans (by rw [dist_comm]; exact L.lenC)) hac
  · exact absurd rfl hkl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact absurd (h.symm.trans (by rw [dist_comm]; exact L.lenB)) hab
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hkl

theorem ang (L : Lab T α a b c) (k : Fin 3) : T.localAngle (T.pts k) = α ∨ T.localAngle (T.pts k) = Real.pi / 3 - α ∨
    T.localAngle (T.pts k) = 2 * Real.pi / 3 := by
  rcases L.cases k with rfl | rfl | rfl
  · exact Or.inl L.angA
  · exact Or.inr (Or.inl L.angB)
  · exact Or.inr (Or.inr L.angC)

theorem a_pos (L : Lab T α a b c) : 0 < a := by
  rw [← L.lenA]; exact dist_pos.mpr (fun h => L.hBC (T.indep.injective h))

theorem b_pos (L : Lab T α a b c) : 0 < b := by
  rw [← L.lenB]; exact dist_pos.mpr (fun h => L.hAC (T.indep.injective h))

theorem c_pos (L : Lab T α a b c) : 0 < c := by
  rw [← L.lenC]; exact dist_pos.mpr (fun h => L.hAB (T.indep.injective h))

end Lab

/-! ## Sums of edge lengths -/

/-- `t a` is a sum of edge lengths containing at least one `b` or `c` -/
def Word (a b c t : ℝ) : Prop := ∃ na nb nc : ℕ, 0 < nb + nc ∧ t * a = na * a + nb * b + nc * c

theorem Word.pos {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : Word a b c t) : 0 < t := by
  obtain ⟨na, nb, nc, hpos, h⟩ := h
  have h1 : (0 : ℝ) ≤ na * a := by positivity
  have h2 : (0 : ℝ) < nb * b + nc * c := by
    rcases Nat.eq_zero_or_pos nb with h0 | h0
    · have h3 : 0 < nc := by omega
      have h4 : (0 : ℝ) < nc := by exact_mod_cast h3
      have h5 : (0 : ℝ) ≤ nb * b := by positivity
      nlinarith
    · have h4 : (0 : ℝ) < nb := by exact_mod_cast h0
      have h5 : (0 : ℝ) ≤ nc * c := by positivity
      nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith

/-- **The arithmetic.**  Without a relation `j a = p b + q c`, a sum of edge lengths containing a `b` or a `c` is
never a multiple of `a`. -/
theorem word_ne_nat {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c) {t : ℝ} (h : Word a b c t) (k : ℕ) :
    t ≠ k := by
  rintro rfl
  obtain ⟨na, nb, nc, hpos, h⟩ := h
  by_cases hk : na < k
  · apply hrel (k - na) nb nc (by omega)
    rw [Nat.cast_sub hk.le]
    linarith
  · have h1 : (k : ℝ) ≤ na := by exact_mod_cast (not_lt.mp hk)
    have h2 : (0 : ℝ) < nb * b + nc * c := by
      rcases Nat.eq_zero_or_pos nb with h0 | h0
      · have h3 : 0 < nc := by omega
        have h4 : (0 : ℝ) < nc := by exact_mod_cast h3
        have h5 : (0 : ℝ) ≤ nb * b := by positivity
        nlinarith
      · have h4 : (0 : ℝ) < nb := by exact_mod_cast h0
        have h5 : (0 : ℝ) ≤ nc * c := by positivity
        nlinarith
    nlinarith

theorem word_add {a b c t x : ℝ} (h : Word a b c t) (hx : x = a ∨ x = b ∨ x = c) {s : ℝ} (hs : s * a = x) :
    Word a b c (t + s) := by
  obtain ⟨na, nb, nc, hpos, h⟩ := h
  rcases hx with rfl | rfl | rfl
  · exact ⟨na + 1, nb, nc, hpos, by push_cast; linarith⟩
  · exact ⟨na, nb + 1, nc, by omega, by push_cast; linarith⟩
  · exact ⟨na, nb, nc + 1, by omega, by push_cast; linarith⟩

/-! ## Directed edges, chains, heads -/

section graph

variable {N : ℕ} (D : CongruentDissection N)

/-- directed tile edges: tile, start vertex, end vertex -/
abbrev DE (N : ℕ) := Fin N × Fin 3 × Fin 3

/-- start point -/
def src (e : DE N) : Plane := (D.tile e.1).pts e.2.1

/-- end point -/
def dst (e : DE N) : Plane := (D.tile e.1).pts e.2.2

/-- a directed edge of length `a` -/
def IsA (a : ℝ) (e : DE N) : Prop := e.2.1 ≠ e.2.2 ∧ dist (src D e) (dst D e) = a

/-- the tile `j` has an edge from the point `p` along the ray `w`, of length `x` -/
def EdgeAlong (j : Fin N) (p w : Plane) (x : ℝ) : Prop :=
  ∃ k l : Fin 3, k ≠ l ∧ (D.tile j).pts k = p ∧
    (∃ s : ℝ, 0 < s ∧ (D.tile j).pts l - (D.tile j).pts k = s • w) ∧
    dist ((D.tile j).pts k) ((D.tile j).pts l) = x

/-- a mismatched `a`-edge: another tile has an edge from the same point along the same ray, of another length -/
def Mis (a : ℝ) (e : DE N) : Prop :=
  IsA D a e ∧ ∃ j, j ≠ e.1 ∧ ∃ x, x ≠ a ∧ EdgeAlong D j (src D e) (dst D e - src D e) x

/-- `n` consecutive `a`-edges along the ray of `e`, starting with `e` -/
def Chain (a : ℝ) (e : DE N) (n : ℕ) : Prop :=
  ∀ k : ℕ, k < n → ∃ e' : DE N, IsA D a e' ∧
    src D e' = src D e + (k : ℝ) • (dst D e - src D e) ∧
    dst D e' = src D e + ((k : ℝ) + 1) • (dst D e - src D e)

/-- the head of a mismatched edge: the end of its chain, where a tile continues with an edge that is not an
`a`-edge -/
def Head (a : ℝ) (e : DE N) (H : Plane) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ Chain D a e n ∧ H = src D e + (n : ℝ) • (dst D e - src D e) ∧
    ∃ j x, x ≠ a ∧ EdgeAlong D j H (dst D e - src D e) x

variable {D}

theorem IsA.norm {a : ℝ} {e : DE N} (h : IsA D a e) : ‖dst D e - src D e‖ = a := by
  rw [← dist_eq_norm, dist_comm]; exact h.2

theorem IsA.pos {a : ℝ} {e : DE N} (h : IsA D a e) : 0 < a := by
  rw [← h.2]
  exact dist_pos.mpr (fun hh => h.1 ((D.tile e.1).indep.injective hh))

theorem chain_one {a : ℝ} {e : DE N} (h : IsA D a e) : Chain D a e 1 := by
  intro k hk
  have hk0 : k = 0 := by omega
  subst hk0
  refine ⟨e, h, ?_, ?_⟩
  · simp
  · simp

/-- the length of an edge along `w` -/
theorem len_along {a : ℝ} {w : Plane} (hw : ‖w‖ = a) {j : Fin N} {k l : Fin 3} {s : ℝ} (hs : 0 < s)
    (h : (D.tile j).pts l - (D.tile j).pts k = s • w) :
    dist ((D.tile j).pts k) ((D.tile j).pts l) = s * a := by
  rw [dist_comm, dist_eq_norm, h, norm_smul, Real.norm_eq_abs, abs_of_pos hs, hw]

variable {α a b c : ℝ}

/-- **The other side passes over the chain points.**  Along a chain of `n` edges of a mismatched edge `e`, for
`1 ≤ k ≤ n` some tile has an edge on the line with the point `V + k w` strictly inside. -/
theorem pass (hS : D.model.TwoPiThreeData α a b c)
    (hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c) {e : DE N} (hM : Mis D a e) {n : ℕ}
    (hC : Chain D a e n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃ j, ∃ k' l' : Fin 3, k' ≠ l' ∧ ∃ t₀ t₁ : ℝ, t₀ < k ∧ (k : ℝ) < t₁ ∧
      (D.tile j).pts k' = src D e + t₀ • (dst D e - src D e) ∧
      (D.tile j).pts l' = src D e + t₁ • (dst D e - src D e) := by
  obtain ⟨hA, j₀, hj₀, x₀, hx₀, k₀, l₀, hkl₀, hp₀, ⟨s₀, hs₀, hE₀⟩, hd₀⟩ := hM
  obtain ⟨V, hV⟩ : ∃ V : Plane, V = src D e := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Plane, w = dst D e - src D e := ⟨_, rfl⟩
  have hC' : ∀ k : ℕ, k < n → ∃ e' : DE N, IsA D a e' ∧ src D e' = V + (k : ℝ) • w ∧
      dst D e' = V + ((k : ℝ) + 1) • w := by rw [hV, hw]; exact hC
  rw [← hw] at hE₀ ⊢
  rw [← hV] at hp₀ ⊢
  have hwn : ‖w‖ = a := by rw [hw]; exact hA.norm
  have hapos : 0 < a := hA.pos
  obtain ⟨L₀⟩ := lab_exists D hS j₀
  have hbpos : 0 < b := L₀.b_pos
  have hcpos : 0 < c := L₀.c_pos
  obtain ⟨μ, hμ, hμa, hμb, hμc⟩ : ∃ μ : ℝ, 0 < μ ∧ μ ≤ a ∧ μ ≤ b ∧ μ ≤ c :=
    ⟨min a (min b c), lt_min hapos (lt_min hbpos hcpos), min_le_left _ _,
      le_trans (min_le_right _ _) (min_le_left _ _), le_trans (min_le_right _ _) (min_le_right _ _)⟩
  -- comparing a new edge end with `k`
  have cmp : ∀ (m : ℕ) (j : Fin N) (k' l' : Fin 3) (t₀ t₁ : ℝ), k' ≠ l' → t₀ < k → Word a b c t₁ →
      (m : ℝ) * μ ≤ t₁ * a → (D.tile j).pts k' = V + t₀ • w → (D.tile j).pts l' = V + t₁ • w →
      (∃ j, ∃ k' l' : Fin 3, k' ≠ l' ∧ ∃ t₀ t₁ : ℝ, t₀ < k ∧ (k : ℝ) < t₁ ∧
        (D.tile j).pts k' = V + t₀ • w ∧ (D.tile j).pts l' = V + t₁ • w) ∨
      (∃ t : ℝ, Word a b c t ∧ t < k ∧ (m : ℝ) * μ ≤ t * a ∧ ∃ j, ∃ l' : Fin 3,
        (D.tile j).pts l' = V + t • w) := by
    intro m j k' l' t₀ t₁ hkl ht₀ hW hm h0 h1
    rcases lt_trichotomy t₁ (k : ℝ) with hlt | heq | hgt
    · exact Or.inr ⟨t₁, hW, hlt, hm, j, l', h1⟩
    · exact absurd heq (word_ne_nat hapos hbpos hcpos hrel hW k)
    · exact Or.inl ⟨j, k', l', hkl, t₀, t₁, ht₀, hgt, h0, h1⟩
  have claim : ∀ m : ℕ, 1 ≤ m →
      (∃ j, ∃ k' l' : Fin 3, k' ≠ l' ∧ ∃ t₀ t₁ : ℝ, t₀ < k ∧ (k : ℝ) < t₁ ∧
        (D.tile j).pts k' = V + t₀ • w ∧ (D.tile j).pts l' = V + t₁ • w) ∨
      (∃ t : ℝ, Word a b c t ∧ t < k ∧ (m : ℝ) * μ ≤ t * a ∧ ∃ j, ∃ l' : Fin 3,
        (D.tile j).pts l' = V + t • w) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      have hx : x₀ = s₀ * a := by rw [← hd₀]; exact len_along hwn hs₀ hE₀
      have hx' : x₀ = b ∨ x₀ = c := by
        rcases L₀.len hkl₀ with h | h | h
        · exact absurd (hd₀.symm.trans h) hx₀
        · exact Or.inl (hd₀.symm.trans h)
        · exact Or.inr (hd₀.symm.trans h)
      have hW : Word a b c s₀ := by
        rcases hx' with h | h
        · exact ⟨0, 1, 0, by omega, by push_cast; linarith⟩
        · exact ⟨0, 0, 1, by omega, by push_cast; linarith⟩
      have hμx : μ ≤ s₀ * a := by rcases hx' with h | h <;> linarith
      refine cmp 1 j₀ k₀ l₀ 0 s₀ hkl₀ (by exact_mod_cast hk1) hW (by push_cast; linarith) ?_ ?_
      · rw [hp₀]; module
      · have : (D.tile j₀).pts l₀ = (D.tile j₀).pts k₀ + s₀ • w := by rw [← hE₀]; abel
        rw [this, hp₀]
    | succ m hm ih =>
      rcases ih with h | ⟨t, hW, htk, hmμ, j₁, l₁, h1⟩
      · exact Or.inl h
      · have htpos : 0 < t := hW.pos hapos hbpos hcpos
        obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ⌊t⌋₊ := ⟨_, rfl⟩
        have hq1 : (q : ℝ) ≤ t := by rw [hq]; exact Nat.floor_le htpos.le
        have hq2 : t < (q : ℝ) + 1 := by rw [hq]; exact Nat.lt_floor_add_one t
        have hq3 : (q : ℝ) < t := lt_of_le_of_ne hq1 (Ne.symm (word_ne_nat hapos hbpos hcpos hrel hW q))
        have hqn : q < n := by
          have : (q : ℝ) < n := by
            have : (k : ℝ) ≤ n := by exact_mod_cast hkn
            linarith
          exact_mod_cast this
        obtain ⟨e', hA', hs', hd'⟩ := hC' q hqn
        have hwe : (D.tile e'.1).pts e'.2.2 - (D.tile e'.1).pts e'.2.1 = w := by
          have h3 : (D.tile e'.1).pts e'.2.2 = V + ((q : ℝ) + 1) • w := hd'
          have h4 : (D.tile e'.1).pts e'.2.1 = V + (q : ℝ) • w := hs'
          rw [h3, h4]; module
        have hj1 : (D.tile j₁).pts l₁ = (V + (q : ℝ) • w) + (t - q) • w := by rw [h1]; module
        obtain ⟨j', hj', k'', l'', hkl'', s, hs, hE, hk''⟩ :=
          next_at_junction D.toDissection e'.1 hA'.1 hs' hwe (by linarith) (by linarith) j₁ l₁ hj1
        have hk3 : (D.tile j').pts k'' = V + t • w := by rw [hk'']; module
        have hl3 : (D.tile j').pts l'' = V + (t + s) • w := by
          have : (D.tile j').pts l'' = (D.tile j').pts k'' + s • w := by rw [← hE]; abel
          rw [this, hk3]; module
        obtain ⟨L'⟩ := lab_exists D hS j'
        have hx := len_along hwn hs hE
        have hW' : Word a b c (t + s) := word_add hW (by rw [← hx]; exact L'.len hkl'') rfl
        have hμs : μ ≤ s * a := by
          rcases L'.len hkl'' with h | h | h <;> rw [hx] at h <;> linarith
        refine cmp (m + 1) j' k'' l'' t (t + s) hkl'' htk hW' ?_ hk3 hl3
        push_cast
        nlinarith
  -- a large `m` excludes the second alternative
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, m₀ = ⌈(k : ℝ) * a / μ⌉₊ + 1 := ⟨_, rfl⟩
  rcases claim m₀ (by omega) with h | ⟨t, hW, htk, hmμ, -⟩
  · exact h
  · exfalso
    have h1 : (k : ℝ) * a / μ ≤ ⌈(k : ℝ) * a / μ⌉₊ := Nat.le_ceil _
    have h2 : (m₀ : ℝ) = (⌈(k : ℝ) * a / μ⌉₊ : ℝ) + 1 := by rw [hm₀]; push_cast; ring
    have h3 : (k : ℝ) * a ≤ (⌈(k : ℝ) * a / μ⌉₊ : ℝ) * μ := by
      rw [div_le_iff₀ hμ] at h1; exact h1
    have h4 : t * a < (k : ℝ) * a := by nlinarith
    rw [h2] at hmμ
    nlinarith

/-- **A tile continues at the end of a chain.** -/
theorem chain_next (hS : D.model.TwoPiThreeData α a b c)
    (hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c) {e : DE N} (hM : Mis D a e) {n : ℕ}
    (hn : 1 ≤ n) (hC : Chain D a e n) :
    ∃ j, ∃ k l : Fin 3, k ≠ l ∧ (D.tile j).pts k = src D e + (n : ℝ) • (dst D e - src D e) ∧
      ∃ s : ℝ, 0 < s ∧ (D.tile j).pts l - (D.tile j).pts k = s • (dst D e - src D e) := by
  obtain ⟨jB, k', l', hkl', t₀, t₁, ht₀, ht₁, hB0, hB1⟩ := pass hS hrel hM hC hn (le_refl n)
  obtain ⟨e', hA', hs', hd'⟩ := hC (n - 1) (by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [hcast] at hd'
  obtain ⟨w, hw⟩ : ∃ w : Plane, w = dst D e - src D e := ⟨_, rfl⟩
  rw [← hw] at hB0 hB1 hd' ⊢
  have ht : 0 < t₁ - t₀ := by linarith
  have hwB : (D.tile jB).pts l' - (D.tile jB).pts k' = (t₁ - t₀) • w := by rw [hB0, hB1]; module
  have hθ0 : 0 < ((n : ℝ) - t₀) / (t₁ - t₀) := div_pos (by linarith) ht
  have hθ1 : ((n : ℝ) - t₀) / (t₁ - t₀) < 1 := by rw [div_lt_one ht]; linarith
  have hmul : ((n : ℝ) - t₀) / (t₁ - t₀) * (t₁ - t₀) = (n : ℝ) - t₀ := by field_simp
  have hpt : (D.tile e'.1).pts e'.2.2
      = (D.tile jB).pts k' + (((n : ℝ) - t₀) / (t₁ - t₀)) • ((t₁ - t₀) • w) := by
    have h3 : (D.tile e'.1).pts e'.2.2 = src D e + (n : ℝ) • w := hd'
    rw [h3, hB0, smul_smul, hmul]; module
  obtain ⟨j, hj, k, l, hkl, s, hs, hE, hk⟩ :=
    next_at_junction D.toDissection jB hkl' rfl hwB hθ0 hθ1 e'.1 e'.2.2 hpt
  refine ⟨j, k, l, hkl, ?_, s * (t₁ - t₀), mul_pos hs ht, ?_⟩
  · rw [hk, hB0, smul_smul, hmul]; module
  · rw [hE, smul_smul]

/-- a chain stays in the target, so its length is bounded -/
theorem chain_bound {e : DE N} (hA : IsA D a e) :
    ∃ M : ℕ, ∀ n : ℕ, Chain D a e n → n ≤ M := by
  have hapos := hA.pos
  have hbd : Bornology.IsBounded D.target.carrier := D.target.isCompact.isBounded
  refine ⟨⌈Metric.diam D.target.carrier / a⌉₊ + 1, ?_⟩
  intro n hC
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · omega
  · obtain ⟨e', hA', hs', hd'⟩ := hC (n - 1) (by omega)
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hpos]; push_cast; ring
    rw [hcast] at hd'
    have hmem1 : src D e ∈ D.target.carrier := by
      apply tile_subset_target D.toDissection e.1
      rw [Tri.carrier]; exact subset_convexHull ℝ _ ⟨e.2.1, rfl⟩
    have hmem2 : dst D e' ∈ D.target.carrier := by
      apply tile_subset_target D.toDissection e'.1
      rw [Tri.carrier]; exact subset_convexHull ℝ _ ⟨e'.2.2, rfl⟩
    have hdist := Metric.dist_le_diam_of_mem hbd hmem1 hmem2
    rw [hd', dist_eq_norm, show src D e - (src D e + (n : ℝ) • (dst D e - src D e))
      = -((n : ℝ) • (dst D e - src D e)) by abel, norm_neg, norm_smul, hA.norm, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at hdist
    have h1 : (n : ℝ) ≤ Metric.diam D.target.carrier / a := by
      rw [le_div_iff₀ hapos]; exact hdist
    have h2 : (n : ℝ) ≤ ⌈Metric.diam D.target.carrier / a⌉₊ := le_trans h1 (Nat.le_ceil _)
    have h3 : n ≤ ⌈Metric.diam D.target.carrier / a⌉₊ := by exact_mod_cast h2
    omega

/-- **Every mismatched edge has a head.** -/
theorem head_exists (hS : D.model.TwoPiThreeData α a b c)
    (hrel : ∀ j p q : ℕ, 0 < j → (j : ℝ) * a ≠ p * b + q * c) {e : DE N} (hM : Mis D a e) :
    ∃ H, Head D a e H := by
  have hab : a ≠ b := by
    intro h; exact hrel 1 1 0 one_pos (by push_cast; linarith)
  have hac : a ≠ c := by
    intro h; exact hrel 1 0 1 one_pos (by push_cast; linarith)
  obtain ⟨M, hMb⟩ := chain_bound hM.1
  have key : ∀ m n : ℕ, 1 ≤ n → n + m = M + 1 → Chain D a e n → ∃ H, Head D a e H := by
    intro m
    induction m with
    | zero =>
      intro n hn hnm hC
      have := hMb n hC
      omega
    | succ m ih =>
      intro n hn hnm hC
      obtain ⟨j, k, l, hkl, hk, s, hs, hE⟩ := chain_next hS hrel hM hn hC
      by_cases hx : dist ((D.tile j).pts k) ((D.tile j).pts l) = a
      · -- the chain continues
        have hs1 : s = 1 := by
          have h1 := len_along hM.1.norm hs hE
          rw [hx] at h1
          have hapos := hM.1.pos
          have : s * a = 1 * a := by linarith
          exact mul_right_cancel₀ hapos.ne' this
        apply ih (n + 1) (by omega) (by omega)
        intro k₁ hk₁
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk₁ with h | h
        · exact hC k₁ h
        · subst h
          refine ⟨(j, k, l), ⟨hkl, hx⟩, hk, ?_⟩
          have : (D.tile j).pts l = (D.tile j).pts k + s • (dst D e - src D e) := by rw [← hE]; abel
          show (D.tile j).pts l = _
          rw [this, hk, hs1]; module
      · exact ⟨_, n, hn, hC, rfl, j, _, hx, k, l, hkl, hk, ⟨s, hs, hE⟩, rfl⟩
  exact key M 1 (le_refl 1) (by omega) (chain_one hM.1)

end graph

end Erdos634.Draft.E120Graph

#print axioms Erdos634.Draft.E120Graph.pass
#print axioms Erdos634.Draft.E120Graph.head_exists
