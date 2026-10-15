import Erdos634.Draft.GLGArith
import Erdos634.Draft.GLGSide

/-!
# The boundary model of leaf G is empty (`leafG_model_empty`), `k ≥ 3`

Given three sides (legs `La` with `α` at the apex, `Lb` with `β` at the apex, base `Ba`) of the boundary of a
dissection of the `N = 4(2k+1)` isosceles target by `(k², 2k+1, k(k+1))`, in the combinatorial model of `GLGSide`,
with the rules `V`, corner `α`, apex, `C2` (second tile has `α` next to the corner tile = `corner_G1`),
corner coupling `K` and `G*` (= `corner_G2` (ii) on `Lb`), this is contradictory.  Steps:
words (`GLGArith`), `r ≥ 1` and `q ≥ 1` (pigeonhole), both legs `(1,k,1)` dead (`base r ≥ 3`), mixed pair dead (`G*`).
The geometry → model interface is not proved in this module.
-/

namespace Erdos634.GLG

def lenK (k : ℕ) : TT → ℕ | .a => k ^ 2 | .b => 2 * k + 1 | .c => k * (k + 1)

theorem word_eq (k : ℕ) (S : Side) (L : ℕ) (h : ∑ i ∈ Finset.range S.n, lenK k (S.ty i) = L) :
    S.cnt .a * k ^ 2 + S.cnt .b * (2 * k + 1) + S.cnt .c * (k * (k + 1)) = L := by
  rw [sumty] at h; simpa [lenK] using h

theorem n_pos (k : ℕ) (S : Side) (L : ℕ) (hL : 0 < L) (h : ∑ i ∈ Finset.range S.n, lenK k (S.ty i) = L) :
    0 < S.n := by
  by_contra hh
  have h0 : S.n = 0 := by omega
  rw [h0] at h; simp at h; omega

theorem ty0_bc (S : Side) (h : S.sa 0 = .al) : S.ty 0 = .b ∨ S.ty 0 = .c := by
  unfold Side.sa at h
  generalize S.ty 0 = t at *; generalize S.fl 0 = f at *
  cases t <;> cases f <;> simp_all [sAng, ends]

theorem ty_ne_a (S : Side) (i : ℕ) (h : S.sa i = .al) : S.ty i ≠ .a := by
  unfold Side.sa at h
  generalize S.ty i = t at *; generalize S.fl i = f at *
  cases t <;> cases f <;> simp_all [sAng, ends]

theorem sa_a (S : Side) (i : ℕ) (h : S.ty i = .a) : S.sa i ≠ .al := fun h' => ty_ne_a S i h' h

/-- Corner tile of type `c` ⇒ at least two `c`-edges (the vertex `1` carries no `γ`). -/
theorem c0_two (S : Side) (hv : S.V) (hn2 : 2 ≤ S.n) (h0 : S.sa 0 = .al) (hn : S.na (S.n - 1) ≠ .ga)
    (c2 : S.sa 1 = .al) (hc : S.ty 0 = .c) : 2 ≤ S.cnt .c := by
  have := gamma_count S hv (by omega) h0 hn {1} (by simp; omega) (by
    intro i _ hne
    simp only [Finset.mem_singleton]
    split_ifs with hs
    · intro h; subst h; rw [c2] at hs; exact absurd hs (by simp)
    · intro h; have : i = 0 := by omega
      subst this; exact hne hc)
  simp at this; omega

/-- Corner tiles of type `c` at both ends ⇒ at least three `c`-edges. -/
theorem c0_three (S : Side) (hv : S.V) (hn3 : 3 ≤ S.n) (h0 : S.sa 0 = .al) (hn : S.na (S.n - 1) ≠ .ga)
    (c2 : S.sa 1 = .al) (c2h : S.na (S.n - 2) = .al) (hc : S.ty 0 = .c) (hc' : S.ty (S.n - 1) = .c) :
    3 ≤ S.cnt .c := by
  have := gamma_count S hv (by omega) h0 hn {1, S.n - 1} (by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]; omega) (by
    intro i hi hne
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    split_ifs with hs
    · refine ⟨?_, ?_⟩
      · intro h; subst h; rw [c2] at hs; exact absurd hs (by simp)
      · intro h; rw [h] at hne; exact hne hc'
    · have hna : S.na i = .ga := by
        unfold Side.na Side.sa at *
        rcases gam_end (S.ty i) (S.fl i) hne with h | h
        · exact absurd h hs
        · exact h
      refine ⟨?_, ?_⟩
      · intro h; have : i = 0 := by omega
        subst this; exact hne hc
      · intro h; have : i = S.n - 2 := by omega
        subst this; rw [c2h] at hna; exact absurd hna (by simp))
  rw [Finset.card_pair (by omega)] at this; omega

/-- The model of the three sides. -/
structure Model (k : ℕ) (La Lb Ba : Side) : Prop where
  sumLa : ∑ i ∈ Finset.range La.n, lenK k (La.ty i) = 2 * k * (2 * k + 1)
  sumLb : ∑ i ∈ Finset.range Lb.n, lenK k (Lb.ty i) = 2 * k * (2 * k + 1)
  sumBa : ∑ i ∈ Finset.range Ba.n, lenK k (Ba.ty i) = 2 * (k + 1) * (2 * k + 1)
  vLa : La.V
  vLb : Lb.V
  vBa : Ba.V
  c0La : La.sa 0 = .al
  c0Lb : Lb.sa 0 = .al
  c0Ba : Ba.sa 0 = .al
  apLa : La.na (La.n - 1) = .al
  apLb : Lb.na (Lb.n - 1) = .be
  hiBa : Ba.na (Ba.n - 1) = .al
  c2La : 1 < La.n → La.sa 1 = .al
  c2Lb : 1 < Lb.n → Lb.sa 1 = .al
  c2Ba : 1 < Ba.n → Ba.sa 1 = .al
  c2hiBa : 1 < Ba.n → Ba.na (Ba.n - 2) = .al
  Klo : (La.ty 0 = .b ∧ Ba.ty 0 = .c) ∨ (La.ty 0 = .c ∧ Ba.ty 0 = .b)
  Khi : (Lb.ty 0 = .b ∧ Ba.ty (Ba.n - 1) = .c) ∨ (Lb.ty 0 = .c ∧ Ba.ty (Ba.n - 1) = .b)

/-- `G*` on a side = `corner_G2` (ii): corner tile `c`, second tile `c` (with `α` at its south end), then the third
tile has `α` at its south end. -/
def GStar (S : Side) : Prop := S.ty 0 = .c → S.ty 1 = .c → 2 < S.n → S.sa 2 = .al

theorem leafG_model_empty (k : ℕ) (hk : 3 ≤ k) (La Lb Ba : Side) (M : Model k La Lb Ba)
    (hG : GStar Lb) : False := by
  have hLa := word_eq k La _ M.sumLa
  have hLb := word_eq k Lb _ M.sumLb
  have hBa := word_eq k Ba _ M.sumBa
  have nLa := n_pos k La _ (by nlinarith) M.sumLa
  have nLb := n_pos k Lb _ (by nlinarith) M.sumLb
  have nBa := n_pos k Ba _ (by nlinarith) M.sumBa
  have tLa := cnt_total La
  have tLb := cnt_total Lb
  have tBa := cnt_total Ba
  have rLa := gamma_count La M.vLa nLa M.c0La (by rw [M.apLa]; simp) ∅ (by simp) (by simp)
  have rLb := gamma_count Lb M.vLb nLb M.c0Lb (by rw [M.apLb]; simp) ∅ (by simp) (by simp)
  have rBa := gamma_count Ba M.vBa nBa M.c0Ba (by rw [M.hiBa]; simp) ∅ (by simp) (by simp)
  have qLa := beta_count La M.vLa nLa M.c0La (by rw [M.apLa]; simp)
  simp only [Finset.card_empty, add_zero] at rLa rLb rBa
  -- words
  rcases leg_words k _ _ _ hk hLa with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · omega
  swap
  · omega
  -- La = (1,k,1)
  have nLa2 : 2 ≤ La.n := by omega
  have hLa0 : La.ty 0 ≠ .c := by
    intro hc
    have := c0_two La M.vLa nLa2 M.c0La (by rw [M.apLa]; simp) (M.c2La (by omega)) hc
    omega
  have hBa0 : Ba.ty 0 = .c := by
    rcases M.Klo with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hLa0
  have nBa2 : 2 ≤ Ba.n := by
    have := base_words k (Ba.cnt .a) (Ba.cnt .b) (Ba.cnt .c) hk (by omega) hBa
    omega
  have hc2 := c0_two Ba M.vBa nBa2 M.c0Ba (by rw [M.hiBa]; simp) (M.c2Ba (by omega)) hBa0
  have hBw := base_words k (Ba.cnt .a) (Ba.cnt .b) (Ba.cnt .c) hk (by omega) hBa
  have hBw' : Ba.cnt .a = 2 ∧ Ba.cnt .b = 2 ∧ Ba.cnt .c = 2 := by omega
  rcases leg_words k _ _ _ hk hLb with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
  · omega
  · -- both legs (1,k,1): base needs three c's
    have hLb0 : Lb.ty 0 ≠ .c := by
      intro hc
      have := c0_two Lb M.vLb (by omega) M.c0Lb (by rw [M.apLb]; simp) (M.c2Lb (by omega)) hc
      omega
    have hBn : Ba.ty (Ba.n - 1) = .c := by
      rcases M.Khi with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hLb0
    have := c0_three Ba M.vBa (by omega) M.c0Ba (by rw [M.hiBa]; simp) (M.c2Ba (by omega))
      (M.c2hiBa (by omega)) hBa0 hBn
    omega
  · -- mixed pair: Lb = (2,0,2) reads c, c, a, a: G* contradiction
    have hb0 : ∀ i < Lb.n, Lb.ty i ≠ .b := by
      intro i hi hh
      have : i ∈ (Finset.range Lb.n).filter (fun i => Lb.ty i = .b) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hh⟩
      have h0 : Lb.cnt .b = 0 := g2
      unfold Side.cnt at h0
      rw [Finset.card_eq_zero.mp h0] at this; simp at this
    have t0 : Lb.ty 0 = .c := (ty0_bc Lb M.c0Lb).resolve_left (hb0 0 (by omega))
    have c2 := M.c2Lb (by omega)
    have t1 : Lb.ty 1 = .c := by
      have h1 := ty_ne_a Lb 1 c2
      have h2 := hb0 1 (by omega)
      cases h : Lb.ty 1 <;> simp_all
    have t2 : Lb.ty 2 = .a := by
      have h2 := hb0 2 (by omega)
      by_contra hne
      have hc : Lb.ty 2 = .c := by cases h : Lb.ty 2 <;> simp_all
      have : ({0, 1, 2} : Finset ℕ) ⊆ (Finset.range Lb.n).filter (fun i => Lb.ty i = .c) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_filter, Finset.mem_range]
        rcases hx with rfl | rfl | rfl <;> simp_all <;> omega
      have := Finset.card_le_card this
      simp at this; unfold Side.cnt at g3; omega
    exact sa_a Lb 2 t2 (hG t0 t1 (by omega))

/-- **Leaf G, model form.**  The boundary-model data that a dissection of the `N = 4(2k+1)` target by the tile
`(k²,2k+1,k(k+1))` must produce (NOT derived from a geometric `CongruentDissection` here). -/
def LeafGBoundary (k : ℕ) : Prop := ∃ La Lb Ba : Side, Model k La Lb Ba ∧ GStar Lb

/-- `leafG_closed` (model form, `k ≥ 3`): the leaf-G boundary model is empty. -/
theorem leafG_closed (k : ℕ) (hk : 3 ≤ k) : ¬ LeafGBoundary k := by
  rintro ⟨La, Lb, Ba, M, hG⟩; exact leafG_model_empty k hk La Lb Ba M hG

end Erdos634.GLG
