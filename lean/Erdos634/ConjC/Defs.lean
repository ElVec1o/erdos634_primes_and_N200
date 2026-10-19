/-
ConjC/Defs.lean -- the family predicates of Conjecture C ((project working notes)), existence side.

Each predicate is EXACTLY the parameter range of an existing Lean existence theorem (statement-match rule, foot of
lean/PAPER_MAP.md).  Where the Lean range differs from C's table, the docstring says so.  `ConjCBase N` is the
disjunction of the families, closed under `N ↦ k² N` (`k ≥ 1`).  The existence theorem is `ConjC.Exist.conjC_existence`.

Credits (the constructions are theirs; what is ours is the formal proof of some of them and the bookkeeping):
Snover–Waiveris–Williams and Laczkovich (F0), D. Paliy (F1 W/β collars and residue seeds, F2, F3a/b, seeds of F3d),
M. Beeson and Roșu (β seed, families), B. Herdt (F6 template, 1125), Zhang (arXiv:2512.22696, F3c, F3d),
J. P. Harries (88), Laczkovich (macro-dissections), our template engine `bto` (F5).

Composite-N bookkeeping; not prime-case work.  UNAUDITED.  No sorry.
-/
import Mathlib.Tactic
import Erdos634.Draft.ZhangEqui

namespace Erdos634.ConjC

/-- **F0a**: `1` and sums of two positive squares (`x² + y²`, `x, y ≥ 1`).  With the `k²` closure this is C's
`k², k²(x²+y²)`.  Lean: `TileCountFamilies.tileCount_one`, `tileCount_two_squares`. -/
def F0a (N : ℕ) : Prop := N = 1 ∨ ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ N = x * x + y * y

/-- **F0b**: `3` and `6` (C's `3k², 6k²` after the closure).  Lean: `tileCount_three_sq`, `tileCount_six_sq`. -/
def F0b (N : ℕ) : Prop := N = 3 ∨ N = 6

/-- **F1T**: `M²(3f² − e²)`, coprime `1 ≤ e < f`, `M ≥ f` (C's range exactly).  Lean: `Residue.betaTilable_ge`
plus the count lemma `ConjC.Exist.tileCount_beta_ge` (new). -/
def F1T (N : ℕ) : Prop :=
  ∃ e f M : ℕ, 1 ≤ e ∧ e < f ∧ Nat.Coprime e f ∧ f ≤ M ∧ N = M ^ 2 * (3 * f ^ 2 - e ^ 2)

/-- **F1W**: `M²(2f² − e²)`, coprime `1 ≤ e < f`, `M ≥ f`.  Lean: `Residue.wTilable_ge` (count in the type).
C writes `e < f` without `1 ≤ e`; `e = 0` is not a member (tile degenerate), so this is C's range. -/
def F1W (N : ℕ) : Prop :=
  ∃ e f M : ℕ, 1 ≤ e ∧ e < f ∧ Nat.Coprime e f ∧ f ≤ M ∧ N = (2 * f ^ 2 - e ^ 2) * M ^ 2

/-- **F2**: `(2q² − p²)(3q² − p²)`, `0 < p < q`.  Lean: `S2All.s2_family_all`.  The Lean range is WIDER than C's
(no coprimality; the non-coprime values are `k²`-multiples of coprime ones anyway). -/
def F2 (N : ℕ) : Prop := ∃ p q : ℕ, 0 < p ∧ p < q ∧ N = (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)

/-- Eisenstein triple: `c² = a² + ab + b²` (tile with angle `2π/3`). -/
def Eis (a b c : ℕ) : Prop := c ^ 2 = a ^ 2 + a * b + b ^ 2

/-- Paliy's semigroup precondition `bc − a² ∈ ⟨a, b, c⟩`, as used in `PRevAll`/`PF2All`. -/
def PSemi (a b c : ℕ) : Prop := ∃ A B s : ℕ, A * a + B * b + s * c + a ^ 2 = b * c

/-- **F3a**: `(2a + b)(a + b)`; `0 < a < b` (Lean `F4All.f4_family`) or `0 < b < a` with `PSemi`
(Lean `PRevAll.prev_family`). -/
def F3a (N : ℕ) : Prop :=
  (∃ a b c : ℕ, 0 < a ∧ a < b ∧ Eis a b c ∧ N = (2 * a + b) * (a + b)) ∨
  (∃ a b c : ℕ, 0 < b ∧ b < a ∧ Eis a b c ∧ PSemi a b c ∧ N = (2 * a + b) * (a + b))

/-- **F3b**: `3(a + b)(a + 2b)` for `0 < a < b` (`F3All.f3_family`) or `0 < b < a < 2b` (`PF3All.pf3_family`);
`(a + 2b)(2a + b)` for `0 < b < a` with `PSemi` (`PF2All.pf2_family`). -/
def F3b (N : ℕ) : Prop :=
  (∃ a b c : ℕ, 0 < a ∧ a < b ∧ Eis a b c ∧ N = 3 * (a + b) * (a + 2 * b)) ∨
  (∃ a b c : ℕ, 0 < b ∧ b < a ∧ a < 2 * b ∧ Eis a b c ∧ N = 3 * (a + b) * (a + 2 * b)) ∨
  (∃ a b c : ℕ, 0 < b ∧ b < a ∧ Eis a b c ∧ PSemi a b c ∧ N = (a + 2 * b) * (2 * a + b))

/-- **F3c** (Zhang): the five forms times `m²`, `m ≥ 3 t0`, `Frob a b t0`.  Lean `ZhangProps.zhang_five` (exact). -/
def F3c (N : ℕ) : Prop :=
  ∃ a b c t0 m : ℕ, 0 < a ∧ 0 < b ∧ Eis a b c ∧ Erdos634.Draft.ZhangEqui.Frob a b t0 ∧ 3 * t0 ≤ m ∧
    (N = a * b * m ^ 2 ∨ N = a * (b + 2 * a) * m ^ 2 ∨ N = b * (a + 2 * b) * m ^ 2 ∨
      N = b * (a + b) * m ^ 2 ∨ N = a * (b + a) * m ^ 2)

/-- **F3d**: `15 m²`, `33 m²`, `m ∈ ⟨4, 9⟩ \ {0}`.  Lean `EqSemigroup.eq357_semigroup`,
`Iso357Semigroup.iso357_semigroup`.  Paliy's claim `15 m²` for all `m ≥ 4` is NOT included (not proved). -/
def F3d (N : ℕ) : Prop :=
  ∃ m : ℕ, m ∈ AddSubmonoid.closure ({4, 9} : Set ℕ) ∧ m ≠ 0 ∧ (N = 15 * m ^ 2 ∨ N = 33 * m ^ 2)

/-- **F4** (sporadic): `84, 88, 143, 189` (Lean: `R84/R88/R143/R189TilingBridge`).  NARROWER than C: C also lists
the value `183`, which is NOT a tile count (excluded; paper main.tex:1001) and is NOT in this predicate. -/
def F4 (N : ℕ) : Prop := N = 84 ∨ N = 88 ∨ N = 143 ∨ N = 189

/-- **F5** (base-α templates).  Three parts, all formally proved (2026-10-19, `Draft.CollarUp`, `Draft.CollarFam`):
(i) the **e = 1 collar up-set** `(f²−1)(2f²−1) g²`, `f ≥ 2`, `g ≥ f+1` (`CollarUp.tileCount_e1_up`; Theorem A seed `g = f+1` plus the layer
step; this contains the former sporadic values 11625 = (4,5), 121765 = (6,7), and 189 = (2,3));
(ii) the row `(e,f) = (2,5)` tail `966 g²`, `g ≥ 25` (`CollarFam.tileCount_966_sq`, from the template 603750);
(iii) the five remaining engine values `66960, 119040, 167865, 186000, 364560` (`T<N>.tileCount_<N>`; the twelve values of `TemplateSquares`
are `k²`-multiples and covered by the closure).
Still NARROWER than C's `N0(e,f) g²` for general `(e,f)`; `g_min(e,f)` for the other rows is not a theorem here.  Credit: Paliy's alpha up-set
(docs/eventual-rational-families.md, 2026-09-29, independent construction), Beeson/Harries (84, 189), our engine `bto` + collar session (layer step, seed). -/
def F5 (N : ℕ) : Prop :=
  (∃ f g : ℕ, 2 ≤ f ∧ f + 1 ≤ g ∧ N = (f * f - 1) * (2 * (f * f) - 1) * (g * g)) ∨
  (∃ g : ℕ, 25 ≤ g ∧ N = 966 * (g * g)) ∨
  N = 66960 ∨ N = 119040 ∨ N = 167865 ∨ N = 186000 ∨ N = 364560

/-- **F6** (Herdt `γ = 2α` family): exactly the hypotheses of `HerdtFamily.herdt_family`
(`b(v(D + τv))²`, `b = v² − u²`, `u < v < 2u`, two linear Diophantine conditions), plus the three instances
`1125, 19600, 130977`.  This is WIDER than C's F6 row (which lists the three values only) and narrower than C's
conjectured `v ∣ g, g ≥ g_D` range. -/
def F6 (N : ℕ) : Prop :=
  N = 1125 ∨ N = 19600 ∨ N = 130977 ∨
  ∃ u v b τ D a1 n1 a2 n2 : ℕ, 0 < u ∧ u < v ∧ v < 2 * u ∧ 0 < τ ∧ 0 < D ∧ 0 < a1 ∧ 0 < n1 ∧ 0 < a2 ∧ 0 < n2 ∧
    b + u ^ 2 = v ^ 2 ∧ b * a1 + u * v * n1 + D * u ^ 4 = τ * v * b ^ 2 ∧ b * a2 + v * n2 + τ * u ^ 4 = D * v * b ∧
    N = b * (v * (D + τ * v)) ^ 2

/-- The cores: the union of the families before the square closure. -/
def ConjCCore (n : ℕ) : Prop :=
  F0a n ∨ F0b n ∨ F1T n ∨ F1W n ∨ F2 n ∨ F3a n ∨ F3b n ∨ F3c n ∨ F3d n ∨ F4 n ∨ F5 n ∨ F6 n

/-- **The existence side of Conjecture C, as formally proved**: `N = k² n` with `k ≥ 1` and `n` a core. -/
def ConjCBase (N : ℕ) : Prop := ∃ k n : ℕ, 0 < k ∧ ConjCCore n ∧ N = k * k * n

theorem conjCBase_of_core {n : ℕ} (h : ConjCCore n) : ConjCBase n := ⟨1, n, one_pos, h, by ring⟩

/-- closure under `N ↦ j² N` -/
theorem ConjCBase.sq_mul {N : ℕ} (h : ConjCBase N) {j : ℕ} (hj : 0 < j) : ConjCBase (j * j * N) := by
  obtain ⟨k, n, hk, hn, rfl⟩ := h
  exact ⟨j * k, n, Nat.mul_pos hj hk, hn, by ring⟩

end Erdos634.ConjC
