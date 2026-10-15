/-
Draft/ResidueTools.lean -- tools for the residue seeds of the target `W` (scales `v + t`, `1 ≤ t < u`).

Frame `Φ_φ` with `φ = φβ u e` (`v = u + e`): the cell `a × c`, `a = uv`, `c = v²`, is cut by its diagonal into two
copies of the tile `(a, b, c)`, `b = v² − u²`.  Model `ModC`: the lower half of that cell.  Here:

  * `cellAC`, `cellCA`: the cells `a × c` and `c × a`; `rtRA`, `rtRC`: rectangles of such cells; `ORect`, `rtOC`:
    a rectangle of `c × a` cells that is allowed to have no column (then the region is empty);
  * `TA`, `TB`, `TB'`: the three axis-parallel positions of the tile at scale `k`, with their tilings (`rtTA`, …)
    and the inequalities that hold on them (`mem_TA`, …);
  * `unionF`: the union of two region tilings of the same frame; `stack`: a pile of strips, separated by the
    horizontal lines `y = lvl j`.

The seeds themselves are due to D. Paliy (2026, unrefereed); see `Draft.ResidueSeed`.  No sorry, no native_decide.
-/
import Erdos634.Draft.CollarG

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.Residue
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (triC triC_pts carrier_triC brickL brickU brick_rt cong_U_cell grid scaledRT baseTri
  baseTri_cong vol_triC sq_Phi' dPhi' disjoint_image' f_ne)
open Erdos634.Draft.BrickGridF (shift_rect)
open Erdos634.Draft.S2L (hull_le hull_ge)
open Erdos634.Draft.CollarE1 (cong_swap)
open Erdos634.Draft.CollarG (φβ hφβ ca cb hapos hbpos hvpos hPpos)

/-! ## Generic: the empty tiling, unions, piles -/

/-- the empty region has a tiling by no tile -/
noncomputable def emptyRT {M : Erdos634.Geometry.Tri} : RTiling (∅ : Set Plane) M 0 where
  tile := fun i => i.elim0
  covers := by simp
  disj := fun i _ _ => i.elim0
  cong := fun i => i.elim0

theorem unionF {φ : ℝ} (hφ : 1 < 4 * φ ^ 2) {M : Erdos634.Geometry.Tri} {A B : Set (ℝ × ℝ)} {n1 n2 : ℕ}
    (R1 : Nonempty (RTiling (Phi φ '' A) M n1)) (R2 : Nonempty (RTiling (Phi φ '' B) M n2))
    (h : Disjoint (interior A) (interior B)) : Nonempty (RTiling (Phi φ '' (A ∪ B)) M (n1 + n2)) := by
  obtain ⟨R1⟩ := R1
  obtain ⟨R2⟩ := R2
  exact ⟨RTiling.cast (Set.image_union _ _ _).symm (union R1 R2 (disjoint_image' hφ h))⟩

/-- **A pile of strips.**  Regions `S j` between the levels `lvl j ≤ lvl (j+1)`, each with a tiling, give a tiling
of their union. -/
theorem stack {φ : ℝ} (hφ : 1 < 4 * φ ^ 2) {M : Erdos634.Geometry.Tri} (S : ℕ → Set (ℝ × ℝ)) (cnt : ℕ → ℕ)
    (lvl : ℕ → ℝ) (hmono : ∀ j, lvl j ≤ lvl (j + 1))
    (hlo : ∀ j, ∀ q ∈ S j, lvl j ≤ q.2) (hhi : ∀ j, ∀ q ∈ S j, q.2 ≤ lvl (j + 1)) :
    ∀ n : ℕ, (∀ j, j < n → Nonempty (RTiling (Phi φ '' S j) M (cnt j))) →
      Nonempty (RTiling (Phi φ '' ⋃ j ∈ Finset.range n, S j) M (∑ j ∈ Finset.range n, cnt j)) := by
  have hm : Monotone lvl := monotone_nat_of_le_succ hmono
  intro n
  induction n with
  | zero =>
    intro _
    have hE : (⋃ j ∈ Finset.range 0, S j) = (∅ : Set (ℝ × ℝ)) := by simp
    rw [hE, Set.image_empty, Finset.sum_range_zero]
    exact ⟨emptyRT⟩
  | succ n ih =>
    intro R
    have Rn := R n (Nat.lt_succ_self n)
    have Rp := ih (fun j hj => R j (Nat.lt_succ_of_lt hj))
    have hU : (⋃ j ∈ Finset.range (n + 1), S j) = (⋃ j ∈ Finset.range n, S j) ∪ S n := by
      ext q
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union]
      constructor
      · rintro ⟨j, hj, hq⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact Or.inl ⟨j, h, hq⟩
        · subst h; exact Or.inr hq
      · rintro (⟨j, hj, hq⟩ | hq)
        · exact ⟨j, Nat.lt_succ_of_lt hj, hq⟩
        · exact ⟨n, Nat.lt_succ_self n, hq⟩
    rw [hU, Finset.sum_range_succ]
    refine unionF hφ Rp Rn (interior_disj_snd (lvl n) ?_ (hlo n))
    intro q hq
    simp only [Set.mem_iUnion, Finset.mem_range] at hq
    obtain ⟨j, hj, hqj⟩ := hq
    exact (hhi j q hqj).trans (hm (Nat.succ_le_of_lt hj))

/-- membership in a pile -/
theorem mem_stack {S : ℕ → Set (ℝ × ℝ)} {n : ℕ} {q : ℝ × ℝ} (hq : q ∈ ⋃ j ∈ Finset.range n, S j) :
    ∃ j, j < n ∧ q ∈ S j := by
  simp only [Set.mem_iUnion, Finset.mem_range] at hq
  obtain ⟨j, hj, hqj⟩ := hq
  exact ⟨j, hj, hqj⟩

/-- a rectangle of `c × a` cells that may have no column -/
def ORect (x0 x1 y0 y1 : ℝ) : Set (ℝ × ℝ) := {q | x0 < x1 ∧ x0 ≤ q.1 ∧ q.1 ≤ x1 ∧ y0 ≤ q.2 ∧ q.2 ≤ y1}

/-- the tile at scale `k`, legs `k a` (bottom) and `k c` (right) -/
def TA (u e x0 y0 k : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(x0, y0), (x0 + k * ca u e, y0), (x0 + k * ca u e, y0 + k * (u + e) ^ 2)}
/-- the tile at scale `k`, legs `k a` (left) and `k c` (top) -/
def TB (u e x0 y0 k : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(x0, y0), (x0, y0 + k * ca u e), (x0 + k * (u + e) ^ 2, y0 + k * ca u e)}
/-- the tile at scale `k`, legs `k a` (right) and `k c` (bottom) -/
def TB' (u e x1 y0 k : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(x1, y0 + k * ca u e), (x1, y0), (x1 - k * (u + e) ^ 2, y0)}

/-! ## The frame `φβ`, the model, cells and pieces -/
section frame
variable {u e : ℝ} (hu : 0 < u) (he : 0 < e)
include hu he

theorem hc2 : (0 : ℝ) < (u + e) ^ 2 := pow_pos (hvpos hu he) 2

/-- the model tile: edges `01, 12, 20` of lengths `a, c, b` -/
noncomputable def ModC : Erdos634.Geometry.Tri :=
  brickL (φβ u e) (hφβ hu he) (ca u e) ((u + e) ^ 2) (hapos hu he) (hc2 hu he)

theorem habC : ca u e ^ 2 + ((u + e) ^ 2) ^ 2 + ca u e * (u + e) ^ 2 / φβ u e = (cb u e) ^ 2 := by
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have h3 : 3 * (u + e) ^ 2 - u ^ 2 ≠ 0 := (hPpos hu he).ne'
  simp only [ca, cb, φβ]; field_simp; ring

/-- the cell `a × c` -/
noncomputable def cellAC : RTiling (Phi (φβ u e) '' Rect 0 (ca u e) 0 ((u + e) ^ 2)) (ModC hu he) 2 :=
  brick_rt (φβ u e) (hφβ hu he) (ca u e) ((u + e) ^ 2) (hapos hu he) (hc2 hu he) _
    (Erdos634.Geometry.Tri.Congruent.refl _) (cong_U_cell (hφβ hu he) _ _ _ _)

/-- the cell `c × a` -/
noncomputable def cellCA : RTiling (Phi (φβ u e) '' Rect 0 ((u + e) ^ 2) 0 (ca u e)) (ModC hu he) 2 :=
  brick_rt (φβ u e) (hφβ hu he) ((u + e) ^ 2) (ca u e) (hc2 hu he) (hapos hu he) _
    (cong_swap (hφβ hu he) _ _ _ _)
    ((cong_U_cell (hφβ hu he) _ _ _ _).trans (cong_swap (hφβ hu he) _ _ _ _))

/-- `nx × nu` cells `a × c` -/
theorem rtRA (x0 x1 y0 y1 : ℝ) (nx nu : ℕ) (hnx : 0 < nx) (hnu : 0 < nu)
    (hx : x1 = x0 + ca u e * nx) (hy : y1 = y0 + (u + e) ^ 2 * nu) :
    Nonempty (RTiling (Phi (φβ u e) '' Rect x0 x1 y0 y1) (ModC hu he) (2 * nx * nu)) := by
  obtain ⟨kx, rfl⟩ : ∃ kx, nx = kx + 1 := ⟨nx - 1, by omega⟩
  obtain ⟨ku, rfl⟩ : ∃ ku, nu = ku + 1 := ⟨nu - 1, by omega⟩
  exact ⟨shift_rect (grid (hφβ hu he) (hapos hu he) (hc2 hu he) (cellAC hu he) kx ku) x0 y0 x1 y1
    (by rw [hx]; push_cast; ring) (by rw [hy]; push_cast; ring)⟩

/-- `nx × nv` cells `c × a` -/
theorem rtRC (x0 x1 y0 y1 : ℝ) (nx nv : ℕ) (hnx : 0 < nx) (hnv : 0 < nv)
    (hx : x1 = x0 + (u + e) ^ 2 * nx) (hy : y1 = y0 + ca u e * nv) :
    Nonempty (RTiling (Phi (φβ u e) '' Rect x0 x1 y0 y1) (ModC hu he) (2 * nx * nv)) := by
  obtain ⟨kx, rfl⟩ : ∃ kx, nx = kx + 1 := ⟨nx - 1, by omega⟩
  obtain ⟨kv, rfl⟩ : ∃ kv, nv = kv + 1 := ⟨nv - 1, by omega⟩
  exact ⟨shift_rect (grid (hφβ hu he) (hc2 hu he) (hapos hu he) (cellCA hu he) kx kv) x0 y0 x1 y1
    (by rw [hx]; push_cast; ring) (by rw [hy]; push_cast; ring)⟩

/-- `ny × nv` cells `c × a`, `ny ≥ 0` -/
theorem rtOC (x0 x1 y0 y1 : ℝ) (ny nv : ℕ) (hnv : 0 < nv)
    (hx : x1 = x0 + (u + e) ^ 2 * ny) (hy : y1 = y0 + ca u e * nv) :
    Nonempty (RTiling (Phi (φβ u e) '' ORect x0 x1 y0 y1) (ModC hu he) (2 * ny * nv)) := by
  rcases Nat.eq_zero_or_pos ny with h0 | hpos
  · subst h0
    have hE : ORect x0 x1 y0 y1 = ∅ := by
      ext q
      simp only [ORect, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, -⟩
      rw [hx] at h
      simp at h
    rw [hE, Set.image_empty]
    exact ⟨RTiling.castN (by ring) emptyRT⟩
  · have hpos' : (0 : ℝ) < ny := by exact_mod_cast hpos
    have hlt : x0 < x1 := by rw [hx]; linarith [mul_pos (hc2 hu he) hpos']
    have hE : ORect x0 x1 y0 y1 = Rect x0 x1 y0 y1 := by
      ext q
      simp only [ORect, Rect, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨hlt, h⟩⟩
    rw [hE]
    exact rtRC hu he x0 x1 y0 y1 ny nv hpos hnv hx hy

theorem mem_ORect {x0 x1 y0 y1 : ℝ} {q : ℝ × ℝ} (hq : q ∈ ORect x0 x1 y0 y1) :
    x0 ≤ q.1 ∧ q.1 ≤ x1 ∧ y0 ≤ q.2 ∧ q.2 ≤ y1 := hq.2

theorem rtTA (x0 y0 kr : ℝ) (k : ℕ) (hk : 0 < k) (hkr : kr = k) :
    Nonempty (RTiling (Phi (φβ u e) '' TA u e x0 y0 kr) (ModC hu he) (k * k)) := by
  subst hkr
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have h3 : 3 * (u + e) ^ 2 - u ^ 2 ≠ 0 := (hPpos hu he).ne'
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdet : (((x0 + (k : ℝ) * ca u e, y0) : ℝ × ℝ).1 - ((x0, y0) : ℝ × ℝ).1)
        * (((x0 + (k : ℝ) * ca u e, y0 + (k : ℝ) * (u + e) ^ 2) : ℝ × ℝ).2 - ((x0, y0) : ℝ × ℝ).2)
      - (((x0 + (k : ℝ) * ca u e, y0 + (k : ℝ) * (u + e) ^ 2) : ℝ × ℝ).1 - ((x0, y0) : ℝ × ℝ).1)
        * (((x0 + (k : ℝ) * ca u e, y0) : ℝ × ℝ).2 - ((x0, y0) : ℝ × ℝ).2) ≠ 0 := by
    have hE : (((x0 + (k : ℝ) * ca u e, y0) : ℝ × ℝ).1 - ((x0, y0) : ℝ × ℝ).1)
        * (((x0 + (k : ℝ) * ca u e, y0 + (k : ℝ) * (u + e) ^ 2) : ℝ × ℝ).2 - ((x0, y0) : ℝ × ℝ).2)
      - (((x0 + (k : ℝ) * ca u e, y0 + (k : ℝ) * (u + e) ^ 2) : ℝ × ℝ).1 - ((x0, y0) : ℝ × ℝ).1)
        * (((x0 + (k : ℝ) * ca u e, y0) : ℝ × ℝ).2 - ((x0, y0) : ℝ × ℝ).2)
        = (k : ℝ) * ca u e * ((k : ℝ) * (u + e) ^ 2) := by ring
    rw [hE]
    exact (mul_pos (mul_pos hk' (hapos hu he)) (mul_pos hk' (hc2 hu he))).ne'
  exact ⟨scaledRT (φβ u e) (hφβ hu he) (x0, y0) (x0 + (k : ℝ) * ca u e, y0)
    (x0 + (k : ℝ) * ca u e, y0 + (k : ℝ) * (u + e) ^ 2) k hk hdet _
    (baseTri_cong _ _ (ca u e) ((u + e) ^ 2) ((cb u e) ^ 2) (hapos hu he) (hc2 hu he) (habC hu he) _ _ _ k hk _
      (by simp only [ca, φβ]; field_simp; ring) (by simp only [ca, φβ]; field_simp; ring)
      (by simp only [ca, cb, φβ]; field_simp; ring))⟩

theorem rtTB (x0 y0 kr : ℝ) (k : ℕ) (hk : 0 < k) (hkr : kr = k) :
    Nonempty (RTiling (Phi (φβ u e) '' TB u e x0 y0 kr) (ModC hu he) (k * k)) := by
  subst hkr
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have h3 : 3 * (u + e) ^ 2 - u ^ 2 ≠ 0 := (hPpos hu he).ne'
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdet : (((x0, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).1 - ((x0, y0) : ℝ × ℝ).1)
        * (((x0 + (k : ℝ) * (u + e) ^ 2, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).2 - ((x0, y0) : ℝ × ℝ).2)
      - (((x0 + (k : ℝ) * (u + e) ^ 2, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).1 - ((x0, y0) : ℝ × ℝ).1)
        * (((x0, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).2 - ((x0, y0) : ℝ × ℝ).2) ≠ 0 := by
    have hE : (((x0, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).1 - ((x0, y0) : ℝ × ℝ).1)
        * (((x0 + (k : ℝ) * (u + e) ^ 2, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).2 - ((x0, y0) : ℝ × ℝ).2)
      - (((x0 + (k : ℝ) * (u + e) ^ 2, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).1 - ((x0, y0) : ℝ × ℝ).1)
        * (((x0, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).2 - ((x0, y0) : ℝ × ℝ).2)
        = -((k : ℝ) * ca u e * ((k : ℝ) * (u + e) ^ 2)) := by ring
    rw [hE]
    exact neg_ne_zero.mpr (mul_pos (mul_pos hk' (hapos hu he)) (mul_pos hk' (hc2 hu he))).ne'
  exact ⟨scaledRT (φβ u e) (hφβ hu he) (x0, y0) (x0, y0 + (k : ℝ) * ca u e)
    (x0 + (k : ℝ) * (u + e) ^ 2, y0 + (k : ℝ) * ca u e) k hk hdet _
    (baseTri_cong _ _ (ca u e) ((u + e) ^ 2) ((cb u e) ^ 2) (hapos hu he) (hc2 hu he) (habC hu he) _ _ _ k hk _
      (by simp only [ca, φβ]; field_simp; ring) (by simp only [ca, φβ]; field_simp; ring)
      (by simp only [ca, cb, φβ]; field_simp; ring))⟩

theorem rtTB' (x1 y0 kr : ℝ) (k : ℕ) (hk : 0 < k) (hkr : kr = k) :
    Nonempty (RTiling (Phi (φβ u e) '' TB' u e x1 y0 kr) (ModC hu he) (k * k)) := by
  subst hkr
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have h3 : 3 * (u + e) ^ 2 - u ^ 2 ≠ 0 := (hPpos hu he).ne'
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdet : (((x1, y0) : ℝ × ℝ).1 - ((x1, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).1)
        * (((x1 - (k : ℝ) * (u + e) ^ 2, y0) : ℝ × ℝ).2 - ((x1, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).2)
      - (((x1 - (k : ℝ) * (u + e) ^ 2, y0) : ℝ × ℝ).1 - ((x1, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).1)
        * (((x1, y0) : ℝ × ℝ).2 - ((x1, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).2) ≠ 0 := by
    have hE : (((x1, y0) : ℝ × ℝ).1 - ((x1, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).1)
        * (((x1 - (k : ℝ) * (u + e) ^ 2, y0) : ℝ × ℝ).2 - ((x1, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).2)
      - (((x1 - (k : ℝ) * (u + e) ^ 2, y0) : ℝ × ℝ).1 - ((x1, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).1)
        * (((x1, y0) : ℝ × ℝ).2 - ((x1, y0 + (k : ℝ) * ca u e) : ℝ × ℝ).2)
        = -((k : ℝ) * ca u e * ((k : ℝ) * (u + e) ^ 2)) := by ring
    rw [hE]
    exact neg_ne_zero.mpr (mul_pos (mul_pos hk' (hapos hu he)) (mul_pos hk' (hc2 hu he))).ne'
  exact ⟨scaledRT (φβ u e) (hφβ hu he) (x1, y0 + (k : ℝ) * ca u e) (x1, y0)
    (x1 - (k : ℝ) * (u + e) ^ 2, y0) k hk hdet _
    (baseTri_cong _ _ (ca u e) ((u + e) ^ 2) ((cb u e) ^ 2) (hapos hu he) (hc2 hu he) (habC hu he) _ _ _ k hk _
      (by simp only [ca, φβ]; field_simp; ring) (by simp only [ca, φβ]; field_simp; ring)
      (by simp only [ca, cb, φβ]; field_simp; ring))⟩

/-- on `TA`: the box and the diagonal -/
theorem mem_TA {x0 y0 k : ℝ} (hk : 0 ≤ k) {q : ℝ × ℝ} (hq : q ∈ TA u e x0 y0 k) :
    x0 ≤ q.1 ∧ q.1 ≤ x0 + k * ca u e ∧ y0 ≤ q.2 ∧ q.2 ≤ y0 + k * (u + e) ^ 2 ∧
      ca u e * (q.2 - y0) ≤ (u + e) ^ 2 * (q.1 - x0) := by
  have ha := hapos hu he
  have hc := hc2 hu he
  have hka : 0 ≤ k * ca u e := mul_nonneg hk ha.le
  have hkc : 0 ≤ k * (u + e) ^ 2 := mul_nonneg hk hc.le
  have hprod : 0 ≤ (u + e) ^ 2 * (k * ca u e) := mul_nonneg hc.le hka
  have hv : ∀ p ∈ ({(x0, y0), (x0 + k * ca u e, y0), (x0 + k * ca u e, y0 + k * (u + e) ^ 2)} : Set (ℝ × ℝ)),
      p = (x0, y0) ∨ p = (x0 + k * ca u e, y0) ∨ p = (x0 + k * ca u e, y0 + k * (u + e) ^ 2) := by
    intro p hp
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp
  have hq' := hq
  unfold TA at hq'
  have b1 := hull_ge 1 0 x0 (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b2 := hull_le 1 0 (x0 + k * ca u e) (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b3 := hull_ge 0 1 y0 (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b4 := hull_le 0 1 (y0 + k * (u + e) ^ 2) (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b5 := hull_le (-(u + e) ^ 2) (ca u e) (ca u e * y0 - (u + e) ^ 2 * x0) (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> nlinarith) q hq'
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- on `TB`: the box and the diagonal -/
theorem mem_TB {x0 y0 k : ℝ} (hk : 0 ≤ k) {q : ℝ × ℝ} (hq : q ∈ TB u e x0 y0 k) :
    x0 ≤ q.1 ∧ q.1 ≤ x0 + k * (u + e) ^ 2 ∧ y0 ≤ q.2 ∧ q.2 ≤ y0 + k * ca u e ∧
      ca u e * (q.1 - x0) ≤ (u + e) ^ 2 * (q.2 - y0) := by
  have ha := hapos hu he
  have hc := hc2 hu he
  have hka : 0 ≤ k * ca u e := mul_nonneg hk ha.le
  have hkc : 0 ≤ k * (u + e) ^ 2 := mul_nonneg hk hc.le
  have hprod : 0 ≤ (u + e) ^ 2 * (k * ca u e) := mul_nonneg hc.le hka
  have hv : ∀ p ∈ ({(x0, y0), (x0, y0 + k * ca u e), (x0 + k * (u + e) ^ 2, y0 + k * ca u e)} : Set (ℝ × ℝ)),
      p = (x0, y0) ∨ p = (x0, y0 + k * ca u e) ∨ p = (x0 + k * (u + e) ^ 2, y0 + k * ca u e) := by
    intro p hp
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp
  have hq' := hq
  unfold TB at hq'
  have b1 := hull_ge 1 0 x0 (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b2 := hull_le 1 0 (x0 + k * (u + e) ^ 2) (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b3 := hull_ge 0 1 y0 (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b4 := hull_le 0 1 (y0 + k * ca u e) (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b5 := hull_le (ca u e) (-(u + e) ^ 2) (ca u e * x0 - (u + e) ^ 2 * y0) (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> nlinarith) q hq'
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- on `TB'`: the box and the diagonal -/
theorem mem_TB' {x1 y0 k : ℝ} (hk : 0 ≤ k) {q : ℝ × ℝ} (hq : q ∈ TB' u e x1 y0 k) :
    x1 - k * (u + e) ^ 2 ≤ q.1 ∧ q.1 ≤ x1 ∧ y0 ≤ q.2 ∧ q.2 ≤ y0 + k * ca u e ∧
      (u + e) ^ 2 * (q.2 - y0) ≤ ca u e * (q.1 - (x1 - k * (u + e) ^ 2)) := by
  have ha := hapos hu he
  have hc := hc2 hu he
  have hka : 0 ≤ k * ca u e := mul_nonneg hk ha.le
  have hkc : 0 ≤ k * (u + e) ^ 2 := mul_nonneg hk hc.le
  have hprod : 0 ≤ (u + e) ^ 2 * (k * ca u e) := mul_nonneg hc.le hka
  have hv : ∀ p ∈ ({(x1, y0 + k * ca u e), (x1, y0), (x1 - k * (u + e) ^ 2, y0)} : Set (ℝ × ℝ)),
      p = (x1, y0 + k * ca u e) ∨ p = (x1, y0) ∨ p = (x1 - k * (u + e) ^ 2, y0) := by
    intro p hp
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp
  have hq' := hq
  unfold TB' at hq'
  have b1 := hull_ge 1 0 (x1 - k * (u + e) ^ 2) (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b2 := hull_le 1 0 x1 (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b3 := hull_ge 0 1 y0 (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b4 := hull_le 0 1 (y0 + k * ca u e) (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> linarith) q hq'
  have b5 := hull_le (-ca u e) ((u + e) ^ 2) ((u + e) ^ 2 * y0 - ca u e * (x1 - k * (u + e) ^ 2)) (fun p hp => by
    rcases hv p hp with rfl | rfl | rfl <;> dsimp only <;> nlinarith) q hq'
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

end frame

end Erdos634.Draft.Residue

#print axioms Erdos634.Draft.Residue.stack
#print axioms Erdos634.Draft.Residue.rtOC
#print axioms Erdos634.Draft.Residue.rtTB'
#print axioms Erdos634.Draft.Residue.mem_TB'
