/-
Draft/F1StripGeom.lean -- geometry of the "F1 strip lemma" (Erdos #634): the oblique chart, the regions
`T_m`, `S_m`, rectangles, the two half-cells, and the closure operations on tilings.

CONTEXT.  Let `(a,b,c)` be positive integers with `c^2 = a^2 + a b + b^2` (the tile has an angle of 120
degrees opposite `c`).  With `e = (1,0)`, `u = (cos 60, sin 60)` the plane gets the oblique coordinates
`x = p*a*e + q*b*u` (`pc`, `qc` below).  In them the triangle `T_m` with sides `m*a*b`, `m*b*c`,
`m*b*(a+b)` is `{p,q >= 0, (a+b)p + b q <= m b (a+b)}`, the strip `S_m` is the part of it with
`p <= b`, and the unit cell is `[0,1]^2`, cut by its diagonal `a e + b u` (length `c`) into two tiles.
This file contains no tile data and no induction; `F1StripLemma` has the lemma.

CREDIT.  The family (tile `(a,b,c)`, angle 2 pi/3, `T_m` with `m^2 b (a+b)` tiles) is Yan Zhang's
(arXiv 2512.22696); strip decompositions of this kind go back to Laczkovich; the nearest relative in this
project is the collar lemma (`Collar.lean`, `CollarInputs`).  Tilings of regions: `Draft/RegionTiling.lean`
(`RTiling`, `union`, `map`); half-plane disjointness: `CertGeom.interiors_disjoint_of_separating`
(re-proved here for sets).

UNAUDITED beyond the internal build.  No sorry, no native_decide.
-/
import Erdos634.Draft.RegionTiling
import Erdos634.SssCongruent
import Erdos634.CertGeom
import Erdos634.CertCoord

namespace Erdos634.Draft.F1StripGeom

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling

noncomputable section

/-! ### Real helpers -/

def r3 : ℝ := Real.sqrt 3

theorem r3_pos : 0 < r3 := Real.sqrt_pos.mpr (by norm_num)

theorem r3_ne : r3 ≠ 0 := r3_pos.ne'

theorem r3_sq : r3 * r3 = 3 := Real.mul_self_sqrt (by norm_num)

/-- the affine functional `v ↦ α v₀ + β v₁ + γ` -/
def afn (α β γ : ℝ) : Plane →ᵃ[ℝ] ℝ where
  toFun v := α * v 0 + β * v 1 + γ
  linear :=
    { toFun := fun w => α * w 0 + β * w 1
      map_add' := by intro w z; simp only [PiLp.add_apply]; ring
      map_smul' := by intro c w; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_vadd' := by
    intro v w
    simp only [vadd_eq_add, PiLp.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring

theorem afn_apply (α β γ : ℝ) (v : Plane) : afn α β γ v = α * v 0 + β * v 1 + γ := rfl

theorem afn_linear_ne_zero {α β : ℝ} (γ : ℝ) (h : α ≠ 0 ∨ β ≠ 0) : (afn α β γ).linear ≠ 0 := by
  intro hcon
  set e0 : Plane := EuclideanSpace.single 0 (1 : ℝ) with he0
  set e1 : Plane := EuclideanSpace.single 1 (1 : ℝ) with he1
  have hb00 : e0 0 = 1 := by simp [he0]
  have hb01 : e0 1 = 0 := by simp [he0]
  have hb10 : e1 0 = 0 := by simp [he1]
  have hb11 : e1 1 = 1 := by simp [he1]
  have h0 : (afn α β γ).linear e0 = 0 := by rw [hcon]; rfl
  have h1 : (afn α β γ).linear e1 = 0 := by rw [hcon]; rfl
  have eq0 : α * e0 0 + β * e0 1 = 0 := h0
  have eq1 : α * e1 0 + β * e1 1 = 0 := h1
  rw [hb00, hb01] at eq0
  rw [hb10, hb11] at eq1
  rcases h with h | h
  · exact h (by linarith)
  · exact h (by linarith)

/-- **Sets separated by a line have disjoint interiors** (the argument of
`CertGeom.interiors_disjoint_of_separating`, for arbitrary sets). -/
theorem disj_of_sep {A B : Set Plane} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ)
    (h1 : ∀ x ∈ A, f x ≤ c) (h2 : ∀ x ∈ B, c ≤ f x) :
    Disjoint (interior A) (interior B) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hxt : x ∈ A := interior_subset hx1
  have hxu : x ∈ B := interior_subset hx2
  have hxc : f x = c := le_antisymm (h1 x hxt) (h2 x hxu)
  set g : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane c - f with hg
  have hglin : g.linear ≠ 0 := by
    intro hcon
    apply hf
    have : (AffineMap.const ℝ Plane c).linear - f.linear = 0 := hcon
    have hzero : (AffineMap.const ℝ Plane c).linear = 0 := rfl
    rw [hzero, zero_sub, neg_eq_zero] at this
    exact this
  have hgx : g x = 0 := by simp [hg, hxc]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx1)
  obtain ⟨y, hy, hyneg⟩ := Erdos634.Geometry.exists_neg_near_of_affine_zero g hglin hgx hr
  have hyt : y ∈ A := hball hy
  have : c < f y := by
    have hgy : g y = c - f y := rfl
    rw [hgy] at hyneg
    linarith
  exact absurd (h1 y hyt) (not_le.mpr this)

/-! ### The oblique chart -/

/-- the `p`-coordinate: `x = p a e + q b u` -/
def pc (a : ℝ) (x : Plane) : ℝ := (x 0 - x 1 / r3) / a

/-- the `q`-coordinate -/
def qc (b : ℝ) (x : Plane) : ℝ := 2 * x 1 / (r3 * b)

/-- the point with chart coordinates `(p,q)` -/
def psiPt (a b p q : ℝ) : Plane := mkPt (p * a + q * b / 2) (q * b * r3 / 2)

/-- `d p + e q` as an affine functional of the plane -/
def ch (a b d e : ℝ) : Plane →ᵃ[ℝ] ℝ := afn (d / a) (-d / (a * r3) + 2 * e / (r3 * b)) 0

theorem ch_apply (a b d e : ℝ) (x : Plane) : ch a b d e x = d * pc a x + e * qc b x := by
  simp only [ch, afn_apply, pc, qc]
  ring

theorem ch_linear_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {d e : ℝ} (h : d ≠ 0 ∨ e ≠ 0) :
    (ch a b d e).linear ≠ 0 := by
  apply afn_linear_ne_zero
  have h3 := r3_pos
  by_cases hd : d = 0
  · right
    have he : e ≠ 0 := h.resolve_left (not_not.mpr hd)
    subst hd
    simp only [neg_zero, zero_div, zero_add]
    positivity
  · left
    exact div_ne_zero hd ha.ne'

section chart
variable {a b : ℝ}

theorem pc_psi (ha : 0 < a) (p q : ℝ) : pc a (psiPt a b p q) = p := by
  have h := r3_ne
  have h' := ha.ne'
  simp only [pc, psiPt, mkPt_zero, mkPt_one]
  field_simp
  ring

theorem qc_psi (hb : 0 < b) (p q : ℝ) : qc b (psiPt a b p q) = q := by
  have h := r3_ne
  have h' := hb.ne'
  simp only [qc, psiPt, mkPt_one]
  field_simp

theorem psi_chart (ha : 0 < a) (hb : 0 < b) (x : Plane) : psiPt a b (pc a x) (qc b x) = x := by
  have h := r3_ne
  have h1 := ha.ne'
  have h2 := hb.ne'
  refine PiLp.ext ?_
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · simp only [psiPt, pc, qc, mkPt_zero]
    field_simp
    ring
  · simp only [psiPt, pc, qc, mkPt_one]
    field_simp

theorem pc_add (a : ℝ) (x y : Plane) : pc a (x + y) = pc a x + pc a y := by
  simp only [pc, PiLp.add_apply]; ring

theorem qc_add (b : ℝ) (x y : Plane) : qc b (x + y) = qc b x + qc b y := by
  simp only [qc, PiLp.add_apply]; ring

theorem pc_neg (a : ℝ) (x : Plane) : pc a (-x) = - pc a x := by
  simp only [pc, PiLp.neg_apply]; ring

theorem qc_neg (b : ℝ) (x : Plane) : qc b (-x) = - qc b x := by
  simp only [qc, PiLp.neg_apply]; ring

theorem pc_shift (ha : 0 < a) (x : Plane) (p q : ℝ) :
    pc a (x + -psiPt a b p q) = pc a x - p := by
  rw [pc_add, pc_neg, pc_psi ha]; ring

theorem qc_shift (hb : 0 < b) (x : Plane) (p q : ℝ) :
    qc b (x + -psiPt a b p q) = qc b x - q := by
  rw [qc_add, qc_neg, qc_psi hb]; ring

end chart

/-! ### Regions -/

/-- the rectangle `0 ≤ p ≤ n`, `0 ≤ q ≤ k` -/
def rectR (a b n k : ℝ) : Set Plane :=
  {x | 0 ≤ pc a x ∧ pc a x ≤ n ∧ 0 ≤ qc b x ∧ qc b x ≤ k}

/-- the strip `S_m`: `0 ≤ p ≤ B`, `q ≥ 0`, `(A+B) p + B q ≤ m B (A+B)`.  Here `a`, `b` are the chart
scales (the edge lengths of the cell: `a = u A`, `b = u B` for a unit `u`) while `A`, `B` are the cell
counts (the integer shape of the tile). -/
def stripR (a b A B m : ℝ) : Set Plane :=
  {x | 0 ≤ pc a x ∧ pc a x ≤ B ∧ 0 ≤ qc b x ∧ (A + B) * pc a x + B * qc b x ≤ m * (B * (A + B))}

/-- the triangle `T_m`: `p, q ≥ 0`, `(A+B) p + B q ≤ m B (A+B)` -/
def triR (a b A B m : ℝ) : Set Plane :=
  {x | 0 ≤ pc a x ∧ 0 ≤ qc b x ∧ (A + B) * pc a x + B * qc b x ≤ m * (B * (A + B))}

/-! ### Tilings of regions -/

/-- `S` is tiled by `n` copies of `M` -/
def Tiled (S : Set Plane) (M : Tri) (n : ℕ) : Prop := Nonempty (RTiling S M n)

theorem Tiled.union {S₁ S₂ : Set Plane} {M : Tri} {n₁ n₂ n : ℕ} (h₁ : Tiled S₁ M n₁)
    (h₂ : Tiled S₂ M n₂) (hd : Disjoint (interior S₁) (interior S₂)) (hn : n = n₁ + n₂) :
    Tiled (S₁ ∪ S₂) M n := by
  obtain ⟨R₁⟩ := h₁
  obtain ⟨R₂⟩ := h₂
  subst hn
  exact ⟨Erdos634.Draft.RegionTiling.union R₁ R₂ hd⟩

theorem Tiled.congr_set {S S' : Set Plane} {M : Tri} {n : ℕ} (h : Tiled S M n) (e : S = S') :
    Tiled S' M n := e ▸ h

theorem Tiled.congr_count {S : Set Plane} {M : Tri} {n n' : ℕ} (h : Tiled S M n) (e : n = n') :
    Tiled S M n' := e ▸ h

theorem Tiled.remodel {S : Set Plane} {M M' : Tri} {n : ℕ} (h : Tiled S M n)
    (hM : M.Congruent M') : Tiled S M' n := by
  obtain ⟨R⟩ := h
  exact ⟨Erdos634.Draft.RegionTiling.remodel R hM⟩

/-- **Translation.**  The tiling of `S` moved by `-w`... stated as the preimage form
`{x | x + -w ∈ S}` (the image of `S` under `x ↦ x + w`). -/
theorem Tiled.shift {S : Set Plane} {M : Tri} {n : ℕ} (h : Tiled S M n) (w : Plane) :
    Tiled {x | x + -w ∈ S} M n := by
  obtain ⟨R⟩ := h
  have e : (IsometryEquiv.addRight w : Plane ≃ᵢ Plane) '' S = {x | x + -w ∈ S} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [IsometryEquiv.addRight] using hy
    · intro hx
      exact ⟨x + -w, hx, by simp [IsometryEquiv.addRight]⟩
  exact ⟨e ▸ Erdos634.Draft.RegionTiling.map R (IsometryEquiv.addRight w)⟩

/-! ### Chart coordinates of explicit points -/

theorem pc_mkPt (a x y : ℝ) : pc a (mkPt x y) = (x - y / r3) / a := by
  simp [pc]

theorem qc_mkPt (b x y : ℝ) : qc b (mkPt x y) = 2 * y / (r3 * b) := by
  simp [qc]

theorem coords {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : Plane) :
    x 0 = pc a x * a + qc b x * b / 2 ∧ x 1 = qc b x * b * r3 / 2 := by
  have h := psi_chart ha hb x
  constructor
  · have := congrArg (fun y : Plane => y 0) h
    simp only [psiPt, mkPt_zero] at this
    exact this.symm
  · have := congrArg (fun y : Plane => y 1) h
    simp only [psiPt, mkPt_one] at this
    exact this.symm

theorem mkPt_sub_mkPt (x y x' y' : ℝ) : mkPt x y - mkPt x' y' = mkPt (x - x') (y - y') := by
  refine PiLp.ext ?_
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> simp

/-! ### The two half-cells -/

section cells
variable {a b : ℝ}

/-- half-cell `(0, a e, a e + b u)`: sides `a`, `b`, `c`; the model tile of the lemma -/
def cell1 (ha : 0 < a) (hb : 0 < b) : Tri :=
  mkTri 0 0 a 0 (a + b / 2) (b * r3 / 2) (by
    have := r3_pos
    simp only [det3]
    have : 0 < a * (b * r3 / 2) := by positivity
    nlinarith)

/-- half-cell `(0, b u, a e + b u)` -/
def cell2 (ha : 0 < a) (hb : 0 < b) : Tri :=
  mkTri 0 0 (b / 2) (b * r3 / 2) (a + b / 2) (b * r3 / 2) (by
    have := r3_pos
    simp only [det3]
    have : 0 < a * (b * r3 / 2) := by positivity
    nlinarith)

theorem pc_c1_0 (ha : 0 < a) : pc a (mkPt 0 0) = 0 := by simp [pc_mkPt]
theorem qc_c1_0 (hb : 0 < b) : qc b (mkPt 0 0) = 0 := by simp [qc_mkPt]
theorem pc_c1_1 (ha : 0 < a) : pc a (mkPt a 0) = 1 := by
  have := ha.ne'
  simp [pc_mkPt, this]
theorem qc_c1_1 (hb : 0 < b) : qc b (mkPt a 0) = 0 := by simp [qc_mkPt]
theorem pc_c1_2 (ha : 0 < a) : pc a (mkPt (a + b / 2) (b * r3 / 2)) = 1 := by
  have := r3_ne
  simp only [pc_mkPt]; field_simp; ring
theorem qc_c1_2 (hb : 0 < b) : qc b (mkPt (a + b / 2) (b * r3 / 2)) = 1 := by
  have := r3_ne
  simp only [qc_mkPt]; field_simp
theorem pc_c2_1 (ha : 0 < a) (hb : 0 < b) : pc a (mkPt (b / 2) (b * r3 / 2)) = 0 := by
  have := r3_ne
  simp only [pc_mkPt]; field_simp; ring
theorem qc_c2_1 (hb : 0 < b) : qc b (mkPt (b / 2) (b * r3 / 2)) = 1 := by
  have := r3_ne
  simp only [qc_mkPt]; field_simp

/-- a point is in the carrier of `cell1` iff `0 ≤ q ≤ p ≤ 1` -/
theorem carrier_cell1 (ha : 0 < a) (hb : 0 < b) :
    (cell1 ha hb).carrier = {x | 0 ≤ qc b x ∧ qc b x ≤ pc a x ∧ pc a x ≤ 1} := by
  ext x
  constructor
  · intro hx
    have hv : ∀ k, 0 ≤ qc b ((cell1 ha hb).pts k) ∧
        qc b ((cell1 ha hb).pts k) ≤ pc a ((cell1 ha hb).pts k) ∧ pc a ((cell1 ha hb).pts k) ≤ 1 := by
      intro k
      fin_cases k
      · show 0 ≤ qc b (mkPt 0 0) ∧ qc b (mkPt 0 0) ≤ pc a (mkPt 0 0) ∧ pc a (mkPt 0 0) ≤ 1
        rw [pc_c1_0 ha, qc_c1_0 hb]; norm_num
      · show 0 ≤ qc b (mkPt a 0) ∧ qc b (mkPt a 0) ≤ pc a (mkPt a 0) ∧ pc a (mkPt a 0) ≤ 1
        rw [pc_c1_1 ha, qc_c1_1 hb]; norm_num
      · show 0 ≤ qc b (mkPt (a + b / 2) (b * r3 / 2)) ∧
          qc b (mkPt (a + b / 2) (b * r3 / 2)) ≤ pc a (mkPt (a + b / 2) (b * r3 / 2)) ∧
          pc a (mkPt (a + b / 2) (b * r3 / 2)) ≤ 1
        rw [pc_c1_2 ha, qc_c1_2 hb]; norm_num
    have h1 := Erdos634.CertGeom.le_of_forall_pts_le (t := cell1 ha hb) (ch a b 0 (-1)) (c := 0)
      (fun k => by
        rw [ch_apply]
        obtain ⟨g1, _, _⟩ := hv k
        linarith) x hx
    have h2 := Erdos634.CertGeom.le_of_forall_pts_le (t := cell1 ha hb) (ch a b (-1) 1) (c := 0)
      (fun k => by
        rw [ch_apply]
        obtain ⟨_, g2, _⟩ := hv k
        linarith) x hx
    have h3 := Erdos634.CertGeom.le_of_forall_pts_le (t := cell1 ha hb) (ch a b 1 0) (c := 1)
      (fun k => by
        rw [ch_apply]
        obtain ⟨_, _, g3⟩ := hv k
        linarith) x hx
    rw [ch_apply] at h1 h2 h3
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    set p := pc a x with hp
    set q := qc b x with hq
    refine Erdos634.CertGeom.mem_carrier_of_combo _ x ![1 - p, p - q, q] ?_ ?_ ?_
    · show (1 - p) + (p - q) + q = 1
      ring
    · intro k
      fin_cases k
      · show 0 ≤ 1 - p
        linarith
      · show 0 ≤ p - q
        linarith
      · show 0 ≤ q
        linarith
    · obtain ⟨c0, c1⟩ := coords ha hb x
      refine PiLp.ext ?_
      intro i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · show x 0 = (1 - p) * (mkPt 0 0 : Plane) 0 + (p - q) * (mkPt a 0 : Plane) 0 +
          q * (mkPt (a + b / 2) (b * r3 / 2) : Plane) 0
        simp only [mkPt_zero]
        rw [c0]; ring
      · show x 1 = (1 - p) * (mkPt 0 0 : Plane) 1 + (p - q) * (mkPt a 0 : Plane) 1 +
          q * (mkPt (a + b / 2) (b * r3 / 2) : Plane) 1
        simp only [mkPt_one]
        rw [c1]; ring

/-- a point is in the carrier of `cell2` iff `0 ≤ p ≤ q ≤ 1` -/
theorem carrier_cell2 (ha : 0 < a) (hb : 0 < b) :
    (cell2 ha hb).carrier = {x | 0 ≤ pc a x ∧ pc a x ≤ qc b x ∧ qc b x ≤ 1} := by
  ext x
  constructor
  · intro hx
    have hv : ∀ k, 0 ≤ pc a ((cell2 ha hb).pts k) ∧
        pc a ((cell2 ha hb).pts k) ≤ qc b ((cell2 ha hb).pts k) ∧ qc b ((cell2 ha hb).pts k) ≤ 1 := by
      intro k
      fin_cases k
      · show 0 ≤ pc a (mkPt 0 0) ∧ pc a (mkPt 0 0) ≤ qc b (mkPt 0 0) ∧ qc b (mkPt 0 0) ≤ 1
        rw [pc_c1_0 ha, qc_c1_0 hb]; norm_num
      · show 0 ≤ pc a (mkPt (b / 2) (b * r3 / 2)) ∧
          pc a (mkPt (b / 2) (b * r3 / 2)) ≤ qc b (mkPt (b / 2) (b * r3 / 2)) ∧
          qc b (mkPt (b / 2) (b * r3 / 2)) ≤ 1
        rw [pc_c2_1 ha hb, qc_c2_1 hb]; norm_num
      · show 0 ≤ pc a (mkPt (a + b / 2) (b * r3 / 2)) ∧
          pc a (mkPt (a + b / 2) (b * r3 / 2)) ≤ qc b (mkPt (a + b / 2) (b * r3 / 2)) ∧
          qc b (mkPt (a + b / 2) (b * r3 / 2)) ≤ 1
        rw [pc_c1_2 ha, qc_c1_2 hb]; norm_num
    have h1 := Erdos634.CertGeom.le_of_forall_pts_le (t := cell2 ha hb) (ch a b (-1) 0) (c := 0)
      (fun k => by
        rw [ch_apply]
        obtain ⟨g1, _, _⟩ := hv k
        linarith) x hx
    have h2 := Erdos634.CertGeom.le_of_forall_pts_le (t := cell2 ha hb) (ch a b 1 (-1)) (c := 0)
      (fun k => by
        rw [ch_apply]
        obtain ⟨_, g2, _⟩ := hv k
        linarith) x hx
    have h3 := Erdos634.CertGeom.le_of_forall_pts_le (t := cell2 ha hb) (ch a b 0 1) (c := 1)
      (fun k => by
        rw [ch_apply]
        obtain ⟨_, _, g3⟩ := hv k
        linarith) x hx
    rw [ch_apply] at h1 h2 h3
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    set p := pc a x with hp
    set q := qc b x with hq
    refine Erdos634.CertGeom.mem_carrier_of_combo _ x ![1 - q, q - p, p] ?_ ?_ ?_
    · show (1 - q) + (q - p) + p = 1
      ring
    · intro k
      fin_cases k
      · show 0 ≤ 1 - q
        linarith
      · show 0 ≤ q - p
        linarith
      · show 0 ≤ p
        linarith
    · obtain ⟨c0, c1⟩ := coords ha hb x
      refine PiLp.ext ?_
      intro i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · show x 0 = (1 - q) * (mkPt 0 0 : Plane) 0 + (q - p) * (mkPt (b / 2) (b * r3 / 2) : Plane) 0 +
          p * (mkPt (a + b / 2) (b * r3 / 2) : Plane) 0
        simp only [mkPt_zero]
        rw [c0]; ring
      · show x 1 = (1 - q) * (mkPt 0 0 : Plane) 1 + (q - p) * (mkPt (b / 2) (b * r3 / 2) : Plane) 1 +
          p * (mkPt (a + b / 2) (b * r3 / 2) : Plane) 1
        simp only [mkPt_one]
        rw [c1]; ring

/-- the half-turn about the cell centre is an isometry carrying `cell1` onto `cell2` -/
theorem cell1_congruent_cell2 (ha : 0 < a) (hb : 0 < b) : (cell1 ha hb).Congruent (cell2 ha hb) := by
  refine ⟨IsometryEquiv.subLeft (mkPt (a + b / 2) (b * r3 / 2) : Plane), Equiv.swap 0 2, ?_⟩
  intro k
  fin_cases k
  · show (mkPt (a + b / 2) (b * r3 / 2) : Plane) - mkPt 0 0 = mkPt (a + b / 2) (b * r3 / 2)
    rw [mkPt_sub_mkPt]; congr 1 <;> ring
  · show (mkPt (a + b / 2) (b * r3 / 2) : Plane) - mkPt a 0 = mkPt (b / 2) (b * r3 / 2)
    rw [mkPt_sub_mkPt]; congr 1 <;> ring
  · show (mkPt (a + b / 2) (b * r3 / 2) : Plane) - mkPt (a + b / 2) (b * r3 / 2) = mkPt 0 0
    rw [mkPt_sub_mkPt]; congr 1 <;> ring

/-- **The unit cell** `[0,1]²` is tiled by the two half-cells. -/
theorem cell_tiled (ha : 0 < a) (hb : 0 < b) : Tiled (rectR a b 1 1) (cell1 ha hb) 2 := by
  have key : Disjoint (interior (cell1 ha hb).carrier) (interior (cell2 ha hb).carrier) := by
    refine disj_of_sep (ch a b (-1) 1) (ch_linear_ne_zero ha hb (Or.inl (by norm_num))) 0 ?_ ?_
    · intro x hx
      rw [carrier_cell1 ha hb] at hx
      rw [ch_apply]; obtain ⟨_, h2, _⟩ := hx; linarith
    · intro x hx
      rw [carrier_cell2 ha hb] at hx
      rw [ch_apply]; obtain ⟨_, h2, _⟩ := hx; linarith
  refine ⟨{ tile := ![cell1 ha hb, cell2 ha hb], covers := ?_, disj := ?_, cong := ?_ }⟩
  · ext x
    simp only [Set.mem_iUnion, Fin.exists_fin_two]
    show (x ∈ (cell1 ha hb).carrier ∨ x ∈ (cell2 ha hb).carrier) ↔ x ∈ rectR a b 1 1
    rw [carrier_cell1 ha hb, carrier_cell2 ha hb]
    simp only [rectR, Set.mem_setOf_eq]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨by linarith, h3, h1, by linarith⟩
      · exact ⟨h1, by linarith, by linarith, h3⟩
    · rintro ⟨h1, h2, h3, h4⟩
      rcases le_total (qc b x) (pc a x) with h | h
      · exact Or.inl ⟨h3, h, h2⟩
      · exact Or.inr ⟨h1, h, h4⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using key
    · simpa using key.symm
    · exact absurd rfl hij
  · intro i
    fin_cases i
    · exact Tri.Congruent.refl _
    · exact (cell1_congruent_cell2 ha hb).symm

end cells

end

end Erdos634.Draft.F1StripGeom

#print axioms Erdos634.Draft.F1StripGeom.cell_tiled
