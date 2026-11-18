/-
Draft/F1StripLemma.lean -- the **strip lemma** for the tiles `(a,b,c)` with `c^2 = a^2 + a b + b^2`
(Erdos #634), as a statement about tilings of the regions `T_m` and `S_m` of `F1StripGeom`.

THE LEMMA (this file proves it for all positive integers `A = a`, `B = b` and every unit `u > 0`; `c`
enters only through the tile: the model is the half-cell `cell1` with sides `u a`, `u b`,
`u sqrt(a^2+ab+b^2)`):

  If `T_k` is tiled by `k^2 b (a+b)` copies of the model and `S_{k+1}` by `(2k+1) b (a+b)` copies
  (any `k >= 1`; the hand proof states `k >= 2`), then `T_m` is tiled by `m^2 b (a+b)` copies for
  every `m >= k`.

PROOF (as in the hand proof).  `T_{m+1} = (T_m + (b,0)) ∪ S_{m+1}` (interiors separated by `p = b`);
`S_{m+1} = Π ∪ (S_m + (0,a+b))` for `m >= 1` (separated by `q = a+b`), where `Π` is the rectangle
`[0,b] x [0,a+b]` of `b (a+b)` unit cells, each cut by its diagonal into two tiles.

The unit `u` is there because the certificates live in `Z[sqrt3]` after scaling by 26.

CREDIT.  The family is Yan Zhang's (arXiv 2512.22696); strip decompositions: Laczkovich; nearest relative
in this project: the collar lemma (`Collar.lean`).  UNAUDITED beyond the internal build.
No sorry, no native_decide.
-/
import Erdos634.Draft.F1StripGeom

namespace Erdos634.Draft.F1StripLemma

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling Erdos634.Draft.F1StripGeom

noncomputable section

section rect
variable {a b : ℝ}

/-- the row `[0,n] x [0,1]` of `n` cells, `2n` tiles -/
theorem row_tiled (ha : 0 < a) (hb : 0 < b) :
    ∀ n : ℕ, 1 ≤ n → Tiled (rectR a b (n : ℝ) 1) (cell1 ha hb) (2 * n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simpa using cell_tiled ha hb
  | succ n hn ih =>
    have hsh := (cell_tiled ha hb).shift (psiPt a b (n : ℝ) 0)
    have hu := Tiled.union ih hsh (M := cell1 ha hb) (n := 2 * (n + 1)) ?_ (by ring)
    · refine hu.congr_set ?_
      ext x
      simp only [rectR, Set.mem_union, Set.mem_setOf_eq, pc_shift ha, qc_shift hb]
      push_cast
      constructor
      · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
        · exact ⟨h1, by linarith, h3, h4⟩
        · exact ⟨by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)], by linarith, by linarith, by linarith⟩
      · rintro ⟨h1, h2, h3, h4⟩
        rcases le_total (pc a x) n with h | h
        · exact Or.inl ⟨h1, h, h3, h4⟩
        · exact Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩
    · refine disj_of_sep (ch a b 1 0) (ch_linear_ne_zero ha hb (Or.inl (by norm_num))) (n : ℝ) ?_ ?_
      · intro x hx
        rw [ch_apply]
        have := hx.2.1
        linarith
      · intro x hx
        rw [ch_apply]
        have := hx
        simp only [rectR, Set.mem_setOf_eq, pc_shift ha, qc_shift hb] at this
        linarith [this.1]

/-- the rectangle `[0,n] x [0,k]`, `2 n k` tiles -/
theorem rect_tiled (ha : 0 < a) (hb : 0 < b) (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, 1 ≤ k → Tiled (rectR a b (n : ℝ) (k : ℝ)) (cell1 ha hb) (2 * n * k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simpa using row_tiled ha hb n hn
  | succ k hk ih =>
    have hsh := (row_tiled ha hb n hn).shift (psiPt a b 0 (k : ℝ))
    have hu := Tiled.union ih hsh (M := cell1 ha hb) (n := 2 * n * (k + 1)) ?_ (by ring)
    · refine hu.congr_set ?_
      ext x
      simp only [rectR, Set.mem_union, Set.mem_setOf_eq, pc_shift ha, qc_shift hb]
      push_cast
      constructor
      · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
        · exact ⟨h1, h2, h3, by linarith⟩
        · exact ⟨by linarith, by linarith, by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)], by linarith⟩
      · rintro ⟨h1, h2, h3, h4⟩
        rcases le_total (qc b x) k with h | h
        · exact Or.inl ⟨h1, h2, h3, h⟩
        · exact Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩
    · refine disj_of_sep (ch a b 0 1) (ch_linear_ne_zero ha hb (Or.inr (by norm_num))) (k : ℝ) ?_ ?_
      · intro x hx
        rw [ch_apply]
        have := hx.2.2.2
        linarith
      · intro x hx
        rw [ch_apply]
        have := hx
        simp only [rectR, Set.mem_setOf_eq, pc_shift ha, qc_shift hb] at this
        linarith [this.2.2.1]

end rect

/-- positivity of the real parameters -/
theorem real_pos {n : ℕ} (h : 0 < n) : (0 : ℝ) < n := Nat.cast_pos.mpr h

/-- the chart scale `u * A` -/
theorem scale_pos {A : ℕ} (hA : 0 < A) {u : ℝ} (hu : 0 < u) : 0 < u * (A : ℝ) :=
  mul_pos hu (real_pos hA)

section induction
variable {A B : ℕ} (hA : 0 < A) (hB : 0 < B) {u : ℝ} (hu : 0 < u)
include hA hB hu

/-- **The model tile**: the half-cell with sides `u A`, `u B`, `u sqrt(A²+AB+B²)`. -/
def model : Tri := cell1 (scale_pos hA hu) (scale_pos hB hu)

/-- **Π = [0,b] x [0,a+b]**: `b (a+b)` cells, `2 b (a+b)` tiles. -/
theorem pi_tiled :
    Tiled (rectR (u * A) (u * B) (B : ℝ) ((A : ℝ) + B)) (model hA hB hu) (2 * B * (A + B)) := by
  have h := rect_tiled (scale_pos hA hu) (scale_pos hB hu) B hB (A + B) (by omega)
  have e : (((A + B : ℕ)) : ℝ) = (A : ℝ) + B := by push_cast; ring
  rw [e] at h
  exact h

/-- the strips: `S_{m+1}` for `m ≥ 1` splits into `Π` and the translate of `S_m` -/
theorem strip_split (m : ℝ) (hm : 1 ≤ m) :
    stripR (u * A) (u * B) (A : ℝ) (B : ℝ) (m + 1) =
      rectR (u * A) (u * B) (B : ℝ) ((A : ℝ) + B) ∪
        {x | x + -psiPt (u * A) (u * B) 0 ((A : ℝ) + B) ∈ stripR (u * A) (u * B) (A : ℝ) (B : ℝ) m} := by
  have ha := scale_pos hA hu
  have hb := scale_pos hB hu
  have hA' := real_pos hA
  have hB' := real_pos hB
  ext x
  simp only [rectR, stripR, Set.mem_union, Set.mem_setOf_eq, pc_shift ha, qc_shift hb]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_total (qc (u * B) x) ((A : ℝ) + B) with h | h
    · exact Or.inl ⟨h1, h2, h3, h⟩
    · refine Or.inr ⟨by linarith, by linarith, by linarith, ?_⟩
      nlinarith
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · refine ⟨by linarith, by linarith, by linarith, ?_⟩
      have e1 : ((A : ℝ) + B) * pc (u * A) x ≤ ((A : ℝ) + B) * B :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have e2 : (B : ℝ) * qc (u * B) x ≤ (B : ℝ) * ((A : ℝ) + B) :=
        mul_le_mul_of_nonneg_left h4 hB'.le
      have e3 : (1 : ℝ) * ((B : ℝ) * ((A : ℝ) + B)) ≤ m * ((B : ℝ) * ((A : ℝ) + B)) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      nlinarith
    · refine ⟨by linarith, by linarith, by linarith, ?_⟩
      nlinarith

/-- **Strips.**  From `S_{k+1}` tiled by `(2k+1) b (a+b)` tiles, every `S_{k+1+i}` is tiled by
`(2(k+i)+1) b (a+b)` tiles. -/
theorem strip_induction (k : ℕ) (hk : 1 ≤ k)
    (hS : Tiled (stripR (u * A) (u * B) (A : ℝ) (B : ℝ) ((k + 1 : ℕ) : ℝ)) (model hA hB hu)
      ((2 * k + 1) * (B * (A + B)))) :
    ∀ i : ℕ, Tiled (stripR (u * A) (u * B) (A : ℝ) (B : ℝ) ((k + 1 + i : ℕ) : ℝ)) (model hA hB hu)
      ((2 * (k + i) + 1) * (B * (A + B))) := by
  intro i
  induction i with
  | zero => simpa using hS
  | succ i ih =>
    have hsh := ih.shift (psiPt (u * A) (u * B) 0 ((A : ℝ) + B))
    have hm : (1 : ℝ) ≤ ((k + 1 + i : ℕ) : ℝ) := by
      have : 1 ≤ k + 1 + i := by omega
      exact_mod_cast this
    have hun := Tiled.union (pi_tiled hA hB hu) hsh (n := (2 * (k + (i + 1)) + 1) * (B * (A + B))) ?_
      (by ring)
    · refine hun.congr_set ?_
      have e : ((k + 1 + (i + 1) : ℕ) : ℝ) = ((k + 1 + i : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [e, strip_split hA hB hu _ hm]
    · exact disj_of_sep (ch (u * A) (u * B) 0 1)
        (ch_linear_ne_zero (scale_pos hA hu) (scale_pos hB hu) (Or.inr (by norm_num))) ((A : ℝ) + B)
        (fun x hx => by rw [ch_apply]; have := hx.2.2.2; linarith)
        (fun x hx => by
          rw [ch_apply]
          have := hx
          simp only [stripR, Set.mem_setOf_eq, pc_shift (scale_pos hA hu), qc_shift (scale_pos hB hu)]
            at this
          linarith [this.2.2.1])

/-- `T_{m+1} = (T_m + (b,0)) ∪ S_{m+1}` -/
theorem tri_split (m : ℝ) :
    triR (u * A) (u * B) (A : ℝ) (B : ℝ) (m + 1) =
      {x | x + -psiPt (u * A) (u * B) (B : ℝ) 0 ∈ triR (u * A) (u * B) (A : ℝ) (B : ℝ) m} ∪
        stripR (u * A) (u * B) (A : ℝ) (B : ℝ) (m + 1) := by
  have ha := scale_pos hA hu
  have hb := scale_pos hB hu
  have hA' := real_pos hA
  have hB' := real_pos hB
  ext x
  simp only [triR, stripR, Set.mem_union, Set.mem_setOf_eq, pc_shift ha, qc_shift hb]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases le_total (B : ℝ) (pc (u * A) x) with h | h
    · refine Or.inl ⟨by linarith, by linarith, ?_⟩
      nlinarith
    · exact Or.inr ⟨h1, h, h2, h3⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩)
    · refine ⟨by linarith, by linarith, ?_⟩
      nlinarith
    · exact ⟨h1, h3, h4⟩

/-- **THE STRIP LEMMA.**  If `T_k` is tiled by `k² b (a+b)` copies of the model and `S_{k+1}` by
`(2k+1) b (a+b)` copies, then `T_{k+i}` is tiled by `(k+i)² b (a+b)` copies, for all `i`. -/
theorem strip_lemma (k : ℕ) (hk : 1 ≤ k)
    (hT : Tiled (triR (u * A) (u * B) (A : ℝ) (B : ℝ) (k : ℝ)) (model hA hB hu) (k * k * (B * (A + B))))
    (hS : Tiled (stripR (u * A) (u * B) (A : ℝ) (B : ℝ) ((k + 1 : ℕ) : ℝ)) (model hA hB hu)
      ((2 * k + 1) * (B * (A + B)))) :
    ∀ i : ℕ, Tiled (triR (u * A) (u * B) (A : ℝ) (B : ℝ) ((k + i : ℕ) : ℝ)) (model hA hB hu)
      ((k + i) * (k + i) * (B * (A + B))) := by
  intro i
  induction i with
  | zero => simpa using hT
  | succ i ih =>
    have hsh := ih.shift (psiPt (u * A) (u * B) (B : ℝ) 0)
    have hSi := strip_induction hA hB hu k hk hS i
    have e : ((k + 1 + i : ℕ) : ℝ) = ((k + i : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e] at hSi
    have hun := Tiled.union hsh hSi (n := (k + (i + 1)) * (k + (i + 1)) * (B * (A + B))) ?_ (by ring)
    · refine hun.congr_set ?_
      have e2 : ((k + (i + 1) : ℕ) : ℝ) = ((k + i : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [e2, tri_split hA hB hu]
    · exact disj_of_sep (ch (u * A) (u * B) (-1) 0)
        (ch_linear_ne_zero (scale_pos hA hu) (scale_pos hB hu) (Or.inl (by norm_num))) (-(B : ℝ))
        (fun x hx => by
          rw [ch_apply]
          have := hx
          simp only [triR, Set.mem_setOf_eq, pc_shift (scale_pos hA hu), qc_shift (scale_pos hB hu)]
            at this
          linarith [this.1])
        (fun x hx => by rw [ch_apply]; have := hx.2.1; linarith)

end induction

end

end Erdos634.Draft.F1StripLemma

#print axioms Erdos634.Draft.F1StripLemma.strip_lemma
