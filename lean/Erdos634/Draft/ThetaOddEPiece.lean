-- Draft/ThetaOddEPiece.lean -- ODD-E formalization, module 8: hexagon pieces `HP`, builders for lattice parallelograms / triangles, hexagon join.
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
An `HP` is a tile family (`TFam`) over an image region `Phi '' S`, with `S` inside a hexagon of the chart (`HexS`).  `parPiece` is the
lattice parallelogram `Par` of `2 p q` cells (cell congruent to the tile by `Qc`), `triPiece` the lattice triangle of `k^2` cells;
a parallelogram with a zero cell count is the empty family.  `hexJoin` joins pieces with pairwise separated hexagons.
Credit: Beeson-Rosu (skew frame, lattice cells), the AI assistant's Theorem B pieces; the project.  INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddEChart

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)

theorem parC_hex (bx : OBx) (u0 v0 d1u d1v d2u d2v p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (c00 : ChartHex bx u0 v0) (c10 : ChartHex bx (u0 + p * d1u) (v0 + p * d1v))
    (c01 : ChartHex bx (u0 + q * d2u) (v0 + q * d2v))
    (c11 : ChartHex bx (u0 + p * d1u + q * d2u) (v0 + p * d1v + q * d2v)) :
    ∀ c ∈ Par (u0, v0) (d1u, d1v) (d2u, d2v) p q, ChartHex bx c.1 c.2 := by
  intro c hc
  have key : ∀ (u w γ : ℝ), u * u0 + w * v0 ≤ γ → u * (u0 + p * d1u) + w * (v0 + p * d1v) ≤ γ →
      u * (u0 + q * d2u) + w * (v0 + q * d2v) ≤ γ →
      u * (u0 + p * d1u + q * d2u) + w * (v0 + p * d1v + q * d2v) ≤ γ → u * c.1 + w * c.2 ≤ γ := by
    intro u w γ h00 h10 h01 h11
    refine Par_le (u0, v0) (d1u, d1v) (d2u, d2v) p q hp hq u w γ ?_ ?_ ?_ ?_ c hc
    · exact h00
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; exact h10
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; exact h01
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; exact h11
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := c00
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := c10
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := c01
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := c11
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := key (-1) 0 (-bx.ulo) (by linarith) (by linarith) (by linarith) (by linarith); linarith
  · have := key 1 0 bx.uhi (by linarith) (by linarith) (by linarith) (by linarith); linarith
  · have := key 0 (-1) (-bx.vlo) (by linarith) (by linarith) (by linarith) (by linarith); linarith
  · have := key 0 1 bx.vhi (by linarith) (by linarith) (by linarith) (by linarith); linarith
  · have := key (-1) (-1) (-bx.slo) (by linarith) (by linarith) (by linarith) (by linarith); linarith
  · have := key 1 1 bx.shi (by linarith) (by linarith) (by linarith) (by linarith); linarith

theorem pregC_hex (bx : OBx) (u0 v0 u1 v1 u2 v2 : ℝ)
    (c0 : ChartHex bx u0 v0) (c1 : ChartHex bx u1 v1) (c2 : ChartHex bx u2 v2) :
    ∀ c ∈ Preg (u0, v0) (u1, v1) (u2, v2) 0, ChartHex bx c.1 c.2 := by
  intro c hc
  have key : ∀ (u w γ : ℝ), u * u0 + w * v0 ≤ γ → u * u1 + w * v1 ≤ γ → u * u2 + w * v2 ≤ γ → u * c.1 + w * c.2 ≤ γ := by
    intro u w γ h0 h1 h2
    refine preg_le (u0, v0) (u1, v1) (u2, v2) 0 u w γ le_rfl zero_le_one ?_ ?_ ?_ ?_ c hc
    · simpa using h0
    · simpa using h0
    · exact h1
    · exact h2
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := c0
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := c1
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := c2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := key (-1) 0 (-bx.ulo) (by linarith) (by linarith) (by linarith); linarith
  · have := key 1 0 bx.uhi (by linarith) (by linarith) (by linarith); linarith
  · have := key 0 (-1) (-bx.vlo) (by linarith) (by linarith) (by linarith); linarith
  · have := key 0 1 bx.vhi (by linarith) (by linarith) (by linarith); linarith
  · have := key (-1) (-1) (-bx.slo) (by linarith) (by linarith) (by linarith); linarith
  · have := key 1 1 bx.shi (by linarith) (by linarith) (by linarith); linarith

/-- the empty family -/
def TFam.emptyN {S : Set Plane} {Mt : Erdos634.Geometry.Tri} {n : ℕ} (h : n = 0) : TFam S Mt n := by
  subst h
  exact ⟨fun i => i.elim0, fun i => i.elim0, by intro i; exact i.elim0, fun i => i.elim0⟩

/-- a tile family on (the image of) a subset of a chart hexagon -/
structure HP (φ : ℝ) (Mt : Erdos634.Geometry.Tri) (E F s M K : ℝ) where
  bx : OBx
  n : ℕ
  S : Set (ℝ × ℝ)
  T : TFam (Phi φ '' S) Mt n
  h : S ⊆ HexS E F s M K bx

/-- an `HP` with prescribed hexagon and tile count -/
abbrev HPs (φ : ℝ) (Mt : Erdos634.Geometry.Tri) (E F s M K : ℝ) (bx : OBx) (n : ℕ) : Type :=
  {P : HP φ Mt E F s M K // P.bx = bx ∧ P.n = n}

/-- the six admissible side-length patterns of a cell (as in `cong_cell_apex`) -/
def Pat6 (e f : ℕ) (x y z : ℝ) : Prop :=
  (x = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ y = (((e : ℝ) * f) ^ 2) ∧ z = (((f : ℝ) ^ 2) ^ 2)) ∨
  (x = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ y = (((f : ℝ) ^ 2) ^ 2) ∧ z = (((e : ℝ) * f) ^ 2)) ∨
  (x = (((e : ℝ) * f) ^ 2) ∧ y = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ z = (((f : ℝ) ^ 2) ^ 2)) ∨
  (x = (((e : ℝ) * f) ^ 2) ∧ y = (((f : ℝ) ^ 2) ^ 2) ∧ z = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2)) ∨
  (x = (((f : ℝ) ^ 2) ^ 2) ∧ y = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) ∧ z = (((e : ℝ) * f) ^ 2)) ∨
  (x = (((f : ℝ) ^ 2) ^ 2) ∧ y = (((e : ℝ) * f) ^ 2) ∧ z = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2))

/-- **lattice parallelogram piece**: `2 p q` cells (empty if `p = 0` or `q = 0`) -/
def parPiece {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) (hφE : φ = (f : ℝ) / e) (s M K : ℝ)
    (u0 v0 d1u d1v d2u d2v : ℝ) (p q : ℕ) (bx : OBx) (hdet : d1u * d2v - d2u * d1v ≠ 0) (X Y Z : ℝ)
    (hX : Qc e f d1u d1v = X) (hY : Qc e f (d2u - d1u) (d2v - d1v) = Y) (hZ : Qc e f d2u d2v = Z) (hp : Pat6 e f X Y Z)
    (hcorn : (0 : ℝ) < p → (0 : ℝ) < q → ChartHex bx u0 v0 ∧ ChartHex bx (u0 + p * d1u) (v0 + p * d1v) ∧
      ChartHex bx (u0 + q * d2u) (v0 + q * d2v) ∧ ChartHex bx (u0 + p * d1u + q * d2u) (v0 + p * d1v + q * d2v)) :
    HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K bx (2 * p * q) := by
  by_cases h0 : p = 0 ∨ q = 0
  · refine ⟨⟨bx, 2 * p * q, ∅, ?_, Set.empty_subset _⟩, rfl, rfl⟩
    exact castTF (by simp) rfl (TFam.emptyN (S := (∅ : Set Plane)) (by rcases h0 with h | h <;> simp [h]))
  · push_neg at h0
    have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero h0.1
    have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero h0.2
    have hE : (0 : ℝ) < e := by exact_mod_cast he
    have hEF : (e : ℝ) < f := by exact_mod_cast hef
    have hne : (chv (e : ℝ) f d1u d1v).1 * (chv (e : ℝ) f d2u d2v).2 - (chv (e : ℝ) f d2u d2v).1 * (chv (e : ℝ) f d1u d1v).2 ≠ 0 := by
      rw [chv_det hE hEF]; exact div_ne_zero hdet (chart_pos hE hEF).2.ne'
    have hdet' := det_cell_ne (E := (e : ℝ)) (F := f) s hE hEF (ch (e : ℝ) f M K u0 v0) (chv (e : ℝ) f d1u d1v) (chv (e : ℝ) f d2u d2v) hne
    have hc := cong_cell_apex hφ e f he hef hφE s (ch (e : ℝ) f M K u0 v0) (chv (e : ℝ) f d1u d1v) (chv (e : ℝ) f d2u d2v) hdet' X Y Z
      (by rw [ch_add_chv, qf_ch hE hEF]; convert hX using 2 <;> ring)
      (by rw [ch_add_chv, ch_add_chv, qf_ch hE hEF]; convert hY using 2 <;> ring)
      (by rw [ch_add_chv, qf_ch hE hEF]; convert hZ using 2 <;> ring) hp
    have T := parFam φ hφ _ _ _ p q hdet' (Mrow hφ e f he hef) hc
    refine ⟨⟨bx, 2 * p * q, (fun c : ℝ × ℝ => cH (e : ℝ) f s (ch (e : ℝ) f M K c.1 c.2)) '' Par (u0, v0) (d1u, d1v) (d2u, d2v) (p : ℝ) (q : ℝ),
      castTF (by rw [par_image]) rfl T, ?_⟩, rfl, rfl⟩
    obtain ⟨c00, c10, c01, c11⟩ := hcorn hpR hqR
    exact hexS_of_chart hE hEF s M K bx _ (parC_hex bx u0 v0 d1u d1v d2u d2v p q hpR hqR c00 c10 c01 c11)

/-- **lattice triangle piece**: `k^2` cells, apex `(u0,v0)`, legs to `(u1,v1)`, `(u2,v2)` -/
def triPiece {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) (hφE : φ = (f : ℝ) / e) (s M K : ℝ)
    (u0 v0 u1 v1 u2 v2 : ℝ) (k : ℕ) (hk : 0 < k) (bx : OBx)
    (hdet : (u1 - u0) * (v2 - v0) - (u2 - u0) * (v1 - v0) ≠ 0) (X Y Z : ℝ)
    (hX : Qc e f (u1 - u0) (v1 - v0) = (k : ℝ) ^ 2 * X) (hY : Qc e f (u2 - u1) (v2 - v1) = (k : ℝ) ^ 2 * Y)
    (hZ : Qc e f (u2 - u0) (v2 - v0) = (k : ℝ) ^ 2 * Z) (hp : Pat6 e f X Y Z)
    (hcorn : ChartHex bx u0 v0 ∧ ChartHex bx u1 v1 ∧ ChartHex bx u2 v2) :
    HPs φ (Mrow hφ e f he hef) (e : ℝ) f s M K bx (k * k) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  have hdetA : ((ch (e : ℝ) f M K u1 v1).1 - (ch (e : ℝ) f M K u0 v0).1) * ((ch (e : ℝ) f M K u2 v2).2 - (ch (e : ℝ) f M K u0 v0).2) -
      ((ch (e : ℝ) f M K u2 v2).1 - (ch (e : ℝ) f M K u0 v0).1) * ((ch (e : ℝ) f M K u1 v1).2 - (ch (e : ℝ) f M K u0 v0).2) ≠ 0 := by
    rw [ch_det hE hEF]; exact div_ne_zero hdet (chart_pos hE hEF).2.ne'
  have hc := cong_base_apex hφ e f he hef hφE s (ch (e : ℝ) f M K u0 v0) (ch (e : ℝ) f M K u1 v1) (ch (e : ℝ) f M K u2 v2) k hk (det_cH_ne s hE hEF _ _ _ hdetA) X Y Z
    (by rw [qf_ch hE hEF]; exact hX) (by rw [qf_ch hE hEF]; exact hY) (by rw [qf_ch hE hEF]; exact hZ) hp
  have T := ladderFam φ hφ _ _ _ k 0 hk (Nat.zero_le _) (det_cH_ne s hE hEF _ _ _ hdetA) (Mrow hφ e f he hef) hc
  refine ⟨⟨bx, k * k, (fun c : ℝ × ℝ => cH (e : ℝ) f s (ch (e : ℝ) f M K c.1 c.2)) '' Preg (u0, v0) (u1, v1) (u2, v2) 0,
    castTF (by simp only [Nat.cast_zero, zero_div]; rw [preg_image]) (by simp) T, ?_⟩, rfl, rfl⟩
  obtain ⟨c0, c1, c2⟩ := hcorn
  exact hexS_of_chart hE hEF s M K bx _ (pregC_hex bx u0 v0 u1 v1 u2 v2 c0 c1 c2)

/-- join `HP`s with pairwise separated hexagons inside a big hexagon -/
def hexJoin {φ : ℝ} {Mt : Erdos634.Geometry.Tri} {E F s M K : ℝ} (hE : 0 < E) (hEF : E < F) (hφ : 1 < φ) {m : ℕ}
    (ps : Fin m → HP φ Mt E F s M K) (big : OBx)
    (hsub : ∀ a, big.ulo ≤ (ps a).bx.ulo ∧ (ps a).bx.uhi ≤ big.uhi ∧ big.vlo ≤ (ps a).bx.vlo ∧ (ps a).bx.vhi ≤ big.vhi ∧
      big.slo ≤ (ps a).bx.slo ∧ (ps a).bx.shi ≤ big.shi)
    (hsep : ∀ a b, a ≠ b → OSep (ps a).bx (ps b).bx) : HP φ Mt E F s M K where
  bx := big
  n := ∑ a, (ps a).n
  S := HexS E F s M K big
  T := TFam.join (Phi φ '' HexS E F s M K big) (fun a => Phi φ '' (ps a).S) (fun a => (ps a).n) (fun a => (ps a).T)
    (fun a => Set.image_mono ((ps a).h.trans (hexS_mono (hsub a).1 (hsub a).2.1 (hsub a).2.2.1 (hsub a).2.2.2.1 (hsub a).2.2.2.2.1 (hsub a).2.2.2.2.2)))
    (fun a b hab => hexS_disj hE hEF s M K hφ (ps a).h (ps b).h (hsep a b hab))
  h := subset_rfl

/-- join with prescribed boxes and counts -/
def hexJoinF {φ : ℝ} {Mt : Erdos634.Geometry.Tri} {E F s M K : ℝ} (hE : 0 < E) (hEF : E < F) (hφ : 1 < φ) {m : ℕ}
    (bxs : Fin m → OBx) (ns : Fin m → ℕ) (ps : ∀ a, HPs φ Mt E F s M K (bxs a) (ns a)) (big : OBx)
    (hsub : ∀ a, big.ulo ≤ (bxs a).ulo ∧ (bxs a).uhi ≤ big.uhi ∧ big.vlo ≤ (bxs a).vlo ∧ (bxs a).vhi ≤ big.vhi ∧
      big.slo ≤ (bxs a).slo ∧ (bxs a).shi ≤ big.shi)
    (hsep : ∀ a b, a ≠ b → OSep (bxs a) (bxs b)) : HPs φ Mt E F s M K big (∑ a, ns a) := by
  refine ⟨hexJoin hE hEF hφ (fun a => (ps a).1) big ?_ ?_, rfl, ?_⟩
  · intro a; rw [(ps a).2.1]; exact hsub a
  · intro a b hab; rw [(ps a).2.1, (ps b).2.1]; exact hsep a b hab
  · show ∑ a, (ps a).1.n = ∑ a, ns a
    exact Finset.sum_congr rfl (fun a _ => (ps a).2.2)

end

end Erdos634.Draft.ThetaNotch
