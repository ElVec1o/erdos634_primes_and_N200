import Erdos634.Draft.ThmDStmt
import Erdos634.Draft.TheoremPConditional

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D', R9b (continued): `D1Spec -> ThmDStatement`  

The reduction of a `GPair` dissection (`Row4`: law of sines, `M(a+c) = X = M'(c-a)`) to the normal form of `thmD_of_D1_scaled`:
`(u,d,g)` from `pair_param` (`thmDChk_param`), the scale `s = a/u^2`, the model relabelled by `permTri` so that `alpha` sits at
vertex 0, `beta` at 1, `gamma` at 2, and the target relabelled by taking `i = 1` (target angles `alpha` at 0 and 1).
-/

open scoped Classical

namespace Erdos634.Draft.ThmD

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.ThmC Erdos634.SssCongruent Erdos634.Draft.TheoremPConditional

theorem perm_idx : ∀ (σ : Equiv.Perm (Fin 3)) (j : Fin 3),
    (σ (j + 1) = σ j + 1 ∧ σ (j + 2) = σ j + 2) ∨ (σ (j + 1) = σ j + 2 ∧ σ (j + 2) = σ j + 1) := by decide

theorem angleAt_permTri (U : Erdos634.Geometry.Tri) (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (permTri U σ).angleAt j = U.angleAt (σ j) := by
  unfold Tri.angleAt
  show cornerAngle (U.pts (σ (j + 1))) (U.pts (σ j)) (U.pts (σ (j + 2))) = _
  rcases perm_idx σ j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    unfold cornerAngle
    exact EuclideanGeometry.angle_comm _ _ _

theorem sideOpp_permTri (U : Erdos634.Geometry.Tri) (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    sideOpp (permTri U σ) j = U.oppLen (σ j) := by
  unfold sideOpp Tri.oppLen
  show dist (U.pts (σ (j + 1))) (U.pts (σ (j + 2))) = _
  rcases perm_idx σ j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, dist_comm]

theorem irrational_of_irrPi {α : ℝ} (h : IrrPi α) : Irrational (α / Real.pi) := by
  rintro ⟨q, hq⟩
  apply h
  refine ⟨q, ?_⟩
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hq]
  field_simp

/-- Theorem D' in the G-leaf format (identical to `ThmDLeaf.ThmDStatement`; restated here to keep this module light). -/
def GPairBody (N : ℕ) (M M' : ℤ) : Prop :=
  ∀ (D : CongruentDissection N) {α a b c : ℝ}, IrrPi α → D.model.TwoAlphaData α a b c →
    D.target.angleAt 0 = α → D.target.angleAt 1 = α →
    (M : ℝ) * (a + c) = D.target.oppLen 0 → (M' : ℝ) * (c - a) = D.target.oppLen 0 → False

/-- `GPair` of `GPairCert`, restated verbatim (the definition body) to keep this module free of `GPairCert`'s imports. -/
def ThmDStatement' : Prop :=
  ∀ (N M M' : ℕ), 0 < M → M * M' = N → 3 * M < M' → M % 2 = M' % 2 → thmDChk M M' → GPairBody N (M : ℤ) (M' : ℤ)

theorem thmDStatement_of_D1 (hD1 : D1Spec) : ThmDStatement' := by
  intro N M M' hM hMM' hlt hpar hchk
  obtain ⟨g, u, d, hg2, hd, hdu, hcop, hMg, hM'g, hcond⟩ := thmDChk_param hM hlt hpar hchk
  intro D α a b c hirrpi hdata hA hB hX1 hX2
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := hdata
  have hdata' : D.model.TwoAlphaData α a b c := ⟨σ, h0, o0, h1, o1, h2, o2⟩
  obtain ⟨κ, hκ1, hκ2, ha, hX, hc, hb, hY, hX1'⟩ := Row4.sides D hdata' hA hB
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hMR : ((M : ℤ) : ℝ) = (g : ℝ) * d := by rw [hMg]; push_cast; ring
  have hM'R : ((M' : ℤ) : ℝ) = (g : ℝ) * (u + (u + d)) := by rw [hM'g]; push_cast; ring
  rw [hMR] at hX1
  rw [hM'R] at hX2
  -- the ratio  u c = (u+d) a
  have hratio : (u : ℝ) * c = ((u : ℝ) + d) * a := by
    have e : (g : ℝ) * (((d : ℝ) * (a + c)) - ((u + (u + d)) * (c - a))) = 0 := by linear_combination hX1 - hX2
    have e2 := (mul_eq_zero.mp e).resolve_left hg0.ne'
    linear_combination (-1 / 2 : ℝ) * e2
  set s : ℝ := a / (u : ℝ) ^ 2 with hs
  have hspos : 0 < s := by positivity
  have has : a = s * ((u * u : ℕ) : ℝ) := by rw [hs]; push_cast; field_simp
  have hcs : c = s * ((u * (u + d) : ℕ) : ℝ) := by
    have : (u : ℝ) * c = (u : ℝ) * (s * ((u * (u + d) : ℕ) : ℝ)) := by
      rw [hratio, has]; push_cast; ring
    exact mul_left_cancel₀ hu0.ne' this
  have hab : a * b = c ^ 2 - a ^ 2 := by rw [hc, hb]; ring
  have hbs : b = s * ((d * (u + (u + d)) : ℕ) : ℝ) := by
    have : (s * (u : ℝ) ^ 2) * b = (s * (u : ℝ) ^ 2) * (s * ((d * (u + (u + d)) : ℕ) : ℝ)) := by
      have e1 : a = s * (u : ℝ) ^ 2 := by rw [has]; push_cast; ring
      have e2 : c = s * ((u : ℝ) * (u + d)) := by rw [hcs]; push_cast; ring
      rw [e1, e2] at hab
      push_cast
      linear_combination hab
    exact mul_left_cancel₀ (by positivity) this
  have hXs : D.target.oppLen 0 = s * ((g * u * (d * (u + (u + d))) : ℕ) : ℝ) := by
    rw [← hX1, has, hcs]; push_cast; ring
  -- the relabelled model
  have hα : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβ : 0 < Real.pi - 3 * α := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hcong : ∀ j, (permTri D.model σ).Congruent (D.tile j) :=
    fun j => (congruent_permTri D.model σ).trans (D.tiles_congruent j).symm
  have hA0 : cornerAngle ((permTri D.model σ).pts 1) ((permTri D.model σ).pts 0) ((permTri D.model σ).pts 2) = α := by
    have := angleAt_permTri D.model σ 0
    rw [h0] at this
    exact this
  have hA1 : cornerAngle ((permTri D.model σ).pts 2) ((permTri D.model σ).pts 1) ((permTri D.model σ).pts 0)
      = Real.pi - 3 * α := by
    have := angleAt_permTri D.model σ 1
    rw [h1] at this
    exact this
  have hA2 : cornerAngle ((permTri D.model σ).pts 0) ((permTri D.model σ).pts 2) ((permTri D.model σ).pts 1)
      = 2 * α := by
    have := angleAt_permTri D.model σ 2
    rw [h2] at this
    exact this
  have hs0 : sideOpp (permTri D.model σ) 0 = s * ((u * u : ℕ) : ℝ) := by
    rw [sideOpp_permTri, o0, has]
  have hs1 : sideOpp (permTri D.model σ) 1 = s * ((d * (u + (u + d)) : ℕ) : ℝ) := by
    rw [sideOpp_permTri, o1, hbs]
  have hs2 : sideOpp (permTri D.model σ) 2 = s * ((u * (u + d) : ℕ) : ℝ) := by
    rw [sideOpp_permTri, o2, hcs]
  have hC : D.target.angleAt 2 = Real.pi - 2 * α := by
    have hsum := D.target.angleAt_sum; rw [hA, hB] at hsum; linarith
  have h3α : 3 * α < Real.pi := by linarith
  have hirr := irrational_of_irrPi hirrpi
  have hL1 : dist (D.target.pts 1) (D.target.pts (1 + 1)) = s * ((g * u * (d * (u + (u + d))) : ℕ) : ℝ) := by
    rw [← hXs]; rfl
  have hL2 : dist (D.target.pts (1 + 1)) (D.target.pts (1 + 1 + 1)) = s * ((g * u * (d * (u + (u + d))) : ℕ) : ℝ) := by
    rw [← hXs, ← hX1']; rfl
  have hD1h := hD1 D.toDissection (permTri D.model σ) α 1 u d g s hcong hirr hA0 hA1 hA2 hα h3α hB hC hA
    hd (by omega) hcop hg2 hcond hspos hs0 hs1 hs2 hL1 hL2
  exact thmD_of_D1_scaled D.toDissection (permTri D.model σ) hcong α hirr hA0 hA1 hA2 hα h3α 1 hB hC hA
    hd (by omega) hcop hcond s hspos hs0 hs1 hs2 hL1 hL2 hD1h

#print axioms thmDStatement_of_D1
end Erdos634.Draft.ThmD
