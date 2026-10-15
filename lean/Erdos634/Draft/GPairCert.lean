/-
The `γ = 2α` leaf (`CaseGClosed N`) from a table of pairs `(M, M')`, each closed separately.

`Row4.P5`: a dissection of an isosceles target with base angles `α` by the `γ = 2α` tile `(a, b, c)` gives integers
`M, M'` with `M M' = N`, `M ≡ M' ≡ N (mod 2)`, `3M < M'`, `M (a + c) = X = M' (c − a)` (`X` the leg of the target).
The pair pins the instance up to scale: `c/a = (M' + M)/(M' − M)`, `a b = c² − a²`, base `= X c / a`; in integers
tile `((M' − M)², 4 M M', (M' + M)(M' − M))`, target legs `2 M M' (M' − M)`, base `2 M M' (M' + M)`.

* `refute_scaled`: a refutation of (`TGT`, `MODEL`) refutes every dissection whose target and model are a common
  multiple `l` of side triples that determine `TGT` and `MODEL` up to congruence.
* `GPair N M M'`: the oriented `γ = 2α` statement for one pair.
* `caseG_of_pairs`: `CaseGClosed N` once the arithmetic of `N` confines `(M, M')` to a list and every pair of the list
  satisfies `GPair`.  (`GLK.caseG_of_leafOnly` is the case of the one-element list `[(2, 2(2k+1))]`.)
* `gPair_of_leafG`: the pairs `(2, 2(2k+1))`, `k ≥ 3`, by `GLI.leafG_of_dissection` (no certificate).
* `gPair_of_cert`: any pair from a refutation of its pinned instance at any scale.

No sorry, no native_decide.
-/
import Erdos634.Draft.GLKBridge
import Erdos634.Draft.HasSidesPerm
import Erdos634.Realizable

open scoped Classical

namespace Erdos634.Draft.GPairCert

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.ChainComposite
open Erdos634.Draft.FDBBaseBetaE1

/-- **Scaling a certificate.**  If the target of `D` has sides `l·(X, Y, Z)` and its model has sides `l·(x, y, z)`,
every triangle with sides `X, Y, Z` is congruent to `TGT` and every triangle with sides `x, y, z` to `MODEL`, then a
refutation of (`TGT`, `MODEL`) refutes `D`. -/
theorem refute_scaled {N : ℕ} (D : CongruentDissection N) (TGT MODEL : Erdos634.Geometry.Tri)
    (X Y Z x y z l : ℝ) (hl : 0 < l)
    (hT : HasSides D.target (X * l) (Y * l) (Z * l)) (hM : HasSides D.model (x * l) (y * l) (z * l))
    (cT : ∀ T : Erdos634.Geometry.Tri, HasSides T X Y Z → T.Congruent TGT)
    (cM : ∀ T : Erdos634.Geometry.Tri, HasSides T x y z → T.Congruent MODEL)
    (hno : ∀ D' : CongruentDissection N, D'.target.Congruent TGT → D'.model.Congruent MODEL → False) : False := by
  have hr : 0 < l⁻¹ := inv_pos.mpr hl
  have hrl : ∀ x : ℝ, l⁻¹ * (x * l) = x := fun x => by field_simp
  set D' := Erdos634.Realizable.scaleDissection 0 l⁻¹ hr.ne' D with hD'
  have tdist : ∀ i j, dist (D'.target.pts i) (D'.target.pts j) = l⁻¹ * dist (D.target.pts i) (D.target.pts j) := by
    intro i j
    rw [hD', Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.homothetyEquiv_dist, abs_of_pos hr]
  have mdist : ∀ i j, dist (D'.model.pts i) (D'.model.pts j) = l⁻¹ * dist (D.model.pts i) (D.model.pts j) := by
    intro i j
    rw [hD', Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.homothetyEquiv_dist, abs_of_pos hr]
  obtain ⟨τ, t1, t2, t3⟩ := hT
  obtain ⟨μ, m1, m2, m3⟩ := hM
  exact hno D'
    (cT _ ⟨τ, by rw [tdist, t1]; exact hrl X, by rw [tdist, t2]; exact hrl Y, by rw [tdist, t3]; exact hrl Z⟩)
    (cM _ ⟨μ, by rw [mdist, m1]; exact hrl x, by rw [mdist, m2]; exact hrl y, by rw [mdist, m3]; exact hrl z⟩)

/-- the oriented `γ = 2α` statement for one pair `(M, M')` of `Row4.P5` -/
def GPair (N : ℕ) (M M' : ℤ) : Prop :=
  ∀ (D : CongruentDissection N) {α a b c : ℝ}, IrrPi α → D.model.TwoAlphaData α a b c →
    D.target.angleAt 0 = α → D.target.angleAt 1 = α →
    (M : ℝ) * (a + c) = D.target.oppLen 0 → (M' : ℝ) * (c - a) = D.target.oppLen 0 → False

/-- **`CaseGClosed N` from a pair table.** -/
theorem caseG_of_pairs (N : ℕ) (L : List (ℤ × ℤ))
    (harith : ∀ M M' : ℤ, 0 < M → 0 < M' → (N : ℤ) = M * M' → (2 : ℤ) ∣ M - N → (2 : ℤ) ∣ M' - N →
      3 * M < M' → (M, M') ∈ L)
    (hL : ∀ p ∈ L, GPair N p.1 p.2) : CaseGClosed N :=
  Erdos634.GLK.caseG_of_oriented N (fun D _ _ _ _ hα h hA hB => by
    obtain ⟨M, M', hM, hM', hX1, hX2, hNM, hp, hp', hlt, -, -, -⟩ := Row4.P5 D hα h hA hB
    exact hL (M, M') (harith M M' hM hM' hNM hp hp' hlt) D hα h hA hB hX1 hX2)

/-- the pairs `(2, 2(2k+1))`, `k ≥ 3`: `GLI.leafG_of_dissection` (the argument of `GLK.caseG_oriented`) -/
theorem gPair_of_leafG (N k : ℕ) (hk : 3 ≤ k) : GPair N 2 (2 * (2 * (k : ℤ) + 1)) := by
  intro D α a b c hα h hA hB hX1 hX2
  obtain ⟨κ, -, -, ha, -, hcκ, hbκ, -, -⟩ := Row4.sides D h hA hB
  have hab : a * b = c ^ 2 - a ^ 2 := by rw [hcκ, hbκ]; ring
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  push_cast at hX1 hX2
  have hc : c = (k + 1) / k * a := by
    field_simp
    nlinarith [hX1, hX2]
  obtain ⟨s, hs0, has⟩ : ∃ s : ℝ, 0 < s ∧ a = s * (k : ℝ) ^ 2 :=
    ⟨a / (k : ℝ) ^ 2, by positivity, by field_simp⟩
  have hcs : c = s * (k * (k + 1)) := by rw [hc, has]; field_simp
  have hbs : b = s * (2 * k + 1) := by
    have h1 : (s * (k : ℝ) ^ 2) * (b - s * (2 * k + 1)) = 0 := by
      rw [hcs, has] at hab; linear_combination hab
    have h2 : s * (k : ℝ) ^ 2 ≠ 0 := by positivity
    have := (mul_eq_zero.mp h1).resolve_left h2
    linarith
  refine Erdos634.GLI.leafG_of_dissection D k hk hs0 has hbs hcs hα h hA hB ?_
  have hX : D.target.oppLen 0 = 2 * (a + c) := hX1.symm
  rw [show dist (D.target.pts 1) (D.target.pts 2) = D.target.oppLen 0 from rfl, hX, hcs, has]
  push_cast; ring

/-- **`GPair N M M'` from a certificate** of the pinned instance at any scale: tile `(x, y, z)` (opposite the angles
`α, π − 3α, 2α`) with `z (M' − M) = x (M' + M)`, `x y = z² − x²`; isosceles target with legs `X = M (x + z)` and base
`B = X z / x`. -/
theorem gPair_of_cert (N : ℕ) (M M' : ℤ) (hlt : M < M') (X B x y z : ℝ) (hx : 0 < x)
    (hz : z * ((M' : ℝ) - M) = x * ((M' : ℝ) + M)) (hy : x * y = z ^ 2 - x ^ 2)
    (hX : X = (M : ℝ) * (x + z)) (hBx : B * x = X * z)
    (TGT MODEL : Erdos634.Geometry.Tri)
    (cT : ∀ T : Erdos634.Geometry.Tri, HasSides T X X B → T.Congruent TGT)
    (cM : ∀ T : Erdos634.Geometry.Tri, HasSides T x y z → T.Congruent MODEL)
    (hno : ∀ D' : CongruentDissection N, D'.target.Congruent TGT → D'.model.Congruent MODEL → False) :
    GPair N M M' := by
  intro D α a b c hα h hA hB hX1 hX2
  obtain ⟨κ, -, -, ha, -, hcκ, hbκ, hYκ, hX01⟩ := Row4.sides D h hA hB
  have hab : a * b = c ^ 2 - a ^ 2 := by rw [hcκ, hbκ]; ring
  have hMM : (0 : ℝ) < (M' : ℝ) - M := by
    have : (M : ℝ) < M' := by exact_mod_cast hlt
    linarith
  have hca : c * ((M' : ℝ) - M) = a * ((M' : ℝ) + M) := by linear_combination hX2 - hX1
  set l := a / x with hldef
  have hl : 0 < l := div_pos ha hx
  have hax : a = x * l := by rw [hldef]; field_simp
  have hcz : c = z * l := by
    have h1 : (c - z * l) * ((M' : ℝ) - M) = 0 := by rw [hax] at hca; linear_combination hca - l * hz
    have := (mul_eq_zero.mp h1).resolve_right hMM.ne'
    linarith
  have hby : b = y * l := by
    have h1 : (x * l) * (b - y * l) = 0 := by rw [hax, hcz] at hab; linear_combination hab - l ^ 2 * hy
    have h2 : x * l ≠ 0 := (mul_pos hx hl).ne'
    have := (mul_eq_zero.mp h1).resolve_left h2
    linarith
  have h0 : D.target.oppLen 0 = X * l := by rw [← hX1, hX, hax, hcz]; ring
  have h1 : D.target.oppLen 1 = X * l := by rw [hX01, h0]
  have h2 : D.target.oppLen 2 = B * l := by
    have e : D.target.oppLen 2 * a = c * D.target.oppLen 0 := by rw [hYκ, hcκ]; ring
    rw [h0, hax, hcz] at e
    have h3 : (x * l) * (D.target.oppLen 2 - B * l) = 0 := by linear_combination e - l ^ 2 * hBx
    have := (mul_eq_zero.mp h3).resolve_left (mul_pos hx hl).ne'
    linarith
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := h
  exact refute_scaled D TGT MODEL X X B x y z l hl (hasSides_of_oppLen h0 h1 h2)
    (hasSides_of_sigma σ (by rw [o0, hax]) (by rw [o1, hby]) (by rw [o2, hcz])) cT cM hno

end Erdos634.Draft.GPairCert

#print axioms Erdos634.Draft.GPairCert.refute_scaled
#print axioms Erdos634.Draft.GPairCert.caseG_of_pairs
#print axioms Erdos634.Draft.GPairCert.gPair_of_leafG
#print axioms Erdos634.Draft.GPairCert.gPair_of_cert
