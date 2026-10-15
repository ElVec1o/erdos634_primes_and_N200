/-
Draft/OtherSpectraFull.lean -- the spectrum statements for the other shapes, on a real dissection.

Let `(a, b, c)` be a primitive `2π/3` triple (`gcd(a, b) = 1`, `c² = a² + ab + b²`) and let a triangle be cut into `N`
congruent copies of the tile with sides `K·(a, b, c)` (any scale `K > 0`).  Then, according to the shape of the target:
* `F₁ = (α, α+β, α+2β)`: `N = d w² (a + b)` whenever `b = d e²` with `d` squarefree;
* `F₂ = (2α, 2β, α+β)`: `N = (a + 2b)(2a + b) k²`;  `F₃ = (α, 2α, 3β)`: `N = 3(a + b)(a + 2b) k²`;
  `F₄ = (α, 2β, 2α+β)`: `N = (a + b)(2a + b) k²`;
* target similar to the tile: `N = n²`;
* equilateral target of side `K·S`: `ab ∣ S²`, `N = S²/(ab)`, `N` and `ab` have the same squarefree kernel, and
  `(c + a − b) ∣ 3S`, `(c + b − a) ∣ 3S`.

Assembly of existing theorems: `RSGWire.bridge_irr` (a real dissection gives a shape of the table, an integer scale and
the area equation), `FDDShapes.F1_scale`, `scalene_N0`, `equilateral_clauses`, `Row5.theoremE_twoPiThree` (the two
invariants on the equilateral boundary), and `shape_unique` below (the shape is determined by the target's angles).
The irrationality of `α/π` is derived from the triple (`RSGWire.irrPi_of_model`), not assumed.

No sorry, no native_decide.
-/
import Mathlib
import Erdos634.Draft.RSGWire
import Erdos634.Draft.FDDShapes
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.G3CF1nControl

open scoped Classical

namespace Erdos634.Draft.OtherSpectraFull

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.FDDShapes
  Erdos634.Draft.RSBSine Erdos634.Draft.RSBCorner Erdos634.Draft.RSBArea Erdos634.Draft.RSGWire

variable {N : ℕ}

/-- two shapes whose corner triples have the same entries are equal -/
theorem shape_eq_of_triples : ∀ s s' : Shape, (∀ j, ∃ i, s.triple j = s'.triple i) →
    (∀ i, ∃ j, s'.triple i = s.triple j) → s = s' := by decide

/-- **The shape of the table is determined by the target's angles.** -/
theorem shape_unique (D : CongruentDissection N) {α : ℝ} (hα : IrrPi α) (s s' : Shape)
    (σ σ' : Equiv.Perm (Fin 3))
    (h : ∀ j, D.target.angleAt (σ j) = (s.triple j).1 * α + (s.triple j).2 * (Real.pi / 3))
    (h' : ∀ j, D.target.angleAt (σ' j) = (s'.triple j).1 * α + (s'.triple j).2 * (Real.pi / 3)) :
    s = s' := by
  refine shape_eq_of_triples s s' ?_ ?_
  · intro j
    obtain ⟨i, hi⟩ := σ'.surjective (σ j)
    refine ⟨i, ?_⟩
    have h1 := h j
    have h2 := h' i
    rw [hi] at h2
    obtain ⟨e1, e2⟩ := pair_unique hα _ _ _ _ (h1.symm.trans h2)
    exact Prod.ext e1 e2
  · intro i
    obtain ⟨j, hj⟩ := σ.surjective (σ' i)
    refine ⟨j, ?_⟩
    have h1 := h' i
    have h2 := h j
    rw [hj] at h2
    obtain ⟨e1, e2⟩ := pair_unique hα _ _ _ _ (h1.symm.trans h2)
    exact Prod.ext e1 e2

/-- target angles `x, y, z` (in some order) in the form of a corner triple -/
theorem triple_of_tgt (D : CongruentDissection N) {α x y z : ℝ} (s' : Shape) (h : TgtAngles D x y z)
    (h0 : x = (s'.triple 0).1 * α + (s'.triple 0).2 * (Real.pi / 3))
    (h1 : y = (s'.triple 1).1 * α + (s'.triple 1).2 * (Real.pi / 3))
    (h2 : z = (s'.triple 2).1 * α + (s'.triple 2).2 * (Real.pi / 3)) :
    ∃ σ' : Equiv.Perm (Fin 3),
      ∀ j, D.target.angleAt (σ' j) = (s'.triple j).1 * α + (s'.triple j).2 * (Real.pi / 3) := by
  obtain ⟨σ', a0, a1, a2⟩ := h
  refine ⟨σ', fun j => ?_⟩
  fin_cases j
  · exact a0.trans h0
  · exact a1.trans h1
  · exact a2.trans h2

/-- the bridge, with the shape identified from the target's angles -/
theorem bridge_named (D : CongruentDissection N) {α K : ℝ} (hK : 0 < K) (a b c : ℕ)
    (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hm : D.model.TwoPiThreeData α (K * a) (K * b) (K * c)) (s' : Shape)
    (h' : ∃ σ' : Equiv.Perm (Fin 3),
      ∀ j, D.target.angleAt (σ' j) = (s'.triple j).1 * α + (s'.triple j).2 * (Real.pi / 3)) :
    ∃ (σ : Equiv.Perm (Fin 3)) (k : ℕ), 0 < k ∧
      (∀ j, D.target.oppLen (σ j) = K * k * (s'.sideV a b c j)) ∧ s'.AreaEq a b k N := by
  obtain ⟨s, σ, k, hk, hang, hside, harea⟩ := bridge_irr D hK a b c hcop hc hm
  obtain ⟨σ', hσ'⟩ := h'
  have hs : s = s' := shape_unique D (irrPi_of_model D hK a b c hc hm) s s' σ σ' hang hσ'
  subst hs
  exact ⟨σ, k, hk, hside, harea⟩

/-- **`prop:otherspectra`.** -/
theorem otherspectra (D : CongruentDissection N) {α K : ℝ} (hK : 0 < K) (a b c : ℕ)
    (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hm : D.model.TwoPiThreeData α (K * a) (K * b) (K * c)) :
    (TgtAngles D α (α + (Real.pi / 3 - α)) (α + 2 * (Real.pi / 3 - α)) →
       ∀ d e : ℕ, b = d * e ^ 2 → Squarefree d → ∃ w : ℕ, 0 < w ∧ N = d * w ^ 2 * (a + b)) ∧
    (TgtAngles D (2 * α) (2 * (Real.pi / 3 - α)) (α + (Real.pi / 3 - α)) →
       ∃ k : ℕ, 0 < k ∧ N = (a + 2 * b) * (2 * a + b) * k ^ 2) ∧
    (TgtAngles D α (2 * α) (3 * (Real.pi / 3 - α)) →
       ∃ k : ℕ, 0 < k ∧ N = 3 * (a + b) * (a + 2 * b) * k ^ 2) ∧
    (TgtAngles D α (2 * (Real.pi / 3 - α)) (2 * α + (Real.pi / 3 - α)) →
       ∃ k : ℕ, 0 < k ∧ N = (a + b) * (2 * a + b) * k ^ 2) ∧
    (TgtAngles D α (Real.pi / 3 - α) (2 * Real.pi / 3) → ∃ n : ℕ, 0 < n ∧ N = n ^ 2) ∧
    ((∀ i, D.target.angleAt i = Real.pi / 3) →
       ∃ S : ℕ, 0 < S ∧ (∀ i, D.target.oppLen i = K * S) ∧ a * b ∣ S ^ 2 ∧ N = S ^ 2 / (a * b) ∧
         (∀ p : ℕ, N.factorization p % 2 = (a * b).factorization p % 2) ∧
         ((c : ℤ) + a - b) ∣ 3 * S ∧ ((c : ℤ) + b - a) ∣ 3 * S) := by
  obtain ⟨-, hcK, haK, hbK⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hb : 0 < b := by
    have : (0 : ℝ) < b := (pos_iff_pos_of_mul_pos hbK).mp hK
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- F₁
    intro ht d e hbde hd
    obtain ⟨σ, k, hk, -, harea⟩ := bridge_named D hK a b c hcop hc hm Shape.F1
      (triple_of_tgt D Shape.F1 ht (by simp [Shape.triple] <;> ring) (by simp [Shape.triple] <;> ring)
        (by simp [Shape.triple] <;> ring))
    have h : N * b = k ^ 2 * (a + b) := harea
    obtain ⟨w, hw, -, hN⟩ := F1_scale a b d e k N hb hcop hbde hd hk h
    exact ⟨w, hw, hN⟩
  · -- F₂
    intro ht
    obtain ⟨σ, k, hk, -, harea⟩ := bridge_named D hK a b c hcop hc hm Shape.F2
      (triple_of_tgt D Shape.F2 ht (by simp [Shape.triple] <;> ring) (by simp [Shape.triple] <;> ring)
        (by simp [Shape.triple] <;> ring))
    exact ⟨k, hk, (scalene_N0 a b k N).1.mp harea⟩
  · -- F₃
    intro ht
    obtain ⟨σ, k, hk, -, harea⟩ := bridge_named D hK a b c hcop hc hm Shape.F3
      (triple_of_tgt D Shape.F3 ht (by simp [Shape.triple] <;> ring) (by simp [Shape.triple] <;> ring)
        (by simp [Shape.triple] <;> ring))
    exact ⟨k, hk, (scalene_N0 a b k N).2.1.mp harea⟩
  · -- F₄
    intro ht
    obtain ⟨σ, k, hk, -, harea⟩ := bridge_named D hK a b c hcop hc hm Shape.F4
      (triple_of_tgt D Shape.F4 ht (by simp [Shape.triple] <;> ring) (by simp [Shape.triple] <;> ring)
        (by simp [Shape.triple] <;> ring))
    exact ⟨k, hk, (scalene_N0 a b k N).2.2.1.mp harea⟩
  · -- tile-similar
    intro ht
    obtain ⟨σ, k, hk, -, harea⟩ := bridge_named D hK a b c hcop hc hm Shape.tileSimilar
      (triple_of_tgt D Shape.tileSimilar ht (by simp [Shape.triple] <;> ring) (by simp [Shape.triple] <;> ring)
        (by simp [Shape.triple] <;> ring))
    exact ⟨k, hk, (scalene_N0 a b k N).2.2.2.mp harea⟩
  · -- equilateral
    intro hP
    obtain ⟨σ, k, hk, hside, harea⟩ := bridge_named D hK a b c hcop hc hm Shape.equilateral
      ⟨1, fun j => by
        simp only [Equiv.Perm.coe_one, id_eq]
        rw [hP]
        fin_cases j <;> simp [Shape.triple]⟩
    have hsides : ∀ i, D.target.oppLen i = K * k := by
      intro i
      obtain ⟨j, hj⟩ := σ.surjective i
      rw [← hj, hside j]
      fin_cases j <;> simp [Shape.sideV, Shape.sideVec]
    obtain ⟨s, t, -, -, -, -, -, -, hs, ht, -, -, -⟩ :=
      Row5.theoremE_twoPiThree D (irrPi_of_model D hK a b c hc hm) hm hP
    rw [hsides 0] at hs ht
    have hMa : s * ((c : ℤ) + a - b) = 3 * k := by
      have h1 : K * ((s : ℝ) * ((c : ℝ) + a - b)) = K * (3 * k) := by linear_combination hs
      have h2 := mul_left_cancel₀ hK.ne' h1
      exact_mod_cast h2
    have hMb : t * ((c : ℤ) + b - a) = 3 * k := by
      have h1 : K * ((t : ℝ) * ((c : ℝ) + b - a)) = K * (3 * k) := by linear_combination ht
      have h2 := mul_left_cancel₀ hK.ne' h1
      exact_mod_cast h2
    obtain ⟨h1, h2, h3, h4, h5⟩ := equilateral_clauses a b c N k hk harea s t hMa hMb
    exact ⟨k, hk, hsides, h1, h2, h3, h4, h5⟩

/-! ## Non-vacuity: the `F₁` clause on a real dissection -/

open Erdos634.Draft.G3CF1nControl in
open Erdos634.Draft.G3CF1n3240 (cert cert_len) in
/-- On the certified 3240-tiling of the `F₁` triangle `(135, 315, 360)` by the tile `(3, 5, 7)` the hypotheses of the
`F₁` clause hold, and the clause gives `3240 = 5 · w² · 8` (`w = 9`). -/
theorem otherspectra_F1_witness : ∃ w : ℕ, 0 < w ∧ (3240 : ℕ) = 5 * w ^ 2 * (3 + 5) := by
  have hm : D.model.TwoPiThreeData α (1890 * ((3 : ℕ) : ℝ)) (1890 * ((5 : ℕ) : ℝ)) (1890 * ((7 : ℕ) : ℝ)) := by
    exact_mod_cast data
  have ht : TgtAngles D α (α + (Real.pi / 3 - α)) (α + 2 * (Real.pi / 3 - α)) := by
    rcases f1_shape with h | h
    · exact h
    · exfalso
      -- the second shape `F₁'` has the angle `π/3 − α` where this target has `α`
      obtain ⟨τ, t0, t1, t2⟩ := h
      have h2 : D.target.angleAt 2 = α := G3CAng.angle_eq_of_cos 2 (σm 0) (t_cos2.trans cos_α.symm)
      have hs := D.target.angleAt_sum
      have hirr := α_irr
      have hpi := Real.pi_pos
      -- the three angles of the target are `α`, `π/3`, `2π/3 − α`; none equals `π/3 − α` or `π/3 + α` twice
      obtain ⟨i, hi⟩ := τ.surjective 2
      fin_cases i
      · -- angle `π/3 − α` = `α`: `α = π/6`
        have : D.target.angleAt (τ 0) = α := by rw [show τ 0 = 2 from hi]; exact h2
        rw [t0] at this
        exact hirr ⟨1 / 6, by push_cast; linarith⟩
      · have : D.target.angleAt (τ 1) = α := by rw [show τ 1 = 2 from hi]; exact h2
        rw [t1] at this
        exact hirr ⟨1 / 3, by push_cast; linarith⟩
      · have : D.target.angleAt (τ 2) = α := by rw [show τ 2 = 2 from hi]; exact h2
        rw [t2] at this
        linarith
  have h := (otherspectra D (K := 1890) (by norm_num) 3 5 7 (by norm_num) (by norm_num) hm).1 ht 5 1
    (by norm_num) (by
      have : Nat.Prime 5 := by norm_num
      exact this.prime.squarefree)
  rw [cert_len] at h
  exact h

end Erdos634.Draft.OtherSpectraFull

#print axioms Erdos634.Draft.OtherSpectraFull.otherspectra
#print axioms Erdos634.Draft.OtherSpectraFull.otherspectra_F1_witness
