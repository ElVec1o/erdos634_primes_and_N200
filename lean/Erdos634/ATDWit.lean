import Erdos634.ATDFinal
import Erdos634.B84Final
import Erdos634.Draft.FDCCevianAtom

/-!
# ATD witness: `atomDiv_L2_full` on the REAL 48-tile atom `A_4@(1,2)`, and negative controls  `AHyp e f X Y D` is, verbatim, the hypothesis list of `atomDiv_L2_full`
(after `D e f X Y`).  `FDCCevianAtom.atomTiles_four_scaled` is an exact `CongruentDissection` with target
sides `(12,24,24)` and model sides `(2,3,4)` (`48` tiles).  `witness_A4 : AHyp 1 2 24 12 D` (legs `24`, base
`12`, base angles `α+β`, `cos = 1/4`).  `atom_A4`: the theorem is applied, `μ = 12`, `3 ∣ 12`, `48 = 3·4²`.
Controls: `(1,3)` data unsatisfiable by this dissection; the perturbed base `Y = 13` unsatisfiable.
-/

namespace Erdos634.ATDL2
open Erdos634.Geometry Erdos634.BADL2
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)
open Erdos634.B84 (opp_of_hasSides opp_mem)

noncomputable section

def AHyp {N : ℕ} (e f : ℤ) (X Y : ℝ) (D : CongruentDissection N) : Prop :=
  ∃ σ τ : Equiv.Perm (Fin 3),
    D.model.oppLen (σ 0) = (e : ℝ) * f ∧
    D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
    D.model.oppLen (σ 2) = (f : ℝ) ^ 2 ∧
    D.target.angleAt (τ 0) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1) ∧
    D.target.angleAt (τ 1) = D.model.angleAt (σ 0) + D.model.angleAt (σ 1) ∧
    D.target.oppLen (τ 0) = X ∧ D.target.oppLen (τ 1) = X ∧ D.target.oppLen (τ 2) = Y

theorem apply_atom {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (h0 : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f) (X Y : ℝ) (h : AHyp e f X Y D) :
    ∃ μ : ℤ, X = (f : ℝ) * μ ∧ Y = (e : ℝ) * μ ∧ (f ^ 2 - e ^ 2) ∣ μ := by
  obtain ⟨σ, τ, l0, l1, l2, a0, a1, m0, m1, m2⟩ := h
  exact atomDiv_L2_full D e f h0 hef hcop X Y σ l0 l1 l2 τ a0 a1 m0 m1 m2

theorem angle_sum_perm (T : Tri) (ρ : Equiv.Perm (Fin 3)) :
    T.angleAt (ρ 0) + T.angleAt (ρ 1) + T.angleAt (ρ 2) = Real.pi := by
  have := Equiv.sum_comp ρ (fun k => T.angleAt k)
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
  linarith [T.angleAt_sum]

/-- the real atom: `∃ D`, `48` tiles, with all hypotheses of `atomDiv_L2_full` at `(1,2)`, `X=24`, `Y=12`. -/
theorem witness_A4 : ∃ D : CongruentDissection G3CAtomTiling.tiles.length,
    HasSides D.model 2 3 4 ∧ AHyp 1 2 24 12 D := by
  obtain ⟨D, h1, h2⟩ := Erdos634.Draft.FDCCevianAtom.atomTiles_four_scaled
  obtain ⟨ρ, l0, l1, l2⟩ := opp_of_hasSides D.model h2
  obtain ⟨ρ', k0, k1, k2⟩ := opp_of_hasSides D.target h1
  obtain ⟨c0, c1, c2⟩ := cos_laws_perm D.model ρ 2 3 4 l0 l1 l2
  obtain ⟨d0, d1, d2⟩ := cos_laws_perm D.target ρ' 12 24 24 k0 k1 k2
  have hs := angle_sum_perm D.model ρ
  obtain ⟨g0, g1⟩ := ang_bounds D.model (ρ 2)
  obtain ⟨p0, p1⟩ := ang_bounds D.target (ρ' 1)
  obtain ⟨q0, q1⟩ := ang_bounds D.target (ρ' 2)
  have hα : D.model.angleAt (ρ 0) + D.model.angleAt (ρ 1) = Real.pi - D.model.angleAt (ρ 2) := by
    linarith
  have hcm : Real.cos (D.model.angleAt (ρ 0) + D.model.angleAt (ρ 1)) = 1 / 4 := by
    rw [hα, Real.cos_pi_sub]; linarith
  have hb : Real.pi - D.model.angleAt (ρ 2) ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have hb' : D.model.angleAt (ρ 0) + D.model.angleAt (ρ 1) ∈ Set.Icc 0 Real.pi := by
    rw [hα]; exact hb
  have t1 : Real.cos (D.target.angleAt (ρ' 1)) = 1 / 4 := by linarith
  have t2 : Real.cos (D.target.angleAt (ρ' 2)) = 1 / 4 := by linarith
  refine ⟨D, h2, ρ, (finRotate 3).trans ρ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [l0]; norm_num
  · rw [l1]; norm_num
  · rw [l2]; norm_num
  · exact Real.injOn_cos ⟨p0, p1⟩ hb' (by rw [t1, hcm])
  · exact Real.injOn_cos ⟨q0, q1⟩ hb' (by rw [t2, hcm])
  · exact k1
  · exact k2
  · exact k0

/-- **Atom divisibility on a real object**: `X = 24 = 2 μ`, `Y = 12 = 1·μ`, `μ = 12`, `3 ∣ 12`,
and the integer corollary `48 = 3·4²`. -/
theorem atom_A4 : ∃ D : CongruentDissection G3CAtomTiling.tiles.length,
    AHyp 1 2 24 12 D ∧ ∃ μ : ℤ, μ = 12 ∧ ((2 : ℤ) ^ 2 - 1 ^ 2) ∣ μ ∧
      ∃ r : ℤ, ((G3CAtomTiling.tiles.length : ℕ) : ℤ) = ((2 : ℤ) ^ 2 - 1 ^ 2) * r ^ 2 := by
  obtain ⟨D, -, h⟩ := witness_A4
  obtain ⟨μ, hX, -, hd⟩ := apply_atom D 1 2 (by norm_num) (by norm_num) (by norm_num) 24 12 h
  have hμ : μ = 12 := by
    have : (24 : ℝ) = 2 * μ := by simpa using hX
    have : (24 : ℤ) = 2 * μ := by exact_mod_cast this
    omega
  refine ⟨D, h, μ, hμ, hd, ?_⟩
  have hl : ((G3CAtomTiling.tiles.length : ℕ) : ℤ) = 48 := by
    rw [Erdos634.G3CAtomTilingBridge.tiles_length_eq_48]; norm_num
  exact atom_count _ μ _ (by norm_num) hd (by rw [hl, hμ]; norm_num)

/-- **Control 1**: `(e,f) = (1,3)` data (model sides `(3,8,9)`) is unsatisfiable for any
dissection whose model has sides `2,3,4` (it demands a model side `8`). -/
theorem control_13 {N : ℕ} (D : CongruentDissection N) (hm : HasSides D.model 2 3 4)
    (X Y : ℝ) : ¬ AHyp 1 3 X Y D := by
  rintro ⟨σ, τ, l0, l1, l2, -⟩
  rcases opp_mem D.model hm (σ 1) with h | h | h <;>
  · rw [l1] at h; norm_num at h

/-- **Control 2**: on the real atom, the perturbed base `Y = 13` (legs `24`) violates the
theorem's conclusion `Y = e μ`, hence is not an `AHyp`. -/
theorem control_perturbed {N : ℕ} (D : CongruentDissection N) : ¬ AHyp 1 2 24 13 D := by
  intro h
  obtain ⟨μ, hX, hY, -⟩ := apply_atom D 1 2 (by norm_num) (by norm_num) (by norm_num) 24 13 h
  have h1 : (24 : ℝ) = 2 * μ := by simpa using hX
  have h2 : (13 : ℝ) = μ := by simpa using hY
  linarith

theorem controls_at_A4 : ∃ D : CongruentDissection G3CAtomTiling.tiles.length,
    AHyp 1 2 24 12 D ∧ (∀ X Y : ℝ, ¬ AHyp 1 3 X Y D) ∧ ¬ AHyp 1 2 24 13 D := by
  obtain ⟨D, hm, h⟩ := witness_A4
  exact ⟨D, h, control_13 D hm, control_perturbed D⟩

end

end Erdos634.ATDL2

#print axioms Erdos634.ATDL2.witness_A4
#print axioms Erdos634.ATDL2.atom_A4
#print axioms Erdos634.ATDL2.controls_at_A4
