/-
Draft/NSQF1.lean — F1/F1' (2π/3 tile, scalene target) with the PARITY of `Paper.cor_int`.
`AllNExclusion.F1Chk` quantifies over EVERY factorisation `N = Ma Mb` (`Ma > 1`) and demands `Ma ≡ Mb (mod 2)`; for odd N (and, via the
N ≡ 2 (4) shortcut, for N ≡ 2 mod 4) that is automatic, for N ≡ 0 (4) a mixed-parity factorisation (e.g. 152 = 1·152, 8·19, 19·8) makes the
check false although `cor_int` gives `Mα ≡ Mβ ≡ N (mod 2)`.  Here `f1_split` is redone keeping `Ma ≡ Mb ≡ N (2)`; `F1MaGt1par`,
`gapF1_of_MaGt1par`, `f1MaGt1par_of_list` are the parity-guarded forms.  No sorry, no native_decide.
-/
import Erdos634.Draft.F1KappaSide3

open scoped Classical

namespace Erdos634.Draft.NSQF1

open Erdos634.Geometry Erdos634.F1AlgebraReal Erdos634.Draft.F1AreaIdentity Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.Chain15

private lemma c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

/-- the output of the split, in the `Ma, Mb` integers. -/
private lemma split_core {N : ℕ} {Ma Mb : ℤ} {a b c μ : ℝ} (hpa : (2 : ℤ) ∣ Ma - N) (hpb : (2 : ℤ) ∣ Mb - N)
    (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ) (hca : a < c)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hN_b : (N : ℝ) * b = μ ^ 2 * (a + b))
    (hMa : (Ma : ℝ) * (c + a - b) = μ * (2 * a + b - c))
    (hMb : (Mb : ℝ) * (c + b - a) = μ * (2 * a + b + c)) :
    (c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b) ∨
    ∃ Ma' Mb' : ℕ, 1 < Ma' ∧ Ma' * Mb' = N ∧ Ma' % 2 = N % 2 ∧ Mb' % 2 = N % 2 ∧
      (Ma' : ℝ) * b = μ * (c - a) ∧ (Mb' : ℝ) * b = μ * (c + a) := by
  have hca_pos : 0 < c - a := by linarith
  have eMa : (Ma : ℝ) * b = μ * (c - a) := F1_Ma_real a b c μ Ma hc2 ha.ne' hMa
  have eMb : (Mb : ℝ) * b = μ * (c + a) := F1_Mb_real a b c μ Mb hc2 ha.ne' hMb
  have hMa_pos_R : 0 < (Ma : ℝ) := by
    have h : 0 < (Ma : ℝ) * b := by rw [eMa]; exact mul_pos hμ hca_pos
    rcases mul_pos_iff.mp h with ⟨h', _⟩ | ⟨_, h'⟩
    · exact h'
    · linarith
  have hMb_pos_R : 0 < (Mb : ℝ) := by
    have h : 0 < (Mb : ℝ) * b := by rw [eMb]; exact mul_pos hμ (by linarith)
    rcases mul_pos_iff.mp h with ⟨h', _⟩ | ⟨_, h'⟩
    · exact h'
    · linarith
  have hMa_Z : (0 : ℤ) < Ma := Int.cast_pos.mp hMa_pos_R
  have hMb_Z : (0 : ℤ) < Mb := Int.cast_pos.mp hMb_pos_R
  have hprod_R : (Ma : ℝ) * Mb = N :=
    F1_product_real a b c μ N Ma Mb hc2 ha.ne' hb.ne' hN_b hMa hMb
  have hprod_Z : Ma * Mb = ↑N := by exact_mod_cast hprod_R
  have hratio : (Mb : ℝ) * (c - a) = (Ma : ℝ) * (c + a) :=
    F1_ratio_real a b c μ Ma Mb hc2 ha.ne' hb.ne' hMa hMb
  have hMa_toNat : (Ma.toNat : ℤ) = Ma := Int.toNat_of_nonneg (le_of_lt hMa_Z)
  have hMb_toNat : (Mb.toNat : ℤ) = Mb := Int.toNat_of_nonneg (le_of_lt hMb_Z)
  have hprod_Nat : Ma.toNat * Mb.toNat = N := by
    have h : (Ma.toNat : ℤ) * Mb.toNat = N := by rw [hMa_toNat, hMb_toNat]; exact hprod_Z
    exact_mod_cast h
  rcases Nat.lt_or_ge 1 Ma.toNat with hgt | hle
  · right
    refine ⟨Ma.toNat, Mb.toNat, hgt, hprod_Nat, by omega, by omega, ?_, ?_⟩
    · rw [← hMa_toNat] at eMa; exact_mod_cast eMa
    · rw [← hMb_toNat] at eMb; exact_mod_cast eMb
  · left
    have h1 : Ma.toNat = 1 := by
      have : 0 < Ma.toNat := by omega
      omega
    have hMa1 : Ma = 1 := by
      have := hMa_toNat; rw [h1] at this; exact_mod_cast this.symm
    have hMbN : Mb = ↑N := by
      have : (1 : ℤ) * Mb = N := by rwa [hMa1] at hprod_Z
      omega
    have hMa1_R : (Ma : ℝ) = 1 := by exact_mod_cast hMa1
    have hMbN_R : (Mb : ℝ) = N := by exact_mod_cast hMbN
    have hkey : (N : ℝ) * (c - a) = c + a := by
      calc (N : ℝ) * (c - a) = (Mb : ℝ) * (c - a) := by rw [hMbN_R]
        _ = (Ma : ℝ) * (c + a) := hratio
        _ = 1 * (c + a) := by rw [hMa1_R]
        _ = c + a := by ring
    have hmu : μ * (c - a) = b := by
      have := eMa; rw [hMa1_R, one_mul] at this; linarith
    exact ⟨by linarith, hmu⟩

/-- **F1 split (any `N`), with the parity `Ma ≡ Mb ≡ N (mod 2)` of `cor_int`.** -/
theorem f1_split_par {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) (hμ : 0 < μ) :
    (c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b) ∨
    ∃ Ma Mb : ℕ, 1 < Ma ∧ Ma * Mb = N ∧ Ma % 2 = N % 2 ∧ Mb % 2 = N % 2 ∧
      (Ma : ℝ) * b = μ * (c - a) ∧ (Mb : ℝ) * b = μ * (c + a) := by
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  have hca : a < c := by
    have h2 : a ^ 2 < c ^ 2 := by nlinarith [mul_pos ha0 hb0]
    by_contra hle
    push Not at hle
    nlinarith [mul_le_mul hle hle hc0.le ha0.le]
  have hN_b : (N : ℝ) * b = μ ^ 2 * (a + b) := F1_area_identity D hm hF1 ha0 hb0 hμ
  obtain ⟨Mα, Mβ, hpα, hpβ, hcor_α, hcor_β⟩ := Paper.cor_int D hα hm
  have hWα := Row7.lemmaW_alpha D.target hα hF1
  have hWβ := Row7.lemmaW_beta D.target hα hF1
  rcases hWα with hα1 | hα2 <;> rcases hWβ with hβ1 | hβ2
  · exact split_core (by omega) (by omega) ha0 hb0 hμ hca hc2 hN_b (Ma := Mα) (Mb := Mβ)
      (hcor_α.symm.trans hα1) (hcor_β.symm.trans hβ1)
  · exact split_core (by omega) (by omega) ha0 hb0 hμ hca hc2 hN_b (Ma := Mα) (Mb := -Mβ)
      (hcor_α.symm.trans hα1) (by push_cast; linarith [hcor_β.symm.trans hβ2])
  · exact split_core (by omega) (by omega) ha0 hb0 hμ hca hc2 hN_b (Ma := -Mα) (Mb := Mβ)
      (by push_cast; linarith [hcor_α.symm.trans hα2]) (hcor_β.symm.trans hβ1)
  · exact split_core (by omega) (by omega) ha0 hb0 hμ hca hc2 hN_b (Ma := -Mα) (Mb := -Mβ)
      (by push_cast; linarith [hcor_α.symm.trans hα2])
      (by push_cast; linarith [hcor_β.symm.trans hβ2])

/-- **`F1MaGt1 N`** — the F1 pair branch with `Ma > 1`: a 2π/3 tile (`α ∉ ℚπ`) whose F1 target has invariants `Ma b = μ(c−a)`,
`Mb b = μ(c+a)` with natural `1 < Ma`, `Ma Mb = N` is impossible.  (By `f1_split` this is exactly what is missing from `GapF1 N`
beyond the `Ma = 1` pin that `F1FreeProofM.f1_free_Ma1` kills.) -/
def F1MaGt1par (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (α a b c μ : ℝ), IrrPi α → D.model.TwoPiThreeData α a b c →
    D.target.F1Data α a b c μ → 0 < μ → ∀ Ma Mb : ℕ, 1 < Ma → Ma * Mb = N → Ma % 2 = N % 2 → Mb % 2 = N % 2 →
      (Ma : ℝ) * b = μ * (c - a) → (Mb : ℝ) * b = μ * (c + a) → False

/-- **`GapF1 N` from `F1MaGt1 N`** (N > 6). -/
theorem gapF1_of_MaGt1par (N : ℕ) (h6 : 6 < N) (g : F1MaGt1par N) : GapF1 N := by
  intro D α a b c hirr hm hshape
  refine Erdos634.Draft.F1FreeProofM.f1_free_Ma1 D h6 hirr hm hshape ?_ ?_
  · intro μ hμ hF1
    rcases f1_split_par D hirr hm hF1 hμ with h | ⟨Ma, Mb, h1, hp, hpa, hpb, e1, e2⟩
    · exact h
    · exact (g D α a b c μ hirr hm hF1 hμ Ma Mb h1 hp hpa hpb e1 e2).elim
  · intro μ hμ hF1'
    have hirr' : IrrPi (Real.pi / 3 - α) := by
      intro ⟨q, hq⟩; apply hirr; exact ⟨1/3 - q, by push_cast; linarith⟩
    have hm' : D.model.TwoPiThreeData (Real.pi / 3 - α) b a c :=
      Erdos634.Geometry.twoPiThreeData_swap D.model hm
    rcases f1_split_par D hirr' hm' hF1' hμ with h | ⟨Ma, Mb, h1, hp, hpa, hpb, e1, e2⟩
    · exact h
    · exact (g D _ b a c μ hirr' hm' hF1' hμ Ma Mb h1 hp hpa hpb e1 e2).elim


/-! ## The pair list with parity -/

/-- **`F1MaGt1par N` from a finite list of admissible same-parity pairs** (`Ma ≡ Mb ≡ N mod 2` by `Paper.cor_int`). -/
theorem f1MaGt1par_of_list (N : ℕ)
    (hlist : ∀ Ma Mb : ℕ, 1 < Ma → Ma < Mb → Ma * Mb = N → Ma % 2 = N % 2 → Mb % 2 = N % 2 →
      ∃ κ : ℕ, 0 < κ ∧ Mb = Ma + 2 * κ ∧ ¬ IsSquare (((Ma : ℤ) + Mb) ^ 2 + 12 * (N : ℤ)) ∧
        Ma ^ 2 + Mb ^ 2 ≠ 4 * Ma * Mb) : F1MaGt1par N := by
  intro D α a b c μ hirr hm hF1 hμ Ma Mb h1 hp hpa hpb e1 e2
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hcA : a < c := by
    have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
    have h2 : a ^ 2 < c ^ 2 := by nlinarith [mul_pos ha0 hb0]
    by_contra hle
    push Not at hle
    nlinarith [mul_le_mul hle hle hc0.le ha0.le]
  have hlt : Ma < Mb := by
    have : (Ma : ℝ) * b < (Mb : ℝ) * b := by rw [e1, e2]; nlinarith
    have := lt_of_mul_lt_mul_right this hb0.le
    exact_mod_cast this
  obtain ⟨κ, hκ0, hκ, hns, hne⟩ := hlist Ma Mb h1 hlt hp hpa hpb
  exact Erdos634.Draft.F1KappaSide.f1_pair_false D hirr hm hF1 hμ Ma Mb κ (by omega) hκ0 hp hκ hns hne e1 e2

end Erdos634.Draft.NSQF1



#print axioms Erdos634.Draft.NSQF1.f1_split_par
#print axioms Erdos634.Draft.NSQF1.gapF1_of_MaGt1par
#print axioms Erdos634.Draft.NSQF1.f1MaGt1par_of_list
