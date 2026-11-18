/-
Draft/LeafFixS3.lean -- the corrected S3 leaf (base-alpha target (alpha, alpha, alpha+2 beta), tile with `ThreeAlphaData`).

`S3newChk N` : there is no coprime `0 < e < f` with `N = r^2 (f^2-e^2)(2f^2-e^2)` (`r` a positive integer).
`s3Closed_of_fix : 0 < N -> S3newChk N -> S3Closed N`.

Why it is stronger than the existing leaf (`AllNExclusionArith.S3Chk`, via `Row11.excluded_isoQRef_any_label`): that leaf only uses
the reduced Row-11 equation `N d = m^2 (2e+d) Q`; `ARA.theoremA_N_form_full` (paper `prop:basealphadiv`) adds `b | w`, i.e. `d | m`.
The two statements are NOT about different families: both are about a `CongruentDissection N` of the base-alpha target by the `3 alpha + 2 beta = pi` tile.
`theoremA_N_form_full` needs the model to have sides EXACTLY `(ef, f^2-e^2, f^2)`; here the model has sides `(a, b, c)` with `a = q c`, `b = (1-q^2) c`
(`Row11.rational_any_label`).  The rescaling wrapper `s3_scaled` is a similarity scaling by `f^2 / c` (`Realizable.scaleDissection`, a homothety:
angles preserved, sides multiplied) followed by `theoremA_N_form_full`.  No new geometry.

Credit: Beeson-Rosu (framework), Paliy, Laczkovich; `prop:basealphadiv` and `ARAForm` are project theorems.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.ARAForm
import Erdos634.Draft.Rows11_13AnyLabel
import Erdos634.Draft.ThmDScale
import Erdos634.Draft.CompositeGen2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.LeafFix

open Erdos634.Geometry Erdos634.Realizable Erdos634.TilePlacement Erdos634.Draft.CompositeGen2

/-- a homothety of positive ratio preserves the angles of target and model of a dissection -/
theorem angleAt_scale_gen {N : ℕ} (D : CongruentDissection N) (p : Plane) (r : ℝ) (hr : r ≠ 0) (hr0 : 0 < r) (k : Fin 3) :
    (scaleDissection p r hr D).target.angleAt k = D.target.angleAt k ∧
    (scaleDissection p r hr D).model.angleAt k = D.model.angleAt k := by
  constructor <;>
  · show cornerAngle _ _ _ = cornerAngle _ _ _
    simp only [scaleDissection_target_pts, scaleDissection_model_pts]
    exact Erdos634.Draft.ThmDRun.angle_homothety _ _ hr hr0 _ _ _

/-- a homothety of ratio `r > 0` multiplies the opposite sides of target and model by `r` -/
theorem oppLen_scale_gen {N : ℕ} (D : CongruentDissection N) (p : Plane) (r : ℝ) (hr : r ≠ 0) (hr0 : 0 < r) (k : Fin 3) :
    (scaleDissection p r hr D).target.oppLen k = r * D.target.oppLen k ∧
    (scaleDissection p r hr D).model.oppLen k = r * D.model.oppLen k := by
  constructor
  · show dist _ _ = r * dist _ _
    simp only [scaleDissection_target_pts]
    rw [homothetyEquiv_dist, abs_of_pos hr0]
  · show dist _ _ = r * dist _ _
    simp only [scaleDissection_model_pts]
    rw [homothetyEquiv_dist, abs_of_pos hr0]

/-- **The rescaling wrapper.**  A base-alpha dissection (any scale of the model) gives integers `e < f` coprime with `N = r^2 b Q`. -/
theorem s3_scaled {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) {t₀ t₁ : Fin 3} (ht : t₀ ≠ t₁)
    (hP0 : D.target.angleAt t₀ = α) (hP1 : D.target.angleAt t₁ = α) :
    ∃ e f r : ℤ, 0 < e ∧ e < f ∧ IsCoprime e f ∧
      (N : ℤ) = r ^ 2 * (f ^ 2 - e ^ 2) * (2 * f ^ 2 - e ^ 2) := by
  obtain ⟨q, ha, hb⟩ := Row11.rational_any_label D hα hrel h ht hP0 hP1
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have hapos : 0 < a := o0 ▸ D.model.oppLen_pos (σ 0)
  have hbpos : 0 < b := o1 ▸ D.model.oppLen_pos (σ 1)
  have hcpos : 0 < c := o2 ▸ D.model.oppLen_pos (σ 2)
  have hqR0 : (0 : ℝ) < q := by
    by_contra hneg
    push_neg at hneg
    have : (q : ℝ) * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hcpos.le
    linarith
  have hqR1 : (q : ℝ) < 1 := by
    by_contra hge
    push_neg at hge
    have : (1 - (q : ℝ) ^ 2) * c ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hcpos.le
    linarith
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hqR0
  have hqd : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
  have hden : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have he0 : 0 < q.num := Rat.num_pos.mpr hq0
  have hef : q.num < (q.den : ℤ) := by
    have h1' : (q.num : ℝ) / (q.den : ℝ) < 1 := hqd ▸ hqR1
    rw [div_lt_one hden] at h1'
    exact_mod_cast h1'
  have hcop : IsCoprime q.num (q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using q.reduced
  set e : ℤ := q.num with he
  set f : ℤ := (q.den : ℤ) with hf
  have hfR : (0 : ℝ) < (f : ℝ) := by simpa [hf] using hden
  have hqef : (q : ℝ) = (e : ℝ) / (f : ℝ) := by simpa [he, hf] using hqd
  -- scale so that the model has sides exactly (ef, f^2 - e^2, f^2)
  have hs : (0 : ℝ) < (f : ℝ) ^ 2 / c := by positivity
  set D' : CongruentDissection N := scaleDissection (D.target.pts 0) ((f : ℝ) ^ 2 / c) hs.ne' D with hD'
  have hang := fun k => angleAt_scale_gen D (D.target.pts 0) ((f : ℝ) ^ 2 / c) hs.ne' hs k
  have hlen := fun k => oppLen_scale_gen D (D.target.pts 0) ((f : ℝ) ^ 2 / c) hs.ne' hs k
  have l0 : D'.model.oppLen (σ 0) = (e : ℝ) * f := by
    rw [(hlen _).2, o0, ha, hqef]; field_simp
  have l1 : D'.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [(hlen _).2, o1, hb, hqef]; field_simp
  have l2 : D'.model.oppLen (σ 2) = (f : ℝ) ^ 2 := by
    rw [(hlen _).2, o2]; field_simp
  obtain ⟨τ, hτ0, hτ1⟩ := Row14AnyLabel.exists_perm t₀ t₁ ht
  have a0 : D'.target.angleAt (τ 0) = D'.model.angleAt (σ 0) := by
    rw [(hang _).1, (hang _).2, hτ0, hP0, h0]
  have a1 : D'.target.angleAt (τ 1) = D'.model.angleAt (σ 0) := by
    rw [(hang _).1, (hang _).2, hτ1, hP1, h0]
  -- equal base angles => equal opposite sides (law of sines)
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hsin : 0 < Real.sin α := by
    apply Real.sin_pos_of_pos_of_lt_pi hαpos
    linarith [Real.pi_pos]
  have hτne : τ 0 ≠ τ 1 := τ.injective.ne (by decide)
  have heq : D'.target.oppLen (τ 1) = D'.target.oppLen (τ 0) := by
    have hl := D'.target.lawSin (τ 0) (τ 1)
    have e0 : D'.target.angleAt (τ 0) = α := by rw [a0, (hang _).2, h0]
    have e1 : D'.target.angleAt (τ 1) = α := by rw [a1, (hang _).2, h0]
    rw [e0, e1] at hl
    exact mul_left_cancel₀ hsin.ne' hl
  have key := Erdos634.ARA.theoremA_N_form_full D' e f he0 hef hcop (D'.target.oppLen (τ 0))
    (D'.target.oppLen (τ 2)) σ l0 l1 l2 τ a0 a1 rfl heq rfl
  obtain ⟨r, hr⟩ := key
  exact ⟨e, f, r, he0, hef, hcop, hr⟩

/-- **The corrected S3 arithmetic leaf**: no coprime `1 <= e < f` with `b Q ∣ N` and `N / (b Q)` a perfect square.
(`b = f^2 - e^2`, `Q = 2 f^2 - e^2`; the guards `f <= sqrt N`, `f^3 <= N` hold automatically when `b Q ∣ N`, `N > 0`.) -/
def S3newChk (N : ℕ) : Prop :=
  ∀ f ≤ Nat.sqrt N, 2 ≤ f → f * f * f ≤ N → ∀ e < f, 1 ≤ e → Nat.Coprime e f →
    (f * f - e * e) * (2 * f * f - e * e) ∣ N →
    ¬ (Nat.sqrt (N / ((f * f - e * e) * (2 * f * f - e * e))) * Nat.sqrt (N / ((f * f - e * e) * (2 * f * f - e * e)))
        = N / ((f * f - e * e) * (2 * f * f - e * e)))

instance (N : ℕ) : Decidable (S3newChk N) := by unfold S3newChk; infer_instance

/-- **`S3Closed N` from the corrected leaf** (`N > 0`: a dissection has at least one tile; here supplied by the chain's `NQ`). -/
theorem s3Closed_of_fix (N : ℕ) (hN0 : 0 < N) (h : S3newChk N) : S3Closed N := by
  intro D α β a b c hα hrel hd t₀ t₁ ht h0 h1
  obtain ⟨e, f, r, he, hef, hcop, hN⟩ := s3_scaled D hα hrel hd ht h0 h1
  lift e to ℕ using he.le
  lift f to ℕ using (by omega)
  have he1 : 1 ≤ e := by exact_mod_cast he
  have hef' : e < f := by exact_mod_cast hef
  have hcop' : Nat.Coprime e f := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have := Int.isCoprime_iff_gcd_eq_one.mp hcop
    simpa [Int.gcd] using this
  have hf2 : 2 ≤ f := by omega
  set B : ℕ := (f * f - e * e) * (2 * f * f - e * e) with hB
  have hef2 : e * e ≤ f * f := Nat.mul_le_mul hef'.le hef'.le
  have hef3 : e * e ≤ 2 * f * f := by nlinarith
  have hBz : (B : ℤ) = ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) * (2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2) := by
    rw [hB]; push_cast [Nat.cast_sub hef2, Nat.cast_sub hef3]; ring
  have h2ff : 2 * f * f = 2 * (f * f) := by ring
  have hr2 : (r : ℤ) ^ 2 = ((r.natAbs : ℕ) : ℤ) ^ 2 := by
    rw [Int.natCast_natAbs, sq_abs]
  have hNz : (N : ℤ) = ((r.natAbs : ℕ) : ℤ) ^ 2 * (B : ℤ) := by
    rw [hBz, ← hr2]; linear_combination hN
  have hNn : N = r.natAbs ^ 2 * B := by exact_mod_cast hNz
  have hr0 : r.natAbs ≠ 0 := by
    intro hr; rw [hr] at hNn; simp at hNn; omega
  have hlt : e * e < f * f := Nat.mul_self_lt_mul_self hef'
  have hBpos : 0 < B := by
    have h1 : 0 < f * f - e * e := by omega
    have h2 : 0 < 2 * f * f - e * e := by omega
    rw [hB]; exact Nat.mul_pos h1 h2
  have hdvd : B ∣ N := ⟨r.natAbs ^ 2, by rw [hNn]; ring⟩
  have hdiv : N / B = r.natAbs ^ 2 := by
    rw [hNn, mul_comm]; exact Nat.mul_div_cancel_left _ hBpos
  -- guards: f^3 <= B <= N
  have hb1 : f ≤ f * f - e * e := by
    have hm : f * (e + 1) ≤ f * f := Nat.mul_le_mul_left f hef'
    have hm2 : e * e ≤ f * e := Nat.mul_le_mul_right e hef'.le
    have hm3 : f * (e + 1) = f * e + f := by ring
    omega
  have hb2 : f * f ≤ 2 * f * f - e * e := by omega
  have hf3 : f * f * f ≤ B := by
    rw [hB]
    calc f * f * f = f * (f * f) := by ring
      _ ≤ (f * f - e * e) * (2 * f * f - e * e) := Nat.mul_le_mul hb1 hb2
  have hBN : B ≤ N := Nat.le_of_dvd hN0 hdvd
  have hfs : f ≤ Nat.sqrt N := by
    apply Nat.le_sqrt.mpr
    have : f * f ≤ f * f * f := Nat.le_mul_of_pos_right _ (by omega)
    omega
  apply h f hfs hf2 (le_trans hf3 hBN) e hef' he1 hcop' (by rw [← hB]; exact hdvd)
  rw [← hB, hdiv]
  have : Nat.sqrt (r.natAbs ^ 2) = r.natAbs := by
    rw [sq]; exact Nat.sqrt_eq _
  rw [this]; ring

end Erdos634.Draft.LeafFix

#print axioms Erdos634.Draft.LeafFix.s3_scaled
#print axioms Erdos634.Draft.LeafFix.s3Closed_of_fix
