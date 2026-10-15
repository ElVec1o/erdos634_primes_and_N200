import Erdos634.Draft.CompositeE5Gen
import Erdos634.Draft.LemmaPProof
import Erdos634.Draft.GapE120Exc
import Erdos634.ReflS.MT30Sound
import Erdos634.Draft.N566076

/-! Draft/T30Cert.lean -- `GapE60 60` WITHOUT the axiom `no_T30_equilateral_60`, hence `60` is not a tile count.

The `π/3` pair `(30, 6)` of `N = 60` pins the tile to `l·(9+√21, 9−√21, 12)` and the equilateral target to side `60 l`
(`r6_arith` + law of cosines).  That instance is refuted by the kernel-checked certificate
`ReflS.MT30.not_dissection` (free-branch-point checker with coefficients in `ℤ[√21]`, 940 nodes).
`T30LPi3Close.e60_pair_30_6` proved the same statement from the axiom `no_T30_equilateral_60`; this file does NOT import
`T30LPi3Close` (the two axiom-free lemmas it needs, `r6_arith` and `pairs60_60_table`, are restated here), so no axiom
declaration is in the import closure of `not_tile_60`.

Composite-N result (`thm:frontier3`, row 60).  NOT prime-case work.  No sorry, no native_decide. -/

open scoped Classical
open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeE5Gen
open Erdos634.Draft.GapE120Exc

namespace Erdos634.Draft.T30Cert

/-- from `30(a+b-c) = 3S` and `6(a+b+c) = 3S`: `c = S/5`, `a+b = 3S/10` (copy of `Pi3Close.r6_arith`) -/
theorem r6_arith {a b c S : ℝ} (h1 : 30 * (a + b - c) = 3 * S) (h2 : 6 * (a + b + c) = 3 * S) :
    c = S / 5 ∧ a + b = 3 * S / 10 := ⟨by linarith, by linarith⟩

/-- the `π/3` pair table of `N = 60` (copy of `Pi3Close.pairs60_60_table`) -/
theorem pairs60_60_table : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ 60 → 1 ≤ m₂ → m₂ ≤ 60 →
    m₁ * m₂ = 3 * (60 : ℤ) → m₂ < m₁ →
    (m₁ = 60 ∧ m₂ = 3) ∨ (m₁ = 30 ∧ m₂ = 6) ∨
    (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (60 : ℤ)) ∧
      (0 ≤ (m₁ + m₂) ^ 2 - 16 * (60 : ℤ) →
        ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * (60 : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ hm1 hm1N hm2 hm2N hprod hlt
  -- Strategy: interval_cases on m₁; omega closes non-divisor cases;
  -- for the 7 pairs (60,3),(45,4),(36,5),(30,6),(20,9),(18,10),(15,12) use specific tactics.
  interval_cases m₁
  all_goals first
  | omega  -- no valid m₂ exists
  | (-- (60, 3): pin
     left; constructor <;> omega)
  | (-- (30, 6): exceptional T30 pair
     right; left; constructor <;> omega)
  | (-- (45, 4): D = 1441, 37²<1441<38²; linear: 120 ≠ p*49 + rr*41 for p,rr≥0
     right; right
     have hm2_eq : m₂ = 4 := by omega
     subst hm2_eq
     refine ⟨fun ⟨r, hr⟩ => ?_, fun _ p rr hp hrr => ?_⟩
     · have h76 : 76 * r ≤ 2885 := by nlinarith [mul_self_nonneg (r - 38)]
       have h76' : 76 * r ≥ -2885 := by nlinarith [mul_self_nonneg (r + 38)]
       nlinarith [mul_nonneg (show (0 : ℤ) ≤ 37 - r by omega) (show (0 : ℤ) ≤ 37 + r by omega)]
     · omega)
  | (-- (36, 5): D = 721, 26²<721<27²; linear: 120 ≠ p*41 + rr*31 for p,rr≥0
     right; right
     have hm2_eq : m₂ = 5 := by omega
     subst hm2_eq
     refine ⟨fun ⟨r, hr⟩ => ?_, fun _ p rr hp hrr => ?_⟩
     · have h54 : 54 * r ≤ 1457 := by nlinarith [mul_self_nonneg (r - 27)]
       have h54' : 54 * r ≥ -1457 := by nlinarith [mul_self_nonneg (r + 27)]
       nlinarith [mul_nonneg (show (0 : ℤ) ≤ 26 - r by omega) (show (0 : ℤ) ≤ 26 + r by omega)]
     · omega)
  | (-- (20, 9): D = (29²-960) = -119 < 0
     right; right
     have hm2_eq : m₂ = 9 := by omega
     subst hm2_eq
     refine ⟨fun ⟨r, hr⟩ => ?_, fun hD _ _ _ _ => ?_⟩
     · nlinarith [mul_self_nonneg r]
     · norm_num at hD)
  | (-- (18, 10): D = (28²-960) = -176 < 0
     right; right
     have hm2_eq : m₂ = 10 := by omega
     subst hm2_eq
     refine ⟨fun ⟨r, hr⟩ => ?_, fun hD _ _ _ _ => ?_⟩
     · nlinarith [mul_self_nonneg r]
     · norm_num at hD)
  | (-- (15, 12): D = (27²-960) = -231 < 0
     right; right
     have hm2_eq : m₂ = 12 := by omega
     subst hm2_eq
     refine ⟨fun ⟨r, hr⟩ => ?_, fun hD _ _ _ _ => ?_⟩
     · nlinarith [mul_self_nonneg r]
     · norm_num at hD)

open Erdos634.Geometry.GapE120Dis in
/-- **Closing a `π/3` exceptional pair by a certificate** (`SixtyData` version of `GapE120Exc.close_of_cert`).  If the pair equations force the tile to be `l·(·,·,z)` with
`{a, b} = {x l, y l}` and the target side to be `L l`, and no dissection of `TGT` (equilateral, side `L`) by `MODEL`
(sides `x, y, z` in vertex order `01, 12, 02`) exists, then no such dissection `D` exists. -/
theorem close_of_cert60 {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (h : D.model.SixtyData α a b c) (hE : Equilateral D)
    (TGT MODEL : Erdos634.Geometry.Tri) (L x y z l : ℝ) (hl : 0 < l)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = L ∧ dist (TGT.pts 1) (TGT.pts 2) = L ∧ dist (TGT.pts 0) (TGT.pts 2) = L)
    (hM : dist (MODEL.pts 0) (MODEL.pts 1) = x ∧ dist (MODEL.pts 1) (MODEL.pts 2) = y ∧
      dist (MODEL.pts 0) (MODEL.pts 2) = z)
    (hS : D.target.oppLen 0 = L * l) (hc : c = z * l)
    (hab : (b = x * l ∧ a = y * l) ∨ (a = x * l ∧ b = y * l))
    (hno : ∀ D' : CongruentDissection N, D'.target.Congruent TGT → D'.model.Congruent MODEL → False) : False := by
  have hα' : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi := hα
  have hr : 0 < l⁻¹ := inv_pos.mpr hl
  have hrl : ∀ x : ℝ, l⁻¹ * (x * l) = x := fun x => by field_simp
  set D' := Erdos634.Realizable.scaleDissection 0 l⁻¹ hr.ne' D with hD'
  obtain ⟨e1, e2, -⟩ := Row5.equilateral_boundary D hα' 0 (fun k => D.model.sixty_angles_mem hα' h 0 _ k) hE
  have d01 : dist (D.target.pts 0) (D.target.pts 1) = L * l := by
    rw [← hS, ← e2]; unfold Tri.oppLen; rfl
  have d12 : dist (D.target.pts 1) (D.target.pts 2) = L * l := by
    rw [← hS]; unfold Tri.oppLen; rfl
  have d02 : dist (D.target.pts 0) (D.target.pts 2) = L * l := by
    rw [← hS, ← e1, dist_comm]; unfold Tri.oppLen; rfl
  have tdist : ∀ i j, dist (D'.target.pts i) (D'.target.pts j) = l⁻¹ * dist (D.target.pts i) (D.target.pts j) := by
    intro i j
    rw [hD', Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.homothetyEquiv_dist, abs_of_pos hr]
  obtain ⟨g1, g2, g3⟩ := hT
  have hTc : D'.target.Congruent TGT :=
    Tri.congruent_of_dist _ _ (by rw [tdist, d01, g1]; exact hrl L) (by rw [tdist, d12, g2]; exact hrl L)
      (by rw [tdist, d02, g3]; exact hrl L)
  obtain ⟨σ, -, oa, -, ob, -, oc⟩ := h
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  rw [oa] at s1; rw [ob] at s2; rw [oc] at s3
  have hMc : D'.model.Congruent MODEL := by
    rcases hab with ⟨hb, ha⟩ | ⟨ha, hb⟩
    · refine cong_of_sides' D.model MODEL x y z hM l⁻¹ hr ((Equiv.swap (1 : Fin 3) 2).trans σ) ?_ ?_ ?_
      · have : ((Equiv.swap (1 : Fin 3) 2).trans σ) 0 = σ 0 := by simp [sw0]
        have h2 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 1 = σ 2 := by simp [sw1]
        rw [this, h2, s2, hb]; exact hrl x
      · have h1 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 1 = σ 2 := by simp [sw1]
        have h2 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 2 = σ 1 := by simp [sw2]
        rw [h1, h2, dist_comm, s1, ha]; exact hrl y
      · have h0 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 0 = σ 0 := by simp [sw0]
        have h2 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 2 = σ 1 := by simp [sw2]
        rw [h0, h2, s3, hc]; exact hrl z
    · refine cong_of_sides' D.model MODEL x y z hM l⁻¹ hr ((finRotate 3).trans σ) ?_ ?_ ?_
      · have h0 : ((finRotate 3).trans σ) 0 = σ 1 := by simp [fr0]
        have h1 : ((finRotate 3).trans σ) 1 = σ 2 := by simp [fr1]
        rw [h0, h1, s1, ha]; exact hrl x
      · have h1 : ((finRotate 3).trans σ) 1 = σ 2 := by simp [fr1]
        have h2 : ((finRotate 3).trans σ) 2 = σ 0 := by simp [fr2]
        rw [h1, h2, dist_comm, s2, hb]; exact hrl y
      · have h0 : ((finRotate 3).trans σ) 0 = σ 1 := by simp [fr0]
        have h2 : ((finRotate 3).trans σ) 2 = σ 0 := by simp [fr2]
        rw [h0, h2, dist_comm, s3, hc]; exact hrl z
  exact hno D' hTc hMc

/-- **`E60Pair 60 30 6`**, from the certificate. -/
theorem e60_pair_30_6_cert : E60Pair 60 30 6 := by
  intro D α a b c hα hS hE hm1 hm2
  have hSD := hS
  obtain ⟨σ, hα0, oa, hβ0, ob, hγ0, oc⟩ := hS
  set S := D.target.oppLen 0 with hSdef
  have ⟨hc_eq, hab_eq⟩ := r6_arith hm1 hm2
  have hc_pos : 0 < c := oc ▸ D.model.oppLen_pos (σ 2)
  have hS_pos : 0 < S := by linarith [hc_eq]
  have hcos_eq : c ^ 2 = a ^ 2 + b ^ 2 - a * b := by
    have hl := D.model.lawCos_perm σ
    rw [oa, ob, oc, hγ0, Real.cos_pi_div_three] at hl
    linarith
  have hab_prod : a * b = S ^ 2 / 60 := by
    have hc2 : c ^ 2 = S ^ 2 / 25 := by rw [hc_eq]; ring
    have hab2 : (a + b) ^ 2 = 9 * S ^ 2 / 100 := by rw [hab_eq]; ring
    nlinarith [sq_nonneg (a - b), hcos_eq, hc2, hab2]
  -- normalise by `l = S/60`
  set l : ℝ := S / 60 with hl
  have hlpos : 0 < l := by positivity
  have hSl : D.target.oppLen 0 = 60 * l := by rw [hl]; ring
  have hsum : a + b = 18 * l := by rw [hab_eq, hl]; ring
  have hprod : a * b = 60 * l ^ 2 := by rw [hab_prod, hl]; ring
  have hc_val : c = 12 * l := by rw [hc_eq, hl]; ring
  have s21 : Real.sqrt 21 * Real.sqrt 21 = 21 := Real.mul_self_sqrt (by norm_num)
  have hquad : a ^ 2 - 18 * l * a + 60 * l ^ 2 = 0 := by linear_combination a * hsum - hprod
  have hfact : (a - (9 + Real.sqrt 21) * l) * (a - (9 - Real.sqrt 21) * l) = 0 := by
    have e : (a - (9 + Real.sqrt 21) * l) * (a - (9 - Real.sqrt 21) * l)
        = a ^ 2 - 18 * l * a + (81 - Real.sqrt 21 * Real.sqrt 21) * l ^ 2 := by ring
    rw [e, s21]; linarith
  have hno : ∀ D' : CongruentDissection 60, D'.target.Congruent ReflS.MT30.TGT →
      D'.model.Congruent ReflS.MT30.MODEL → False := fun D' hT hM => ReflS.MT30.not_dissection D' hT hM
  rcases mul_eq_zero.mp hfact with h1 | h2
  · have ha : a = (9 + Real.sqrt 21) * l := by linarith
    have hb : b = (9 - Real.sqrt 21) * l := by linarith
    exact close_of_cert60 D hα hSD hE ReflS.MT30.TGT ReflS.MT30.MODEL 60 (9 + Real.sqrt 21) (9 - Real.sqrt 21) 12 l
      hlpos ReflS.MT30.TGT_sides ReflS.MT30.MODEL_sides hSl hc_val (Or.inr ⟨ha, hb⟩) hno
  · have ha : a = (9 - Real.sqrt 21) * l := by linarith
    have hb : b = (9 + Real.sqrt 21) * l := by linarith
    exact close_of_cert60 D hα hSD hE ReflS.MT30.TGT ReflS.MT30.MODEL 60 (9 + Real.sqrt 21) (9 - Real.sqrt 21) 12 l
      hlpos ReflS.MT30.TGT_sides ReflS.MT30.MODEL_sides hSl hc_val (Or.inl ⟨hb, ha⟩) hno

/-- **`GapE60 60`**, axiom-free. -/
theorem gapE60_60_cert : GapE60 60 :=
  gapE60_of_pairs_exc 60 (by norm_num) 30 6 e60_pair_30_6_cert pairs60_60_table

/-- **`60` is not a tile count** (no `CongruentDissection 60` exists). -/
theorem not_tile_60 (D : CongruentDissection 60) : False :=
  Erdos634.Draft.N566076.not_tile_60_of_gapE60 gapE60_60_cert D

end Erdos634.Draft.T30Cert

#print axioms Erdos634.Draft.T30Cert.e60_pair_30_6_cert
#print axioms Erdos634.Draft.T30Cert.gapE60_60_cert
#print axioms Erdos634.Draft.T30Cert.not_tile_60
