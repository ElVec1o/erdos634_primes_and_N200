/-
Draft/E60Cert.lean -- the `π/3` equilateral leaf (`GapE60 N`) from a pair table with certified exceptional pairs.

A dissection of an equilateral triangle by a tile with an angle `π/3` (and an irrational angle `α`) determines a pair
`(m₁, m₂)`, `m₁ m₂ = 3N` (`Row5.theoremE_sixty`).  The pair pins the instance up to scale: with `S` the side of the
target and `l = S / N`, the tile has sides `x l, y l` around the angle `π/3` and `z l` opposite it, where
`x + y = (m₁ + m₂)/2`, `x y = N`, `z = (m₁ − m₂)/2`.

* `close60`: `GapE120Exc`/`T30Cert.close_of_cert60` with the tile given as a `HasSides` triple (any vertex order).
* `e60Pair_of_cert`: `E60Pair N m₁ m₂` from a refutation of the pinned instance (equilateral side `N`, tile `x, y, z`).
* `Pairs60ChkExc N L`: the decidable pair table `AllN2.Pairs60Chk'` with a list `L` of exceptional pairs;
  `gapE60_of_chk_exc`: `GapE60 N` once every pair of `L` satisfies `E60Pair`.

Composite-N leaf work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.AllN2Cond
import Erdos634.Draft.T30Cert
import Erdos634.Draft.HasSidesPerm

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.E60Cert

open Erdos634.Draft.AllNExclusion

/-! ## The pair table with exceptional pairs -/

/-- `AllN2.Pairs60Chk'` with a list `L` of exceptional pairs `(m₁, m₂)`. -/
def Pairs60ChkExc (N : ℕ) (L : List (ℕ × ℕ)) : Prop :=
  ∀ m ≤ N, 1 ≤ m → m ∣ 3 * N → 3 * N / m ≤ N → 3 * N / m < m →
    L.contains (m, 3 * N / m) = true ∨
    (m = N ∧ 3 * N / m = 3) ∨
    ((16 * N ≤ (m + 3 * N / m) ^ 2 → ¬ sqChk ((m + 3 * N / m) ^ 2 - 16 * N)) ∧ m % 3 ≠ 0) ∨
    (16 * N ≤ (m + 3 * N / m) ^ 2 →
      ¬ sqChk ((m + 3 * N / m) ^ 2 - 16 * N) ∧
      ∀ p ≤ 2 * N / (m + 3 * N / m),
        ¬ (p * (m + 3 * N / m) ≤ 2 * N ∧ (m - 3 * N / m) ∣ (2 * N - p * (m + 3 * N / m))))

instance (N : ℕ) (L : List (ℕ × ℕ)) : Decidable (Pairs60ChkExc N L) := by
  unfold Pairs60ChkExc sqChk; infer_instance

end Erdos634.Draft.E60Cert

open scoped Classical
open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeE5Gen
open Erdos634.Draft.GapE120Exc Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2 Erdos634.Draft.FDBBaseBetaE1

set_option maxRecDepth 8000

namespace Erdos634.Draft.E60Cert

open Erdos634.Geometry.GapE120Dis in
/-- **Closing a `π/3` pair by a certificate**, tile given as a `HasSides` triple.  If the pair equations force the tile
to be `l·(x, y, z)` (`z` opposite the angle `π/3`) and the target side to be `L l`, and every triangle with sides
`x, y, z` is congruent to `MODEL`, then a refutation of (`TGT`, `MODEL`) refutes `D`. -/
theorem close60 {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (h : D.model.SixtyData α a b c) (hE : Equilateral D)
    (TGT MODEL : Erdos634.Geometry.Tri) (L x y z l : ℝ) (hl : 0 < l)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = L ∧ dist (TGT.pts 1) (TGT.pts 2) = L ∧ dist (TGT.pts 0) (TGT.pts 2) = L)
    (hM : ∀ T : Erdos634.Geometry.Tri, HasSides T x y z → T.Congruent MODEL)
    (hS : D.target.oppLen 0 = L * l) (hc : c = z * l)
    (hab : (a = x * l ∧ b = y * l) ∨ (a = y * l ∧ b = x * l))
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
  have mdist : ∀ i j, dist (D'.model.pts i) (D'.model.pts j) = l⁻¹ * dist (D.model.pts i) (D.model.pts j) := by
    intro i j
    rw [hD', Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.homothetyEquiv_dist, abs_of_pos hr]
  have mo : ∀ k : Fin 3, D'.model.oppLen k = l⁻¹ * D.model.oppLen k := fun k => by
    unfold Tri.oppLen; exact mdist _ _
  obtain ⟨g1, g2, g3⟩ := hT
  have hTc : D'.target.Congruent TGT :=
    Tri.congruent_of_dist _ _ (by rw [tdist, d01, g1]; exact hrl L) (by rw [tdist, d12, g2]; exact hrl L)
      (by rw [tdist, d02, g3]; exact hrl L)
  obtain ⟨σ, -, oa, -, ob, -, oc⟩ := h
  have hMc : D'.model.Congruent MODEL := by
    apply hM
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hasSides_of_sigma σ (by rw [mo, oa, ha]; exact hrl x) (by rw [mo, ob, hb]; exact hrl y)
        (by rw [mo, oc, hc]; exact hrl z)
    · exact hasSides_swap (hasSides_of_sigma σ (by rw [mo, oa, ha]; exact hrl y) (by rw [mo, ob, hb]; exact hrl x)
        (by rw [mo, oc, hc]; exact hrl z))
  exact hno D' hTc hMc

/-- **`E60Pair N m₁ m₂` from a certificate** of the pinned instance at any scale: equilateral target of side `L`,
tile with sides `x, y` around the angle `π/3` and `z` opposite it, where
`x + y = L (m₁ + m₂)/(2N)`, `x y = L²/N`, `z = L (m₁ − m₂)/(2N)`. -/
theorem e60Pair_of_cert_scaled (N : ℕ) (hN : 0 < N) (m₁ m₂ : ℤ) (hprod : m₁ * m₂ = 3 * (N : ℤ)) (hm2 : 0 < m₂)
    (hlt : m₂ < m₁) (L x y z : ℝ) (hL : 0 < L) (hsum : 2 * (N : ℝ) * (x + y) = L * ((m₁ : ℝ) + m₂))
    (hxy : (N : ℝ) * (x * y) = L ^ 2) (hz : 2 * (N : ℝ) * z = L * ((m₁ : ℝ) - m₂))
    (TGT MODEL : Erdos634.Geometry.Tri)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = L ∧ dist (TGT.pts 1) (TGT.pts 2) = L ∧ dist (TGT.pts 0) (TGT.pts 2) = L)
    (hM : ∀ T : Erdos634.Geometry.Tri, HasSides T x y z → T.Congruent MODEL)
    (hno : ∀ D' : CongruentDissection N, D'.target.Congruent TGT → D'.model.Congruent MODEL → False) :
    E60Pair N m₁ m₂ := by
  intro D α a b c hα hS hE hm1e hm2e
  have hSD := hS
  obtain ⟨σ, hα0, oa, hβ0, ob, hγ0, oc⟩ := hS
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hprodR : (m₁ : ℝ) * m₂ = 3 * (N : ℝ) := by exact_mod_cast hprod
  have hcos : c ^ 2 = a ^ 2 + b ^ 2 - a * b := by
    have hl := D.model.lawCos_perm σ
    rw [oa, ob, oc, hγ0, Real.cos_pi_div_three] at hl
    linarith
  generalize hSdef : D.target.oppLen 0 = S at hm1e hm2e
  have hSpos : 0 < S := by rw [← hSdef]; exact D.target.oppLen_pos 0
  -- `a + b` and `c` from the two pair equations
  have key1 : 2 * (N : ℝ) * (a + b) = S * ((m₁ : ℝ) + m₂) := by
    linear_combination ((m₂ : ℝ) / 3) * hm1e + ((m₁ : ℝ) / 3) * hm2e - (2 * (a + b) / 3) * hprodR
  have key2 : 2 * (N : ℝ) * c = S * ((m₁ : ℝ) - m₂) := by
    linear_combination ((m₁ : ℝ) / 3) * hm2e - ((m₂ : ℝ) / 3) * hm1e - (2 * c / 3) * hprodR
  have h2N : (0 : ℝ) < 2 * (N : ℝ) := by positivity
  have hsumab : a + b = (x + y) * (S / L) := by
    have h1 : 2 * (N : ℝ) * (a + b) = 2 * (N : ℝ) * ((x + y) * (S / L)) := by
      rw [key1]
      have : 2 * (N : ℝ) * ((x + y) * (S / L)) = (2 * (N : ℝ) * (x + y)) * (S / L) := by ring
      rw [this, hsum]; field_simp
    exact mul_left_cancel₀ h2N.ne' h1
  have hcz : c = z * (S / L) := by
    have h1 : 2 * (N : ℝ) * c = 2 * (N : ℝ) * (z * (S / L)) := by
      rw [key2]
      have : 2 * (N : ℝ) * (z * (S / L)) = (2 * (N : ℝ) * z) * (S / L) := by ring
      rw [this, hz]; field_simp
    exact mul_left_cancel₀ h2N.ne' h1
  -- `a b = x y l²`
  have hprodab : a * b = x * y * (S / L) ^ 2 := by
    have h1 : 3 * (a * b) = (a + b) ^ 2 - c ^ 2 := by linear_combination hcos
    have h2 : (a + b) ^ 2 - c ^ 2 = ((x + y) ^ 2 - z ^ 2) * (S / L) ^ 2 := by rw [hsumab, hcz]; ring
    -- `4 N² ((x+y)² − z²) = L² · 4 m₁ m₂ = 12 N L²`
    have h3 : (N : ℝ) * ((x + y) ^ 2 - z ^ 2) = 3 * L ^ 2 := by
      have h4 : (2 * (N : ℝ)) ^ 2 * ((x + y) ^ 2 - z ^ 2) = L ^ 2 * (4 * ((m₁ : ℝ) * m₂)) := by
        have e : (2 * (N : ℝ)) ^ 2 * ((x + y) ^ 2 - z ^ 2)
            = (2 * (N : ℝ) * (x + y)) ^ 2 - (2 * (N : ℝ) * z) ^ 2 := by ring
        rw [e, hsum, hz]; ring
      rw [hprodR] at h4
      have h5 : (4 * (N : ℝ)) * ((N : ℝ) * ((x + y) ^ 2 - z ^ 2)) = (4 * (N : ℝ)) * (3 * L ^ 2) := by
        linear_combination h4
      exact mul_left_cancel₀ (by positivity : (4 * (N : ℝ)) ≠ 0) h5
    have h6 : (N : ℝ) * (3 * (a * b)) = (N : ℝ) * (3 * (x * y * (S / L) ^ 2)) := by
      rw [h1, h2]
      have : (N : ℝ) * (((x + y) ^ 2 - z ^ 2) * (S / L) ^ 2) = ((N : ℝ) * ((x + y) ^ 2 - z ^ 2)) * (S / L) ^ 2 := by
        ring
      rw [this, h3]
      have : (N : ℝ) * (3 * (x * y * (S / L) ^ 2)) = 3 * ((N : ℝ) * (x * y)) * (S / L) ^ 2 := by ring
      rw [this, hxy]
    have := mul_left_cancel₀ hNR.ne' h6
    linarith
  have hlpos : 0 < S / L := div_pos hSpos hL
  have hSl : D.target.oppLen 0 = L * (S / L) := by rw [hSdef]; field_simp
  have hfact : (a - x * (S / L)) * (a - y * (S / L)) = 0 := by linear_combination a * hsumab - hprodab
  rcases mul_eq_zero.mp hfact with h1 | h2
  · have ha : a = x * (S / L) := by linarith
    have hb : b = y * (S / L) := by rw [ha] at hsumab; linarith
    exact close60 D hα hSD hE TGT MODEL L x y z (S / L) hlpos hT hM hSl hcz (Or.inl ⟨ha, hb⟩) hno
  · have ha : a = y * (S / L) := by linarith
    have hb : b = x * (S / L) := by rw [ha] at hsumab; linarith
    exact close60 D hα hSD hE TGT MODEL L x y z (S / L) hlpos hT hM hSl hcz (Or.inr ⟨ha, hb⟩) hno

/-- `e60Pair_of_cert_scaled` at the natural scale `L = N`: `x + y = (m₁ + m₂)/2`, `x y = N`, `z = (m₁ − m₂)/2`. -/
theorem e60Pair_of_cert (N : ℕ) (hN : 0 < N) (m₁ m₂ : ℤ) (hprod : m₁ * m₂ = 3 * (N : ℤ)) (hm2 : 0 < m₂)
    (hlt : m₂ < m₁) (x y z : ℝ) (hsum : x + y = ((m₁ : ℝ) + m₂) / 2) (hxy : x * y = N)
    (hz : z = ((m₁ : ℝ) - m₂) / 2)
    (TGT MODEL : Erdos634.Geometry.Tri)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = (N : ℝ) ∧ dist (TGT.pts 1) (TGT.pts 2) = (N : ℝ) ∧
      dist (TGT.pts 0) (TGT.pts 2) = (N : ℝ))
    (hM : ∀ T : Erdos634.Geometry.Tri, HasSides T x y z → T.Congruent MODEL)
    (hno : ∀ D' : CongruentDissection N, D'.target.Congruent TGT → D'.model.Congruent MODEL → False) :
    E60Pair N m₁ m₂ :=
  e60Pair_of_cert_scaled N hN m₁ m₂ hprod hm2 hlt N x y z (by exact_mod_cast hN)
    (by rw [hsum]; ring) (by rw [hxy]; ring) (by rw [hz]; ring) TGT MODEL hT hM hno

/-- **`GapE60 N` from the pair table with certified exceptional pairs.** -/
theorem gapE60_of_chk_exc {N : ℕ} (hN : 11 ≤ N) (L : List (ℕ × ℕ)) (h : Pairs60ChkExc N L)
    (hL : ∀ p ∈ L, E60Pair N (p.1 : ℤ) (p.2 : ℤ)) : GapE60 N := by
  intro D α a b c hα hd hE
  obtain ⟨m₁, m₂, -, -, hm1, hm1N, hm2, hm2N, hS1, hS2, harea, hprod, hlt, -⟩ := Row5.theoremE_sixty D hα hd hE
  lift m₁ to ℕ using (by omega)
  lift m₂ to ℕ using (by omega)
  have hp' : m₁ * m₂ = 3 * N := by exact_mod_cast hprod
  have h1 : 1 ≤ m₁ := by exact_mod_cast hm1
  have h1N : m₁ ≤ N := by exact_mod_cast hm1N
  have h2N : m₂ ≤ N := by exact_mod_cast hm2N
  have hlt' : m₂ < m₁ := by exact_mod_cast hlt
  have hdvd : m₁ ∣ 3 * N := ⟨m₂, hp'.symm⟩
  have hdiv : 3 * N / m₁ = m₂ := by rw [← hp']; exact Nat.mul_div_cancel_left _ h1
  -- the single-pair restriction of the table, as a `Pairs60Chk'`-style statement for THIS pair
  rcases h m₁ h1N h1 hdvd (by rw [hdiv]; exact h2N) (by rw [hdiv]; exact hlt') with hmem | hrest
  · rw [hdiv] at hmem
    exact hL (m₁, m₂) (List.contains_iff_mem.mp hmem) D α a b c hα hd hE hS1 hS2
  · -- the remaining three alternatives: reuse `gapE60_of_pairs_mod3` on a table that is constant on this pair
    rw [hdiv] at hrest
    have key : ((m₁ : ℤ) = N ∧ (m₂ : ℤ) = 3) ∨
        (¬ IsSquare (((m₁ : ℤ) + m₂) ^ 2 - 16 * (N : ℤ)) ∧ ¬ (3 : ℤ) ∣ (m₁ : ℤ)) ∨
        (¬ IsSquare (((m₁ : ℤ) + m₂) ^ 2 - 16 * (N : ℤ)) ∧
          (0 ≤ ((m₁ : ℤ) + m₂) ^ 2 - 16 * (N : ℤ) →
            ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * (N : ℤ) ≠ p * ((m₁ : ℤ) + m₂) + r * ((m₁ : ℤ) - m₂))) := by
      rcases hrest with ⟨e1, e2⟩ | ⟨hg, h3⟩ | hR
      · left; exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
      · right; left
        refine ⟨nonsq_of_guard N m₁ m₂ hg, ?_⟩
        intro hd3
        have : 3 ∣ m₁ := by exact_mod_cast hd3
        omega
      · right; right
        constructor
        · exact nonsq_of_guard N m₁ m₂ (fun hc => (hR hc).1)
        · intro hD p r hp0 hr0 hcon
          have hc : 16 * N ≤ (m₁ + m₂) ^ 2 := by
            by_contra hc
            have : (m₁ + m₂) ^ 2 < 16 * N := by omega
            have : (((m₁ + m₂) ^ 2 : ℕ) : ℤ) < ((16 * N : ℕ) : ℤ) := by exact_mod_cast this
            push_cast at this hD; linarith
          lift p to ℕ using hp0
          lift r to ℕ using hr0
          have hcon' : 2 * N = p * (m₁ + m₂) + r * (m₁ - m₂) := by
            have e : (2 * N : ℤ) = p * (m₁ + m₂) + r * ((m₁ : ℤ) - m₂) := by exact_mod_cast hcon
            have e2 : (2 * N : ℤ) = ((p * (m₁ + m₂) + r * (m₁ - m₂) : ℕ) : ℤ) := by
              push_cast [Nat.cast_sub hlt'.le]; linarith
            exact_mod_cast e2
          have hApos : 0 < m₁ + m₂ := by omega
          refine (hR hc).2 p ?_ ⟨by omega, ⟨r, by rw [show 2 * N - p * (m₁ + m₂) = r * (m₁ - m₂) by omega]; ring⟩⟩
          exact (Nat.le_div_iff_mul_le hApos).mpr (by omega)
    rcases key with ⟨e1, e2⟩ | ⟨hD, h3⟩ | ⟨hD, hno⟩
    · have e1' : m₁ = N := by exact_mod_cast e1
      have e2' : m₂ = 3 := by exact_mod_cast e2
      subst e1'; subst e2'
      exact sixty_pinned_false D hα hd hE hN (by exact_mod_cast hS1) (by exact_mod_cast hS2) harea
    · exact Erdos634.Draft.E60V.e60Pair_of_not_three_dvd N (by omega) m₁ m₂ hprod hD h3 D α a b c hα hd hE hS1 hS2
    · obtain ⟨p, q, r, hpqr⟩ := sixty_side_decomposition D hd
      obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0
        (fun k => D.model.sixty_angles_mem hα hd 0 _ k) hE
      have hdd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
        rw [← e2]; unfold Tri.oppLen; rfl
      rw [hdd] at hpqr
      exact sixty_side_kill (N := N) (a := a) (b := b) (c := c) (S := D.target.oppLen 0) (m₁ : ℤ) (m₂ : ℤ) (by omega)
        hS1 hS2 harea hprod (D.target.oppLen_pos 0) (p : ℤ) (q : ℤ) (r : ℤ)
        (by rw [hpqr]; push_cast; ring) hD (fun hnn => hno hnn (p : ℤ) (r : ℤ) (by positivity) (by positivity))

end Erdos634.Draft.E60Cert

#print axioms Erdos634.Draft.E60Cert.close60
#print axioms Erdos634.Draft.E60Cert.e60Pair_of_cert_scaled
#print axioms Erdos634.Draft.E60Cert.e60Pair_of_cert
#print axioms Erdos634.Draft.E60Cert.gapE60_of_chk_exc
