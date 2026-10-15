-- Draft/F1N3.lean — N=3 F1 exclusion.
--
-- For N=3 the equation Pa+Rc=μ(a+b) has TWO natural-number solutions (P=1,R=1) and (P=3,R=0),
-- so `f1_word_from_bzero` (which uses N>3 to rule out P=3,R=0) fails.  This file proves
-- `f1_N3_free` by a P≥1 argument that works for both words, then provides
-- `f1_prime_free_any` unifying the N=3 and N>3 cases.

import Erdos634.Draft.F1BEdgeBoundary
import Erdos634.Draft.F1AlgebraPin
import Erdos634.Draft.F1IrrationalRatio
import Erdos634.Draft.F1AreaIdentity
import Erdos634.Draft.F1BoundaryK2
import Erdos634.Draft.F1K2Core
import Erdos634.Draft.F1K2Contradiction
import Erdos634.Draft.F1Bridge
import Erdos634.Draft.G1NFinal
import Erdos634.Draft.F1SideWord
import Erdos634.Draft.FluxFRow14
import Erdos634.EdgeChain

open scoped Classical
open Erdos634.Geometry
open Erdos634.Draft.TheoremPConditional (IrrPi F1Shape)
open Erdos634.Draft.F1AlgebraPin (f1_pin_mu_of_prime)
open Erdos634.Draft.F1IrrationalRatio (f1_b_over_c_irrational)
open Erdos634.Draft.F1BEdgeBoundary (f1_V1V2_b_zero f1_mu_ab_val f1_tile_b_unique)
open Erdos634.Draft.F1AreaIdentity (F1_area_identity)
open Erdos634.Row14 (NotRat rat_coeff_unique)
open Erdos634.Draft.F1SideWord (f1_total_b_count)

namespace Erdos634.Draft.F1N3

private instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp⟩

private lemma sum_three_filter {ι : Type*} (s : Finset ι) (len : ι → ℝ) (a b c : ℝ)
    (hab : b ≠ a) (h : ∀ e ∈ s, len e = a ∨ len e = b ∨ len e = c) :
    ((s.filter fun e => len e = a).card : ℝ) * a +
    (s.filter fun e => len e = b).card * b +
    (s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card * c =
    ∑ e ∈ s, len e := by
  have hfilt : s.filter (fun e => len e = b) =
      s.filter (fun e => ¬ len e = a ∧ len e = b) := by
    ext e; simp only [Finset.mem_filter]
    exact ⟨fun ⟨he, hb⟩ => ⟨he, fun ha => hab (ha.symm ▸ hb ▸ rfl), hb⟩,
           fun ⟨he, _, hb⟩ => ⟨he, hb⟩⟩
  rw [hfilt]
  have hsplit1 := Finset.sum_filter_add_sum_filter_not s (fun e => len e = a) len
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (s.filter fun e => ¬ len e = a) (fun e => len e = b) len
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit2
  have hA : ∑ e ∈ s.filter (fun e => len e = a), len e =
      ((s.filter fun e => len e = a).card : ℝ) * a := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
        Finset.sum_const, nsmul_eq_mul]
  have hB : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ len e = b), len e =
      ((s.filter fun e => ¬ len e = a ∧ len e = b).card : ℝ) * b := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2.2),
        Finset.sum_const, nsmul_eq_mul]
  have hC : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ ¬ len e = b), len e =
      ((s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card : ℝ) * c := by
    rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
    rcases h e (Finset.mem_filter.mp he).1 with h' | h' | h'
    · exact absurd h' (Finset.mem_filter.mp he).2.1
    · exact absurd h' (Finset.mem_filter.mp he).2.2
    · exact h'
  linarith [hsplit1, hsplit2, hA, hB, hC]

/-! ## Blocker A: a-edge tile exists (P≥1 arithmetic) -/

/-- BLOCKER-F1N3-A.
    For N=3 and Q=0 on side V1V2, the side-walk count satisfies P+2R=3 (arithmetic), so P≥1,
    and hence the a-filter of the walk's part is nonempty.
    Proof: μ(a+b)=3c/2, a=c/2 (from hpin), Pa+Rc=3c/2 (Q=0) → P+2R=3 → P≥1 → ∃(i',k'). -/
lemma f1_a_tile_exists {α a b c μ : ℝ}
    (D : CongruentDissection 3)
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) (hμ : 0 < μ)
    (σ : Equiv.Perm (Fin 3))
    (hside_eq : dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) = μ * (a + b))
    (hQzero : ∀ P Q R : ℕ, (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c =
        dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) → Q = 0) :
    ∃ (part : Finset (Fin 3 × Fin 3)) (i' : Fin 3) (k' : Fin 3),
      ((⋃ e ∈ part, (D.toDissection.tile e.1).edge e.2)
          = segment ℝ (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)))
      ∧ (i', k') ∈ part
      ∧ dist ((D.tile i').pts k') ((D.tile i').pts (k' + 1)) = a := by
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨hpin, hmu⟩ := f1_pin_mu_of_prime D hirr hm hF1 hμ (by norm_num : Nat.Prime 3)
  have harea : (3 : ℝ) * b = μ ^ 2 * (a + b) := F1_area_identity D hm hF1 ha0 hb0 hμ
  -- a = c/2 (from hpin: c*(N-1) = a*(N+1) with N=3 → 2c = 4a)
  have ha_half : a = c / 2 := by
    have h := hpin; push_cast at h; linarith
  -- μ(a+b) = 3c/2
  have hmu_ab : μ * (a + b) = 3 * c / 2 := by
    have := f1_mu_ab_val ha0 hb0 hc0 hμ hpin hmu harea (by norm_num : (0:ℝ) < 3 + 1)
    simp only [Nat.cast_ofNat] at this; linarith
  -- habc: every tile edge in {a, b, c}
  have habc : ∀ (j : Fin 3) (k : Fin 3),
      dist ((D.toDissection.tile j).pts k) ((D.toDissection.tile j).pts (k + 1)) = a ∨
      dist ((D.toDissection.tile j).pts k) ((D.toDissection.tile j).pts (k + 1)) = b ∨
      dist ((D.toDissection.tile j).pts k) ((D.toDissection.tile j).pts (k + 1)) = c := by
    intro j k
    obtain ⟨m, hm_eq⟩ := D.eLen_mem ⟨j, k⟩
    have hdef : D.eLen ⟨j, k⟩ = dist ((D.toDissection.tile j).pts k)
        ((D.toDissection.tile j).pts (k + 1)) := rfl
    rw [← hdef, hm_eq]
    obtain ⟨σ', -, ha_op, -, hb_op, -, hc_op⟩ := hm
    obtain ⟨i, rfl⟩ := σ'.surjective m
    fin_cases i
    · exact Or.inl ha_op
    · exact Or.inr (Or.inl hb_op)
    · exact Or.inr (Or.inr hc_op)
  -- b ≠ a: b/c is irrational (f1_b_over_c_irrational), but a = c/2 is rational*c
  have hb_ne_a : b ≠ a := by
    intro heq
    exact f1_b_over_c_irrational D hirr hm hF1 hμ (by norm_num)
      ⟨1/2, by rw [heq, ha_half]; push_cast; ring⟩
  -- Get part from side_walk
  obtain ⟨part, hcov, -, hlen_sum⟩ := D.toDissection.side_walk (σ 2 + 1)
  -- P, Q, R as explicit filter counts (avoids opaque existential from sum_three_values)
  let lenD : Fin 3 × Fin 3 → ℝ :=
    fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
  let P := (part.filter fun e => lenD e = a).card
  let Q := (part.filter fun e => lenD e = b).card
  let R := (part.filter fun e => ¬ lenD e = a ∧ ¬ lenD e = b).card
  have hPQR : (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c =
      ∑ e ∈ part, lenD e :=
    sum_three_filter part lenD a b c hb_ne_a (fun e _ => habc e.1 e.2)
  -- hPQR_side: Pa + Qb + Rc = dist(V1,V2)
  -- hlen_sum uses σ 2 + 1 + 1; hPQR_side uses σ 2 + 2 (equal in Fin 3)
  have hPQR_side : (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c =
      dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) := by
    have h := hPQR.trans hlen_sum
    rw [(show ∀ x : Fin 3, x + 1 + 1 = x + 2 from by decide) (σ 2)] at h
    exact h
  -- Q = 0
  have hQ0 : Q = 0 := hQzero P Q R hPQR_side
  -- Pa + Rc = μ(a+b) = 3c/2
  have hPR : (P : ℝ) * a + (R : ℝ) * c = 3 * c / 2 := by
    have hQ0r : (Q : ℝ) = 0 := by exact_mod_cast hQ0
    have hside3 : dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) = 3 * c / 2 :=
      hside_eq.trans hmu_ab
    nlinarith [hPQR_side, hQ0r, hside3]
  -- P + 2R = 3
  have hP2R : P + 2 * R = 3 := by
    have h : (P : ℝ) * (c / 2) + (R : ℝ) * c = 3 * c / 2 := by rw [← ha_half]; exact hPR
    have hcne : c ≠ 0 := hc0.ne'
    have h' : ((P : ℝ) / 2 + (R : ℝ)) * c = 3 * c / 2 := by ring_nf; linarith [h]
    have h'' : (P : ℝ) / 2 + (R : ℝ) = 3 / 2 :=
      mul_right_cancel₀ hcne (by rw [h']; ring)
    have h''' : (P : ℝ) + 2 * (R : ℝ) = 3 := by linarith
    exact_mod_cast h'''
  -- P ≥ 1 → the a-filter is nonempty (P is definitionally the a-filter count)
  have hP_ge1 : 1 ≤ P := by omega
  obtain ⟨⟨i', k'⟩, hmem_filt⟩ := Finset.card_pos.mp (show 0 < P from by omega)
  have hmem : (i', k') ∈ part := (Finset.mem_filter.mp hmem_filt).1
  have hka : dist ((D.tile i').pts k') ((D.tile i').pts (k' + 1)) = a :=
    (Finset.mem_filter.mp hmem_filt).2
  have hcov' := (show ∀ x : Fin 3, x + 1 + 1 = x + 2 from by decide) (σ 2) ▸ hcov
  exact ⟨part, i', k', hcov', hmem, hka⟩

/-! ## Main contradiction for N=3, F1Data case -/

private theorem f1_N3_F1Data {α a b c μ : ℝ}
    (D : CongruentDissection 3)
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) (hμ : 0 < μ) : False := by
  have hN : Nat.Prime 3 := by norm_num
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨hpin, hmu⟩ := f1_pin_mu_of_prime D hirr hm hF1 hμ hN
  -- V1V2 carries zero b-edges
  obtain ⟨σ, hside_eq, hQzero⟩ := f1_V1V2_b_zero D hirr hm hF1 hμ hN
  -- Extract tile i' with a-edge on V1V2 part
  obtain ⟨part, i', k', hpart_cov, hmem, hka⟩ :=
    f1_a_tile_exists D hirr hm hF1 hμ σ hside_eq hQzero
  -- Identify k_γ = 2π/3-vertex index of tile i'
  obtain ⟨σ', hσ'⟩ := (D.tiles_congruent i').exists_perm
  have hm_orig := hm
  obtain ⟨σ_m, hm0a, hm0s, hm1a, hm1s, hm2a, hm2s⟩ := hm
  let k_γ := σ'.symm (σ_m 2)
  have hangle_γ : (D.tile i').angleAt k_γ = 2 * Real.pi / 3 := by
    have h := (hσ' k_γ).1
    simp only [k_γ, Equiv.apply_symm_apply] at h; rw [h, hm2a]
  let X := (D.tile i').pts k_γ
  have hγ : (D.tile i').localAngle X = 2 * Real.pi / 3 := by
    simp only [X, Tri.localAngle_vertex]; exact hangle_γ
  -- k' is the α-vertex edge (j_a+1); k_γ is an endpoint of k' (not j_a)
  let j_a := σ'.symm (σ_m 0)
  have hjγ_ne_ja : k_γ ≠ j_a := by
    simp only [k_γ, j_a]; intro h
    exact absurd (σ_m.injective (σ'.symm.injective h)) (by decide)
  have hkγ_endpoint : k_γ = j_a + 1 ∨ k_γ = j_a + 2 := by
    have : k_γ ≠ j_a := hjγ_ne_ja
    exact (show ∀ x y : Fin 3, x ≠ y → x = y + 1 ∨ x = y + 2 from by decide) k_γ j_a this
  -- Uniqueness of a-edge: k' = j_a+1
  have hb_ne_a : b ≠ a := by
    intro h
    apply (f1_b_over_c_irrational D hirr hm_orig hF1 hμ hN)
    exact ⟨((3:ℚ)-1)/((3:ℚ)+1), by
      rw [h]; push_cast; field_simp [hc0.ne']; have hp := hpin; push_cast at hp; linarith⟩
  have hc_ne_a : c ≠ a := by
    intro h
    have hN1pos : (0:ℝ) < 3 + 1 := by norm_num
    linarith [mul_pos ha0 hN1pos, mul_pos hc0 (show (0:ℝ) < 3-1 by norm_num), h ▸ hpin]
  have hk'_ja1 : k' = j_a + 1 := by
    have hk'_opp : (D.tile i').oppLen (k' + 2) = a := by
      simp only [Tri.oppLen]
      have h1 : k' + 2 + 1 = k' := (show ∀ x : Fin 3, x + 2 + 1 = x from by decide) k'
      have h2 : k' + 2 + 2 = k' + 1 := (show ∀ x : Fin 3, x + 2 + 2 = x + 1 from by decide) k'
      rw [h1, h2]; exact hka
    have hσ'_k'2 : D.model.oppLen (σ' (k' + 2)) = a := by
      rw [← (hσ' (k' + 2)).2]; exact hk'_opp
    have hσm_k' : σ' (k' + 2) = σ_m 0 := by
      obtain ⟨j, hj⟩ := σ_m.surjective (σ' (k' + 2))
      fin_cases j
      · exact hj.symm
      · exfalso; rw [← hj] at hσ'_k'2; exact absurd (hm1s.symm.trans hσ'_k'2) hb_ne_a
      · exfalso; rw [← hj] at hσ'_k'2; exact absurd (hm2s.symm.trans hσ'_k'2) hc_ne_a
    -- j_a+1+2 = j_a in Fin 3 (wraps), so σ'(j_a+1+2) = σ'(j_a) = σ_m(0) directly.
    have hσm_ja12 : σ' (j_a + 1 + 2) = σ_m 0 := by
      have hmod : j_a + 1 + 2 = j_a := (show ∀ x : Fin 3, x + 1 + 2 = x from by decide) j_a
      rw [hmod]; simp only [j_a, Equiv.apply_symm_apply]
    have heq := σ'.injective (hσm_k'.trans hσm_ja12.symm)
    exact (show ∀ x y : Fin 3, x + 2 = y + 1 + 2 → x = y + 1 from by decide) k' j_a heq
  -- X = pts(k_γ) is an endpoint of edge k' (which goes from pts(k') to pts(k'+1))
  -- k_γ = j_a+1 = k' OR k_γ = j_a+2 = k'+1
  have hX_in_edge_k' : X ∈ (D.tile i').edge k' := by
    rcases hkγ_endpoint with h | h
    · -- k_γ = j_a+1 = k', X = pts(k') = left endpoint
      have heq : k_γ = k' := by rw [hk'_ja1]; exact h
      simp only [Tri.edge, X]; exact heq ▸ left_mem_segment ℝ _ _
    · -- k_γ = j_a+2 = k'+1, X = pts(k'+1) = right endpoint
      have heq : k_γ = k' + 1 := by
        rw [hk'_ja1]; exact h.trans ((show ∀ x : Fin 3, x + 2 = (x+1)+1 from by decide) j_a)
      simp only [Tri.edge, X]; exact heq ▸ right_mem_segment ℝ _ _
  -- X ∈ target.edge(V1V2)
  have hX_on_V1V2 : X ∈ segment ℝ (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) := by
    rw [← hpart_cov]; exact Set.mem_iUnion₂.mpr ⟨⟨i', k'⟩, hmem, hX_in_edge_k'⟩
  -- X ≠ target corners (from f1_no_gamma_at_corners + hγ)
  -- X on some j₂ ≠ V1V2 via b-edge and injection argument (Parts D-E, adapted from F1TprimeExtract)
  suffices ∃ (j₂ : Fin 3), j₂ ≠ σ 2 + 1 ∧
      X ∈ segment ℝ (D.target.pts j₂) (D.target.pts (j₂ + 1)) by
    obtain ⟨j₂, hj_ne, hX₂⟩ := this
    exact f1_k2_contradiction D hirr hm_orig hF1 i' X hγ (σ 2 + 1) j₂ hj_ne.symm
      (by simp only [Tri.edge]
          have : (σ 2 : Fin 3) + 1 + 1 = σ 2 + 2 :=
            (show ∀ x : Fin 3, x + 1 + 1 = x + 2 from by decide) (σ 2)
          rw [this]; exact hX_on_V1V2)
      (by simp only [Tri.edge]; exact hX₂)
  -- ha_half: a = c/2 (from hpin: a*(3+1) = c*(3-1))
  have ha_half : a = c / 2 := by have h := hpin; push_cast at h; linarith
  -- habc: every tile edge in {a, b, c}
  have habc : ∀ (j : Fin 3) (k : Fin 3),
      dist ((D.toDissection.tile j).pts k) ((D.toDissection.tile j).pts (k + 1)) = a ∨
      dist ((D.toDissection.tile j).pts k) ((D.toDissection.tile j).pts (k + 1)) = b ∨
      dist ((D.toDissection.tile j).pts k) ((D.toDissection.tile j).pts (k + 1)) = c := by
    intro j k
    obtain ⟨m, hm_eq⟩ := D.eLen_mem ⟨j, k⟩
    have hdef : D.eLen ⟨j, k⟩ = dist ((D.toDissection.tile j).pts k)
        ((D.toDissection.tile j).pts (k + 1)) := rfl
    rw [← hdef, hm_eq]
    obtain ⟨σ'', -, ha_op, -, hb_op, -, hc_op⟩ := hm_orig
    obtain ⟨ii, rfl⟩ := σ''.surjective m
    fin_cases ii
    · exact Or.inl ha_op
    · exact Or.inr (Or.inl hb_op)
    · exact Or.inr (Or.inr hc_op)
  -- j_b: the b-vertex/edge index of tile i'
  let j_b := σ'.symm (σ_m 1)
  have hopp_b : (D.tile i').oppLen j_b = b := by
    have h := (hσ' j_b).2
    rw [show σ' j_b = σ_m 1 from Equiv.apply_symm_apply σ' (σ_m 1)] at h
    rw [h, hm1s]
  have hkb_b : dist ((D.tile i').pts (j_b + 1)) ((D.tile i').pts (j_b + 2)) = b := by
    simp only [Tri.oppLen] at hopp_b; exact hopp_b
  obtain ⟨k_bU, hkbU_b, hkbU_uniq⟩ := f1_tile_b_unique D hirr hm_orig hF1 hμ hN i'
  have hkb_eq : j_b + 1 = k_bU :=
    hkbU_uniq (j_b + 1) (by
      have hfin : (j_b + 1 : Fin 3) + 1 = j_b + 2 :=
        (show ∀ x : Fin 3, (x + 1) + 1 = x + 2 from by decide) j_b
      simp only [hfin]; exact hkb_b)
  -- Get side-walks for sides A (σ2) and B (σ2+2)
  obtain ⟨partA, hcovA, -, hsumA⟩ := D.toDissection.side_walk (σ 2)
  obtain ⟨partB, hcovB, -, hsumB⟩ := D.toDissection.side_walk (σ 2 + 2)
  -- (i', k_bU) is in partA or partB (b-edge injection argument)
  have hbedge_located : (i', k_bU) ∈ partA ∨ (i', k_bU) ∈ partB := by
    -- Q-uniqueness: b/c irrational → the Q-coefficient of any Pa+Qb+Rc=L is unique
    have hbci := f1_b_over_c_irrational D hirr hm_orig hF1 hμ hN
    have hbc_notrat : NotRat (b / c) := by
      intro ⟨q, hq⟩; apply hbci
      exact ⟨q, by rw [div_eq_iff hc0.ne'] at hq; linarith⟩
    have hQ_uniq : ∀ (Pq1 Qq1 Rq1 Pq2 Qq2 Rq2 : ℕ) (L : ℝ),
        (Pq1 : ℝ) * a + Qq1 * b + Rq1 * c = L →
        (Pq2 : ℝ) * a + Qq2 * b + Rq2 * c = L → Qq1 = Qq2 := by
      intro Pq1 Qq1 Rq1 Pq2 Qq2 Rq2 L h1 h2
      by_contra hne
      -- (Qq1-Qq2)*b = ((Pq2-Pq1)/2 - (Rq1-Rq2))*c  [from ha_half and h1, h2]
      have hdiff : ((Qq1 : ℝ) - Qq2) * b = (((Pq2 : ℝ) - Pq1) / 2 - ((Rq1 : ℝ) - Rq2)) * c := by
        rw [ha_half] at h1 h2; linarith
      have hQne_real : (Qq1 : ℝ) - Qq2 ≠ 0 := by
        intro h; exact hne (by exact_mod_cast (sub_eq_zero.mp h))
      have hQne_int : ((Qq1 : ℤ) - Qq2 : ℤ) ≠ 0 := by omega
      have hQne_rat : (((Qq1 : ℤ) - Qq2 : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hQne_int
      -- b/c = (Pq2-Pq1)/2/(Qq1-Qq2) - (Rq1-Rq2)/(Qq1-Qq2) is rational → contradiction
      apply hbci
      refine ⟨(((Pq2 : ℤ) - Pq1 : ℤ) : ℚ) / 2 / (((Qq1 : ℤ) - Qq2 : ℤ) : ℚ) -
              (((Rq1 : ℤ) - Rq2 : ℤ) : ℚ) / (((Qq1 : ℤ) - Qq2 : ℤ) : ℚ), ?_⟩
      push_cast
      field_simp [hQne_real]
      linarith [hdiff]
    -- b-counts for sides A and B from sum_three_values
    obtain ⟨PA, QA, RA, hA_eq, _⟩ := sum_three_values partA
        (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) a b c
        (fun e _ => habc e.1 e.2)
    obtain ⟨PB, QB, RB, hB_eq, _⟩ := sum_three_values partB
        (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) a b c
        (fun e _ => habc e.1 e.2)
    have hfin22 : (σ 2 + 2 : Fin 3) + 1 = σ 2 + 3 :=
      (show ∀ x : Fin 3, (x + 2 : Fin 3) + 1 = x + 3 from by decide) (σ 2)
    have hA_side : (PA : ℝ) * a + QA * b + RA * c =
        dist (D.target.pts (σ 2)) (D.target.pts (σ 2 + 1)) := by linarith [hA_eq, hsumA]
    have hB_side : (PB : ℝ) * a + QB * b + RB * c =
        dist (D.target.pts (σ 2 + 2)) (D.target.pts (σ 2 + 3)) := by
      linarith [hB_eq, hfin22 ▸ hsumB]
    -- QA + QB = 3 via f1_total_b_count + hQzero (Q_V = 0 on V-side)
    have hQAB : QA + QB = 3 := by
      obtain ⟨P0, Q0, R0, P1, Q1, R1, P2, Q2, R2, hs0, hs1, hs2, hQtot⟩ :=
        f1_total_b_count D hirr hm_orig hF1 hμ hN
      have hs2' : (P2 : ℝ) * a + Q2 * b + R2 * c =
          dist (D.target.pts 2) (D.target.pts 0) := hs2
      have h_σ2_cases : σ 2 = 0 ∨ σ 2 = 1 ∨ σ 2 = 2 :=
        (show ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 from by decide) (σ 2)
      rcases h_σ2_cases with h_σ2 | h_σ2 | h_σ2
      · -- σ 2 = 0: A=side0, V=side1, B=side2
        have hA0 : (PA : ℝ) * a + QA * b + RA * c =
            dist (D.target.pts 0) (D.target.pts 1) := by
          simp only [h_σ2, show (0 : Fin 3) + 1 = 1 from by decide] at hA_side; exact hA_side
        have hB2 : (PB : ℝ) * a + QB * b + RB * c =
            dist (D.target.pts 2) (D.target.pts 0) := by
          simp only [h_σ2, show (0 : Fin 3) + 2 = 2 from by decide,
                     show (0 : Fin 3) + 3 = 0 from by decide] at hB_side; exact hB_side
        have hQAeq : QA = Q0 := hQ_uniq PA QA RA P0 Q0 R0 _ hA0 hs0
        have hQBeq : QB = Q2 := hQ_uniq PB QB RB P2 Q2 R2 _ hB2 hs2'
        have hQV : Q1 = 0 := by
          apply hQzero P1 Q1 R1
          simp only [h_σ2, show (0 : Fin 3) + 1 = 1 from by decide,
                     show (0 : Fin 3) + 2 = 2 from by decide]; exact hs1
        omega
      · -- σ 2 = 1: A=side1, V=side2, B=side0
        have hA1 : (PA : ℝ) * a + QA * b + RA * c =
            dist (D.target.pts 1) (D.target.pts 2) := by
          simp only [h_σ2, show (1 : Fin 3) + 1 = 2 from by decide] at hA_side; exact hA_side
        have hB0 : (PB : ℝ) * a + QB * b + RB * c =
            dist (D.target.pts 0) (D.target.pts 1) := by
          simp only [h_σ2, show (1 : Fin 3) + 2 = 0 from by decide,
                     show (1 : Fin 3) + 3 = 1 from by decide] at hB_side; exact hB_side
        have hQAeq : QA = Q1 := hQ_uniq PA QA RA P1 Q1 R1 _ hA1 hs1
        have hQBeq : QB = Q0 := hQ_uniq PB QB RB P0 Q0 R0 _ hB0 hs0
        have hQV : Q2 = 0 := by
          apply hQzero P2 Q2 R2
          simp only [h_σ2, show (1 : Fin 3) + 1 = 2 from by decide,
                     show (1 : Fin 3) + 2 = 0 from by decide]; exact hs2'
        omega
      · -- σ 2 = 2: A=side2, V=side0, B=side1
        have hA2 : (PA : ℝ) * a + QA * b + RA * c =
            dist (D.target.pts 2) (D.target.pts 0) := by
          simp only [h_σ2, show (2 : Fin 3) + 1 = 0 from by decide] at hA_side; exact hA_side
        have hB1 : (PB : ℝ) * a + QB * b + RB * c =
            dist (D.target.pts 1) (D.target.pts 2) := by
          simp only [h_σ2, show (2 : Fin 3) + 2 = 1 from by decide,
                     show (2 : Fin 3) + 3 = 2 from by decide] at hB_side; exact hB_side
        have hQAeq : QA = Q2 := hQ_uniq PA QA RA P2 Q2 R2 _ hA2 hs2'
        have hQBeq : QB = Q1 := hQ_uniq PB QB RB P1 Q1 R1 _ hB1 hs1
        have hQV : Q0 = 0 := by
          apply hQzero P0 Q0 R0
          simp only [h_σ2, show (2 : Fin 3) + 1 = 0 from by decide,
                     show (2 : Fin 3) + 2 = 1 from by decide]; exact hs0
        omega
    -- b ≠ a
    have hba : b ≠ a := hb_ne_a
    -- hbA_eq: b-filter cardinality of partA = QA (via Q-uniqueness + sum_three_filter)
    have hbA_eq : (partA.filter fun e =>
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card = QA := by
      apply hQ_uniq
          ((partA.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a).card)
          ((partA.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card)
          ((partA.filter fun e =>
            ¬ dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a ∧
            ¬ dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card)
          PA QA RA (dist (D.target.pts (σ 2)) (D.target.pts (σ 2 + 1)))
      · linarith [sum_three_filter partA
            (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) a b c
            hba (fun e _ => habc e.1 e.2), hsumA]
      · exact hA_side
    have hbB_eq : (partB.filter fun e =>
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card = QB := by
      have hsumB' : ∑ e ∈ partB, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
          dist (D.target.pts (σ 2 + 2)) (D.target.pts (σ 2 + 3)) := hfin22 ▸ hsumB
      apply hQ_uniq
          ((partB.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a).card)
          ((partB.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card)
          ((partB.filter fun e =>
            ¬ dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a ∧
            ¬ dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card)
          PB QB RB (dist (D.target.pts (σ 2 + 2)) (D.target.pts (σ 2 + 3)))
      · linarith [sum_three_filter partB
            (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) a b c
            hba (fun e _ => habc e.1 e.2), hsumB']
      · exact hB_side
    -- Combined b-edges on A and B
    let bAB := (partA ∪ partB).filter fun e =>
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b
    -- Injection: each tile appears at most once in bAB (unique b-edge per tile)
    have hinj : ∀ e1 ∈ bAB, ∀ e2 ∈ bAB, e1.1 = e2.1 → e1 = e2 := by
      intro ⟨i1, k1⟩ he1 ⟨i2, k2⟩ he2 heq
      simp only at heq; subst heq
      simp only [Finset.mem_filter, Finset.mem_union, bAB] at he1 he2
      have hb1 : dist ((D.tile i1).pts k1) ((D.tile i1).pts (k1 + 1)) = b := he1.2
      have hb2 : dist ((D.tile i1).pts k2) ((D.tile i1).pts (k2 + 1)) = b := he2.2
      obtain ⟨k_b, -, huniq⟩ := f1_tile_b_unique D hirr hm_orig hF1 hμ hN i1
      congr 1; exact (huniq k1 hb1).trans (huniq k2 hb2).symm
    -- |bAB| = QA + QB = 3
    have hbAB_card : bAB.card = 3 := by
      have hdisj : Disjoint partA partB := by
        rw [Finset.disjoint_left]
        intro e heA heB
        have hsubA : (D.tile e.1).edge e.2 ⊆
            segment ℝ (D.target.pts (σ 2)) (D.target.pts (σ 2 + 1)) := by
          intro y hy; rw [← hcovA]; exact Set.mem_iUnion₂.mpr ⟨e, heA, hy⟩
        have hsubB : (D.tile e.1).edge e.2 ⊆
            segment ℝ (D.target.pts (σ 2 + 2)) (D.target.pts ((σ 2 + 2) + 1)) := by
          intro y hy; rw [← hcovB]; exact Set.mem_iUnion₂.mpr ⟨e, heB, hy⟩
        have hσ_add3 : (σ 2 + 2 : Fin 3) + 1 = σ 2 :=
          (show ∀ x : Fin 3, (x + 2 : Fin 3) + 1 = x from by decide) (σ 2)
        have hpt0_in_A : (D.tile e.1).pts e.2 ∈ D.target.edge (σ 2) :=
          hsubA (left_mem_segment ℝ _ _)
        have hpt0_in_B : (D.tile e.1).pts e.2 ∈ D.target.edge (σ 2 + 2) :=
          hsubB (left_mem_segment ℝ _ _)
        have hpt1_in_A : (D.tile e.1).pts (e.2 + 1) ∈ D.target.edge (σ 2) :=
          hsubA (right_mem_segment ℝ _ _)
        have hpt1_in_B : (D.tile e.1).pts (e.2 + 1) ∈ D.target.edge (σ 2 + 2) :=
          hsubB (right_mem_segment ℝ _ _)
        have hedge_eq : D.target.edge ((σ 2 + 2 : Fin 3) + 1) = D.target.edge (σ 2) :=
          congrArg D.target.edge hσ_add3
        have hpt0_corner : (D.tile e.1).pts e.2 = D.target.pts ((σ 2 + 2 : Fin 3) + 1) := by
          exact tri_adjacent_edges_inter_vertex D.target (σ 2 + 2) hpt0_in_B
            (hedge_eq ▸ hpt0_in_A)
        have hpt1_corner : (D.tile e.1).pts (e.2 + 1) = D.target.pts ((σ 2 + 2 : Fin 3) + 1) := by
          exact tri_adjacent_edges_inter_vertex D.target (σ 2 + 2) hpt1_in_B
            (hedge_eq ▸ hpt1_in_A)
        have hpts_eq : (D.tile e.1).pts e.2 = (D.tile e.1).pts (e.2 + 1) :=
          hpt0_corner.trans hpt1_corner.symm
        have hlen_pos : 0 < dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
          rcases habc e.1 e.2 with h | h | h <;> linarith [ha0, hb0, hc0, h.symm.le]
        exact absurd (hpts_eq ▸ dist_self ((D.tile e.1).pts e.2)) (ne_of_gt hlen_pos)
      have hcard_split : bAB.card = (partA.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card +
          (partB.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card := by
        rw [show bAB = (partA.filter fun e =>
              dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b) ∪
            (partB.filter fun e =>
              dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b) from
          Finset.filter_union _ _ _]
        apply Finset.card_union_of_disjoint
        exact hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      omega
    -- bAB.image Prod.fst = univ (all 3 tiles covered)
    have himg_full : bAB.image Prod.fst = Finset.univ := by
      apply Finset.eq_univ_of_card
      have hinj_on : Set.InjOn Prod.fst (bAB : Set (Fin 3 × Fin 3)) :=
        fun e1 he1 e2 he2 h => hinj e1 (Finset.mem_coe.mp he1) e2 (Finset.mem_coe.mp he2) h
      rw [Finset.card_image_of_injOn hinj_on, hbAB_card]
      simp only [Fintype.card_fin]
    -- Tile i' is in the image → (i', k_bU) ∈ bAB
    obtain ⟨⟨itile, ktile⟩, hmem_b, hitile_eq⟩ :=
      Finset.mem_image.mp (show i' ∈ bAB.image Prod.fst by rw [himg_full]; exact Finset.mem_univ i')
    have hitile_eq' : itile = i' := hitile_eq
    have hktile_b : dist ((D.tile itile).pts ktile) ((D.tile itile).pts (ktile + 1)) = b :=
      (Finset.mem_filter.mp hmem_b).2
    have hk''_eq : ktile = k_bU :=
      hkbU_uniq ktile (hitile_eq' ▸ hktile_b)
    rw [hk''_eq, hitile_eq'] at hmem_b
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hmem_b).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- Part E: k_γ is an endpoint of b-edge k_bU, so X ∈ target.edge(j₂)
  have hjγ_ne_jb : k_γ ≠ j_b := by
    simp only [k_γ, j_b]; intro h
    exact absurd (σ_m.injective (σ'.symm.injective h)) (by decide)
  have hkγ_endpoint_b : k_γ = k_bU ∨ k_γ = k_bU + 1 := by
    rw [← hkb_eq]
    rcases (show ∀ x y : Fin 3, x ≠ y → x = y + 1 ∨ x = y + 2 from by decide)
        k_γ j_b hjγ_ne_jb with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans ((show ∀ x : Fin 3, x + 2 = (x + 1) + 1 from by decide) j_b))
  have hX_in_edge_b : X ∈ (D.tile i').edge k_bU := by
    have hedge : (D.tile i').edge k_bU =
        segment ℝ ((D.tile i').pts k_bU) ((D.tile i').pts (k_bU + 1)) := rfl
    rcases hkγ_endpoint_b with h | h
    · have hXval : X = (D.tile i').pts k_bU := congrArg (D.tile i').pts h
      exact hXval ▸ hedge.symm ▸ left_mem_segment ℝ _ _
    · have hXval : X = (D.tile i').pts (k_bU + 1) := congrArg (D.tile i').pts h
      exact hXval ▸ hedge.symm ▸ right_mem_segment ℝ _ _
  rcases hbedge_located with hA | hB
  · exact ⟨σ 2, (show ∀ x : Fin 3, x ≠ x + 1 from by decide) (σ 2),
      (hcovA ▸ Set.subset_biUnion_of_mem hA) hX_in_edge_b⟩
  · exact ⟨σ 2 + 2, (show ∀ x : Fin 3, x + 2 ≠ x + 1 from by decide) (σ 2),
      (hcovB ▸ Set.subset_biUnion_of_mem hB) hX_in_edge_b⟩

/-! ## N=3 F1 theorem -/

theorem f1_N3_free {α a b c : ℝ} (D : CongruentDissection 3)
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1shape : F1Shape D α) : False := by
  rcases f1_data_of_f1shape D hm hF1shape with ⟨μ, hμ, hF1⟩ | ⟨μ, hμ, hF1'⟩
  · exact f1_N3_F1Data D hirr hm hF1 hμ
  · have hirr' : IrrPi (Real.pi / 3 - α) :=
      fun ⟨q, hq⟩ => hirr ⟨1/3 - q, by push_cast; linarith⟩
    have hm' : D.model.TwoPiThreeData (Real.pi / 3 - α) b a c :=
      twoPiThreeData_swap D.model hm
    exact f1_N3_F1Data D hirr' hm' hF1' hμ

/-! ## Unified prime-free theorem -/

theorem f1_prime_free_any {N : ℕ} (D : CongruentDissection N) (hN : N.Prime)
    {α a b c : ℝ} (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1shape : F1Shape D α) : False := by
  by_cases h3 : 3 < N
  · exact Erdos634.Draft.G1NFinal.f1_prime_free D hN h3 hirr hm hF1shape
  · have hge2 := hN.two_le
    interval_cases N
    · -- N=2: parity argument — N≡2 mod 4 ⇒ 2|Mα and 2|Mβ ⇒ 4|Mα*Mβ = ±2, contradiction
      rcases f1_data_of_f1shape D hm hF1shape with ⟨μ, hμ, hF1⟩ | ⟨μ, hμ, hF1'⟩
      · obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
        have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
          obtain ⟨σ, -, ha_e, -, hb_e, hγ_e, hc_e⟩ := hm
          have hl := D.model.lawCos_perm σ
          rw [ha_e, hb_e, hc_e, hγ_e,
              show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
              Real.cos_pi_sub, Real.cos_pi_div_three] at hl
          linarith
        have hN_b : (2 : ℝ) * b = μ ^ 2 * (a + b) :=
          F1_area_identity D hm hF1 ha0 hb0 hμ
        obtain ⟨Mα, Mβ, hpα, hpβ, hcα, hcβ⟩ := Paper.cor_int D hirr hm
        have hWα := Row7.lemmaW_alpha D.target hirr hF1
        have hWβ := Row7.lemmaW_beta D.target hirr hF1
        obtain ⟨u, hu⟩ : (2 : ℤ) ∣ Mα := by
          obtain ⟨k, hk⟩ := hpα; push_cast at hk; exact ⟨k + 1, by linarith⟩
        obtain ⟨v, hv⟩ : (2 : ℤ) ∣ Mβ := by
          obtain ⟨k, hk⟩ := hpβ; push_cast at hk; exact ⟨k + 1, by linarith⟩
        have h4w : Mα * Mβ = 4 * (u * v) := by rw [hu, hv]; ring
        have hfin : (Mα * Mβ = (2 : ℤ)) ∨ (Mα * Mβ = -(2 : ℤ)) → False := by
          intro h; rcases h with h | h <;> omega
        rcases hWα with hα1 | hα2 <;> rcases hWβ with hβ1 | hβ2
        · have hpr := Erdos634.F1AlgebraReal.F1_product_real a b c μ 2 (Mα : ℝ) (Mβ : ℝ) hc2
              ha0.ne' hb0.ne' (by exact_mod_cast hN_b) (hcα.symm.trans hα1) (hcβ.symm.trans hβ1)
          exact hfin (Or.inl (by exact_mod_cast hpr))
        · have hpr := Erdos634.F1AlgebraReal.F1_product_real a b c μ 2 (Mα : ℝ) (-(Mβ : ℝ)) hc2
              ha0.ne' hb0.ne' (by exact_mod_cast hN_b) (hcα.symm.trans hα1)
              (by linarith [hcβ.symm.trans hβ2])
          have : (Mα : ℝ) * (Mβ : ℝ) = -(2 : ℝ) := by linarith
          exact hfin (Or.inr (by exact_mod_cast this))
        · have hpr := Erdos634.F1AlgebraReal.F1_product_real a b c μ 2 (-(Mα : ℝ)) (Mβ : ℝ) hc2
              ha0.ne' hb0.ne' (by exact_mod_cast hN_b) (by linarith [hcα.symm.trans hα2])
              (hcβ.symm.trans hβ1)
          have : (Mα : ℝ) * (Mβ : ℝ) = -(2 : ℝ) := by linarith
          exact hfin (Or.inr (by exact_mod_cast this))
        · have hpr := Erdos634.F1AlgebraReal.F1_product_real a b c μ 2 (-(Mα : ℝ)) (-(Mβ : ℝ)) hc2
              ha0.ne' hb0.ne' (by exact_mod_cast hN_b) (by linarith [hcα.symm.trans hα2])
              (by linarith [hcβ.symm.trans hβ2])
          have : (Mα : ℝ) * (Mβ : ℝ) = (2 : ℝ) := by linarith
          exact hfin (Or.inl (by exact_mod_cast this))
      · -- F1Data′ branch: swap α↦π/3−α, a↦b
        have hirr' : IrrPi (Real.pi / 3 - α) :=
          fun ⟨q, hq⟩ => hirr ⟨1/3 - q, by push_cast; linarith⟩
        have hm' : D.model.TwoPiThreeData (Real.pi / 3 - α) b a c :=
          twoPiThreeData_swap D.model hm
        obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm'
        have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
          obtain ⟨σ, -, ha_e, -, hb_e, hγ_e, hc_e⟩ := hm
          have hl := D.model.lawCos_perm σ
          rw [ha_e, hb_e, hc_e, hγ_e,
              show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
              Real.cos_pi_sub, Real.cos_pi_div_three] at hl
          linarith
        have hN_b : (2 : ℝ) * a = μ ^ 2 * (b + a) :=
          F1_area_identity D hm' hF1' ha0 hb0 hμ
        obtain ⟨Mα, Mβ, hpα, hpβ, hcα, hcβ⟩ := Paper.cor_int D hirr' hm'
        have hWα := Row7.lemmaW_alpha D.target hirr' hF1'
        have hWβ := Row7.lemmaW_beta D.target hirr' hF1'
        obtain ⟨u, hu⟩ : (2 : ℤ) ∣ Mα := by
          obtain ⟨k, hk⟩ := hpα; push_cast at hk; exact ⟨k + 1, by linarith⟩
        obtain ⟨v, hv⟩ : (2 : ℤ) ∣ Mβ := by
          obtain ⟨k, hk⟩ := hpβ; push_cast at hk; exact ⟨k + 1, by linarith⟩
        have h4w : Mα * Mβ = 4 * (u * v) := by rw [hu, hv]; ring
        have hfin : (Mα * Mβ = (2 : ℤ)) ∨ (Mα * Mβ = -(2 : ℤ)) → False := by
          intro h; rcases h with h | h <;> omega
        -- hN_b : (2:ℝ) * a = μ^2 * (b + a)  — "a" is the b-role in F1_product_real b a c
        have hc2' : c ^ 2 = b ^ 2 + b * a + a ^ 2 := by linarith [hc2, mul_comm a b]
        rcases hWα with hα1 | hα2 <;> rcases hWβ with hβ1 | hβ2
        · have hpr := Erdos634.F1AlgebraReal.F1_product_real b a c μ 2 (Mα : ℝ) (Mβ : ℝ) hc2'
              ha0.ne' hb0.ne' (by exact_mod_cast hN_b) (hcα.symm.trans hα1) (hcβ.symm.trans hβ1)
          exact hfin (Or.inl (by exact_mod_cast hpr))
        · have hpr := Erdos634.F1AlgebraReal.F1_product_real b a c μ 2 (Mα : ℝ) (-(Mβ : ℝ)) hc2'
              ha0.ne' hb0.ne' (by exact_mod_cast hN_b) (hcα.symm.trans hα1)
              (by linarith [hcβ.symm.trans hβ2])
          have : (Mα : ℝ) * (Mβ : ℝ) = -(2 : ℝ) := by linarith
          exact hfin (Or.inr (by exact_mod_cast this))
        · have hpr := Erdos634.F1AlgebraReal.F1_product_real b a c μ 2 (-(Mα : ℝ)) (Mβ : ℝ) hc2'
              ha0.ne' hb0.ne' (by exact_mod_cast hN_b) (by linarith [hcα.symm.trans hα2])
              (hcβ.symm.trans hβ1)
          have : (Mα : ℝ) * (Mβ : ℝ) = -(2 : ℝ) := by linarith
          exact hfin (Or.inr (by exact_mod_cast this))
        · have hpr := Erdos634.F1AlgebraReal.F1_product_real b a c μ 2 (-(Mα : ℝ)) (-(Mβ : ℝ)) hc2'
              ha0.ne' hb0.ne' (by exact_mod_cast hN_b) (by linarith [hcα.symm.trans hα2])
              (by linarith [hcβ.symm.trans hβ2])
          have : (Mα : ℝ) * (Mβ : ℝ) = (2 : ℝ) := by linarith
          exact hfin (Or.inl (by exact_mod_cast this))
    · exact f1_N3_free D hirr hm hF1shape

#check @f1_prime_free_any
#print axioms f1_N3_free

end Erdos634.Draft.F1N3
