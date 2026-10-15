-- Draft/InterfaceMultiset.lean
-- Second clause of prop:interfacefloor: a wall stretch shorter than f·min(a,b) has
-- the same edge multiset on both sides.
--
-- Imported by: All.lean 
--
-- Strategy: (1) `wall_word` adapts EdgeWordConversion.word_of_chain_sum to use
-- TraceCovering.wall_sum (which works for interior walls, not just boundary chords).
-- (2) `interface_same_multiset` applies InterfaceFloor.interface_floor to the
-- difference of the two side counts.
--
-- Gap: "maximal straight interfaces have unstraddled endpoints" (IsMaximalStretch.not_straddled)
-- is NOT proved here; it is the remaining geometric piece before this file unlocks prop:interfacefloor.
-- The paper statement's scope condition ("any tiling" → "any congruent dissection of a triangle")
import Mathlib.Tactic
import Erdos634.WallChain
import Erdos634.EdgeWordConversion
import Erdos634.InterfaceFloor
import Erdos634.Draft.TraceCovering

namespace Erdos634.Draft.InterfaceMultiset

open Erdos634.Geometry Erdos634.EdgeWordConversion Erdos634.InterfaceFloor
open Erdos634.Draft.TraceCovering Set

variable {N : ℕ}

/-! ## Part 1: wall_word — fiber counting for a wall stretch -/

/-- For a `CongruentDissection`, a wall stretch with unstraddled endpoints has a
near-side edge-count word `n : Fin 3 → ℕ` with `Σ n i * sideLen D i = t - s`. -/
theorem wall_word_near (D : CongruentDissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c₀ : ℝ)
    (X : Plane) (hX : f X = c₀)
    (u : Plane) (hu : f u = 0) (hu1 : ‖u‖ = 1)
    {s t : ℝ} (hst : s ≤ t)
    (hint : ∀ x ∈ Ioo s t, X + x • u ∈ interior D.toDissection.target.carrier)
    (hwall : ∀ x ∈ Ioo s t, ∀ i, X + x • u ∉ interior (D.toDissection.tile i).carrier)
    (hs : ¬ Straddled D.toDissection f c₀ (X + s • u))
    (ht : ¬ Straddled D.toDissection f c₀ (X + t • u)) :
    ∃ n : Fin 3 → ℕ,
      ∑ i : Fin 3, (n i : ℝ) * sideLen D i = t - s := by
  classical
  have hgd : ∀ y, f y = c₀ ↔ f y = c₀ := fun _ => Iff.rfl
  have hws := wall_sum hf hgd hf hX hu hu1 hst hint hwall hs ht
  -- hws : ∑ e ∈ (D.toDissection.lineChain f c₀).filter (...), dist ... = t - s
  -- Categorize each chain edge by which model side it matches
  choose cat hcat using chain_edge_length_mem_model D
  -- Define: for each Fin 3 category i, count the filtered edges with that category
  set S := (D.toDissection.lineChain f c₀).filter
      (fun e => (D.toDissection.tile e.1).edge e.2 ⊆ segment ℝ (X + s • u) (X + t • u))
  refine ⟨fun i => (S.filter (fun e => cat e = i)).card, ?_⟩
  -- Rewrite hws in terms of len D
  -- Convert hws to use `len D` (definitionally equal to dist ...)
  have hws' : ∑ e ∈ S, len D e = t - s := hws
  -- Fiber decomposition
  have hfiber : ∑ i : Fin 3, ∑ e ∈ S.filter (fun e => cat e = i), len D e
      = ∑ e ∈ S, len D e := Finset.sum_fiberwise S cat (len D)
  -- Each fiber has constant len = sideLen D i
  have hconst : ∀ i : Fin 3,
      ∑ e ∈ S.filter (fun e => cat e = i), len D e
        = ((S.filter (fun e => cat e = i)).card : ℝ) * sideLen D i := by
    intro i
    have hval : ∀ e ∈ S.filter (fun e => cat e = i), len D e = sideLen D i := fun e he => by
      rw [len_eq, hcat e, (Finset.mem_filter.mp he).2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  calc ∑ i : Fin 3, ((S.filter (fun e => cat e = i)).card : ℝ) * sideLen D i
      = ∑ i : Fin 3, ∑ e ∈ S.filter (fun e => cat e = i), len D e :=
        Finset.sum_congr rfl (fun i _ => (hconst i).symm)
    _ = ∑ e ∈ S, len D e := hfiber
    _ = t - s := hws'

/-- Same for the far side: `lineChain (-f) (-c₀)`. -/
theorem wall_word_far (D : CongruentDissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c₀ : ℝ)
    (X : Plane) (hX : f X = c₀)
    (u : Plane) (hu : f u = 0) (hu1 : ‖u‖ = 1)
    {s t : ℝ} (hst : s ≤ t)
    (hint : ∀ x ∈ Ioo s t, X + x • u ∈ interior D.toDissection.target.carrier)
    (hwall : ∀ x ∈ Ioo s t, ∀ i, X + x • u ∉ interior (D.toDissection.tile i).carrier)
    (hs : ¬ Straddled D.toDissection (-f) (-c₀) (X + s • u))
    (ht : ¬ Straddled D.toDissection (-f) (-c₀) (X + t • u)) :
    ∃ n : Fin 3 → ℕ,
      ∑ i : Fin 3, (n i : ℝ) * sideLen D i = t - s := by
  classical
  have hf' : (-f : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf (neg_eq_zero.mp h)
  have hX' : (-f) X = -c₀ := by simp [hX]
  have hu' : (-f) u = 0 := by simp [hu]
  have hgd : ∀ y, (-f) y = -c₀ ↔ f y = c₀ := neg_iff
  have hws := wall_sum hf' hgd hf hX hu hu1 hst hint hwall hs ht
  choose cat hcat using chain_edge_length_mem_model D
  set S := (D.toDissection.lineChain (-f) (-c₀)).filter
      (fun e => (D.toDissection.tile e.1).edge e.2 ⊆ segment ℝ (X + s • u) (X + t • u))
  refine ⟨fun i => (S.filter (fun e => cat e = i)).card, ?_⟩
  have hws' : ∑ e ∈ S, len D e = t - s := hws
  have hfiber : ∑ i : Fin 3, ∑ e ∈ S.filter (fun e => cat e = i), len D e
      = ∑ e ∈ S, len D e := Finset.sum_fiberwise S cat (len D)
  have hconst : ∀ i : Fin 3,
      ∑ e ∈ S.filter (fun e => cat e = i), len D e
        = ((S.filter (fun e => cat e = i)).card : ℝ) * sideLen D i := by
    intro i
    have hval : ∀ e ∈ S.filter (fun e => cat e = i), len D e = sideLen D i := fun e he => by
      rw [len_eq, hcat e, (Finset.mem_filter.mp he).2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  calc ∑ i : Fin 3, ((S.filter (fun e => cat e = i)).card : ℝ) * sideLen D i
      = ∑ i : Fin 3, ∑ e ∈ S.filter (fun e => cat e = i), len D e :=
        Finset.sum_congr rfl (fun i _ => (hconst i).symm)
    _ = ∑ e ∈ S, len D e := hfiber
    _ = t - s := hws'

/-! ## Part 2: interface_same_multiset — the short-interface matching theorem -/

/-- **Second clause of prop:interfacefloor (conditional on non-straddled endpoints).**
For a `CongruentDissection` with model tile `(ef, f²−e², f²)`, a wall stretch of length
less than `f · min(ef, f²−e²)` with unstraddled endpoints on both sides carries the
same edge-count vector on both sides.

The remaining geometric gap: proving that endpoints of maximal straight interfaces of a
congruent dissection are unstraddled (`IsMaximalStretch.not_straddled`). -/
theorem interface_same_multiset
    (D : CongruentDissection N)
    (e f : ℤ) (he : 0 < e) (hef : e < f) (hcop : IsCoprime f e)
    -- Model tile has side lengths a = ef, b = f²-e², c = f²
    (ha : sideLen D 0 = ((e * f : ℤ) : ℝ))
    (hb : sideLen D 1 = ((f ^ 2 - e ^ 2 : ℤ) : ℝ))
    (hc : sideLen D 2 = ((f ^ 2 : ℤ) : ℝ))
    -- Wall stretch parametrization
    (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c₀ : ℝ)
    (X : Plane) (hX : F X = c₀)
    (u : Plane) (hu : F u = 0) (hu1 : ‖u‖ = 1)
    {s t : ℝ} (hst : s < t)  -- strict: non-degenerate stretch
    (hint : ∀ x ∈ Ioo s t, X + x • u ∈ interior D.toDissection.target.carrier)
    (hwall : ∀ x ∈ Ioo s t, ∀ i, X + x • u ∉ interior (D.toDissection.tile i).carrier)
    -- Non-straddled on both sides at both endpoints
    (hnsL_s : ¬ Straddled D.toDissection F c₀ (X + s • u))
    (hnsL_t : ¬ Straddled D.toDissection F c₀ (X + t • u))
    (hnsR_s : ¬ Straddled D.toDissection (-F) (-c₀) (X + s • u))
    (hnsR_t : ¬ Straddled D.toDissection (-F) (-c₀) (X + t • u))
    -- Stretch length shorter than the floor
    (hshort : t - s < (f * min (e * f) (f ^ 2 - e ^ 2) : ℤ)) :
    -- Conclusion: same edge-count vector on both sides
    ∃ (nL nR : Fin 3 → ℕ),
      (∀ i, nL i = nR i) ∧
      ∑ i : Fin 3, (nL i : ℝ) * sideLen D i = t - s ∧
      ∑ i : Fin 3, (nR i : ℝ) * sideLen D i = t - s := by
  obtain ⟨nL, hL⟩ := wall_word_near D F hF c₀ X hX u hu hu1 hst.le hint hwall hnsL_s hnsL_t
  obtain ⟨nR, hR⟩ := wall_word_far D F hF c₀ X hX u hu hu1 hst.le hint hwall hnsR_s hnsR_t
  -- Check: nL = nR by showing the difference is zero via interface_floor
  suffices h : ∀ i, (nL i : ℤ) = (nR i : ℤ) by
    refine ⟨nL, nR, fun i => by exact_mod_cast h i, hL, hR⟩
  -- The difference Δᵢ = nLᵢ - nRᵢ satisfies Δ_0 * a + Δ_1 * b + Δ_2 * c = 0
  have hrel : (nL 0 : ℤ) * (e * f) + (nL 1 : ℤ) * (f ^ 2 - e ^ 2) + (nL 2 : ℤ) * f ^ 2 =
              (nR 0 : ℤ) * (e * f) + (nR 1 : ℤ) * (f ^ 2 - e ^ 2) + (nR 2 : ℤ) * f ^ 2 := by
    have hL' : (nL 0 : ℝ) * ((e * f : ℤ) : ℝ) + (nL 1 : ℝ) * ((f ^ 2 - e ^ 2 : ℤ) : ℝ) +
               (nL 2 : ℝ) * ((f ^ 2 : ℤ) : ℝ) = t - s := by
      have := hL; simp only [Fin.sum_univ_three] at this ⊢; rw [← ha, ← hb, ← hc]; exact this
    have hR' : (nR 0 : ℝ) * ((e * f : ℤ) : ℝ) + (nR 1 : ℝ) * ((f ^ 2 - e ^ 2 : ℤ) : ℝ) +
               (nR 2 : ℝ) * ((f ^ 2 : ℤ) : ℝ) = t - s := by
      have := hR; simp only [Fin.sum_univ_three] at this ⊢; rw [← ha, ← hb, ← hc]; exact this
    have heq : (nL 0 : ℝ) * ((e * f : ℤ) : ℝ) + (nL 1 : ℝ) * ((f ^ 2 - e ^ 2 : ℤ) : ℝ) +
               (nL 2 : ℝ) * ((f ^ 2 : ℤ) : ℝ) =
               (nR 0 : ℝ) * ((e * f : ℤ) : ℝ) + (nR 1 : ℝ) * ((f ^ 2 - e ^ 2 : ℤ) : ℝ) +
               (nR 2 : ℝ) * ((f ^ 2 : ℤ) : ℝ) := hL'.trans hR'.symm
    exact_mod_cast heq
  -- Let Δᵢ = nLᵢ - nRᵢ; they satisfy the relation
  set Δ : Fin 3 → ℤ := fun i => (nL i : ℤ) - nR i
  have hΔrel : Δ 0 * (e * f) + Δ 1 * (f ^ 2 - e ^ 2) + Δ 2 * f ^ 2 = 0 := by
    simp only [Δ]; linarith [hrel]
  -- If Δ ≠ 0, interface_floor gives oneSided Δ ≥ f * min(a,b) > t - s: contradiction
  by_contra hne
  obtain ⟨i, hi⟩ := not_forall.mp hne
  have hΔne : ¬ (Δ 0 = 0 ∧ Δ 1 = 0 ∧ Δ 2 = 0) := by
    intro ⟨h0, h1, h2⟩
    simp only [Δ, sub_eq_zero] at h0 h1 h2
    exact hi (by fin_cases i <;> simp_all)
  have hfloor := interface_floor e f (Δ 0) (Δ 1) (Δ 2) he hef hcop hΔrel hΔne
  -- oneSided Δ ≤ near-side total (positive part of Δᵢ ≤ nLᵢ for each i)
  have hef_pos : 0 < e * f := mul_pos he (lt_trans he hef)
  have hb_pos : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hc_pos : (0 : ℤ) < f ^ 2 := by nlinarith [lt_trans he hef]
  have honesided_le : (oneSided (Δ 0) (Δ 1) (Δ 2) (e * f) (f ^ 2 - e ^ 2) (f ^ 2) : ℤ) ≤
      ((nL 0 : ℤ) * (e * f) + (nL 1 : ℤ) * (f ^ 2 - e ^ 2) + (nL 2 : ℤ) * f ^ 2) := by
    simp only [oneSided, Δ]
    have h0 : max ((nL 0 : ℤ) - nR 0) 0 ≤ nL 0 := by omega
    have h1 : max ((nL 1 : ℤ) - nR 1) 0 ≤ nL 1 := by omega
    have h2 : max ((nL 2 : ℤ) - nR 2) 0 ≤ nL 2 := by omega
    nlinarith [mul_le_mul_of_nonneg_right h0 hef_pos.le,
               mul_le_mul_of_nonneg_right h1 hb_pos.le,
               mul_le_mul_of_nonneg_right h2 hc_pos.le]
  -- The near-side total in ℤ is less than f * min(a,b)
  have hL_int : (nL 0 : ℤ) * (e * f) + (nL 1 : ℤ) * (f ^ 2 - e ^ 2) + (nL 2 : ℤ) * f ^ 2 <
      f * min (e * f) (f ^ 2 - e ^ 2) := by
    have hL' : (nL 0 : ℝ) * ((e * f : ℤ) : ℝ) + (nL 1 : ℝ) * ((f ^ 2 - e ^ 2 : ℤ) : ℝ) +
               (nL 2 : ℝ) * ((f ^ 2 : ℤ) : ℝ) = t - s := by
      have := hL; simp only [Fin.sum_univ_three] at this ⊢; rw [← ha, ← hb, ← hc]; exact this
    have hts_real : (t - s : ℝ) < ((f * min (e * f) (f ^ 2 - e ^ 2) : ℤ) : ℝ) := by
      exact_mod_cast hshort
    exact_mod_cast hL'.symm ▸ hts_real
  linarith [hfloor, honesided_le, hL_int]

end Erdos634.Draft.InterfaceMultiset
