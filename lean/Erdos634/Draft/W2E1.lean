/-
For every integer `f ≥ 3` the triangle `W_2(1,f)` with sides `2f(f²−1)`, `2(2f²−1)`, `2f³` cannot be cut into congruent copies of the tile
`(f, f²−1, f²)`.

* `Setup.rules`: the typed side word of a dissection of `W_2(1,n)` in normal position satisfies the seven rules
  (R-Q, R-B, R-GG from `W2E1Frame`; R-H2, R-H1, R-C from `W2E1HalfTurn`; R-CH from `W2E1Last`);
* `Setup.no_tiling`: with the word theorem `no_word_fn` (`W2E1Words`), no such dissection exists;
* `no_dissection_W2`: no congruent dissection has a target congruent to `W2 n` and a model congruent to the tile
  (isometries including reflections, any vertex order, any number of tiles);
* `s4inst_2_1 : S4Inst 2 1 f` (`Draft/RWInst.lean`) and `not_wTilable_1_f_2 : ¬ WTilable 1 f 2`
  (`Draft/CollarG.lean`), for every `f ≥ 3`.

No sorry, no native_decide.
-/
import Erdos634.Draft.W2E1Last
import Erdos634.Draft.RWInst
import Erdos634.Draft.CollarG
import Erdos634.Draft.HasSidesPerm

namespace Erdos634.Draft.W2E1

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose Set

namespace Setup

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ : ℝ}

/-- **The typed side word of a dissection of `W_2(1,n)` satisfies the rules of the proof.** -/
theorem rules (S : Setup D n α β γ) {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}
    (hm0 : 0 < m) (hX0 : X 0 = 0) (hXm : X m = Lw n)
    (hstep : ∀ k, k < m → X (k + 1) = X k + (τ k).lenR n)
    (htile : ∀ k, k < m → BaseTile D n (tile k) (τ k) (X k)) : RulesFn m τ := by
  have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by have := S.f0; positivity
  have hprevX : ∀ k, 0 < k → k < m + 1 → X (k - 1) + (τ (k - 1)).lenR n = X k := by
    intro k hk0 hkm
    have h1 := hstep (k - 1) (by omega)
    rw [Nat.sub_add_cancel hk0] at h1
    exact h1.symm
  have hXnn : ∀ k, k < m → 0 ≤ X k := fun k hk => (S.baseTile_range (htile k hk)).1
  have hXlt : ∀ k, k < m → X k < Lw n := by
    intro k hk
    have h1 := (S.baseTile_range (htile k hk)).2
    have h2 := Ty.lenR_pos S.f2 (τ k)
    linarith
  have hXpos : ∀ k, 0 < k → k < m → 0 < X k := by
    intro k hk0 hk
    have h1 := hprevX k hk0 (by omega)
    have h2 := hXnn (k - 1) (by omega)
    have h3 := Ty.lenR_pos S.f2 (τ (k - 1))
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- R-Q
    intro _
    have h := htile 0 hm0
    rw [hX0] at h
    exact S.rule_Q h
  · -- R-B
    intro _
    have hx := hprevX m hm0 (by omega)
    rw [hXm] at hx
    exact S.rule_B (htile (m - 1) (by omega)) hx
  · -- R-GG
    intro k hk hg
    have h := htile k (by omega)
    have h' := htile (k + 1) hk
    have hs := hstep k (by omega)
    rw [hs] at h'
    have hx0 : 0 < X k + (τ k).lenR n := by
      rw [← hs]; exact hXpos (k + 1) (by omega) hk
    have hxL : X k + (τ k).lenR n < Lw n := by
      rw [← hs]; exact hXlt (k + 1) hk
    exact S.rule_GG h h' hx0 hxL hg
  · -- R-H2
    intro k hk hC hyp
    have h := htile k hk
    rw [hC] at h
    have hprev : X k = 0 ∨ ∃ (jp : Fin N) (t' : Ty) (xp : ℝ),
        BaseTile D n jp t' xp ∧ xp + t'.lenR n = X k ∧ t'.gR := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · left; rw [h0]; exact hX0
      · right
        rcases hyp with h1 | h1
        · exact absurd h1 (by omega)
        · exact ⟨tile (k - 1), τ (k - 1), X (k - 1), htile (k - 1) (by omega),
            hprevX k h0 (by omega), h1⟩
    obtain ⟨hxL, hnext⟩ := S.rule_H2 h hprev
    have hs := hstep k hk
    rw [hC] at hs
    have hs' : X (k + 1) = X k + (n:ℝ) ^ 2 := hs
    have hk1 : k + 1 < m := by
      by_contra hcon
      have hkm : k + 1 = m := by omega
      rw [hkm, hXm] at hs'
      linarith
    refine ⟨hk1, hnext (tile (k + 1)) (τ (k + 1)) ?_⟩
    have h' := htile (k + 1) hk1
    rw [hs'] at h'
    exact h'
  · -- R-H1
    intro k hk hC hg
    have h := htile k (by omega)
    rw [hC] at h
    have hs := hstep k (by omega)
    rw [hC] at hs
    have hs' : X (k + 1) = X k + (n:ℝ) ^ 2 := hs
    have h' := htile (k + 1) hk
    rw [hs'] at h'
    obtain ⟨hx0, hprev⟩ := S.rule_H1 h h' hg
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, hX0] at hx0
        exact absurd hx0 (lt_irrefl 0)
      · exact h0
    exact ⟨hk0, hprev (tile (k - 1)) (τ (k - 1)) (X (k - 1)) (htile (k - 1) (by omega))
      (hprevX k hk0 (by omega))⟩
  · -- R-C
    intro _ hC
    have h := htile (m - 1) (by omega)
    rw [hC] at h
    have hx : X (m - 1) + (n:ℝ) ^ 2 = Lw n := by
      have h1 := hprevX m hm0 (by omega)
      rw [hC, hXm] at h1
      exact h1
    obtain ⟨hx0, hprev⟩ := S.rule_C h hx
    have hm1 : 1 < m := by
      by_contra hcon
      have hm1' : m - 1 = 0 := by omega
      rw [hm1', hX0] at hx0
      exact absurd hx0 (lt_irrefl 0)
    refine ⟨hm1, hprev (tile (m - 2)) (τ (m - 2)) (X (m - 2)) (htile (m - 2) (by omega)) ?_⟩
    have h1 := hprevX (m - 1) (by omega) (by omega)
    rw [show m - 1 - 1 = m - 2 by omega] at h1
    exact h1
  · -- R-CH
    intro hm3 hC hC2 hg
    have h4 := htile (m - 1) (by omega)
    rw [hC] at h4
    have h3 := htile (m - 2) (by omega)
    rw [hC2] at h3
    have h2 := htile (m - 3) (by omega)
    have e1 : X (m - 3) + (τ (m - 3)).lenR n = X (m - 2) := by
      have h1 := hprevX (m - 2) (by omega) (by omega)
      rw [show m - 2 - 1 = m - 3 by omega] at h1
      exact h1
    have e2 : X (m - 1) = X (m - 2) + (n:ℝ) ^ 2 := by
      have h1 := hprevX (m - 1) (by omega) (by omega)
      rw [show m - 1 - 1 = m - 2 by omega, hC2] at h1
      exact h1.symm
    have e3 : X (m - 2) + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 = Lw n := by
      have h1 := hprevX m hm0 (by omega)
      rw [hC, hXm, e2] at h1
      exact h1
    rw [e2] at h4
    exact S.rule_CH h2 e1 hg h3 h4 e3

/-- **No congruent dissection of `W_2(1,n)` in normal position exists**, `n ≥ 3`. -/
theorem no_tiling (S : Setup D n α β γ) : False := by
  obtain ⟨m, X, tile, τ, hm0, hX0, hXm, hstep, htile⟩ := S.typed_chain
  have hR := S.rules hm0 hX0 hXm hstep htile
  have hn1 : 1 ≤ n := by have := S.hn3; omega
  refine no_word_fn n S.hn3 m τ ?_ hR
  have h1 : ((∑ k ∈ Finset.range m, (τ k).len n : ℕ) : ℝ) = Lw n := by
    rw [Nat.cast_sum, Finset.sum_congr rfl (fun k _ => Ty.len_cast n hn1 (τ k))]
    have h2 : ∀ k ∈ Finset.range m, (τ k).lenR n = X (k + 1) - X k := by
      intro k hk
      rw [hstep k (Finset.mem_range.mp hk)]; ring
    rw [Finset.sum_congr rfl h2, Finset.sum_range_sub, hXm, hX0, sub_zero]
  have h3 : ((4 * (n * n) - 2 : ℕ) : ℝ) = Lw n := by
    have h4 : 2 ≤ 4 * (n * n) := by have := S.hn3; nlinarith
    rw [Nat.cast_sub h4]; push_cast; unfold Lw; ring
  exact Nat.cast_injective (R := ℝ) (h1.trans h3.symm)

end Setup

/-- **`prop:w2e1`, congruence form.**  For `n ≥ 3` no congruent dissection (any number of tiles) has a target
congruent to `W_2(1,n)` and a model congruent to the tile `(n, n²−1, n²)`. -/
theorem no_dissection_W2 (n : ℕ) (hn3 : 3 ≤ n) {N : ℕ} (D₀ : CongruentDissection N)
    (htgt : D₀.target.Congruent (W2 (n:ℝ) (by exact_mod_cast (show 1 < n by omega))))
    (hmod : D₀.model.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega)))) : False := by
  obtain ⟨g, σ, hg⟩ := htgt
  have S : Setup (Erdos634.E1NormalForm.normalFormC D₀ g σ hmod) n (modelAlpha 1 n) (modelBeta 1 n)
      (2 * modelAlpha 1 n + modelBeta 1 n) :=
    ⟨hn3, Erdos634.E1NormalForm.modelData_of_model_eq _ n (by omega) rfl,
      Erdos634.E1NormalForm.angleData_model n (by omega),
      fun _ => Erdos634.E1NormalForm.normalFormC_target D₀ hg hmod⟩
  exact S.no_tiling

open Erdos634.Draft.FDBBaseBetaE1 in
theorem hasSides_cast {T : Erdos634.Geometry.Tri} {a b c a' b' c' : ℝ} (h : HasSides T a b c) (ha : a = a')
    (hb : b = b') (hc : c = c') : HasSides T a' b' c' := by
  subst ha; subst hb; subst hc; exact h

open Erdos634.Draft.FDBBaseBetaE1 in
/-- **`prop:w2e1`, side-length form**: no congruent dissection has a target with sides `2n³`, `2n(n²−1)`, `4n²−2`
and a model with sides `n`, `n²−1`, `n²`. -/
theorem no_dissection_hasSides (n : ℕ) (hn3 : 3 ≤ n) {N : ℕ} (D : CongruentDissection N)
    (hT : HasSides D.target (2 * (n:ℝ) ^ 3) (2 * n * ((n:ℝ) ^ 2 - 1)) (Lw n))
    (hM : HasSides D.model (n:ℝ) ((n:ℝ) ^ 2 - 1) ((n:ℝ) ^ 2)) : False := by
  have hf1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hf2 : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  refine no_dissection_W2 n hn3 D ?_ ?_
  · exact congruent_of_hasSides hT (dist_BA hf1) (by rw [dist_comm]; exact dist_QA hf1)
      (dist_QB hf1)
  · obtain ⟨s0, s1, s2⟩ := modelTri_sides hf2
    exact congruent_of_hasSides hM s0 s1 s2

open Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.NSQRW in
/-- **`prop:w2e1`**: the S4 instance `(S', e, f) = (2, 1, f)` has no dissection, for every `f ≥ 3`: the triangle
with `oppLen = (2(2f²−1), 2f(f²−1), 2f³)` is not cut into copies of the tile `(f, f²−1, f²)`. -/
theorem s4inst_2_1 (f : ℕ) (hf : 3 ≤ f) : S4Inst 2 1 f := by
  intro N D h0 h1 h2 hm
  obtain ⟨σ, m0, m1, m2⟩ := hm
  have hT := hasSides_swap (hasSides_rot (hasSides_of_oppLen h0 h1 h2))
  have hM := hasSides_of_sigma σ m0 m1 m2
  refine no_dissection_hasSides f hf D ?_ ?_
  · refine hasSides_cast hT ?_ ?_ ?_
    · push_cast; ring
    · push_cast; ring
    · push_cast; unfold Lw; ring
  · refine hasSides_cast hM ?_ ?_ ?_
    · push_cast; ring
    · push_cast; ring
    · push_cast; ring

open Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.CollarG in
/-- **`W_2` of the member `(1, f)` has no tiling**, for every `f ≥ 3`. -/
theorem not_wTilable_1_f_2 (f : ℕ) (hf : 3 ≤ f) : ¬ WTilable 1 f 2 := by
  rintro ⟨D, hTs, hMs⟩
  refine no_dissection_hasSides f hf D ?_ ?_
  · refine hasSides_cast (hasSides_rot (hasSides_rot hTs)) ?_ ?_ ?_
    · push_cast; ring
    · push_cast; ring
    · push_cast; unfold Lw; ring
  · refine hasSides_cast hMs ?_ ?_ ?_
    · push_cast; ring
    · push_cast; ring
    · ring

open Erdos634.TPErdos Erdos634.RunPartition in
/-- **`first_edge` is not vacuous**: on `TPErdos.wallDissection`, with both ends of the wall `[(0,0), (1,1)]`
clamped by the target boundary (the configuration of `RunPartition.run_partition_witness`), a chain edge inside
the wall starts at `(0,0)`. -/
theorem first_edge_witness :
    ∃ e ∈ wallDissection.lineChain wallF 0,
      (wallDissection.tile e.1).edge e.2 ⊆ segment ℝ wallU wallV ∧
      wallU ∈ (wallDissection.tile e.1).edge e.2 :=
  first_edge wallDissection wallF wallF_ne 0 wallU_ne_wallV (P' := mkPt (-1) (-1)) (Q' := mkPt 2 2)
    (wall_hS (left_mem_segment ℝ _ _)) (wall_hS (right_mem_segment ℝ _ _))
    (by rw [wallF_pt]; norm_num) (by rw [wallF_pt]; norm_num) wallU_mem wallV_mem wall_hint wall_hwall
    (fun e _ => not_straddles_of_outside _ wall_left_outside _ _)
    (fun e _ => not_straddles_of_outside _ wall_right_outside _ _)

open Erdos634.Draft.CollarG in
/-- **The bound `f ≥ 3` is sharp**: `W_2` of the member `(1, 2)` HAS a tiling (the seed at scale `f = 2`: the triangle
`(12, 14, 16)` cut into `28` copies of `(2, 3, 4)`).  So `not_wTilable_1_f_2` is false at `f = 2`. -/
theorem wTilable_1_2_2 : WTilable 1 2 2 := wTilable_seed 1 2 le_rfl (by norm_num)

end Erdos634.Draft.W2E1

#print axioms Erdos634.Draft.W2E1.first_edge_witness
#print axioms Erdos634.Draft.W2E1.Setup.rules
#print axioms Erdos634.Draft.W2E1.no_dissection_W2
#print axioms Erdos634.Draft.W2E1.s4inst_2_1
#print axioms Erdos634.Draft.W2E1.not_wTilable_1_f_2
#print axioms Erdos634.Draft.W2E1.wTilable_1_2_2
