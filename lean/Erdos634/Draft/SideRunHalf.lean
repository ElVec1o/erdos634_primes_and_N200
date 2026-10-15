/-
Draft/SideRunHalf.lean -- the scale `2M = f` of the members `(1, f)`: `T_{f/2}(1,f)` has no tiling.

    theorem not_betaTilable_e1_le_half : 1 ≤ M → 2 * M ≤ f → ¬ BetaTilable 1 f M
    theorem thresholdAt_e1_le_half     : 1 ≤ M → 2 * M ≤ f → ThresholdAt 1 f M

When `2M = f` the base `M (3f² − 1)` of `T_M(1,f)` carries at most `2M = f` tiles with `c` on it, and by the side
theorem at least `f` consecutive tiles of one type `C1` or `C2`; so it carries no `a`-tile and its `c`-tiles are exactly
that run.  But both base corners have the angle `β` and carry one tile: without `a`-tiles the first base tile is `C2`
and the last is `C1`, two `c`-tiles of different types.  (`2M < f` is `SideRun.not_betaTilable_e1_half`.)

This uses an inequality between a count on the base and the length of a run, which is information on the order of the
tiles; it is not one of the invariants of `Draft.ThresholdBlind`, and it cannot go further: for `2M > f` the count
allows the run.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRun

namespace Erdos634.Draft.SideRun

section words
open Erdos634.Draft.W2E1 Erdos634.Draft.W2E1.Ty

/-- **The letters of the base when `2M = n`**: if the side `M (3n² − 1)` carries at least `n` letters `c`, it carries
exactly `n` of them and no letter `a`. -/
theorem rep_half {n x y z M : ℕ} (hn : 2 ≤ n) (h2 : 2 * M = n) (hz : n ≤ z)
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = (M:ℤ) * (3 * (n:ℤ) ^ 2 - 1)) :
    x = 0 ∧ z = n := by
  have hM : M < n := by omega
  have h3 : (z:ℤ) + M ≤ 3 * M := by
    have := rep_side hn hM (κ := 3) (by push_cast; exact h)
    push_cast at this
    exact this
  have hzn : z = n := by omega
  refine ⟨?_, hzn⟩
  have hzn' : (z:ℤ) = n := by exact_mod_cast hzn
  have h2' : (n:ℤ) = 2 * M := by exact_mod_cast h2.symm
  have hn' : (2:ℤ) ≤ n := by exact_mod_cast hn
  have hb : (0:ℤ) < (n:ℤ) ^ 2 - 1 := by nlinarith
  rw [hzn'] at h
  have e : (x:ℤ) * n = ((M:ℤ) - y) * ((n:ℤ) ^ 2 - 1) := by linear_combination h - (n:ℤ) ^ 2 * h2'
  have hyM : (M:ℤ) ≤ y := by
    by_contra hc
    push_neg at hc
    have hdvd : (n:ℤ) ∣ ((M:ℤ) - y) * ((n:ℤ) ^ 2 - 1) := ⟨x, by rw [← e]; ring⟩
    have hco : IsCoprime (n:ℤ) ((n:ℤ) ^ 2 - 1) := ⟨n, -1, by ring⟩
    have hd := hco.dvd_of_dvd_mul_right hdvd
    have hle := Int.le_of_dvd (by linarith) hd
    have hy0 : (0:ℤ) ≤ y := by positivity
    have hMn : (M:ℤ) < n := by exact_mod_cast hM
    linarith
  have hxn : (x:ℤ) * n ≤ 0 := by
    rw [e]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
  have hx0 : (0:ℤ) ≤ x := by positivity
  have hx : (x:ℤ) = 0 := by
    by_contra hne
    have hpos : (0:ℤ) < x := lt_of_le_of_ne hx0 (Ne.symm hne)
    have : (0:ℤ) < (x:ℤ) * n := mul_pos hpos (by linarith)
    linarith
  exact_mod_cast hx

/-- **No typed word at the scale `2M = n`**: a word with the rules of the side theorem, total length `M (3n² − 1)`
and a first tile showing `β` on the left does not exist. -/
theorem no_side_word_half {n m M : ℕ} (hn : 2 ≤ n) (h2 : 2 * M = n) (hm : 0 < m) (τ : ℕ → Ty)
    (hsum : ((∑ k ∈ Finset.range m, (τ k).len n : ℕ) : ℝ) = (M:ℝ) * (3 * (n:ℝ) ^ 2 - 1))
    (hr : SideRules n m τ) (hQ : τ 0 = A1 ∨ τ 0 = C2) : False := by
  obtain ⟨i, him, hrun⟩ := side_word n m τ hm hr
  have hz := cC_run τ i n m him hrun
  obtain ⟨x, hx⟩ : ∃ x, x = ∑ k ∈ Finset.range m, (τ k).cA := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = ∑ k ∈ Finset.range m, (τ k).cB := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z, z = ∑ k ∈ Finset.range m, (τ k).cC := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ k ∈ Finset.range m, (τ k).len n := ⟨_, rfl⟩
  have hrep : x * n + y * (n * n - 1) + z * (n * n) = S := by
    rw [hS, Finset.sum_congr rfl (fun k _ => len_eq n (τ k)), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← hx, ← hy, ← hzdef]
  rw [← hS] at hsum
  have h1 := toInt (by omega : 1 ≤ n) hrep
  have hZ : (S:ℤ) = (M:ℤ) * (3 * (n:ℤ) ^ 2 - 1) := by
    have h' : (((S:ℤ)) : ℝ) = (((M:ℤ) * (3 * (n:ℤ) ^ 2 - 1) : ℤ) : ℝ) := by
      push_cast; exact hsum
    exact Int.cast_injective h'
  rw [hZ] at h1
  rw [← hzdef] at hz
  obtain ⟨hx0, hzn⟩ := rep_half hn h2 hz h1
  -- no a-tile
  have hA : ∀ k, k < m → (τ k).cA = 0 := by
    intro k hk
    have h0 : ∑ k ∈ Finset.range m, (τ k).cA = 0 := by rw [← hx]; exact hx0
    exact (Finset.sum_eq_zero_iff.mp h0) k (Finset.mem_range.mpr hk)
  -- the c-tiles are exactly the run
  have hsub : Finset.Ico i (i + n) ⊆ Finset.range m := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact Finset.mem_range.mpr (by omega)
  have hone : ∀ k ∈ Finset.Ico i (i + n), (τ k).cC = 1 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    obtain ⟨j, rfl⟩ : ∃ j, k = i + j := ⟨k - i, by omega⟩
    rcases hrun with h | h
    · rw [h j (by omega)]; rfl
    · rw [h j (by omega)]; rfl
  have hin : ∑ k ∈ Finset.Ico i (i + n), (τ k).cC = n := by
    rw [Finset.sum_congr rfl hone, Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one,
      Nat.add_sub_cancel_left]
  have hout : ∑ k ∈ Finset.range m \ Finset.Ico i (i + n), (τ k).cC = 0 := by
    have hsd : (∑ k ∈ Finset.range m \ Finset.Ico i (i + n), (τ k).cC)
        + ∑ k ∈ Finset.Ico i (i + n), (τ k).cC = ∑ k ∈ Finset.range m, (τ k).cC := Finset.sum_sdiff hsub
    have htot : ∑ k ∈ Finset.range m, (τ k).cC = n := by rw [← hzdef]; exact hzn
    rw [hin, htot] at hsd
    omega
  have hC : ∀ k, k < m → (τ k).cC = 1 → i ≤ k ∧ k < i + n := by
    intro k hk hc
    by_contra hnot
    have hmem : k ∈ Finset.range m \ Finset.Ico i (i + n) := by
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]; exact ⟨hk, hnot⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hout) k hmem
    omega
  -- the first tile is C2, the last is C1
  have h0 : τ 0 = C2 := by
    rcases hQ with h | h
    · have hc := hA 0 hm
      rw [h] at hc
      exact absurd hc (by decide)
    · exact h
  have hl : τ (m - 1) = C1 := by
    rcases hr.rB with h | h
    · have hc := hA (m - 1) (by omega)
      rw [h] at hc
      exact absurd hc (by decide)
    · exact h
  obtain ⟨a1, a2⟩ := hC 0 hm (by rw [h0]; rfl)
  obtain ⟨b1, b2⟩ := hC (m - 1) (by omega) (by rw [hl]; rfl)
  have hi0 : i = 0 := by omega
  subst hi0
  rcases hrun with h | h
  · have hc := h 0 (by omega)
    rw [Nat.zero_add, h0] at hc
    exact absurd hc (by decide)
  · have hc := h (m - 1) (by omega)
    rw [Nat.zero_add, hl] at hc
    exact absurd hc (by decide)

end words

section geometry
open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.Geometry.Dissection
  Erdos634.Draft.W2E1 Set

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay : ℝ}

namespace Setup

/-- at a corner `Q` of angle `β` the first base tile is `A1` or `C2` -/
theorem first_type_beta (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t) (hax : ax = t * uu n)
    (hay' : ay = t * hh n) {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}
    (Ch : Chain D n L m X tile τ) : τ 0 = Ty.A1 ∨ τ 0 = Ty.C2 := by
  obtain ⟨hαβ', hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hβ2π, hγπ', hγ0, hπ0⟩ := distinct_of_angleData S.hA
  have h := Ch.htile 0 Ch.hm0
  rw [Ch.hX0] at h
  have ha := (S.angles h).1
  obtain ⟨k', m', j', -, -, -, hk', -, -, -⟩ := h
  have hmem : D.target.pts 0 ∈ (D.tile (tile 0)).carrier := by
    rw [S.Q_eq, ← hk']; exact subset_convexHull ℝ _ ⟨k', rfl⟩
  have hang := S.corner_tile_beta 0 (S.corner_left_beta ht hax hay') hmem
  rw [S.Q_eq, ha] at hang
  exact Ty.aL_eq_beta hαβ' hβγ _ hang

/-- **No dissection at the scale `2M = n`** of a target whose side `QB` has the length `M (3n² − 1)` and both
corners `β`. -/
theorem no_tiling_half (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * uu n) (hay' : ay = t * hh n) {M : ℕ} (h2 : 2 * M = n)
    (hL : L = (M:ℝ) * (3 * (n:ℝ) ^ 2 - 1)) : False := by
  obtain ⟨m, X, tile, τ, hm0, hX0, hXm, hstep, htile⟩ := S.typed_chain
  have Ch : Chain D n L m X tile τ := ⟨hm0, hX0, hXm, hstep, htile⟩
  have hn1 : 1 ≤ n := by have := S.hn2; omega
  refine no_side_word_half S.hn2 h2 hm0 τ ?_ (S.side_rules Co Ch) (S.first_type_beta ht hax hay' Ch)
  rw [Nat.cast_sum, Finset.sum_congr rfl (fun k _ => Ty.len_cast n hn1 (τ k))]
  have h3 : ∀ k ∈ Finset.range m, (τ k).lenR n = X (k + 1) - X k := by
    intro k hk
    rw [hstep k (Finset.mem_range.mp hk)]; ring
  rw [Finset.sum_congr rfl h3, Finset.sum_range_sub, hXm, hX0, sub_zero, hL]

end Setup

open Erdos634.BaseBetaTargetCoord Erdos634.Draft.FDBBaseBetaE1 in
/-- **`T_M(1,n)` at the scale `2M = n`, side-length form**: no congruent dissection (any number of tiles) has a target
with sides `M n³`, `M n³`, `M (3n² − 1)` and a model with sides `n`, `n² − 1`, `n²`. -/
theorem no_dissection_T_half (n M : ℕ) (hM : 1 ≤ M) (h : 2 * M = n) {N : ℕ} (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M:ℝ) * (n:ℝ) ^ 3) ((M:ℝ) * (n:ℝ) ^ 3) ((M:ℝ) * (3 * (n:ℝ) ^ 2 - 1)))
    (hMod : HasSides D₀.model (n:ℝ) ((n:ℝ) ^ 2 - 1) ((n:ℝ) ^ 2)) : False := by
  have hn2 : 2 ≤ n := by omega
  have hf1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  obtain ⟨D, S⟩ := setup_T n M hn2 hM D₀ hT hMod
  have hu := uu_spec hf1
  have ht : (0:ℝ) < (M:ℝ) * (n:ℝ) ^ 2 := mul_pos hMr (by nlinarith)
  exact S.no_tiling_half (corners_T n M hf1 hMr) ht (by linear_combination (-(M:ℝ)) * hu) rfl h rfl

end geometry

section final
open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.Draft.FDBBaseBetaE1
  Erdos634.Draft.CollarG Erdos634.Draft.UniformThreshold Erdos634.Draft.W2E1

/-- **`T_M(1,f)` has no tiling whenever `2M ≤ f`** (`M ≥ 1`). -/
theorem not_betaTilable_e1_le_half (f M : ℕ) (hM : 1 ≤ M) (h : 2 * M ≤ f) : ¬ BetaTilable 1 f M := by
  by_cases hlt : 2 * M < f
  · exact not_betaTilable_e1_half f M hM hlt
  · have heq : 2 * M = f := by omega
    rintro ⟨N, D, hTs, hMs⟩
    refine no_dissection_T_half f M hM heq D ?_ ?_
    · exact hasSides_cast' hTs (by ring) (by ring) (by push_cast; ring)
    · exact hasSides_cast' hMs (by push_cast; ring) (by push_cast; ring) (by ring)

/-- the threshold statement holds at the scales `2M ≤ f` of the members `(1, f)` -/
theorem thresholdAt_e1_le_half (f M : ℕ) (hM : 1 ≤ M) (h : 2 * M ≤ f) : ThresholdAt 1 f M :=
  ⟨fun hT => absurd hT (not_betaTilable_e1_le_half f M hM h), fun hle => absurd hle (by omega)⟩

end final

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.no_side_word_half
#print axioms Erdos634.Draft.SideRun.no_dissection_T_half
#print axioms Erdos634.Draft.SideRun.not_betaTilable_e1_le_half
#print axioms Erdos634.Draft.SideRun.thresholdAt_e1_le_half
