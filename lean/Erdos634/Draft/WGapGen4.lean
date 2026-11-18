/-
Draft/WGapGen4.lean -- written 16 November 2026 (session 15).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, State(m,tau) and the inductive step).
Not imported by any aggregate.  No sorry, no native_decide.
* `RLSt D e f x j i m τ` : the State(m,τ) of PROOF 8.2 in minimal form: (nu) `nu(t',m')` tiles for all `m' <= m`, `τ <= t' <= i - m'`; (ga) the last layer's `gamma(t',m-1)`, `τ < t' <= i-m+1`; (left) a tile at `X0 = pi(τ,μ0)` with an `a`- or `c`-edge along `L^(τ)`.
* `ColD`: the dichotomy of the wedge `(2α,3α)` at `pi(t,m)`: `gamma(t,m)` or the FLIPPED tile (`FlipTile`).
* `last_flip`: the largest flipped column.
* `rl_step_core`: State(m,τ) with `τ + m < i`, together with the column dichotomies of layer `m`, gives `False` (flip at the last column, `rl_close`) or State(m+1,τ') for some `τ <= τ'`, `τ' + m + 1 <= i`
  (chord of `k = i-m-τ'` a-edges by `chord_gen_all`, covers by `rl_alpha`, `rl_beta`).
-/
import Erdos634.Draft.WGapGen3

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

section gen4

variable {N : ℕ}

/-- the flipped tile at `pi(t,m)`: an `α`-tile with its `c`-edge `dcvec` on `L^(t)` (left of the line) -/
def FlipTile (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (j i : ℕ) (t m : ℝ) : Prop :=
  ∃ (F : Fin N) (R : Plane), HasV D F (PIR (e : ℝ) f x j i t m) (PIR (e : ℝ) f x j i t m + (1 : ℝ) • dcvec (e : ℝ) f x) R ∧
    0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j i t m)

/-- the column dichotomy at `pi(t,m)`: `gamma(t,m)` or the flipped tile -/
def ColD (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (j i : ℕ) (t m : ℝ) : Prop :=
  (∃ T : Fin N, HasV D T (PIR (e : ℝ) f x j i t m) (PIR (e : ℝ) f x j i t (m + 1)) (PIR (e : ℝ) f x j i (t - 1) (m + 1))) ∨
    FlipTile D e f x j i t m

/-- State(m,τ) of PROOF 8.2 -/
structure RLSt (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (j i m τ : ℕ) : Prop where
  nu : ∀ m' : ℕ, m' ≤ m → ∀ t' : ℕ, τ ≤ t' → t' + m' ≤ i → ∃ T : Fin N,
    HasV D T (PIR (e : ℝ) f x j i ((t' : ℝ) + 1) (m' : ℝ)) (PIR (e : ℝ) f x j i (t' : ℝ) (m' : ℝ))
      (PIR (e : ℝ) f x j i (t' : ℝ) ((m' : ℝ) + 1))
  ga : ∀ m1 : ℕ, m = m1 + 1 → ∀ t' : ℕ, τ < t' → t' + m ≤ i + 1 → ∃ T : Fin N,
    HasV D T (PIR (e : ℝ) f x j i (t' : ℝ) (m1 : ℝ)) (PIR (e : ℝ) f x j i (t' : ℝ) ((m1 : ℝ) + 1))
      (PIR (e : ℝ) f x j i ((t' : ℝ) - 1) ((m1 : ℝ) + 1))
  left : ∃ μ0 : ℕ, μ0 ≤ m ∧ ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
    HasV D F (PIR (e : ℝ) f x j i (τ : ℝ) (μ0 : ℝ)) (PIR (e : ℝ) f x j i (τ : ℝ) (μ0 : ℝ) + lamc • dcvec (e : ℝ) f x) R ∧
    0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j i (τ : ℝ) (μ0 : ℝ))

theorem last_flip (P : ℕ → Prop) (τ a : ℕ) :
    ∃ τ' : ℕ, τ ≤ τ' ∧ (τ' = τ ∨ (τ < τ' ∧ τ' ≤ a ∧ P τ')) ∧ ∀ t : ℕ, τ' < t → t ≤ a → ¬ P t := by
  induction a with
  | zero => exact ⟨τ, le_rfl, Or.inl rfl, fun t h1 h2 => (by omega : False).elim⟩
  | succ a ih =>
    by_cases h : τ < a + 1 ∧ P (a + 1)
    · exact ⟨a + 1, by omega, Or.inr ⟨h.1, le_rfl, h.2⟩, fun t h1 h2 => (by omega : False).elim⟩
    · obtain ⟨τ', h1, h2, h3⟩ := ih
      refine ⟨τ', h1, ?_, ?_⟩
      · rcases h2 with h2 | ⟨h2a, h2b, h2c⟩
        · exact Or.inl h2
        · exact Or.inr ⟨h2a, by omega, h2c⟩
      · intro t ht1 ht2
        by_cases hta : t ≤ a
        · exact h3 t ht1 hta
        · have : t = a + 1 := by omega
          subst this
          intro hp
          exact h ⟨by omega, hp⟩

variable {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 32000000 in
theorem rl_step_core (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i m τ : ℕ) (hi : i + 1 ≤ f - 1)
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j) < 0)
    (hτ : τ + m < i) (st : RLSt D e f x j i m τ)
    (hcol : ∀ t : ℕ, τ < t → t + m ≤ i → ColD D e f x j i (t : ℝ) (m : ℝ)) :
    ∃ τ' : ℕ, τ ≤ τ' ∧ τ' + (m + 1) ≤ i ∧ RLSt D e f x j i (m + 1) τ' := by
  have he0 := S.e0
  have hef := S.hef'
  have hκ := kapG_pos he0 hef
  have hcs : ∀ p q : ℕ, q ≤ p → ((p - q : ℕ) : ℝ) = (p : ℝ) - q := fun p q h => Nat.cast_sub h
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = i - m := ⟨_, rfl⟩
  have haR : (a : ℝ) = (i : ℝ) - m := by rw [ha, hcs i m (by omega)]
  have hmi : m ≤ i := by omega
  have hnuA : ∀ m' : ℕ, m' ≤ m → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i ((i : ℝ) - m' + 1) (m' : ℝ)) (PIR (e : ℝ) f x j i ((i : ℝ) - m') (m' : ℝ))
        (PIR (e : ℝ) f x j i ((i : ℝ) - m') ((m' : ℝ) + 1)) := by
    intro m' hm'
    obtain ⟨T, hT⟩ := st.nu m' hm' (i - m') (by omega) (by omega)
    refine ⟨T, hasV_congr hT ?_ ?_ ?_⟩
    · exact PIR_congr (by rw [hcs i m' (by omega)]) rfl
    · exact PIR_congr (by rw [hcs i m' (by omega)]) rfl
    · exact PIR_congr (by rw [hcs i m' (by omega)]) rfl
  obtain ⟨τ', hττ', hcase, hmax⟩ := last_flip (fun t : ℕ => FlipTile D e f x j i (t : ℝ) (m : ℝ)) τ a
  have hτ'a : τ' ≤ a := by
    rcases hcase with h | ⟨h1, h2, h3⟩
    · omega
    · exact h2
  have hGm : ∀ t : ℕ, τ' < t → t ≤ a → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i (t : ℝ) (m : ℝ)) (PIR (e : ℝ) f x j i (t : ℝ) ((m : ℝ) + 1))
        (PIR (e : ℝ) f x j i ((t : ℝ) - 1) ((m : ℝ) + 1)) := by
    intro t h1 h2
    rcases hcol t (by omega) (by omega) with h | h
    · exact h
    · exact absurd h (hmax t h1 h2)
  have hL : ∃ μ0 : ℕ, μ0 ≤ m ∧ ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f x j i (τ' : ℝ) (μ0 : ℝ)) (PIR (e : ℝ) f x j i (τ' : ℝ) (μ0 : ℝ) + lamc • dcvec (e : ℝ) f x) R ∧
      0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j i (τ' : ℝ) (μ0 : ℝ)) := by
    rcases hcase with h | ⟨h1, h2, ⟨F, R, hF, hcr⟩⟩
    · rw [h]; exact st.left
    · exact ⟨m, le_rfl, F, R, 1, Or.inr rfl, hF, hcr⟩
  obtain ⟨μ0, hμ0, hleft⟩ := hL
  have hnuB : ∀ m' : ℕ, μ0 ≤ m' → m' ≤ m → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i ((τ' : ℝ) + 1) (m' : ℝ)) (PIR (e : ℝ) f x j i (τ' : ℝ) (m' : ℝ))
        (PIR (e : ℝ) f x j i (τ' : ℝ) ((m' : ℝ) + 1)) :=
    fun m' _ hm' => st.nu m' hm' τ' hττ' (by omega)
  have Zc := rl_beta S x j i τ' μ0 m hμ0 hmi hi hnuB hleft
  by_cases hlast : τ' = a
  · exfalso
    exact rl_close S x j i τ' μ0 m hμ0 hmi hi (by omega) hnuA hP4 hnuB hleft
  · -- the chord
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = a - τ' := ⟨_, rfl⟩
    have hkR : (k : ℝ) = (a : ℝ) - τ' := by rw [hk, hcs a τ' hτ'a]
    have hk1 : 1 ≤ k := by omega
    have hka : k ≤ a := by omega
    have hkf : k ≤ f - 1 := by omega
    have hAα := rl_alpha S x j i m hi hmi hnuA hP4
    have hB : PIR (e : ℝ) f x j i (a : ℝ) ((m : ℝ) + 1) = lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j + (((m + 1 : ℕ) : ℝ)) •
        (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j) := by
      rw [show (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 by push_cast; ring]
      exact PIR_on_L3 he0 hef x j i _ _ (by rw [haR]; ring)
    have hΞ : EdgeCoverS D (PIR (e : ℝ) f x j i (a : ℝ) ((m : ℝ) + 1))
        (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j) (-1) := by
      rw [hB]; exact hAα
    have hcr : 0 < cross (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (PIR (e : ℝ) f x j i ((a : ℝ) - 1) ((m : ℝ) + 1) - PIR (e : ℝ) f x j i (a : ℝ) ((m : ℝ) + 1)) := by
      have : cross (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
          (PIR (e : ℝ) f x j i ((a : ℝ) - 1) ((m : ℝ) + 1) - PIR (e : ℝ) f x j i (a : ℝ) ((m : ℝ) + 1)) = kapG (e : ℝ) f := by
        rw [PIR_lp he0 hef, PIR_lp he0 hef, cross_lpG, haR]; ring
      rw [this]; exact hκ
    have hNu : ∀ t : ℕ, t ≤ k → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j i ((a : ℝ) - t + 1) (m : ℝ)) (PIR (e : ℝ) f x j i ((a : ℝ) - t) (m : ℝ))
          (PIR (e : ℝ) f x j i ((a : ℝ) - t) ((m : ℝ) + 1)) := by
      intro t ht
      obtain ⟨T, hT⟩ := st.nu m le_rfl (a - t) (by omega) (by omega)
      refine ⟨T, hasV_congr hT ?_ ?_ ?_⟩
      · exact PIR_congr (by rw [hcs a t (by omega)]) rfl
      · exact PIR_congr (by rw [hcs a t (by omega)]) rfl
      · exact PIR_congr (by rw [hcs a t (by omega)]) rfl
    have hΓ : ∀ t : ℕ, t < k → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j i ((a : ℝ) - t) (m : ℝ)) (PIR (e : ℝ) f x j i ((a : ℝ) - t) ((m : ℝ) + 1))
          (PIR (e : ℝ) f x j i ((a : ℝ) - t - 1) ((m : ℝ) + 1)) := by
      intro t ht
      obtain ⟨T, hT⟩ := hGm (a - t) (by omega) (by omega)
      rw [hcs a t (by omega)] at hT
      exact ⟨T, hT⟩
    have hZc : EdgeCoverS D (PIR (e : ℝ) f x j i ((a : ℝ) - k) ((m : ℝ) + 1)) (wvec (e : ℝ) f x) 1 := by
      have : PIR (e : ℝ) f x j i ((a : ℝ) - k) ((m : ℝ) + 1) = PIR (e : ℝ) f x j i (τ' : ℝ) ((m : ℝ) + 1) :=
        PIR_congr (by rw [hkR]; ring) rfl
      rw [this]; exact Zc
    have hchord := chord_gen_all S x j i a k (m : ℝ) hk1 hka hkf hNu hΓ hΞ hcr hZc
    refine ⟨τ', hττ', by omega, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · -- nu
      intro m' hm' t' ht1 ht2
      by_cases hmm : m' ≤ m
      · exact st.nu m' hmm t' (by omega) (by omega)
      · have hm1 : m' = m + 1 := by omega
        subst hm1
        obtain ⟨s, hs⟩ : ∃ s : ℕ, s = a - 1 - t' := ⟨_, rfl⟩
        have hsR : (s : ℝ) + t' + 1 = a := by exact_mod_cast (show s + t' + 1 = a by omega)
        obtain ⟨T, hT⟩ := hchord s (by omega)
        refine ⟨T, hasV_congr hT ?_ ?_ ?_⟩
        · exact PIR_congr (by linarith) (by push_cast; ring)
        · exact PIR_congr (by linarith) (by push_cast; ring)
        · exact PIR_congr (by linarith) (by push_cast; ring)
    · -- ga
      intro m1 hm1 t' ht1 ht2
      have : m1 = m := by omega
      subst this
      exact hGm t' ht1 (by omega)
    · exact ⟨μ0, by omega, hleft⟩

end gen4

#print axioms rl_step_core

end Erdos634.Draft.WGapStmt
