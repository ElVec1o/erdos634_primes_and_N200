/-
Draft/WGapGen3.lean -- written 16 November 2026 (session 15).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, the whole chord above layer `m`).
Not imported by any aggregate.  No sorry, no native_decide.
`chord_gen_all`: for the chord of `k` lattice `a`-edges `[pi(a,m+1), pi(a-k,m+1)]` (tiles `gamma(a-t,m)`, `t < k`; `nu(a-t,m)`, `t <= k`; cover `hΞ` at the bottom end, cover `hZc` at the top end):
EVERY tile above the chord is `nu(a-s-1,m+1)`, `s < k` (induction along the chord: `chord_gen_first` at the bottom, `chord_gen_inner` at each inner point).
This is step (S4)+(S5) of ROUND15_PLAN.md and replaces `chord2_first` + `chord2_second` (and `chord_a_step` for one edge) at every `i`, `m`, `k`.
-/
import Erdos634.Draft.WGapGen2

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

variable {N : ℕ} {D : CongruentDissection N}

section gen3

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
theorem chord_gen_all (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i a k : ℕ) (m : ℝ)
    (hk1 : 1 ≤ k) (hka : k ≤ a) (hkf : k ≤ f - 1) {d : Plane}
    (hNu : ∀ t : ℕ, t ≤ k → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i ((a : ℝ) - t + 1) m) (PIR (e : ℝ) f x j i ((a : ℝ) - t) m)
        (PIR (e : ℝ) f x j i ((a : ℝ) - t) (m + 1)))
    (hΓ : ∀ t : ℕ, t < k → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i ((a : ℝ) - t) m) (PIR (e : ℝ) f x j i ((a : ℝ) - t) (m + 1))
        (PIR (e : ℝ) f x j i ((a : ℝ) - t - 1) (m + 1)))
    (hΞ : EdgeCoverS D (PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) d (-1))
    (hcr : 0 < cross d (PIR (e : ℝ) f x j i ((a : ℝ) - 1) (m + 1) - PIR (e : ℝ) f x j i (a : ℝ) (m + 1)))
    (hZc : EdgeCoverS D (PIR (e : ℝ) f x j i ((a : ℝ) - k) (m + 1)) (wvec (e : ℝ) f x) 1) :
    ∀ s : ℕ, s < k → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i ((a : ℝ) - s) (m + 1)) (PIR (e : ℝ) f x j i ((a : ℝ) - s - 1) (m + 1))
        (PIR (e : ℝ) f x j i ((a : ℝ) - s - 1) (m + 1 + 1)) := by
  intro s
  induction s with
  | zero =>
    intro _
    obtain ⟨tNa, hNa⟩ := hNu 0 (by omega)
    have hNa' : HasV D tNa (PIR (e : ℝ) f x j i ((a : ℝ) + 1) m) (PIR (e : ℝ) f x j i (a : ℝ) m)
        (PIR (e : ℝ) f x j i (a : ℝ) (m + 1)) :=
      hasV_congr hNa (PIR_congr (by simp) rfl) (PIR_congr (by simp) rfl) (PIR_congr (by simp) rfl)
    obtain ⟨T, hT⟩ := chord_gen_first S x j i a k m hk1 hka hkf hNa' hΓ hΞ hcr hZc
    exact ⟨T, hasV_congr hT (PIR_congr (by simp) rfl) (PIR_congr (by simp) rfl) (PIR_congr (by simp) rfl)⟩
  | succ s ih =>
    intro hs
    obtain ⟨τν, hν⟩ := ih (by omega)
    set u : ℕ := a - (s + 1) with hudef
    set r : ℕ := k - (s + 1) with hrdef
    have hu : (u : ℝ) = (a : ℝ) - s - 1 := by
      rw [hudef, Nat.cast_sub (by omega)]; push_cast; ring
    have hr : (r : ℝ) = (k : ℝ) - s - 1 := by
      rw [hrdef, Nat.cast_sub (by omega)]; push_cast; ring
    obtain ⟨τ2, hτ2⟩ := hΓ s (by omega)
    obtain ⟨tNb, hNb⟩ := hNu (s + 1) (by omega)
    have hΓ' : ∀ t : ℕ, t < r → ∃ T : Fin N,
        HasV D T (PIR (e : ℝ) f x j i ((u : ℝ) - t) m) (PIR (e : ℝ) f x j i ((u : ℝ) - t) (m + 1))
          (PIR (e : ℝ) f x j i ((u : ℝ) - t - 1) (m + 1)) := by
      intro t ht
      obtain ⟨T, hT⟩ := hΓ (t + s + 1) (by omega)
      refine ⟨T, hasV_congr hT ?_ ?_ ?_⟩
      · exact PIR_congr (by rw [hu]; try push_cast; try ring) rfl
      · exact PIR_congr (by rw [hu]; try push_cast; try ring) rfl
      · exact PIR_congr (by rw [hu]; try push_cast; try ring) rfl
    have hΓ2 : HasV D τ2 (PIR (e : ℝ) f x j i ((u : ℝ) + 1) m) (PIR (e : ℝ) f x j i ((u : ℝ) + 1) (m + 1))
        (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) :=
      hasV_congr hτ2 (PIR_congr (by rw [hu]; try push_cast; try ring) rfl) (PIR_congr (by rw [hu]; try push_cast; try ring) rfl)
        (PIR_congr (by rw [hu]; try push_cast; try ring) rfl)
    have hNb' : HasV D tNb (PIR (e : ℝ) f x j i ((u : ℝ) + 1) m) (PIR (e : ℝ) f x j i (u : ℝ) m)
        (PIR (e : ℝ) f x j i (u : ℝ) (m + 1)) := by
      refine hasV_congr hNb ?_ ?_ ?_
      · exact PIR_congr (by rw [hu]; try push_cast; try ring) rfl
      · exact PIR_congr (by rw [hu]; try push_cast; try ring) rfl
      · exact PIR_congr (by rw [hu]; try push_cast; try ring) rfl
    have hν' : HasV D τν (PIR (e : ℝ) f x j i ((u : ℝ) + 1) (m + 1)) (PIR (e : ℝ) f x j i (u : ℝ) (m + 1))
        (PIR (e : ℝ) f x j i (u : ℝ) (m + 1 + 1)) :=
      hasV_congr hν (PIR_congr (by rw [hu]; try push_cast; try ring) rfl) (PIR_congr (by rw [hu]; try push_cast; try ring) rfl)
        (PIR_congr (by rw [hu]; try push_cast; try ring) rfl)
    have hZc' : EdgeCoverS D (PIR (e : ℝ) f x j i ((u : ℝ) - r) (m + 1)) (wvec (e : ℝ) f x) 1 := by
      have : PIR (e : ℝ) f x j i ((u : ℝ) - r) (m + 1) = PIR (e : ℝ) f x j i ((a : ℝ) - k) (m + 1) :=
        PIR_congr (by rw [hu, hr]; ring) rfl
      rw [this]; exact hZc
    obtain ⟨T, hT⟩ := chord_gen_inner S x j i u r m (by omega) (by omega) (by omega) hΓ' hΓ2 hNb' hν' hZc'
    exact ⟨T, hasV_congr hT (PIR_congr (by rw [hu]; try push_cast; try ring) rfl) (PIR_congr (by rw [hu]; try push_cast; try ring) rfl)
      (PIR_congr (by rw [hu]; try push_cast; try ring) rfl)⟩

end gen3

#print axioms chord_gen_all

end Erdos634.Draft.WGapStmt
