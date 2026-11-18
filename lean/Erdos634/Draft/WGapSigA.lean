/-
Draft/WGapSigA.lean -- written 15 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.5 step (a)).
Not imported by any aggregate.  No sorry, no native_decide.
* `beside_mirror`: `SideRunGA.beside_core` without the induction hypothesis: the tile `E` beside the `b`-edge of `U(n,j)` either gives (K1) at the origin `p(n,0)`
  (then Theorem K is contradicted, all sizes) or is the mirror tile at the shifted origin: `MirrorAt D e f ε (shiftX f ε x n) j` (conclusion, no `False`).
* `noN_mirror`: `SideRunGA.noN_M` without `hne`/`IH`: if `N_i(j0)` is a tile then the tile `E′` beside the `b`-edge of `U(i+1,j0)` is the mirror tile at the origin `p(i+1,0)`
  (this is the Ω configuration of PROOF 7.1 minus the filler `F`), for ANY size.
* `sigma_le_e`: `Σ[m]` for `m ≤ e` (Lemma M at the apex uses only `E_{y₀}`), the first rung of the induction.
-/
import Erdos634.Draft.WGapM2

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

section siga

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

theorem beside_mirror (S : SetupG D e f α β γ L ax ay) (hε : ε = 1 ∨ ε = -1) {n s' j : ℕ} {c η : ℝ}
    (hc : c = (n : ℝ)) (hη : η = (j : ℝ))
    (hch : ChordsAt D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n))
    (hK2 : K2G D (e : ℝ) (f : ℝ) ε x (s' + n) j)
    (hK3 : K3G D (e : ℝ) (f : ℝ) ε x ((s' + n : ℕ) : ℝ) (j : ℝ))
    (hjs : j < s') (hsf : s' < f)
    (hE : ColNext D (e : ℝ) (f : ℝ) ε x c η)
    (hnγ : ∀ (iT : Fin N) (k m' : Fin 3), k ≠ m' → (D.tile iT).pts k = lpG (e : ℝ) (f : ℝ) ε x c η →
      (D.tile iT).pts m' = lpG (e : ℝ) (f : ℝ) ε x c (η + 1) →
      (∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile iT).pts i) ≤ lvG (e : ℝ) (f : ℝ) ε x c) →
      (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) ε x c η) ≠ γ) :
    MirrorAt D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) (j : ℝ) := by
  subst hc
  subst hη
  have he2 : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hK2' := K2G_shift hK2
  have hK3' := K3G_shift_nat (D := D) he2 hK3
  rcases hE with ⟨iT, k, m', t, hkm, hk, hm', ht, hlen, hle⟩ | ⟨iT, k, m', hkm, hk, hm', hle⟩
  · exfalso
    have hK1 : K1J D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) j := by
      rw [K1J_shift he2]
      exact ⟨iT, k, m', t, hkm, hk, hm', ht, hlen, hle⟩
    have Cj := CtxJ.of_K1J S hε hch hK1
    exact Cj.K_allGJ (s' - j) (by omega) s' j le_rfl hjs hsf rfl hK2' hK3'
  · exact mirror_of_b_n S he2 hkm hk hm' hle (hnγ iT k m' hkm hk hm' hle)

/-- **`N_i(j0)` is a tile ⟹ the tile `E′` beside the `b`-edge of `U(i+1,j0)` is the mirror tile at the origin `p(i+1,0)`** (any size; PROOF 7.5 (a2): (a2-c) is Theorem K) -/
theorem noN_mirror (S : SetupG D e f α β γ L ax ay) (hε1 : (1 : ℝ) ^ 2 = 1) {s j0 i : ℕ}
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 x s j0) (hK3 : K3G D (e : ℝ) (f : ℝ) 1 x (s : ℝ) (j0 : ℝ))
    (hsf : s < f) (hi : i + 2 ≤ s - j0) :
    ∀ tN, HasV D tN (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ))
      (lpG (e : ℝ) (f : ℝ) 1 x (i : ℝ) ((j0 : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) - nuG (e : ℝ) (f : ℝ)) ((j0 : ℝ) + 2 + nuG (e : ℝ) (f : ℝ))) →
      MirrorAt D (e : ℝ) (f : ℝ) 1 (shiftX (f : ℝ) 1 x (i + 1)) (j0 : ℝ) := by
  intro tN hN
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨tUi, hUi⟩ := hK2.1 i j0 le_rfl (by omega)
  obtain ⟨tU2, hU2⟩ := hK2.1 (i + 1) j0 le_rfl (by omega)
  rw [Nat.cast_add, Nat.cast_one] at hU2
  have hch' := chordsAt_shift_K2 S hK2 (n := i + 1) (by omega) (by omega)
  have hs' : s - (i + 1) + (i + 1) = s := by omega
  have hK2' : K2G D (e : ℝ) (f : ℝ) 1 x (s - (i + 1) + (i + 1)) j0 := by rw [hs']; exact hK2
  have hK3' : K3G D (e : ℝ) (f : ℝ) 1 x ((s - (i + 1) + (i + 1) : ℕ) : ℝ) (j0 : ℝ) := by
    rw [hs']; exact hK3
  have hL : lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1 - 1) (j0 : ℝ) ∈ D.target.carrier := by
    rw [show lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1 - 1) (j0 : ℝ) = lpG (e : ℝ) (f : ℝ) 1 x (i : ℝ) (j0 : ℝ)
      from lpG_congr (by ring) rfl]
    exact hUi.mem₁
  have hint := bedge_interior C (Nat.cast_nonneg j0) hU2 hL
  have hcl : ∃ P' : Plane, FXG (e : ℝ) (f : ℝ) 1 P' = lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ∧
      lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ) ∈
        openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ((j0 : ℝ) + 1)) ∧
      ∀ ed ∈ D.lineChain (FXG (e : ℝ) (f : ℝ) 1) (lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1)),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ))
          (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ((j0 : ℝ) + 1)) := by
    rcases Nat.eq_zero_or_pos j0 with hj0 | hj0
    · exact clamp_side S hε1 _ _ (by rw [hj0]; simp)
    · obtain ⟨j', rfl⟩ : ∃ j', j0 = j' + 1 := ⟨j0 - 1, by omega⟩
      obtain ⟨tD, hD⟩ := hK2.2 i j' (by omega) (by omega)
      have hle : ∀ i', FXG (e : ℝ) (f : ℝ) 1 ((D.tile tD).pts i') ≤ lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) := by
        refine hD.all (P := fun p => FXG (e : ℝ) (f : ℝ) 1 p ≤ lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1))
          (le_of_eq (FXG_lp hε1 _ _)) ?_ (le_of_eq (FXG_lp hε1 _ _))
        dsimp only
        rw [FXG_lp hε1]
        exact lvG_le he0 hef (by linarith)
      obtain ⟨k, m, j₃, hkm, hkj, hmj, hk, hm, hj⟩ := hD
      rw [Nat.cast_add, Nat.cast_one]
      exact clamp_tile S hε1 hkj hk hj hle
  have hE := col_next S hε1 hU2 hint hcl
  have hnγ : ∀ (iT : Fin N) (k m' : Fin 3), k ≠ m' →
      (D.tile iT).pts k = lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ) →
      (D.tile iT).pts m' = lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ((j0 : ℝ) + 1) →
      (∀ i', FXG (e : ℝ) (f : ℝ) 1 ((D.tile iT).pts i') ≤ lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1)) →
      (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ)) ≠ γ := by
    intro iT k m' hkm hk hm' hle hγ0
    rcases Nat.eq_zero_or_pos j0 with hj0 | hj0
    · -- the point `p(i+1, 0)` is on the side
      subst hj0
      obtain ⟨hx0, hxL, -⟩ := open_shift_K2 S hK2 (n := i + 1) (by omega) (by omega)
      have hfr := S.base_frontier hx0 hxL
      have hpt : mkPt (shiftX (f : ℝ) 1 x (i + 1)) 0 = lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) 0 := by
        unfold lpG shiftX; exact mkPt_congr (by push_cast; ring) (by ring)
      rw [hpt] at hfr
      simp only [Nat.cast_zero] at hUi hN hγ0
      exact noN_gamma_bdry S hε1 hUi hN hγ0 hfr
    · obtain ⟨j', rfl⟩ : ∃ j', j0 = j' + 1 := ⟨j0 - 1, by omega⟩
      obtain ⟨tDL, hDL⟩ := hK2.2 i j' (by omega) (by omega)
      obtain ⟨tUl, hUl⟩ := hK2.1 (i + 1) j' (by omega) (by omega)
      obtain ⟨tDl, hDl⟩ := hK2.2 (i + 1) j' (by omega) (by omega)
      obtain ⟨tUr, hUr⟩ := hK2.1 (i + 1) (j' + 1) le_rfl (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hUl hDl hUr hUi hN hγ0 hle hk hm'
      exact noN_gamma_int S hε1 hDL hUl hDl hUr hUi hN hle hγ0
  exact beside_mirror S (Or.inl rfl) (n := i + 1) (s' := s - (i + 1)) (j := j0)
    (c := (i : ℝ) + 1) (η := (j0 : ℝ)) (by norm_num) rfl hch' hK2' hK3'
    (by omega) (by omega) hE hnγ

/-- **`Σ[m]` for `m ≤ e`**: Lemma M at the apex (only `E_{y₀}` is used) -/
theorem sigma_le_e (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (m : ℕ) (hm : m ≤ e) : SigmaAll D e f m := by
  intro c₀ J hA s y₀ hJ hy hsf hsm hσ
  obtain ⟨hS1, hK2, hK3⟩ := hσ
  exact lemma_M S c₀ s y₀ (fun _ => h2) hy hsf (by omega) (hS1 y₀ hJ le_rfl) hK2 hK3

end siga

#print axioms beside_mirror
#print axioms noN_mirror
#print axioms sigma_le_e

end Erdos634.Draft.WGapStmt
