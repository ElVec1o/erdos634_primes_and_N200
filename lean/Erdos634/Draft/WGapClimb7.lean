/-
Draft/WGapClimb7.lean -- written 16 November 2026 (session 16).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 steps (1), (2) at `h_lambda = 0`, `lambda >= 1`).
Not imported by any aggregate.  No sorry, no native_decide.
* `PIR_ij`: `PIR x j i t m` depends on `j + i` only;
* `row_cases`: step (1): the tile `S_x` beside the `a`-edge of `U(x, j+lam)` is `D(x, j+lam)` or `N_x(j+lam)` (the third alternative, `b` or `c` on `m_s`, is `Sigma` of size `x+1 <= i`);
* `rowN_false`: step (2): `S_{i-lam-1} = N_{i-lam-1}(j+lam)` is impossible (the mirror tile at the origin `p(i-lam,0)` (`noN_mirror2`), `rl_A0_fill` there, `rl_nat` at `t = i - lam`); generalizes `lam1_N_false`.
-/
import Erdos634.Draft.WGapClimb6

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

theorem PIR_ij {e f : ℝ} (x : ℝ) {j1 i1 j2 i2 : ℕ} (h : j1 + i1 = j2 + i2) (t m : ℝ) :
    PIR e f x j1 i1 t m = PIR e f x j2 i2 t m := by
  unfold PIR
  refine lpG_congr rfl ?_
  have h' : ((j1 : ℝ) + i1) = (j2 : ℝ) + i2 := by exact_mod_cast h
  linarith

section climb7

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
theorem row_cases (S : SetupG D e f α β γ L ax ay) {c₀ J j i lam : ℕ} (hA : IsApex D e f c₀ J)
    (hJ : J ≤ j + lam) (hij : i + j + 1 ≤ f - 1) (hlam1 : 1 ≤ lam) (hlam : lam < i)
    (hSt : ClimbSt D e f c₀ J j i lam) (hSig : SigmaAll D e f i) {x : ℕ} (hx : x < i - lam) :
    DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x : ℝ) ((j + lam : ℕ) : ℝ) ∨ NTile D e f c₀ x (j + lam) := by
  obtain ⟨hC1, hS1, hUa, hDa⟩ := hSt
  have C : CtxBase D e f α β γ L ax ay 1 (xo f c₀) := ⟨S, Or.inl rfl⟩
  obtain ⟨l1, hl1⟩ : ∃ l1, lam = l1 + 1 := ⟨lam - 1, by omega⟩
  obtain ⟨tU, hUt⟩ := hUa x (j + lam) (by omega) (by omega)
  obtain ⟨tU1, hU1t⟩ := hUa (x + 1) (j + lam) (by omega) (by omega)
  have hD1n : DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (((x + 1 : ℕ)) : ℝ) (((j + lam - 1 : ℕ)) : ℝ) :=
    hDa (x + 1) (j + lam - 1) (by omega) (by omega)
  have hcl := C.m_clamp_natG x (j + lam) (Or.inr ⟨by omega, hD1n⟩)
  have hFw : ∃ δ : ℝ, 0 < δ ∧ lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((x : ℝ) + 1 + δ) ((j + lam : ℕ) : ℝ) ∈ D.target.carrier := by
    refine ⟨1, one_pos, ?_⟩
    have := hU1t.mem₂
    rw [show (((x + 1 : ℕ) : ℝ) + 1) = (x : ℝ) + 1 + 1 by push_cast; ring] at this
    exact this
  rcases C.m_nextG hUt hFw hcl with ⟨tD0, hD0t⟩ | ⟨tN0, hN0t⟩ | ⟨w, hw⟩
  · left; exact ⟨tD0, hD0t⟩
  · right; exact ⟨tN0, hN0t⟩
  · exfalso
    have hs : ((x : ℝ) + ((j + lam : ℕ) : ℝ) + 1) = ((x + (j + lam) + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hs] at hw
    have hK3 : K3G D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((x + (j + lam) + 1 : ℕ) : ℝ) ((j + lam : ℕ) : ℝ) := Or.inr ⟨w, hw⟩
    have hK2 : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x + (j + lam) + 1) (j + lam) :=
      ⟨fun i' j'' hj'' hij'' => hUa i' j'' hj'' (by omega), fun i' j'' hj'' hij'' => hDa i' j'' hj'' (by omega)⟩
    exact hSig c₀ J hA (x + (j + lam) + 1) (j + lam) (by omega) (by omega) (by omega) (by omega) ⟨hS1, hK2, hK3⟩

set_option maxHeartbeats 32000000 in
theorem rowN_false (S : SetupG D e f α β γ L ax ay) {c₀ J j i lam : ℕ}
    (hij : i + j + 1 ≤ f - 1) (hlam1 : 1 ≤ lam) (hlam : lam < i)
    (hSt : ClimbSt D e f c₀ J j i lam) (hP4 : Pi4 D e f c₀ i j)
    (hN : NTile D e f c₀ (i - lam - 1) (j + lam)) : False := by
  obtain ⟨hC1, hS1, hUa, hDa⟩ := hSt
  obtain ⟨l1, rfl⟩ : ∃ l1, lam = l1 + 1 := ⟨lam - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = l1 + 1 + k + 1 := ⟨i - (l1 + 1) - 1, by omega⟩
  have hkk : l1 + 1 + k + 1 - (l1 + 1) - 1 = k := by omega
  rw [hkk] at hN
  obtain ⟨tN, hNt⟩ := hN
  have hN1 := hC1 (k + 1) (by omega) (by omega)
  have e1 : j + (l1 + 1 + k + 1) - (k + 1) = j + l1 + 1 := by omega
  rw [e1] at hN1
  obtain ⟨tN1, hN1t⟩ := hN1
  obtain ⟨tDL, hDLt⟩ := hDa k (j + l1) (by omega) (by omega)
  obtain ⟨tUl, hUlt⟩ := hUa (k + 1) (j + l1) (by omega) (by omega)
  obtain ⟨tDl, hDlt⟩ := hDa (k + 1) (j + l1) (by omega) (by omega)
  obtain ⟨tUr, hUrt⟩ := hUa (k + 1) (j + l1 + 1) (by omega) (by omega)
  obtain ⟨tUi, hUit⟩ := hUa k (j + l1 + 1) (by omega) (by omega)
  have hmir := noN_mirror2 S (xo f c₀) (i := k) (η := ((j + l1 : ℕ) : ℝ)) (Nat.cast_nonneg _)
    (tDL := tDL) (tUl := tUl) (tDl := tDl) (tUr := tUr) (tUi := tUi) (tN := tN) (tN1 := tN1)
    (hv hDLt) (hv hUlt) (hv hDlt) (hv hUrt) (hv hUit) (hv hNt) (hv hN1t)
  have hx' : shiftX (f : ℝ) 1 (xo f c₀) (k + 1) = xshk (f : ℝ) (k + 1) (xo f c₀) := rfl
  rw [hx'] at hmir
  obtain ⟨tE, hE⟩ := (mirrorAt_iff_UTM_gen S _ _).1 hmir
  have hUi' : HasV D tUr (p0j1 (e : ℝ) f (xshk (f : ℝ) (k + 1) (xo f c₀)) (j + l1))
      (pA1 (e : ℝ) f (xshk (f : ℝ) (k + 1) (xo f c₀)) (j + l1)) (pA0 (e : ℝ) f (xshk (f : ℝ) (k + 1) (xo f c₀)) (j + l1)) :=
    hasV_congr hUrt (toShk (by push_cast; ring) (by push_cast; ring)) (toShk (by push_cast; ring) (by push_cast; ring))
      (toShk (by push_cast; ring) (by push_cast; ring))
  have hN0' : HasV D tN1 (pA1 (e : ℝ) f (xshk (f : ℝ) (k + 1) (xo f c₀)) (j + l1))
      (pA0 (e : ℝ) f (xshk (f : ℝ) (k + 1) (xo f c₀)) (j + l1)) (pC0 (e : ℝ) f (xshk (f : ℝ) (k + 1) (xo f c₀)) (j + l1)) :=
    hasV_congr hN1t (toShk (by push_cast; ring) (by push_cast; ring)) (toShk (by push_cast; ring) (by push_cast; ring))
      (toShk (by push_cast; ring) (by push_cast; ring))
  have hE' : HasV D tE (mpG (e : ℝ) f 1 (xshk (f : ℝ) (k + 1) (xo f c₀)) 0 (((j + l1 : ℕ) : ℝ) + 1))
      (mpG (e : ℝ) f 1 (xshk (f : ℝ) (k + 1) (xo f c₀)) (0 + 1) (((j + l1 : ℕ) : ℝ) + 1))
      (mpG (e : ℝ) f 1 (xshk (f : ℝ) (k + 1) (xo f c₀)) 0 (((j + l1 : ℕ) : ℝ) + 1 + 1)) := hE
  obtain ⟨F, R, lamc, hl, hF, hR⟩ := rl_A0_fill S (xshk (f : ℝ) (k + 1) (xo f c₀)) (j + l1) hE' hUi' hN0'
  rw [PIR_shk, dcvec_shk] at hF hR
  have hPe : ∀ t m : ℝ, PIR (e : ℝ) f (xo f c₀) (j + l1) (1 + (k + 1)) t m = PIR (e : ℝ) f (xo f c₀) j (l1 + 1 + k + 1) t m :=
    fun t m => PIR_ij _ (by omega) t m
  rw [hPe] at hF hR
  have hz : (((0 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ)) = (((l1 + 1 + k + 1 - (l1 + 1) : ℕ)) : ℝ) := by
    have : l1 + 1 + k + 1 - (l1 + 1) = k + 1 := by omega
    rw [this]; push_cast; ring
  rw [hz] at hF hR
  refine rl_nat S c₀ j (l1 + 1 + k + 1) (l1 + 1 + k + 1 - (l1 + 1)) (by omega) (by omega) ?_ ?_ ?_ hP4 ⟨F, R, lamc, hl, hF, hR⟩
  · intro t' h1 h2'
    exact hC1 t' (by omega) h2'
  · intro t' h1 h2'
    exact hUa t' (j + (l1 + 1 + k + 1) - t') (by omega) (by omega)
  · intro t' h1 h2'
    exact hDa (t' - 1) (j + (l1 + 1 + k + 1) - t') (by omega) (by omega)

end climb7

#print axioms row_cases
#print axioms rowN_false

end Erdos634.Draft.WGapStmt
