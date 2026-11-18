/-
Draft/WGapRL3.lean -- written 16 November 2026 (session 9).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.1, P8.2 step (alpha)).
Not imported by any aggregate.  The reflected lattice of RL in REAL LATTICE COORDINATES (key observation: the mirror direction `d_c = p'(1,0) - p'(0,0) = p(-1, s) - p(0,0)`, `s = sMir`, so
`pi(t,m) := A_t + m w = lpG x (t - m nu) ((j+i+1-t) + m nu s)`, with `w = nu d_c`, `nu = nuG`, and the identity `nu (s - 1) = 1`; all cross products are `kapG * det` by `cross_lpG`).
`PIR e f x j i t m` = `pi(t,m)`.  `PIR_on_L3`: `pi(i+1-mu, mu) = O + mu d`, `O = p(i+1,j)`, `d = Y - O` (`Y` = third vertex of `N_i(j)`).
`rl_alpha` (RL step (alpha)): the tiles `nu(i-m',m')`, `m' <= m` (c-edges on `Lambda_3`, on its left) and the tile of (r2) = `Pi4` (the `b`-edge from `O`, on its right)
give a tile covering the open half-disk at `B_m = O + (m+1) d` on the right of `Lambda_3` (`EdgeCoverS _ _ _ (-1)`), by `fault_cover` with `(A5)` at multiplier `m+1 <= f-1`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapRL2
import Erdos634.Draft.WGapDefs3
import Erdos634.Draft.WGapMirrorLat

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

/-- the reflected lattice point `pi(t,m) = A_t + m w` of PROOF 8.1 (`A_t = p(t, j+i+1-t)`, `w = nu * (p(-1,s) - p(0,0))`) in lattice coordinates -/
noncomputable def PIR (e f x : ℝ) (j i : ℕ) (t m : ℝ) : Plane :=
  lpG e f 1 x (t - m * nuG e f) ((j : ℝ) + i + 1 - t + m * nuG e f * sMir e f)

/-- `nu (s - 1) = 1` -/
theorem nu_s {e f : ℝ} (he : 0 < e) (hef : e < f) : nuG e f * (sMir e f - 1) = 1 := by
  have hf : 0 < f := he.trans hef
  have h1 : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have h2 : f ^ 2 ≠ 0 := by positivity
  unfold nuG sMir
  field_simp
  ring

/-- `|Y - O| = c` for `O = p(i+1,j)`, `Y = p(i - nu, j + 2 + nu)` -/
theorem dist_dLam {e f : ℝ} (he : 0 < e) (hef : e < f) (x ξ η : ℝ) :
    dist (lpG e f 1 x (ξ - nuG e f) (η + 2 + nuG e f)) (lpG e f 1 x (ξ + 1) η) = f ^ 2 := by
  have hf : 0 < f := he.trans hef
  have hν := nuG_spec he hef
  refine dist_lpG he hef (by norm_num) (by positivity) ?_
  unfold QfG
  have hb : f ^ 2 - e ^ 2 = f ^ 2 * nuG e f := by linarith
  have h2 : 2 * f ^ 2 - e ^ 2 = f ^ 2 * (1 + nuG e f) := by linarith
  rw [hb, h2]
  ring

section rl3

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- the point `pi(i+1-mu, mu)` lies on `Lambda_3`: `= O + mu (Y - O)` -/
theorem PIR_on_L3 {e f : ℝ} (he : 0 < e) (hef : e < f) (x : ℝ) (j i : ℕ) (mu t : ℝ) (ht : t = (i : ℝ) + 1 - mu) :
    PIR e f x j i t mu = lpG e f 1 x ((i : ℝ) + 1) j +
      mu • (lpG e f 1 x ((i : ℝ) - nuG e f) ((j : ℝ) + 2 + nuG e f) - lpG e f 1 x ((i : ℝ) + 1) j) := by
  have hns := nu_s he hef
  have h1 := lineMap_lpG e f 1 x ((i : ℝ) + 1) (j : ℝ) ((i : ℝ) - nuG e f) ((j : ℝ) + 2 + nuG e f) mu
  rw [AffineMap.lineMap_apply] at h1
  simp only [vsub_eq_sub, vadd_eq_add] at h1
  have h2 : lpG e f 1 x ((i : ℝ) + 1) j +
      mu • (lpG e f 1 x ((i : ℝ) - nuG e f) ((j : ℝ) + 2 + nuG e f) - lpG e f 1 x ((i : ℝ) + 1) j) =
      lpG e f 1 x ((i : ℝ) + 1 + mu * (((i : ℝ) - nuG e f) - ((i : ℝ) + 1))) ((j : ℝ) + mu * (((j : ℝ) + 2 + nuG e f) - (j : ℝ))) := by
    rw [← h1, add_comm]
  rw [h2, PIR]
  apply lpG_congr
  · rw [ht]; ring
  · rw [ht]; linear_combination mu * hns

set_option maxHeartbeats 4000000 in
/-- **RL step (alpha)** (PROOF 8.2 (alpha)): `B_m = O + (m+1) d`, `d = Y - O`.  The tiles `nu(i-m', m')`, `m' <= m`, and `Pi4` give a tile covering the open half-disk on the right of `Lambda_3` at `B_m`. -/
theorem rl_alpha (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i m : ℕ) (hi : i + 1 ≤ f - 1) (hm : m ≤ i)
    (hnu : ∀ m' : ℕ, m' ≤ m → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i ((i : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j i ((i : ℝ) - m') m')
        (PIR (e : ℝ) f x j i ((i : ℝ) - m') ((m' : ℝ) + 1)))
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j) < 0) :
    EdgeCoverS D (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j + (((m + 1 : ℕ) : ℝ)) •
        (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j))
      (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j) (-1) := by
  have he0 := S.e0
  have hef := S.hef'
  have hν0 := nuG_pos he0 hef
  have hν1 := nuG_lt_one he0 hef
  have hνb := nuG_spec he0 hef
  have hκ := kapG_pos he0 hef
  set O : Plane := lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j with hO
  set Y : Plane := lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) with hY
  set d : Plane := Y - O with hd
  have hdn : ‖d‖ = (f : ℝ) ^ 2 := by
    have := dist_dLam he0 hef x (i : ℝ) (j : ℝ)
    rw [dist_eq_norm] at this
    exact this
  -- the points of the wall tiles
  have hcr : ∀ m' : ℕ, m' ≤ m →
      cross d (PIR (e : ℝ) f x j i ((i : ℝ) - m') m' - PIR (e : ℝ) f x j i ((i : ℝ) - m' + 1) m') = kapG (e : ℝ) f := by
    intro m' hm'
    have e1 : PIR (e : ℝ) f x j i ((i : ℝ) - m') m' - PIR (e : ℝ) f x j i ((i : ℝ) - m' + 1) m' =
        lpG (e : ℝ) f 1 x (((i : ℝ) - m') - m' * nuG (e : ℝ) f) ((j : ℝ) + i + 1 - ((i : ℝ) - m') + m' * nuG (e : ℝ) f * sMir (e : ℝ) f) -
        lpG (e : ℝ) f 1 x (((i : ℝ) - m' + 1) - m' * nuG (e : ℝ) f) ((j : ℝ) + i + 1 - ((i : ℝ) - m' + 1) + m' * nuG (e : ℝ) f * sMir (e : ℝ) f) := rfl
    rw [e1, hd, hY, hO, cross_lpG]
    ring
  have hWall : ∀ t : ℕ, t < m + 1 → ∃ (T : Fin N) (A : Plane),
      HasV D T (O + (t : ℝ) • d) (O + ((t : ℝ) + 1) • d) A ∧ (-1 : ℝ) * cross d (A - (O + (t : ℝ) • d)) < 0 := by
    intro t ht
    obtain ⟨T, hT⟩ := hnu t (by omega)
    have h1 := PIR_on_L3 he0 hef x j i (t : ℝ) ((i : ℝ) - t + 1) (by ring)
    have h2 := PIR_on_L3 he0 hef x j i ((t : ℝ) + 1) ((i : ℝ) - t) (by ring)
    refine ⟨T, PIR (e : ℝ) f x j i ((i : ℝ) - t) t, hasV_congr hT.rot.rot.swap ?_ ?_ rfl, ?_⟩
    · exact h1
    · exact h2
    · have h3 : O + (t : ℝ) • d = PIR (e : ℝ) f x j i ((i : ℝ) - t + 1) t := h1.symm
      rw [h3, hcr t (by omega)]
      linarith
  obtain ⟨E, A0, hE', hA0'⟩ := hWall 0 (by omega)
  have hE : HasV D E O (O + d) A0 := hasV_congr hE' (by simp) (by simp) rfl
  have hA0 : (-1 : ℝ) * cross d (A0 - O) < 0 := by simpa using hA0'
  obtain ⟨F, R, hF, hcrR⟩ := hP4
  have hnon : ∀ x' y' z' : ℕ, nuG (e : ℝ) f * (f : ℝ) ^ 2 +
      ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) ≠ ((m + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 := by
    intro x' y' z' h
    have hZR : ((x' : ℝ) * ((e : ℝ) * f) + y' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z' * (f : ℝ) ^ 2) =
        ((m + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
      nlinarith [hνb]
    have hZI : (x' : ℤ) * ((e : ℤ) * f) + (y' : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (z' : ℤ) * (f : ℤ) ^ 2 =
        ((m + 1 : ℕ) : ℤ) * (f : ℤ) ^ 2 - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) := by
      exact_mod_cast hZR
    exact Erdos634.Draft.WGapArith.nonmem_mc_sub_b S.he S.hef S.hco (m := m + 1) (by omega) (by omega) ⟨x', y', z', hZI⟩
  exact fault_cover S (q := m + 1) (by omega) O d ((f : ℝ) ^ 2) (nuG (e : ℝ) f) (-1) (Or.inr rfl) hdn
    (by have := S.f1; positivity) hν0 hnon E A0 hE hA0 F R hF (by linarith) hWall

end rl3

end Erdos634.Draft.WGapStmt
