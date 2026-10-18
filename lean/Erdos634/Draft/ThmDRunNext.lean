import Erdos634.Draft.ThmDRunCtx
import Erdos634.Draft.ThmDRunFrame2

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' run port, module R4: recognition of the tile across an `a`-edge  

Port of `SideRunGLattice` section 4 (`cross_mG`, `cross_rowG`, `m_edge_casesG`, `row_edge_UG`) and of `SideRunGChord`
sections 4 (`vertex_dist_casesG`, `m_clamp_baseG`, `m_clamp_tileG`, `m_next_casesG`, `m_nextG`) to the tile `(u^2, v^2-u^2, u v)`.
The mirror tile `N(xi, eta)` has its third vertex at `lp (xi + 2 - mu) (eta + mu)`, `mu = muT u v` (base-beta: `lp (xi - nu) (eta + 2 + nu)`).

NOT PORTED: `N_pushG` (the points `p(xi + delta, eta + 1)` are interior to `N`).  For the gamma = 2 alpha tile its barycentric
coordinates in `N` are `(delta (mu - 1), 1 - delta mu, delta)`, and `mu - 1 < 0` at `(u,v) = (3,5)` (`mu = 50/81`): the point is
NOT in `N`.  The mirror case needs a different argument (see `thmD_lean.md`).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.TilePlacement Erdos634.Draft.SideRun Set

variable {N : ℕ} {D : CongruentDissection N}

namespace SetupT
variable {u v : ℕ} {α β γ L ax ay : ℝ}
theorem a_pos (S : SetupT D u v α β γ L ax ay) : (0 : ℝ) < (u : ℝ) ^ 2 := by have := S.u0; positivity
end SetupT

/-! ## 4. Recognition -/

theorem cross_mT {u v ε x : ℝ} (hε : ε ^ 2 = 1) (ξ η : ℝ) (y : Plane) :
    cross (lpT u v ε x ξ (η + 1) - lpT u v ε x (ξ + 1) η) y = ε * GST u v ε y := by
  unfold GST lpT
  rw [lin_apply]
  simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]
  linear_combination (hhT u v * y 0) * hε

theorem cross_rowT {u v ε x : ℝ} (ξ η : ℝ) (y : Plane) :
    cross (lpT u v ε x (ξ + 1) η - lpT u v ε x ξ η) y = (-ε) * GHT u v y := by
  unfold lpT
  rw [GHT_apply]
  simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]
  ring

section recog

variable {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **A tile of the side `ρ` with the `a`-edge `[lp (ξ+1) η, lp ξ (η+1)]` is `D(ξ,η)` or `N(ξ,η)`.** -/
theorem m_edge_casesT (S : SetupT D u v α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {k m : Fin 3}
    (hkm : k ≠ m) {ξ η : ℝ} (hk : (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
    (hm : (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
    (hle : ∀ i, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts i) ≤ -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1)) :
    HasV D t (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
      (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η + 1)) ∨
    HasV D t (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
      (lpT (u : ℝ) (v : ℝ) ε x (ξ + 2 - muT (u : ℝ) (v : ℝ)) (η + muT (u : ℝ) (v : ℝ))) := by
  obtain ⟨j, hjk, hjm⟩ := fin3_third k m hkm
  have hu := S.u0
  have huv := S.uv'
  have hv := S.v2
  have hnh := nhT_pos hu huv hv
  have hd : dist ((D.tile t).pts k) ((D.tile t).pts m) = (u : ℝ) ^ 2 := by
    rw [hk, hm]; exact dist_step_aT hu huv hv hε ξ η
  have hGk : GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts k) = -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1) := by
    rw [hk, GST_lp hε]; unfold lvT; ring
  have hGm : GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts m) = -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1) := by
    rw [hm, GST_lp hε]; unfold lvT; ring
  have hlt := third_strict (D.tile t) hkm (Ne.symm hjk) (Ne.symm hjm) (GST (u : ℝ) (v : ℝ) ε)
    (GST_ne hu huv hv hε) _ hGk hGm hle
  rw [hk] at hGk
  rcases sides_of_a_edgeT D S.tile S.hM t hkm (Ne.symm hjk) (Ne.symm hjm) hd with
    ⟨s1, s2⟩ | ⟨s1, s2⟩
  · right
    rw [hk] at s1
    rw [hm] at s2
    have hj : (D.tile t).pts j =
        lpT (u : ℝ) (v : ℝ) ε x (ξ + 2 - muT (u : ℝ) (v : ℝ)) (η + muT (u : ℝ) (v : ℝ)) := by
      refine third_unique_F (GST (u : ℝ) (v : ℝ) ε) (eps_neT hε) (cross_mT hε ξ η) hGk ?_ ?_ hlt ?_
      · rw [s1, dist_N_VT hu huv hv hε ξ η]
      · rw [s2, dist_N_GT hu huv hv hε ξ η]
      · rw [GST_lp hε]; unfold lvT; nlinarith
    exact ⟨k, m, j, hkm, Ne.symm hjk, Ne.symm hjm, hk, hm, hj⟩
  · left
    rw [hk] at s1
    rw [hm] at s2
    have hj : (D.tile t).pts j = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η + 1) := by
      refine third_unique_F (GST (u : ℝ) (v : ℝ) ε) (eps_neT hε) (cross_mT hε ξ η) hGk ?_ ?_ hlt ?_
      · rw [s1, dist_comm]; exact (dist_step_vT hu huv hv hε (ξ + 1) η).symm
      · rw [s2, dist_comm]; exact (dist_step_uT hu huv hv hε ξ (η + 1)).symm
      · rw [GST_lp hε]; unfold lvT; nlinarith
    exact ⟨k, m, j, hkm, Ne.symm hjk, Ne.symm hjm, hk, hm, hj⟩

/-- **A tile above a row with the edge `[lp ξ η, lp (ξ+1) η]` whose third vertex is at the distances `b`, `a` from
its ends is `U(ξ,η)`.** -/
theorem row_edge_UT (S : SetupT D u v α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {k m j : Fin 3}
    (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) {ξ η : ℝ}
    (hk : (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x ξ η)
    (hm : (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
    (hle : ∀ i, GHT (u : ℝ) (v : ℝ) ((D.tile t).pts i) ≤ -(((u : ℝ) * v) * hhT (u : ℝ) (v : ℝ) * η))
    (s1 : dist ((D.tile t).pts j) ((D.tile t).pts k) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2)
    (s2 : dist ((D.tile t).pts j) ((D.tile t).pts m) = (u : ℝ) ^ 2) :
    HasV D t (lpT (u : ℝ) (v : ℝ) ε x ξ η) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)) := by
  have hu := S.u0
  have huv := S.uv'
  have hv := S.v2
  have hnh := nhT_pos hu huv hv
  have hGk : GHT (u : ℝ) (v : ℝ) ((D.tile t).pts k) = -(((u : ℝ) * v) * hhT (u : ℝ) (v : ℝ) * η) := by
    rw [hk, GHT_lp]
  have hGm : GHT (u : ℝ) (v : ℝ) ((D.tile t).pts m) = -(((u : ℝ) * v) * hhT (u : ℝ) (v : ℝ) * η) := by
    rw [hm, GHT_lp]
  have hlt := third_strict (D.tile t) hkm hkj hmj (GHT (u : ℝ) (v : ℝ)) (GHT_ne hu huv) _ hGk hGm hle
  rw [hk] at hGk s1
  rw [hm] at s2
  have hj : (D.tile t).pts j = lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1) := by
    refine third_unique_F (GHT (u : ℝ) (v : ℝ)) (neg_ne_zero.mpr (eps_neT hε)) (cross_rowT ξ η) hGk ?_ ?_
      hlt ?_
    · rw [s1, dist_comm]; exact (dist_step_vT hu huv hv hε ξ η).symm
    · rw [s2, dist_comm]; exact (dist_step_aT hu huv hv hε ξ η).symm
    · rw [GHT_lp]; nlinarith
  exact ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩

end recog

/-- every segment between two vertices of a tile has one of the three lengths -/
theorem vertex_dist_casesT {N : ℕ} (D : CongruentDissection N) {u v α β γ : ℝ}
    (hM : ModelDataT D (u ^ 2) (v ^ 2 - u ^ 2) (u * v) α β γ) (i : Fin N) {k m : Fin 3} (hkm : k ≠ m) :
    dist ((D.tile i).pts k) ((D.tile i).pts m) = u ^ 2 ∨
    dist ((D.tile i).pts k) ((D.tile i).pts m) = v ^ 2 - u ^ 2 ∨
    dist ((D.tile i).pts k) ((D.tile i).pts m) = (u * v) := by
  have hcov : ∀ a b : Fin 3, a ≠ b → b = a + 1 ∨ a = b + 1 := by decide
  rcases hcov k m hkm with h | h
  · rw [h]; exact edge_length_casesT D hM i k
  · rw [h, dist_comm]; exact edge_length_casesT D hM i m

namespace CtxBaseT

variable {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- the clamp of an `a`-edge at a point of the side (`η₁ = 0`, `Z` on the side): the line below the side is outside Δ -/
theorem m_clamp_baseT (C : CtxBaseT D u v α β γ L ax ay ε x) (ξ : ℝ) :
    ClampedBelowT D (u : ℝ) (v : ℝ) ε x (ξ + 0 + 1) 0 := by
  refine clampedBelowT_of_outside (η' := -1) (by norm_num) (fun y hy hmem => ?_)
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have h0 := (C.S.mem hmem).1
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, lpT_snd] at h0
  have hh := C.S.hhpos
  nlinarith [mul_pos ha hh]

/-- the clamp of an `a`-edge at `p(ξ+1,η)` by a tile of the side `ρ` with the edge `[p(ξ+2,η−1), p(ξ+1,η)]` -/
theorem m_clamp_tileT (C : CtxBaseT D u v α β γ L ax ay ε x) {ξ η : ℝ} {t₁ : Fin N} {k m : Fin 3}
    (hkm : k ≠ m) (hk : (D.tile t₁).pts k = lpT (u : ℝ) (v : ℝ) ε x (ξ + 2) (η - 1))
    (hm : (D.tile t₁).pts m = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
    (hle : ∀ i, GST (u : ℝ) (v : ℝ) ε ((D.tile t₁).pts i) ≤ -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1)) :
    ClampedBelowT D (u : ℝ) (v : ℝ) ε x (ξ + η + 1) η :=
  clampedBelowT_of_edge C.S.u0 C.S.uv' C.S.v2 C.e2 (by linarith : η - 1 < η) hkm
    (by rw [hk]; exact lpT_congr (by ring) rfl) (by rw [hm]; exact lpT_congr (by ring) rfl) hle

/-- the tile found across an `a`-edge lays exactly `a`, or it gives (K3) for the run that ends there: its edge from
`p(ξ+1,η)` has length `b` or `c` (step (2a) of the proof) -/
theorem m_next_casesT (C : CtxBaseT D u v α β γ L ax ay ε x) {i : Fin N} {k m : Fin 3} (hkm : k ≠ m)
    {ξ : ℝ} {η : ℕ} {t : ℝ}
    (hk : (D.tile i).pts k = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (ht : 0 < t)
    (hm : (D.tile i).pts m = AffineMap.lineMap (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)) t)
    (hle : ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile i).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1))
    (hcl : ClampedBelowT D (u : ℝ) (v : ℝ) ε x (ξ + η + 1) η) :
    (D.tile i).pts m = lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1) ∨
      RhoEdgeT D (u : ℝ) (v : ℝ) ε x i (ξ + η + 1) η := by
  have hε := C.e2
  have hu := C.S.u0
  have huv := C.S.uv'
  have hv := C.S.v2
  have hv0 := C.S.v0
  rw [lineMap_lpT] at hm
  have hd : dist ((D.tile i).pts k) ((D.tile i).pts m) = t * ((u : ℝ) ^ 2) := by
    rw [hk, hm]
    exact dist_lpT hu huv hv hε (by positivity) (by unfold QfT; ring)
  have hk' : (D.tile i).pts k = lpT (u : ℝ) (v : ℝ) ε x (ξ + η + 1 - η) η := by
    rw [hk]; exact lpT_congr (by ring) rfl
  have hm' : (D.tile i).pts m = lpT (u : ℝ) (v : ℝ) ε x (ξ + η + 1 - (η + t)) (η + t) := by
    rw [hm]; exact lpT_congr (by ring) (by ring)
  rcases vertex_dist_casesT D C.S.hM i hkm with h | h | h
  · left
    have h1 : t * ((u : ℝ) ^ 2) = 1 * ((u : ℝ) ^ 2) := by rw [one_mul, ← hd, h]
    have ht1 : t = 1 := mul_right_cancel₀ C.S.a_pos.ne' h1
    rw [hm, ht1]
    exact lpT_congr (by ring) (by ring)
  · right
    refine ⟨k, m, η, η + t, hkm, le_refl _, by linarith, hk', hm', Or.inl ?_, hle, hcl⟩
    rw [show (η : ℝ) + t - η = t by ring, ← hd, h]
  · right
    refine ⟨k, m, η, η + t, hkm, le_refl _, by linarith, hk', hm', Or.inr ?_, hle, hcl⟩
    rw [show (η : ℝ) + t - η = t by ring, ← hd, h]

/-- **The tile across the `a`-edge of `U(ξ,η)` at `p(ξ+1,η)`**: it is `D(ξ,η)`, or `N(ξ,η)`, or it lays `b` or `c` on
the line `m_{ξ+η+1}` from `p(ξ+1,η)` and gives (K3) for the run of length `ξ+η+1` at height `η`.  The clamp of
`p(ξ+1,η)` from below is a hypothesis (sources: `m_clamp_baseT`, `m_clamp_tileT`). -/
theorem m_nextT (C : CtxBaseT D u v α β γ L ax ay ε x) {ξ : ℝ} {η : ℕ} {t₀ : Fin N}
    (hU : HasV D t₀ (lpT (u : ℝ) (v : ℝ) ε x ξ η) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)))
    (hFw : ∃ δ : ℝ, 0 < δ ∧ lpT (u : ℝ) (v : ℝ) ε x (ξ + 1 + δ) η ∈ D.target.carrier)
    (hcl : ClampedBelowT D (u : ℝ) (v : ℝ) ε x (ξ + η + 1) η) :
    (∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
      (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η + 1))) ∨
    (∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
      (lpT (u : ℝ) (v : ℝ) ε x (ξ + 2 - muT (u : ℝ) (v : ℝ)) (η + muT (u : ℝ) (v : ℝ)))) ∨
    (∃ w, RhoEdgeT D (u : ℝ) (v : ℝ) ε x w (ξ + η + 1) η) := by
  have hε := C.e2
  have hu := C.S.u0
  have huv := C.S.uv'
  have hv := C.S.v2
  have hηpos : (0 : ℝ) ≤ η := Nat.cast_nonneg η
  have hVG : lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η ≠ lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1) :=
    lpT_ne_eta hu huv hv (by linarith)
  have hfV : GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      = -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1) := by
    rw [GST_lp hε]; unfold lvT; ring
  have hfG : GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
      = -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1) := by
    rw [GST_lp hε]; unfold lvT; ring
  have hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1))
      ⊆ interior D.target.carrier := by
    refine C.seg_intT hU.mem₂ hU.mem₃ (Or.inr (by linarith)) (Or.inl hFw) (Or.inl ⟨1, one_pos, ?_⟩)
    rw [show ξ + 1 - 1 = ξ by ring]; exact hU.mem₁
  have hwall : ∀ y ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)
      (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)), ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hU
    refine seg_wall D.toDissection (t := t₀) hmj ?_
    rw [hm, hj]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨η', hη', hprop⟩ := hcl
  have hZ : lpT (u : ℝ) (v : ℝ) ε x (ξ + η + 1 - η) η = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η :=
    lpT_congr (by ring) rfl
  have hP'mem : lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η ∈
      openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x (ξ + η + 1 - η') η')
        (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)) := by
    have h := lpT_between (u := (u : ℝ)) (v := (v : ℝ)) (ε := ε) (x := x) (s := ξ + η + 1)
      (η' := η') (η := η) (η'' := η + 1) hη' (by linarith)
    rw [hZ, show lpT (u : ℝ) (v : ℝ) ε x (ξ + η + 1 - (η + 1)) (η + 1)
        = lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1) from lpT_congr (by ring) rfl] at h
    exact h
  have hfP' : GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x (ξ + η + 1 - η') η')
      = -lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1) := by
    rw [GST_lp hε]; unfold lvT; ring
  have hP : ∀ ed ∈ D.lineChain (GST (u : ℝ) (v : ℝ) ε) (-lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1)),
      ¬ Straddles ((D.tile ed.1).edge ed.2) (lpT (u : ℝ) (v : ℝ) ε x (ξ + η + 1 - η') η')
        (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)) := by
    have h := hprop (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)) hfG (by rw [hZ]; exact hP'mem)
    rw [hZ] at h
    exact h
  have hcl' : ClampedBelowT D (u : ℝ) (v : ℝ) ε x (ξ + η + 1) η := ⟨η', hη', hprop⟩
  obtain ⟨ed, hed, k', m', t, hk'm', hk', ht, hm', hle, -, -⟩ :=
    next_tile D.toDissection (GST (u : ℝ) (v : ℝ) ε) (GST_ne hu huv hv hε)
      (-lvT (u : ℝ) (v : ℝ) ε x (ξ + η + 1)) hVG hfV hfG hfP' hP'mem hint hwall hP
  rcases C.m_next_casesT hk'm' hk' ht hm' hle hcl' with hG | hR
  · rcases m_edge_casesT C.S hε hk'm' hk' hG hle with h | h
    · exact Or.inl ⟨ed.1, h⟩
    · exact Or.inr (Or.inl ⟨ed.1, h⟩)
  · exact Or.inr (Or.inr ⟨ed.1, hR⟩)

end CtxBaseT

end Erdos634.Draft.ThmDRun


#print axioms Erdos634.Draft.ThmDRun.m_edge_casesT
#print axioms Erdos634.Draft.ThmDRun.row_edge_UT
#print axioms Erdos634.Draft.ThmDRun.CtxBaseT.m_nextT
#print axioms Erdos634.Draft.ThmDRun.CtxBaseT.m_next_casesT
