import Erdos634.Draft.ThmDRunSetup

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' run port, module R2: `CtxT`, interior segments, clamps, `K3T`  

Mechanical port (constants changed: `a = u^2`, `b = v^2 - u^2`, `c = u v`) of `SideRunGChord` sections 1-3: the four pushes,
`CtxBaseT` / `CtxT` (setup + orientation + (K1) at `P`), `seg_intT`, `lpT_between`, `lpT_mem_seg_of_le`, `ClampedBelowT`,
`RhoEdgeT`, `K3T`.  (`RhoEdgeT` asks for an edge of length `b` or `c` from a lattice point, as `RhoEdgeG` does.)
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set

variable {N : ℕ} {D : CongruentDissection N}

namespace SetupT
variable {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}
theorem c_pos (S : SetupT D u v α β γ L ax ay) : (0 : ℝ) < (u : ℝ) * v := mul_pos S.u0 S.v0
theorem hhpos (S : SetupT D u v α β γ L ax ay) : 0 < hhT (u : ℝ) (v : ℝ) := hhT_pos S.u0 S.uv' S.v2
end SetupT

/-! ## 1. Coordinates, the four pushes, `CtxT` -/

theorem lpT_snd (u v ε x ξ η : ℝ) : (lpT u v ε x ξ η) 1 = η * hhT u v := by
  unfold lpT; rw [mkPt_one]

theorem lpT_fst (u v ε x ξ η : ℝ) :
    (lpT u v ε x ξ η) 0 = x + ε * ((ξ + η) * (u * v) - η * uuT u v) := by
  unfold lpT; rw [mkPt_zero]

namespace SetupT

variable {u v : ℕ} {α β γ L ax ay x : ℝ}

theorem fwd1T (S : SetupT D u v α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lpT (u : ℝ) (v : ℝ) 1 x (ξ + δ) η ∈ D.target.carrier) :
    0 < gB L ax ay (lpT (u : ℝ) (v : ℝ) 1 x ξ η) := by
  have u' : lpT (u : ℝ) (v : ℝ) 1 x (ξ + δ) η
      = mkPt (x + 1 * ((ξ + η) * ((u : ℝ) * v) - η * uuT (u : ℝ) (v : ℝ)) + δ * ((u : ℝ) * v))
          (η * hhT (u : ℝ) (v : ℝ)) := by
    unfold lpT; exact mkPt_congr (by ring) rfl
  rw [u'] at h
  exact S.gB_pos_of_right (mul_pos hδ S.c_pos) h

theorem bwd1T (S : SetupT D u v α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lpT (u : ℝ) (v : ℝ) 1 x (ξ - δ) η ∈ D.target.carrier) :
    0 < gA ax ay (lpT (u : ℝ) (v : ℝ) 1 x ξ η) := by
  have u' : lpT (u : ℝ) (v : ℝ) 1 x (ξ - δ) η
      = mkPt (x + 1 * ((ξ + η) * ((u : ℝ) * v) - η * uuT (u : ℝ) (v : ℝ)) - δ * ((u : ℝ) * v))
          (η * hhT (u : ℝ) (v : ℝ)) := by
    unfold lpT; exact mkPt_congr (by ring) rfl
  rw [u'] at h
  exact S.gA_pos_of_left (mul_pos hδ S.c_pos) h

theorem fwdmT (S : SetupT D u v α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lpT (u : ℝ) (v : ℝ) (-1) x (ξ + δ) η ∈ D.target.carrier) :
    0 < gA ax ay (lpT (u : ℝ) (v : ℝ) (-1) x ξ η) := by
  have u' : lpT (u : ℝ) (v : ℝ) (-1) x (ξ + δ) η
      = mkPt (x + (-1) * ((ξ + η) * ((u : ℝ) * v) - η * uuT (u : ℝ) (v : ℝ)) - δ * ((u : ℝ) * v))
          (η * hhT (u : ℝ) (v : ℝ)) := by
    unfold lpT; exact mkPt_congr (by ring) rfl
  rw [u'] at h
  exact S.gA_pos_of_left (mul_pos hδ S.c_pos) h

theorem bwdmT (S : SetupT D u v α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lpT (u : ℝ) (v : ℝ) (-1) x (ξ - δ) η ∈ D.target.carrier) :
    0 < gB L ax ay (lpT (u : ℝ) (v : ℝ) (-1) x ξ η) := by
  have u' : lpT (u : ℝ) (v : ℝ) (-1) x (ξ - δ) η
      = mkPt (x + (-1) * ((ξ + η) * ((u : ℝ) * v) - η * uuT (u : ℝ) (v : ℝ)) + δ * ((u : ℝ) * v))
          (η * hhT (u : ℝ) (v : ℝ)) := by
    unfold lpT; exact mkPt_congr (by ring) rfl
  rw [u'] at h
  exact S.gB_pos_of_right (mul_pos hδ S.c_pos) h

end SetupT

/-- **The setup part of the standing hypotheses of the run lemma**: a `SetupT` and an orientation.  Every lemma of the chain
that does not use (K1) is stated for it (`CtxBaseT`), and holds for `CtxT` by the parent projection. -/
structure CtxBaseT (D : CongruentDissection N) (u v : ℕ) (α β γ L ax ay ε x : ℝ) : Prop where
  S : SetupT D u v α β γ L ax ay
  hε : ε = 1 ∨ ε = -1

/-- **The standing hypotheses of the run lemma**: a `CtxBaseT` (a `SetupT` and an orientation), and (K1) at `P = (x, 0)`, in the
form of `SideRun.Ctx`. -/
structure CtxT (D : CongruentDissection N) (u v : ℕ) (α β γ L ax ay ε x : ℝ) : Prop
    extends CtxBaseT D u v α β γ L ax ay ε x where
  hK1 : ∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x 0 0 →
    (D.tile t').pts m = lpT (u : ℝ) (v : ℝ) ε x 0 1 →
    (∀ i, FXT (u : ℝ) (v : ℝ) ε ((D.tile t').pts i) ≤ lvT (u : ℝ) (v : ℝ) ε x 0) → False
  hch : ∀ j : ℕ, 1 ≤ j → lpT (u : ℝ) (v : ℝ) ε x 0 j ∈ D.target.carrier →
    openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 0) (lpT (u : ℝ) (v : ℝ) ε x 0 j) ⊆
      interior D.target.carrier

namespace CtxBaseT

variable {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem e2 (C : CtxBaseT D u v α β γ L ax ay ε x) : ε ^ 2 = 1 := by
  rcases C.hε with h | h <;> rw [h] <;> norm_num

/-- **Interior segments between lattice points.** -/
theorem seg_intT (C : CtxBaseT D u v α β γ L ax ay ε x) {ξ η ξ' η' : ℝ}
    (hA : lpT (u : ℝ) (v : ℝ) ε x ξ η ∈ D.target.carrier)
    (hB : lpT (u : ℝ) (v : ℝ) ε x ξ' η' ∈ D.target.carrier)
    (hh' : 0 < η ∨ 0 < η')
    (hF : (∃ δ : ℝ, 0 < δ ∧ lpT (u : ℝ) (v : ℝ) ε x (ξ + δ) η ∈ D.target.carrier) ∨
      (∃ δ : ℝ, 0 < δ ∧ lpT (u : ℝ) (v : ℝ) ε x (ξ' + δ) η' ∈ D.target.carrier))
    (hBk : (∃ δ : ℝ, 0 < δ ∧ lpT (u : ℝ) (v : ℝ) ε x (ξ - δ) η ∈ D.target.carrier) ∨
      (∃ δ : ℝ, 0 < δ ∧ lpT (u : ℝ) (v : ℝ) ε x (ξ' - δ) η' ∈ D.target.carrier)) :
    openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x ξ η) (lpT (u : ℝ) (v : ℝ) ε x ξ' η') ⊆
      interior D.target.carrier := by
  have hhp := C.S.hhpos
  have h1 : 0 < (lpT (u : ℝ) (v : ℝ) ε x ξ η) 1 ∨ 0 < (lpT (u : ℝ) (v : ℝ) ε x ξ' η') 1 := by
    rcases hh' with h | h
    · left; rw [lpT_snd]; exact mul_pos h hhp
    · right; rw [lpT_snd]; exact mul_pos h hhp
  have S := C.S
  rcases C.hε with rfl | rfl
  · refine S.interior_seg hA hB h1 ?_ ?_
    · rcases hBk with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.bwd1T hδ h)
      · exact Or.inr (S.bwd1T hδ h)
    · rcases hF with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.fwd1T hδ h)
      · exact Or.inr (S.fwd1T hδ h)
  · refine S.interior_seg hA hB h1 ?_ ?_
    · rcases hF with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.fwdmT hδ h)
      · exact Or.inr (S.fwdmT hδ h)
    · rcases hBk with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.bwdmT hδ h)
      · exact Or.inr (S.bwdmT hδ h)

end CtxBaseT

/-! ## 2. Points between lattice points of the line `m_s` -/

/-- the point `p(s − η, η)` is strictly between `p(s − η', η')` and `p(s − η'', η'')` for `η' < η < η''` -/
theorem lpT_between {u v ε x s η' η η'' : ℝ} (h1 : η' < η) (h2 : η < η'') :
    lpT u v ε x (s - η) η ∈
      openSegment ℝ (lpT u v ε x (s - η') η') (lpT u v ε x (s - η'') η'') := by
  have hd : 0 < η'' - η' := by linarith
  have hab : (η'' - η) / (η'' - η') + (η - η') / (η'' - η') = 1 := by
    rw [← add_div, show η'' - η + (η - η') = η'' - η' by ring]
    exact div_self hd.ne'
  have hb : (η - η') / (η'' - η') * (η'' - η') = η - η' := div_mul_cancel₀ _ hd.ne'
  have hη : (η'' - η) / (η'' - η') * η' + (η - η') / (η'' - η') * η'' = η := by
    linear_combination hb + η' * hab
  refine ⟨(η'' - η) / (η'' - η'), (η - η') / (η'' - η'), div_pos (by linarith) hd,
    div_pos (by linarith) hd, hab, ?_⟩
  unfold lpT
  apply plane_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero]
    linear_combination (x + ε * s * (u * v)) * hab - (ε * uuT u v) * hη
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_one]
    linear_combination (hhT u v) * hη

/-- the point `p(s − η₂, η₂)`, `η₁ < η₂ ≤ η₃`, lies on the segment `[p(s − η₁, η₁), p(s − η₃, η₃)]` -/
theorem lpT_mem_seg_of_le {u v ε x s η₁ η₂ η₃ : ℝ} (h1 : η₁ < η₂) (h2 : η₂ ≤ η₃) :
    lpT u v ε x (s - η₂) η₂ ∈
      segment ℝ (lpT u v ε x (s - η₁) η₁) (lpT u v ε x (s - η₃) η₃) := by
  have hd : η₃ - η₁ ≠ 0 := by intro h; linarith
  have hd0 : 0 < η₃ - η₁ := by linarith
  have hτ : (η₂ - η₁) / (η₃ - η₁) * (η₃ - η₁) = η₂ - η₁ := div_mul_cancel₀ _ hd
  have hτ1 : (η₂ - η₁) / (η₃ - η₁) ≤ 1 := by rw [div_le_one hd0]; linarith
  have hτ0 : 0 ≤ (η₂ - η₁) / (η₃ - η₁) := div_nonneg (by linarith) hd0.le
  have h := lp_mem_segT (u := u) (v := v) (ε := ε) (x := x) (ξ := s - η₁) (η := η₁)
    (ξ' := s - η₃) (η' := η₃) (τ := (η₂ - η₁) / (η₃ - η₁)) hτ0 hτ1
  rw [show lpT u v ε x (s - η₁ + (η₂ - η₁) / (η₃ - η₁) * (s - η₃ - (s - η₁)))
        (η₁ + (η₂ - η₁) / (η₃ - η₁) * (η₃ - η₁)) = lpT u v ε x (s - η₂) η₂ from
      lpT_congr (by linear_combination (-1 : ℝ) * hτ) (by linear_combination hτ)] at h
  exact h

/-! ## 3. Clamps from below, `RhoEdgeT`, `K3T` -/

/-- **`Z = p(s − η₁, η₁)` is clamped from below on the line `m_s` for the side `ρ_s`** (paper, (K3)(b)): there is a point
`P' = p(s − η', η')` of the line below `Z` such that, for every run `[Z, Q]` of the line above `Z`, no near-side chain edge
straddles `Z` with respect to `P'` and `Q`.  (The paper's two sources: the line just beyond `Z` is outside Δ, or an edge
of a tile on the side `ρ_s` ends at `Z`.) -/
def ClampedBelowT (D : CongruentDissection N) (u v ε x s η₁ : ℝ) : Prop :=
  ∃ η' : ℝ, η' < η₁ ∧ ∀ Q : Plane, GST u v ε Q = -lvT u v ε x s →
    lpT u v ε x (s - η₁) η₁ ∈ openSegment ℝ (lpT u v ε x (s - η') η') Q →
    ∀ ed ∈ D.lineChain (GST u v ε) (-lvT u v ε x s),
      ¬ Straddles ((D.tile ed.1).edge ed.2) (lpT u v ε x (s - η') η') (lpT u v ε x (s - η₁) η₁) Q

/-- **source 1: the line just below `Z` is outside Δ** -/
theorem clampedBelowT_of_outside {u v ε x s η₁ η' : ℝ} (hη : η' < η₁)
    (hout : ∀ y ∈ openSegment ℝ (lpT u v ε x (s - η') η') (lpT u v ε x (s - η₁) η₁),
      y ∉ D.target.carrier) : ClampedBelowT D u v ε x s η₁ :=
  ⟨η', hη, fun Q _ _ ed _ => not_straddles_of_outside D.toDissection hout ed.1 ed.2⟩

/-- **source 2: a tile on the side `ρ_s` has an edge `[p(s − η', η'), Z]` ending at `Z`** -/
theorem clampedBelowT_of_edge {u v ε x s η₁ η' : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1)
    (hη : η' < η₁) {t : Fin N} {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile t).pts k = lpT u v ε x (s - η') η')
    (hm : (D.tile t).pts m = lpT u v ε x (s - η₁) η₁)
    (hle : ∀ i, GST u v ε ((D.tile t).pts i) ≤ -lvT u v ε x s) :
    ClampedBelowT D u v ε x s η₁ := by
  refine ⟨η', hη, fun Q hQ hmem ed hed => ?_⟩
  have hfP' : GST u v ε (lpT u v ε x (s - η') η') = -lvT u v ε x s := by
    rw [GST_lp hε]; unfold lvT; ring
  have hfP : GST u v ε (lpT u v ε x (s - η₁) η₁) = -lvT u v ε x s := by
    rw [GST_lp hε]; unfold lvT; ring
  have hPQ : lpT u v ε x (s - η₁) η₁ ≠ Q := by
    intro h
    rw [← h] at hmem
    exact lpT_ne_eta hu huv hv (by linarith : η' ≠ η₁) (right_mem_openSegment_iff.mp hmem)
  exact clamp_b D.toDissection (GST u v ε) (GST_ne hu huv hv hε) _ hPQ hfP hQ hfP' hmem hkm hk hm hle
    ed hed

/-- **A tile on the side `ρ_s` has an edge on `m_s` that starts at `Z = p(s − η₁, η₁)` (`η₁ ∈ ℕ`, `η₁ ≤ j0`), runs upward,
has length `b` or `c`, and `Z` is clamped from below** (paper, (K3)(a) and (b); the length of the edge from the height
`η₁` to the height `η₂` is `(η₂ − η₁) a`). -/
def RhoEdgeT (D : CongruentDissection N) (u v ε x : ℝ) (w : Fin N) (s j0 : ℝ) : Prop :=
  ∃ (k m : Fin 3) (η₁ : ℕ) (η₂ : ℝ), k ≠ m ∧ (η₁ : ℝ) ≤ j0 ∧ (η₁ : ℝ) < η₂ ∧
    (D.tile w).pts k = lpT u v ε x (s - η₁) η₁ ∧ (D.tile w).pts m = lpT u v ε x (s - η₂) η₂ ∧
    ((η₂ - η₁) * (u ^ 2) = v ^ 2 - u ^ 2 ∨ (η₂ - η₁) * (u ^ 2) = (u * v)) ∧
    (∀ i, GST u v ε ((D.tile w).pts i) ≤ -lvT u v ε x s) ∧
    ClampedBelowT D u v ε x s η₁

/-- **Hypothesis (K3), general member** (paper, "Statement `K(s', j0)`"): the side `ρ_s` is outside Δ (the first form: the
corner of Δ at `p(s,0)` has the angle `β`), or a tile has a `RhoEdgeT` for `(s, j0)`. -/
def K3T (D : CongruentDissection N) (u v ε x : ℝ) (s j0 : ℝ) : Prop :=
  (∀ q ∈ D.target.carrier, -lvT u v ε x s ≤ GST u v ε q) ∨ ∃ w, RhoEdgeT D u v ε x w s j0

theorem K3T.mono {u v ε x s j0 j0' : ℝ} (h : K3T D u v ε x s j0) (hj : j0 ≤ j0') :
    K3T D u v ε x s j0' := by
  rcases h with h | ⟨w, k, m, η₁, η₂, hkm, h1, h2, hk, hm, hl, hle, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, k, m, η₁, η₂, hkm, le_trans h1 hj, h2, hk, hm, hl, hle, hc⟩

theorem K3G_of_out {u v ε x s j0 : ℝ}
    (h : ∀ q ∈ D.target.carrier, -lvT u v ε x s ≤ GST u v ε q) : K3T D u v ε x s j0 := Or.inl h

/-! ## 4. The tile across an `a`-edge -/

end Erdos634.Draft.ThmDRun


#print axioms Erdos634.Draft.ThmDRun.CtxBaseT.seg_intT
#print axioms Erdos634.Draft.ThmDRun.lpT_between
#print axioms Erdos634.Draft.ThmDRun.clampedBelowT_of_edge
