/-
Draft/TApexStruct1.lean -- written 16 November 2026 (work item LEAN_CORNERSTRUCT_2026-11-16, Target 2 probe).  UNAUDITED beyond internal checks.  Not imported by any aggregate.  New leaf module; no existing file is edited.
**The 3α apex of EVERY tiling of `T_M(e,f)` (any scale `M >= 1`): at least one of the two legs carries `f` consecutive tiles `C1` or `f` consecutive tiles `C2` (alternative (i) of `thm:cornerrun`).**
This is the scale-`M` version of the argument of Beeson-Rosu Theorem 37 (as formalized in `BeesonMap31c.thm37_j1`, scale one), with the ONE step that is scale-specific there (the contradiction from the leg length `f^3`) left out:
* `corners_of_dists_M`: the corner angles `β, β, 3α` of the triangle with sides `M f³, M f³, M e (3f² - e²)` (copy of `BeesonRosu37c1.corners_of_dists` with a scale `M`);
* `t_apex_not_both_mirror`: the tiles at the apex cannot show a mirror beside the first `C1` tile on BOTH legs (`BeesonMap31b.not_both_mirror` + `BeesonMap31c.apex_count`, as the end of `thm37_j1`);
* `leg_long_nomirror`: if no mirror stands beside the first tile of a leg, that leg carries alternative (i) (`corner_side_theorem`, `corner_run_mirror`; copy of `BeesonRosu37c2.leg_counts_nomirror` with the structural conclusion kept
  instead of the arithmetically trivial count `(0, 0, M f)`);
* `t_apex_one_leg_long` (the target `t_apex_struct` in its provable form): at least one leg of every `T_M(e,f)` tiling has alternative (i).  Alternative (ii) is NOT excluded on the OTHER leg (fan `(cb, bc, ·)` seen from it).
Credit: Beeson-Rosu (Theorem 37, Lemmas 30, 34), Beeson, Laczkovich, Zhang, Paliy; the project's rooms BeesonMap31a-c, BeesonRosu37b-d.  No sorry, no native_decide.
-/
import Erdos634.Draft.BeesonMap31c
import Erdos634.Draft.WCornerStruct3

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.TApexStruct

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.SideRunG Erdos634.Draft.SideRunGA
  Erdos634.Draft.SideRun Erdos634.Draft.W2E1 Erdos634.BaseBetaTargetCoord Erdos634.TilePlacement Erdos634.Geometry.Dissection
  Erdos634.BeesonRosu37b1 Erdos634.BeesonRosu37c2 Erdos634.BeesonRosu37d1 Erdos634.BeesonRosu37d2
  Erdos634.BeesonMap31a Erdos634.BeesonMap31b Erdos634.BeesonMap31c Erdos634.Draft.UniformThreshold

variable {N : ℕ}

/-- **Corner angles at scale `M`** (copy of `BeesonRosu37c1.corners_of_dists`, sides multiplied by `M > 0`) -/
theorem corners_of_dists_M (T : Erdos634.Geometry.Tri) {e f M : ℝ} (he : 0 < e) (hef : e < f) (hM : 0 < M)
    (τ : Equiv.Perm (Fin 3))
    (h1 : dist (T.pts (τ 1)) (T.pts (τ 2)) = M * f ^ 3) (h2 : dist (T.pts (τ 2)) (T.pts (τ 0)) = M * f ^ 3)
    (h3 : dist (T.pts (τ 0)) (T.pts (τ 1)) = M * (e * (3 * f ^ 2 - e ^ 2))) :
    cornerAngle (T.pts (τ 1)) (T.pts (τ 0)) (T.pts (τ 2)) = modelBeta e f ∧
    cornerAngle (T.pts (τ 2)) (T.pts (τ 1)) (T.pts (τ 0)) = modelBeta e f ∧
    cornerAngle (T.pts (τ 0)) (T.pts (τ 2)) (T.pts (τ 1)) = 3 * modelAlpha e f := by
  have hf : 0 < f := lt_trans he hef
  have hbl : baseLen e f = e * (3 * f ^ 2 - e ^ 2) := by unfold baseLen Nq; rfl
  have hpos := baseLen_pos he hef
  have hb := cos_modelBeta he hef
  have hmb : modelBeta e f ∈ Set.Icc 0 Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hI : ∀ p q r : Plane, cornerAngle p q r ∈ Set.Icc 0 Real.pi := fun p q r =>
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hbpos : M * (e * (3 * f ^ 2 - e ^ 2)) ≠ 0 := by
    rw [← hbl]; exact (mul_pos hM hpos).ne'
  have hf3 : M * f ^ 3 ≠ 0 := by positivity
  have hK : 3 * f ^ 2 - e ^ 2 ≠ 0 := by nlinarith
  have hK' : f ^ 2 * 3 - e ^ 2 ≠ 0 := by nlinarith
  have he0 := he.ne'
  have hf0 := hf.ne'
  have hM0 := hM.ne'
  have h1' : dist (T.pts (τ 2)) (T.pts (τ 1)) = M * f ^ 3 := by rw [dist_comm]; exact h1
  have h2' : dist (T.pts (τ 0)) (T.pts (τ 2)) = M * f ^ 3 := by rw [dist_comm]; exact h2
  have h3' : dist (T.pts (τ 1)) (T.pts (τ 0)) = M * (e * (3 * f ^ 2 - e ^ 2)) := by rw [dist_comm]; exact h3
  have hA : cornerAngle (T.pts (τ 1)) (T.pts (τ 0)) (T.pts (τ 2)) = modelBeta e f := by
    apply Real.injOn_cos (hI _ _ _) hmb
    rw [Erdos634.AngleThreshold.cos_of_sides _ _ _ (by rw [h3']; exact hbpos) (by rw [h2]; exact hf3)]
    rw [h3', h2, h1, hb, hbl]
    field_simp
    ring
  have hB : cornerAngle (T.pts (τ 2)) (T.pts (τ 1)) (T.pts (τ 0)) = modelBeta e f := by
    apply Real.injOn_cos (hI _ _ _) hmb
    rw [Erdos634.AngleThreshold.cos_of_sides _ _ _ (by rw [h1']; exact hf3) (by rw [h3]; exact hbpos)]
    rw [h1', h3, h2, hb, hbl]
    field_simp
    ring
  refine ⟨hA, hB, ?_⟩
  have hne : T.pts (τ 1) ≠ T.pts (τ 0) := fun h => by
    have := τ.injective (T.indep.injective h)
    exact absurd this (by decide)
  have key := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (V := Plane) (p₁ := T.pts (τ 0)) (p₂ := T.pts (τ 1)) (T.pts (τ 2)) hne
  have hrel := modelAngle_rel e f
  have c1 := EuclideanGeometry.angle_comm (V := Plane) (T.pts (τ 1)) (T.pts (τ 0)) (T.pts (τ 2))
  have c2 := EuclideanGeometry.angle_comm (V := Plane) (T.pts (τ 2)) (T.pts (τ 1)) (T.pts (τ 0))
  have c3 := EuclideanGeometry.angle_comm (V := Plane) (T.pts (τ 0)) (T.pts (τ 2)) (T.pts (τ 1))
  unfold cornerAngle at hA hB ⊢
  linarith [key, hA, hB, hrel, c1, c2, c3]

/-- **A leg of a `T_M(e,f)` tiling with alternative (i)**: the leg `[P, Q]` (apex `P`, base corner `Q`) of `D₀`, placed by an isometry `g` on `[0, L]`, `L = M f³`, is the union of a typed chain of base tiles
(a `SetupG` frame with corners) containing `f` consecutive tiles `C1` or `f` consecutive tiles `C2`. -/
def TLegLong (D₀ : CongruentDissection N) (M e f : ℕ) (P Q : Plane) : Prop :=
  ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane) (L ax ay : ℝ),
    (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧ g P = CertCoord.mkPt 0 0 ∧ g Q = CertCoord.mkPt L 0 ∧
    dist P Q = L ∧
    ∃ (S : SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) L ax ay)
      (_ : CornersA e f L ax ay) (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty)
      (_ : ChainG D e f L m X tile τ),
      ∃ i, i + f ≤ m ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2))

/-- **A leg without a mirror beside its first tile has alternative (i)** (scale `M`; the structural conclusion of `leg_counts_nomirror`) -/
theorem leg_long_nomirror (e f M : ℕ) (hm : 1 ≤ e) (hmk : e < f) (hco : Nat.Coprime e f) (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hApex : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
      3 * modelAlpha (e : ℝ) (f : ℝ))
    (hBeta : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
      modelBeta (e : ℝ) (f : ℝ))
    (hNoM : ∀ i₀ T : Fin N, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i₀ Ty.C1 0 →
      ¬ MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) i₀ T) :
    TLegLong D₀ M e f (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := by
  obtain ⟨D, g, L, ax, ay, hL, hdist, hD, hP, hB, S, Co, -⟩ :=
    setup_of_corners e f hm hmk hco D₀ hMod τ (Or.inr hApex) (Or.inl hBeta)
  obtain ⟨c, X, tile, τ', Ch⟩ := S.exists_chainG
  have hi : ∃ i, i + f ≤ c ∧ ((∀ j, j < f → τ' (i + j) = Ty.C1) ∨ (∀ j, j < f → τ' (i + j) = Ty.C2)) := by
    rcases corner_side_theorem S Co Ch with h | ⟨k', hk1, hkf, hkm, hrun, hsucc⟩
    · exact h
    · exfalso
      have hsucc' : k' = c ∨ (k' < c ∧ τ' k' ≠ Ty.B1 ∧ τ' k' ≠ Ty.C1) := by
        rcases hsucc with h | ⟨h, h'⟩
        · exact Or.inl h
        · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
      have hM := corner_run_mirror S Co Ch hk1 hkf hrun hsucc'
      have hU := Ch.htile 0 (by omega)
      rw [hrun 0 (by omega), Ch.hX0] at hU
      obtain ⟨T, hT⟩ := mirrorBeside_of_mirrorAt hD hP S hU hM
      exact hNoM (tile 0) T (laysOn_of_baseTile hL hD hP hB hU) hT
  exact ⟨D, g, L, ax, ay, hD, hP, hB, hdist, S, Co, c, X, tile, τ', Ch, hi⟩

/-- **The two legs of a `T_M(e,f)` apex cannot both have a mirror beside the first `C1` tile** (scale `M`; the end of `thm37_j1`).  `τ 2` is the apex. -/
theorem t_apex_not_both_mirror (e f M : ℕ) (hm : 1 ≤ e) (hmk : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = (M : ℝ) * (f : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = (M : ℝ) * (f : ℝ) ^ 3)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (M : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    {i₁ T₁ i₂ T₂ : Fin N}
    (hL1 : LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) i₁ Ty.C1 0)
    (hM1 : MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 2)) i₁ T₁)
    (hL2 : LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) i₂ Ty.C1 0)
    (hM2 : MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 2)) i₂ T₂) : False := by
  have hmR : (0 : ℝ) < e := by exact_mod_cast hm
  have hmkR : (e : ℝ) < f := by exact_mod_cast hmk
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have T : TileOK (e : ℝ) (f : ℝ) := tileOK_of_nat hm hmk hco
  obtain ⟨cA, cB, cC⟩ := corners_of_dists_M D₀.target hmR hmkR hMR τ h1 h2 h3
  have hApex : cornerAngle (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = 3 * modelAlpha (e : ℝ) (f : ℝ) := by
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cC
  have hBeta : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = modelBeta (e : ℝ) (f : ℝ) := by
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cA
  have f0 : (finRotate 3).symm.trans τ 2 = τ 1 := rfl
  have f1 : (finRotate 3).symm.trans τ 0 = τ 2 := rfl
  have f2 : (finRotate 3).symm.trans τ 1 = τ 0 := rfl
  obtain ⟨D, g, L, ax, ay, hL, hdist, hD, hP, hB, S, Co, -⟩ :=
    setup_of_corners e f hm hmk hco D₀ hMod ((finRotate 3).symm.trans τ)
      (Or.inr (by rw [f0, f1, f2]; exact hApex)) (Or.inl (by rw [f0, f1, f2]; exact hBeta))
  replace hP : g (D₀.target.pts (τ 2)) = CertCoord.mkPt 0 0 := hP
  have hcount : ∀ a b c d : Fin N, (∃ k', (D₀.tile a).pts k' = D₀.target.pts (τ 2)) →
      (∃ k', (D₀.tile b).pts k' = D₀.target.pts (τ 2)) → (∃ k', (D₀.tile c).pts k' = D₀.target.pts (τ 2)) →
      (∃ k', (D₀.tile d).pts k' = D₀.target.pts (τ 2)) →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False := by
    intro a b c d ha hb hc hd
    have tr : ∀ i, (∃ k', (D₀.tile i).pts k' = D₀.target.pts (τ 2)) → ∃ k', (D.tile i).pts k' = CertCoord.mkPt 0 0 := by
      rintro i ⟨k', hk'⟩
      exact ⟨k', by rw [hD, hk', hP]⟩
    exact apex_count S Co a b c d (tr a ha) (tr b hb) (tr c hc) (tr d hd)
  have hpf : (0 : ℝ) < (M : ℝ) * (f : ℝ) ^ 3 := mul_pos hMR (pow_pos (by linarith) 3)
  have hd0 : 0 < dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) := by rw [h2]; exact hpf
  have hd1 : 0 < dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) := by rw [dist_comm, h1]; exact hpf
  have hang : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) = 3 * modelAlpha (e : ℝ) (f : ℝ) := cC
  exact not_both_mirror T hd0 hd1 hang hL1 hM1 hL2 hM2 hcount

/-- **THE 3α APEX OF EVERY `T_M(e,f)` TILING (any `M >= 1`): at least one of the two legs has alternative (i)** (`f` consecutive tiles `C1` or `C2`).  Hypotheses: coprime `1 <= e < f`, `M >= 1`, the sides of the target
(`M f³, M f³, M e (3f² - e²)`, labelling `τ`, apex `τ 2`) and of the model.  Conclusion: `TLegLong` on the leg `[τ 2, τ 0]` or on the leg `[τ 2, τ 1]`.  It does NOT say that alternative (ii) is absent on the other leg. -/
theorem t_apex_one_leg_long (e f M : ℕ) (hm : 1 ≤ e) (hmk : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = (M : ℝ) * (f : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = (M : ℝ) * (f : ℝ) ^ 3)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (M : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    TLegLong D₀ M e f (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) ∨
    TLegLong D₀ M e f (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) := by
  have hmR : (0 : ℝ) < e := by exact_mod_cast hm
  have hmkR : (e : ℝ) < f := by exact_mod_cast hmk
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨cA, cB, cC⟩ := corners_of_dists_M D₀.target hmR hmkR hMR τ h1 h2 h3
  -- second labelling: swap the two base corners
  set τ' : Equiv.Perm (Fin 3) := (Equiv.swap (0 : Fin 3) 1).trans τ with hτ'
  have e0 : τ' 0 = τ 1 := by simp [hτ', Equiv.swap_apply_left]
  have e1 : τ' 1 = τ 0 := by simp [hτ', Equiv.swap_apply_right]
  have e2 : τ' 2 = τ 2 := by
    simp [hτ', Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
  have h1' : dist (D₀.target.pts (τ' 1)) (D₀.target.pts (τ' 2)) = (M : ℝ) * (f : ℝ) ^ 3 := by
    rw [e1, e2, dist_comm]; exact h2
  have h2' : dist (D₀.target.pts (τ' 2)) (D₀.target.pts (τ' 0)) = (M : ℝ) * (f : ℝ) ^ 3 := by
    rw [e0, e2, dist_comm]; exact h1
  have h3' : dist (D₀.target.pts (τ' 0)) (D₀.target.pts (τ' 1)) = (M : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    rw [e0, e1, dist_comm]; exact h3
  by_cases hN : ∀ i₀ T : Fin N, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) i₀ Ty.C1 0 →
      ¬ MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 2)) i₀ T
  · left
    have e2' : (finRotate 3).symm.trans τ 2 = τ 1 := rfl
    have e0' : (finRotate 3).symm.trans τ 0 = τ 2 := rfl
    have e1' : (finRotate 3).symm.trans τ 1 = τ 0 := rfl
    have := leg_long_nomirror e f M hm hmk hco D₀ hMod ((finRotate 3).symm.trans τ)
      (by rw [e2', e0', e1', Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cC)
      (by rw [e2', e0', e1', Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cA)
      (by rw [e0', e1']; exact hN)
    rw [e0', e1'] at this
    exact this
  · right
    by_cases hN' : ∀ i₀ T : Fin N, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ' 2)) (D₀.target.pts (τ' 0)) i₀ Ty.C1 0 →
        ¬ MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ' 2)) i₀ T
    · obtain ⟨cA', cB', cC'⟩ := corners_of_dists_M D₀.target hmR hmkR hMR τ' h1' h2' h3'
      have e2' : (finRotate 3).symm.trans τ' 2 = τ' 1 := rfl
      have e0' : (finRotate 3).symm.trans τ' 0 = τ' 2 := rfl
      have e1' : (finRotate 3).symm.trans τ' 1 = τ' 0 := rfl
      have := leg_long_nomirror e f M hm hmk hco D₀ hMod ((finRotate 3).symm.trans τ')
        (by rw [e2', e0', e1', Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cC')
        (by rw [e2', e0', e1', Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cA')
        (by rw [e0', e1']; exact hN')
      rw [e0', e1', e2, e0] at this
      exact this
    · exfalso
      have hM1 : ∃ i₀ T : Fin N, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) i₀ Ty.C1 0 ∧
          MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 2)) i₀ T := by
        by_contra hcon
        exact hN (fun i₀ T hl hm' => hcon ⟨i₀, T, hl, hm'⟩)
      have hM2 : ∃ i₀ T : Fin N, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ' 2)) (D₀.target.pts (τ' 0)) i₀ Ty.C1 0 ∧
          MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ' 2)) i₀ T := by
        by_contra hcon
        exact hN' (fun i₀ T hl hm' => hcon ⟨i₀, T, hl, hm'⟩)
      obtain ⟨i₁, T₁, hL1, hMi1⟩ := hM1
      obtain ⟨i₂, T₂, hL2, hMi2⟩ := hM2
      rw [e2, e0] at hL2
      rw [e2] at hMi2
      exact t_apex_not_both_mirror e f M hm hmk hco hM D₀ τ h1 h2 h3 hMod hL1 hMi1 hL2 hMi2

/-! ## Controls: real Lean tilings of `T_M(e,f)` (from `CollarG.betaTilable_lin`) -/

theorem ctl_T_2_3_3 : ∃ (N : ℕ) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3)),
    TLegLong D₀ 3 2 3 (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) ∨ TLegLong D₀ 3 2 3 (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) := by
  obtain ⟨N, D₀, ⟨τ, h1, h2, h3⟩, hMod⟩ : BetaTilable 2 3 3 := by
    have := Erdos634.Draft.CollarG.betaTilable_lin 2 3 (by norm_num) (by norm_num) 1 (by norm_num) 0; simpa using this
  refine ⟨N, D₀, τ, ?_⟩
  exact t_apex_one_leg_long 2 3 3 (by omega) (by omega) (by decide) (by omega) D₀ τ (by simpa using h1) (by simpa using h2) (by simpa using h3) hMod

#print axioms corners_of_dists_M
#print axioms leg_long_nomirror
#print axioms t_apex_not_both_mirror
#print axioms t_apex_one_leg_long
#print axioms ctl_T_2_3_3

end Erdos634.Draft.TApexStruct
