/-
Draft/WGapInterior.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (Lemma 3.1, Lemma 5.0).
Not imported by any aggregate.  Module W2b.

The interior-point lemmas of the hand proof, by the project's EXISTING angle-sum theorem `Dissection.hasAngleSums`
(`AngleSumDissection.lean:238`: `∑ i, localAngle = 2π` at interior points, `π` at non-corner frontier points, `cornerAngle ≤ π` at the corners)
instead of the hand proof's tangent-cone argument:

* `sum_angles_le_pi`      : a point of the target that is not interior has total tile angle `≤ π`.
* `interior_of_two_tiles` : (Lemma 3.1/5.0 shape) two DISTINCT tiles with angles summing to more than `π` at `p ∈ target` force `p ∈ interior target`.
* `pts_ne`, `hasV_same`   : the three vertices of a tile are pairwise distinct; a tile with two given vertices has a determined third.
* `mp_zero_eta`, `mp_ne_lp`: `μ` fixes `p(0, η)` and moves `p(1, η)` (it is not on the line `l`).
* `lemma_5_0`             : **Lemma 5.0**: if `U(0,η)` and `T_η = U'(0,η)` are tiles then `p(0, η+1)` is an interior point of the target
  (the two tiles show `γ` there, `2γ = π + α > π`).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapMirror
import Erdos634.Draft.WGapAngles
import Erdos634.AngleSumDissection

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

/-- a point of the target that is not interior has total tile angle at most `π` -/
theorem sum_angles_le_pi (D : Dissection N) {p : Plane} (hp : p ∈ D.target.carrier)
    (hnot : p ∉ interior D.target.carrier) : ∑ i, (D.tile i).localAngle p ≤ Real.pi := by
  have hfr : p ∈ frontier D.target.carrier := ⟨subset_closure hp, hnot⟩
  obtain ⟨h1, h2, h3⟩ := D.hasAngleSums
  by_cases hv : p ∈ Set.range D.target.pts
  · obtain ⟨k, rfl⟩ := hv
    rw [h3 k]
    exact EuclideanGeometry.angle_le_pi _ _ _
  · rw [h2 p hfr hv]

/-- **Lemma 3.1/5.0 shape**: two distinct tiles with angles summing to more than `π` at `p ∈ target` force `p` interior -/
theorem interior_of_two_tiles (D : Dissection N) {p : Plane} (hp : p ∈ D.target.carrier) {t₁ t₂ : Fin N}
    (ht : t₁ ≠ t₂) {a b : ℝ} (h1 : (D.tile t₁).localAngle p = a) (h2 : (D.tile t₂).localAngle p = b)
    (hab : Real.pi < a + b) : p ∈ interior D.target.carrier := by
  by_contra hnot
  have hle := sum_angles_le_pi D hp hnot
  have hsub : ({t₁, t₂} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun i => (D.tile i).localAngle p) (fun i _ _ => Tri.localAngle_nonneg _ _)
  rw [Finset.sum_pair ht, h1, h2] at h
  linarith

section tilepts

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- the three vertices of a tile are pairwise distinct (their distances are `a, b, c > 0`) -/
theorem pts_ne (S : SetupG D e f α β γ L ax ay) (i : Fin N) {k m : Fin 3} (hkm : k ≠ m) :
    (D.tile i).pts k ≠ (D.tile i).pts m := by
  intro h
  rcases vertex_dist_casesG D S.hM i hkm with d | d | d <;> rw [h, dist_self] at d
  · exact S.a_pos.ne d
  · exact S.b_pos.ne d
  · exact S.c_pos.ne d

/-- a tile with two given vertices has its third vertex determined -/
theorem hasV_same (S : SetupG D e f α β γ L ax ay) {t : Fin N} {A B B' C : Plane}
    (h1 : HasV D t A B C) (h2 : HasV D t A B' C) : B = B' := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h1
  obtain ⟨k', m', j', hkm', hkj', hmj', hk', hm', hj'⟩ := h2
  have ek : k = k' := by
    by_contra hne; exact pts_ne S t hne (hk.trans hk'.symm)
  have ej : j = j' := by
    by_contra hne; exact pts_ne S t hne (hj.trans hj'.symm)
  subst ek; subst ej
  have key : ∀ k j m m' : Fin 3, k ≠ j → m ≠ k → m ≠ j → m' ≠ k → m' ≠ j → m = m' := by decide
  have : m = m' := key k j m m' hkj (Ne.symm hkm) hmj (Ne.symm hkm') hmj'
  subst this
  exact hm.symm.trans hm'

end tilepts

/-- `μ` fixes `p(0, η)` -/
theorem mp_zero_eta (e f ε x η : ℝ) : mpG e f ε x 0 η = lpG e f ε x 0 η := by
  unfold mpG reflL
  rw [EuclideanGeometry.reflection_eq_self_iff]
  have h : lpG e f ε x 0 η = AffineMap.lineMap (lpG e f ε x 0 0) (lpG e f ε x 0 1) η := by
    rw [lineMap_lpG]; exact lpG_congr (by ring) (by ring)
  rw [h]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- `μ` moves `p(1, η)` (it is not on the line `l`) -/
theorem mp_ne_lp {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (η : ℝ) :
    mpG e f ε x 1 η ≠ lpG e f ε x 1 η := by
  intro h
  unfold mpG reflL at h
  rw [EuclideanGeometry.reflection_eq_self_iff] at h
  obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ)).mp h
  have h1 := congrArg (FXG e f ε) hr
  rw [AffineMap.lineMap_apply] at h1
  simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, FXG_lp hε, smul_eq_mul] at h1
  have := lvG_lt (e := e) (f := f) (ε := ε) (x := x) he hef (show (0 : ℝ) < 1 by norm_num)
  nlinarith

/-- **Lemma 5.0** (PROOF P5): `U(0,η)` and `T_η = U'(0,η)` are tiles ⟹ `p(0, η+1)` is an interior point of the target. -/
theorem lemma_5_0 {e f : ℕ} {α β γ L ax ay x : ℝ} (S : SetupG D e f α β γ L ax ay) {η : ℝ}
    (hU : UTG D (e : ℝ) (f : ℝ) 1 x 0 η) (hT : UTM D (e : ℝ) (f : ℝ) 1 x 0 η) :
    lpG (e : ℝ) (f : ℝ) 1 x 0 (η + 1) ∈ interior D.target.carrier := by
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  obtain ⟨t₁, h1⟩ := hU
  obtain ⟨t₂, h2⟩ := hT
  rw [mp_zero_eta, mp_zero_eta] at h2
  have ang1 := (U_anglesG S hε h1).2.2
  -- the mirror tile: angle γ at the third vertex (opposite side `c`)
  have hd : dist (lpG (e : ℝ) (f : ℝ) 1 x 0 η) (mpG (e : ℝ) (f : ℝ) 1 x (0 + 1) η) = (f : ℝ) ^ 2 := by
    rw [← mp_zero_eta (e : ℝ) (f : ℝ) 1 x η]
    exact dist_mp_u S.e0 S.hef' hε 0 η
  have ang2 := (h2.rot.rot.anglesG S.tile S.hM).2.2 hd
  have hne : t₁ ≠ t₂ := by
    rintro rfl
    have := hasV_same S h1 (by simpa using h2)
    exact mp_ne_lp S.e0 S.hef' hε η (by simpa using this.symm)
  have hAD := Erdos634.Draft.WGapAngles.angle_ineqs S.hA
  exact interior_of_two_tiles D.toDissection h1.mem₃ hne ang1 ang2 (by linarith [hAD.2.2.2.2.1])

/-- witness for `lemma_5_0`'s second hypothesis: the reflection of the lattice triangle is realizable (the vertices exist): nothing to check
beyond `UTM`; the NEGATIVE control is `mp_ne_lp`: the mirror tile is a different tile from `U(0,η)`. -/
example {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) :
    mpG e f ε x 1 0 ≠ lpG e f ε x 1 0 := mp_ne_lp he hef hε 0

#print axioms lemma_5_0
#print axioms interior_of_two_tiles

end Erdos634.Draft.WGapStmt
