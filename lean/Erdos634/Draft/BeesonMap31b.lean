import Mathlib
import Erdos634.Draft.BeesonMap31a

/-!
# Beeson map, batch 31b: the three-tile vertex figure at the apex of the isosceles-beta triangle (the geometry behind `hNoM`)

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Theorem 37: "there are three tiles at vertex B, each with angle alpha at B. Then the outer
two have their c edges on AB and BC, and their b edges against the middle tile ... the c edge of the middle tile is at the west"), Beeson, Laczkovich.
Formalization debt, not progress on the /goal outcomes.

`not_both_mirror`: on a real `CongruentDissection`, the two first tiles of the two legs (`LaysBaseOn ... C1 0`, `c` edge on the leg, `alpha` at the apex `P`) cannot BOTH have a
mirror tile beside them across their `b` edge.  Proof (distances only, no coordinates): the two first tiles `i1, i2`, their mirrors `T1, T2` are four distinct tiles
with a vertex at `P` (`i1 = i2`: the `c` vertices are on different legs; `T = i`: reflection moves `E`; `T1 = i2`: then `angle E1 P E2 <= alpha + alpha < 3 alpha`; `T1 = T2`: same
`b` vertex, same reflection, `E1 = E2`); the count hypothesis `hcount` ("no four distinct tiles at the apex", `corner_counts` with `sum a = 3`) is discharged in 31c.
-/

open scoped Classical
set_option linter.unusedVariables false

namespace Erdos634.BeesonMap31b

open Erdos634.Geometry Erdos634.Draft.SideRunG Erdos634.Draft.SideRunGA Erdos634.Draft.SideRun Erdos634.Draft.W2E1 Erdos634.BaseBetaTargetCoord

variable {N : ℕ}

theorem fin3_uniq : ∀ u v j u' v' j' : Fin 3, u ≠ v → u ≠ j → v ≠ j → u' ≠ v' → u' ≠ j' → v' ≠ j' → u' = u →
    (v' = v ∧ j' = j) ∨ (v' = j ∧ j' = v) := by decide

theorem fin3_third : ∀ k m j kT mT jT : Fin 3, k ≠ m → k ≠ j → m ≠ j → kT ≠ mT → kT ≠ jT → mT ≠ jT → kT = k → mT = j → jT = m := by decide

theorem modelAlpha_facts {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < modelAlpha e f ∧ modelAlpha e f ≤ Real.pi := by
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he hef
  unfold modelAlpha
  constructor <;> linarith [Real.pi_pos]

/-- the corner angle of a tile at the `alpha` vertex, from the three sides -/
theorem angle_alpha {e f : ℝ} (T : TileOK e f) {P E W : Plane} (hEP : dist E P = f ^ 2) (hWP : dist W P = f ^ 2 - e ^ 2)
    (hEW : dist E W = e * f) : cornerAngle E P W = modelAlpha e f := by
  have he := T.he
  have hef := T.hef
  have hf : 0 < f := he.trans hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hcos := Erdos634.AngleThreshold.cos_of_sides E P W (by rw [hEP]; positivity) (by rw [hWP]; exact hb.ne')
  rw [hEP, hWP, hEW] at hcos
  obtain ⟨h0, hπ⟩ := modelAlpha_facts he hef
  refine Erdos634.MarchCompose.cornerAngle_eq_of_cos h0.le hπ ?_
  rw [hcos, cos_modelAlpha he hef]
  have h1 : 2 * f ^ 2 * (f ^ 2 - e ^ 2) ≠ 0 := by positivity
  have h2 : 2 * f ^ 2 ≠ 0 := by positivity
  rw [div_eq_div_iff h1 h2]
  ring

theorem angle_scaled {P Q R : Plane} {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') :
    EuclideanGeometry.angle (AffineMap.lineMap P Q s) P (AffineMap.lineMap P R s') = EuclideanGeometry.angle Q P R := by
  unfold EuclideanGeometry.angle
  rw [AffineMap.lineMap_vsub_left, AffineMap.lineMap_vsub_left, InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hs']

theorem vtx_unique {Tr : Erdos634.Geometry.Tri} {e f : ℝ} (hc_ne : f ^ 2 ≠ f ^ 2 - e ^ 2) {P E E' W W' : Plane} {k m j k' m' j' : Fin 3}
    (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) (hkm' : k' ≠ m') (hkj' : k' ≠ j') (hmj' : m' ≠ j')
    (hk : Tr.pts k = P) (hm : Tr.pts m = E) (hj : Tr.pts j = W) (hk' : Tr.pts k' = P) (hm' : Tr.pts m' = E')
    (hj' : Tr.pts j' = W')
    (hE : dist E P = f ^ 2) (hW : dist W P = f ^ 2 - e ^ 2) (hE' : dist E' P = f ^ 2) (hW' : dist W' P = f ^ 2 - e ^ 2) :
    E = E' ∧ W = W' := by
  have hkk : k' = k := Tr.indep.injective (hk'.trans hk.symm)
  rcases fin3_uniq k m j k' m' j' hkm hkj hmj hkm' hkj' hmj' hkk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by rw [← hm, ← hm', h1], by rw [← hj, ← hj', h2]⟩
  · exfalso
    have : E' = W := by rw [← hm', h1, hj]
    exact hc_ne (hE'.symm.trans (by rw [this]; exact hW))

/-- the data of a first leg tile together with its mirror -/
theorem mirror_data {D₀ : CongruentDissection N} {e f : ℝ} (T : TileOK e f) {P Q : Plane} {i Tm : Fin N}
    (hL : LaysBaseOn D₀ e f P Q i Ty.C1 0) (hd : 0 < dist P Q) (hM : MirrorBeside D₀ e f P i Tm) :
    ∃ (E W R : Plane) (k m j kT mT jT : Fin 3), k ≠ m ∧ k ≠ j ∧ m ≠ j ∧ (D₀.tile i).pts k = P ∧ (D₀.tile i).pts m = E ∧
      (D₀.tile i).pts j = W ∧ E = AffineMap.lineMap P Q (f ^ 2 / dist P Q) ∧ dist E P = f ^ 2 ∧ dist W P = f ^ 2 - e ^ 2 ∧
      dist E W = e * f ∧ kT ≠ mT ∧ kT ≠ jT ∧ mT ≠ jT ∧ (D₀.tile Tm).pts kT = P ∧ (D₀.tile Tm).pts mT = W ∧
      (D₀.tile Tm).pts jT = R ∧ dist R P = f ^ 2 ∧ dist R W = e * f ∧ R ≠ E ∧
      R = EuclideanGeometry.reflection (affineSpan ℝ {P, W}) E := by
  have he := T.he
  have hef := T.hef
  have hf : 0 < f := he.trans hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hjk, hjm⟩ := hL
  have hkP : (D₀.tile i).pts k = P := by rw [hk]; simp
  have hmE : (D₀.tile i).pts m = AffineMap.lineMap P Q (f ^ 2 / dist P Q) := by
    rw [hm]; simp [Ty.lenG]
  have hjk' : dist ((D₀.tile i).pts j) P = f ^ 2 - e ^ 2 := by rw [← hkP]; exact hjk
  have hjm' : dist ((D₀.tile i).pts j) ((D₀.tile i).pts m) = e * f := hjm
  have hEP : dist ((D₀.tile i).pts m) P = f ^ 2 := by
    rw [hmE, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  obtain ⟨E', W', R, hv, hWb, hvT, hR⟩ := hM
  obtain ⟨k₁, m₁, j₁, hkm₁, hkj₁, hmj₁, hk₁, hm₁, hj₁⟩ := hv
  have hc_ne : f ^ 2 ≠ f ^ 2 - e ^ 2 := by nlinarith
  have hk1k : k₁ = k := (D₀.tile i).indep.injective (hk₁.trans hkP.symm)
  have hmj_eq : m₁ = m ∧ j₁ = j := by
    rcases fin3_uniq k m j k₁ m₁ j₁ hkm hkj hmj hkm₁ hkj₁ hmj₁ hk1k with h | ⟨h1, h2⟩
    · exact h
    · exfalso
      have : dist ((D₀.tile i).pts m) P = f ^ 2 - e ^ 2 := by rw [← h2, hj₁, hWb]
      exact hc_ne (hEP.symm.trans this)
  obtain ⟨hm1m, hj1j⟩ := hmj_eq
  have hWeq : W' = (D₀.tile i).pts j := by rw [← hj₁, hj1j]
  have hEeq : E' = (D₀.tile i).pts m := by rw [← hm₁, hm1m]
  subst hWeq hEeq
  obtain ⟨kT, mT, jT, hkmT, hkjT, hmjT, hkT, hmT, hjT⟩ := hvT
  have hPW : P ∈ affineSpan ℝ {P, (D₀.tile i).pts j} := left_mem_affineSpan_pair ℝ _ _
  have hWW : (D₀.tile i).pts j ∈ affineSpan ℝ {P, (D₀.tile i).pts j} := right_mem_affineSpan_pair ℝ _ _
  have hRP : dist R P = f ^ 2 := by
    rw [hR, dist_comm, EuclideanGeometry.dist_reflection_eq_of_mem _ hPW, dist_comm]; exact hEP
  have hRW : dist R ((D₀.tile i).pts j) = e * f := by
    rw [hR, dist_comm, EuclideanGeometry.dist_reflection_eq_of_mem _ hWW]; exact hjm'
  have hRE : R ≠ (D₀.tile i).pts m := by
    intro hRE
    have hnot := not_collinear_dist he hef (A' := P) (W := (D₀.tile i).pts j) (E := (D₀.tile i).pts m) hEP hjk'
      (by rw [dist_comm]; exact hjm')
    apply hnot
    have : EuclideanGeometry.reflection (affineSpan ℝ {P, (D₀.tile i).pts j}) ((D₀.tile i).pts m) = (D₀.tile i).pts m := by
      rw [← hR]; exact hRE
    exact (EuclideanGeometry.reflection_eq_self_iff _).mp this
  exact ⟨(D₀.tile i).pts m, (D₀.tile i).pts j, R, k, m, j, kT, mT, jT, hkm, hkj, hmj, hkP, rfl, rfl, hmE, hEP, hjk',
    by rw [dist_comm]; exact hjm', hkmT, hkjT, hmjT, hkT, hmT, hjT, hRP, hRW, hRE, hR⟩

theorem three_alpha_contra {e f : ℝ} (T : TileOK e f) {P E R W : Plane}
    (hEP : dist E P = f ^ 2) (hRP : dist R P = f ^ 2) (hWP : dist W P = f ^ 2 - e ^ 2)
    (hEW : dist E W = e * f) (hRW : dist R W = e * f) (h3 : EuclideanGeometry.angle E P R = 3 * modelAlpha e f) : False := by
  obtain ⟨h0, -⟩ := modelAlpha_facts T.he T.hef
  have h1 := angle_alpha T hEP hWP hEW
  have h2 := angle_alpha T hRP hWP hRW
  have := EuclideanGeometry.angle_le_angle_add_angle P E W R
  rw [Erdos634.Geometry.cornerAngle] at h1 h2
  rw [EuclideanGeometry.angle_comm W P R, h1, h2, h3] at this
  linarith

theorem not_both_mirror {D₀ : CongruentDissection N} {e f : ℝ} (T : TileOK e f) {P P0 P1 : Plane}
    (hd0 : 0 < dist P P0) (hd1 : 0 < dist P P1) (hang : cornerAngle P0 P P1 = 3 * modelAlpha e f)
    {i₁ T₁ i₂ T₂ : Fin N}
    (hL1 : LaysBaseOn D₀ e f P P0 i₁ Ty.C1 0) (hM1 : MirrorBeside D₀ e f P i₁ T₁)
    (hL2 : LaysBaseOn D₀ e f P P1 i₂ Ty.C1 0) (hM2 : MirrorBeside D₀ e f P i₂ T₂)
    (hcount : ∀ a b c d : Fin N, (∃ k, (D₀.tile a).pts k = P) → (∃ k, (D₀.tile b).pts k = P) →
      (∃ k, (D₀.tile c).pts k = P) → (∃ k, (D₀.tile d).pts k = P) →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False) : False := by
  have he := T.he
  have hef := T.hef
  have hf : 0 < f := he.trans hef
  have hc_ne : f ^ 2 ≠ f ^ 2 - e ^ 2 := by nlinarith
  obtain ⟨h0, -⟩ := modelAlpha_facts he hef
  obtain ⟨E₁, W₁, R₁, k₁, m₁, j₁, kT₁, mT₁, jT₁, hkm₁, hkj₁, hmj₁, hk₁, hm₁, hj₁, hE₁, hE₁P, hW₁P, hE₁W₁, hkmT₁, hkjT₁,
    hmjT₁, hkT₁, hmT₁, hjT₁, hR₁P, hR₁W₁, hR₁E₁, hR₁⟩ := mirror_data T hL1 hd0 hM1
  obtain ⟨E₂, W₂, R₂, k₂, m₂, j₂, kT₂, mT₂, jT₂, hkm₂, hkj₂, hmj₂, hk₂, hm₂, hj₂, hE₂, hE₂P, hW₂P, hE₂W₂, hkmT₂, hkjT₂,
    hmjT₂, hkT₂, hmT₂, hjT₂, hR₂P, hR₂W₂, hR₂E₂, hR₂⟩ := mirror_data T hL2 hd1 hM2
  have hs₁ : 0 < f ^ 2 / dist P P0 := by positivity
  have hs₂ : 0 < f ^ 2 / dist P P1 := by positivity
  have hA : EuclideanGeometry.angle E₁ P E₂ = 3 * modelAlpha e f := by
    rw [hE₁, hE₂, angle_scaled hs₁ hs₂]; exact hang
  have hE₂P' : E₂ ≠ P := by intro h; rw [h, dist_self] at hE₂P; nlinarith
  have hE12 : E₁ ≠ E₂ := by
    intro h
    rw [h, EuclideanGeometry.angle_self_of_ne hE₂P'] at hA
    linarith
  have hexP₁ : ∃ k, (D₀.tile i₁).pts k = P := ⟨k₁, hk₁⟩
  have hexP₂ : ∃ k, (D₀.tile i₂).pts k = P := ⟨k₂, hk₂⟩
  have hexT₁ : ∃ k, (D₀.tile T₁).pts k = P := ⟨kT₁, hkT₁⟩
  have hexT₂ : ∃ k, (D₀.tile T₂).pts k = P := ⟨kT₂, hkT₂⟩
  -- i₁ ≠ i₂
  have d12 : i₁ ≠ i₂ := by
    intro h
    subst h
    exact hE12 (vtx_unique (Tr := D₀.tile i₁) hc_ne hkm₁ hkj₁ hmj₁ hkm₂ hkj₂ hmj₂ hk₁ hm₁ hj₁ hk₂ hm₂ hj₂
      hE₁P hW₁P hE₂P hW₂P).1
  -- T ≠ i (the reflection moves E)
  have dT : ∀ {E W R : Plane} {i T' : Fin N} {k m j kT mT jT : Fin 3}, k ≠ m → k ≠ j → m ≠ j → kT ≠ mT → kT ≠ jT → mT ≠ jT →
      (D₀.tile i).pts k = P → (D₀.tile i).pts m = E → (D₀.tile i).pts j = W →
      (D₀.tile T').pts kT = P → (D₀.tile T').pts mT = W → (D₀.tile T').pts jT = R → R ≠ E → T' ≠ i := by
    intro E W R i T' k m j kT mT jT hkm hkj hmj hkmT hkjT hmjT hk hm hj hkT hmT hjT hRE h
    rw [h] at hkT hmT hjT
    have hkk : kT = k := (D₀.tile i).indep.injective (hkT.trans hk.symm)
    have hmm : mT = j := (D₀.tile i).indep.injective (hmT.trans hj.symm)
    have := fin3_third k m j kT mT jT hkm hkj hmj hkmT hkjT hmjT hkk hmm
    apply hRE
    rw [← hjT, ← hm, this]
  have d1T₁ : T₁ ≠ i₁ := dT hkm₁ hkj₁ hmj₁ hkmT₁ hkjT₁ hmjT₁ hk₁ hm₁ hj₁ hkT₁ hmT₁ hjT₁ hR₁E₁
  have d2T₂ : T₂ ≠ i₂ := dT hkm₂ hkj₂ hmj₂ hkmT₂ hkjT₂ hmjT₂ hk₂ hm₂ hj₂ hkT₂ hmT₂ hjT₂ hR₂E₂
  -- T₁ ≠ i₂
  have d1T₂ : T₁ ≠ i₂ := by
    intro h
    rw [h] at hkT₁ hmT₁ hjT₁
    obtain ⟨hRE, hWW⟩ := vtx_unique (Tr := D₀.tile i₂) hc_ne hkjT₁ hkmT₁ hmjT₁.symm hkm₂ hkj₂ hmj₂ hkT₁ hjT₁ hmT₁ hk₂ hm₂ hj₂
      hR₁P hW₁P hE₂P hW₂P
    exact three_alpha_contra T hE₁P hR₁P hW₁P hE₁W₁ hR₁W₁ (by rw [hRE]; exact hA)
  -- T₂ ≠ i₁
  have d2T₁ : T₂ ≠ i₁ := by
    intro h
    rw [h] at hkT₂ hmT₂ hjT₂
    obtain ⟨hRE, hWW⟩ := vtx_unique (Tr := D₀.tile i₁) hc_ne hkjT₂ hkmT₂ hmjT₂.symm hkm₁ hkj₁ hmj₁ hkT₂ hjT₂ hmT₂ hk₁ hm₁ hj₁
      hR₂P hW₂P hE₁P hW₁P
    exact three_alpha_contra T hE₂P hR₂P hW₂P hE₂W₂ hR₂W₂ (by rw [hRE, EuclideanGeometry.angle_comm]; exact hA)
  -- T₁ ≠ T₂
  have dTT : T₁ ≠ T₂ := by
    intro h
    rw [h] at hkT₁ hmT₁ hjT₁
    obtain ⟨hRR, hWW⟩ := vtx_unique (Tr := D₀.tile T₂) hc_ne hkjT₁ hkmT₁ hmjT₁.symm hkjT₂ hkmT₂ hmjT₂.symm hkT₁ hjT₁ hmT₁
      hkT₂ hjT₂ hmT₂ hR₁P hW₁P hR₂P hW₂P
    apply hE12
    rw [hWW] at hR₁
    have := (EuclideanGeometry.reflection (affineSpan ℝ {P, W₂})).injective (hR₁.symm.trans (hRR.trans hR₂))
    exact this
  exact hcount i₁ i₂ T₁ T₂ hexP₁ hexP₂ hexT₁ hexT₂ d12 d1T₁.symm d2T₁.symm d1T₂.symm d2T₂.symm dTT

end Erdos634.BeesonMap31b

#print axioms Erdos634.BeesonMap31b.not_both_mirror
