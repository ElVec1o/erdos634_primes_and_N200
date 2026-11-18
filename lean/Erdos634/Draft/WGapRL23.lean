/-
Draft/WGapRL23.lean -- written 16 November 2026 (session 13).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, inner chord point: "the next tile above must show beta").
Not imported by any aggregate.  No sorry, no native_decide.
* `clamp_prev_tile`: if a tile `(X - (Y - X), X, W)` lies on the right of the line `XY`, then no tile edge on the line straddles `X` (`P' = X - (Y - X)`).
* `inner_fill_abs`: at an inner point `X` of a chord, four known tiles (`t0` on the left of the ray `XY`, showing `gamma`; `tA` showing `alpha`; `tB` showing `beta`; the previous chord tile `tnu` on the right showing `gamma`)
  leave the wedge `alpha + beta`; the filler beside the ray shows `alpha` or `beta`: either a beta tile with its `a`-edge on the ray (`dist X P = a`, `dist X W = c`, `dist P W = b`), or a tile whose edge on the ray has length `b` or `c`.
-/
import Erdos634.Draft.WGapRL22

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

set_option maxHeartbeats 4000000 in
theorem clamp_prev_tile (D : CongruentDissection N) {X Y W : Plane} {j₁ : Fin N} (hXY : X ≠ Y)
    (hj : HasV D j₁ (X - (Y - X)) X W) (hcr : cross (Y - X) (W - X) < 0) :
    ∀ ed ∈ D.lineChain (crossL (Y - X)) (cross (Y - X) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) (X - (Y - X)) X Y := by
  intro ed hed
  set u : Plane := Y - X with hu
  have hu0 : u ≠ 0 := by
    intro h; apply hXY; rw [hu] at h; exact (sub_eq_zero.mp h).symm
  set F := crossL u with hF
  set cc := cross u X with hcc
  have hFX : F X = cc := crossL_apply _ _
  have hFu : F u = 0 := by rw [hF, crossL_apply]; simp [cross]; ring
  have hFl : ∀ s : ℝ, F (X + s • u) = cc := by
    intro s; rw [map_add, map_smul, hFu, hFX]; simp
  have hP'eq : X - u = X + (-1 : ℝ) • u := by simp [sub_eq_add_neg]
  have hFP' : F (X - u) = cc := by rw [hP'eq]; exact hFl (-1)
  have hFY : F Y = cc := by
    have := hFl 1
    have hY : X + (1 : ℝ) • u = Y := by rw [hu]; simp
    rwa [hY] at this
  have hFW : F W ≤ cc := by
    have h1 : F W = cross u (W - X) + cc := by
      rw [hF, crossL_apply, hcc, ← cross_add_right]; congr 1; abel
    linarith
  have hle₁ : ∀ y ∈ (D.tile j₁).carrier, F y ≤ cc :=
    Tri.carrier_subset_halfplane (D.tile j₁) F cc (hj.all (P := fun z => F z ≤ cc) (le_of_eq hFP') (le_of_eq hFX) hFW)
  obtain ⟨k₁, hk₁⟩ := hasV_edge_eq hj
  have hE₁ : ∀ y ∈ (D.tile j₁).edge k₁, F y = cc := by
    intro y hy
    rw [hk₁] at hy
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    rw [map_add, map_smul, map_smul, hFP', hFX]
    simp only [smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  have hXP : X ∈ openSegment ℝ (X - u) Y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [hu]; ext i; simp; ring
  by_cases hee : ed = (j₁, k₁)
  · rintro ⟨-, z, hzE, hzQ⟩
    rw [hee] at hzE
    rw [hk₁] at hzE
    obtain ⟨a, b, ha, hb, hab, hz1⟩ := hzE
    obtain ⟨c', d, hc', hd, hcd, hz2⟩ := hzQ
    have hb' : b = 1 - a := by linarith
    have hc'' : c' = 1 - d := by linarith
    subst hb' hc''
    have hz : (a + d) • u = 0 := by
      have e := hz1.trans hz2.symm
      ext x
      have := congrArg (fun z => z x) e
      rw [hu] at this ⊢
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, PiLp.zero_apply] at this ⊢
      nlinarith [this]
    rcases smul_eq_zero.mp hz with h0 | h0
    · linarith
    · exact hu0 h0
  · exact not_straddles_of_sameside_edge D.toDissection F (Erdos634.Geometry.crossL_ne_zero hu0) cc hXY hFX hFY hFP' hXP hle₁ hE₁
      (by rw [hk₁]) hed hee

section rl23

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 8000000 in
theorem inner_fill_abs (S : SetupG D e f α β γ L ax ay) {X Y Z W : Plane} {t0 tA tB tν : Fin N}
    (hXY : X ≠ Y) (hV : HasV D t0 X Y Z) (hZ : 0 < cross (Y - X) (Z - X))
    (hν : HasV D tν (X - (Y - X)) X W) (hWc : cross (Y - X) (W - X) < 0)
    (a0 : (D.tile t0).localAngle X = γ) (aA : (D.tile tA).localAngle X = α)
    (aB : (D.tile tB).localAngle X = β) (aν : (D.tile tν).localAngle X = γ)
    (n0ν : t0 ≠ tν)
    (rA : ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile tA).pts j ≠ AffineMap.lineMap X Y s)
    (rB : ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile tB).pts j ≠ AffineMap.lineMap X Y s)
    (rν : ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile tν).pts j ≠ AffineMap.lineMap X Y s) :
    (∃ (τ : Fin N) (P W' : Plane), HasV D τ X P W' ∧ (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap X Y s) ∧
      cross (Y - X) (W' - X) < 0 ∧ dist P W' = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist X P = (e : ℝ) * f ∧
      dist X W' = (f : ℝ) ^ 2) ∨
    (∃ (τ : Fin N) (P W' : Plane), HasV D τ X P W' ∧ (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap X Y s) ∧
      cross (Y - X) (W' - X) < 0 ∧ (dist X P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨ dist X P = (f : ℝ) ^ 2)) := by
  have hA := S.hA
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  have h0A : t0 ≠ tA := ne_of_angle (by rw [a0, aA]; exact hαγ.symm)
  have h0B : t0 ≠ tB := ne_of_angle (by rw [a0, aB]; exact hβγ.symm)
  have hνA : tν ≠ tA := ne_of_angle (by rw [aν, aA]; exact hαγ.symm)
  have hνB : tν ≠ tB := ne_of_angle (by rw [aν, aB]; exact hβγ.symm)
  have hAB : tA ≠ tB := ne_of_angle (by rw [aA, aB]; exact hαβ)
  set K : Finset (Fin N) := {t0, tν, tA, tB} with hKdef
  have hXt : X ∈ D.target.carrier := hV.mem₁
  have hYt : Y ∈ D.target.carrier := hV.mem₂
  have hr := hA.hrel
  have hg := hA.hγdef
  have h1 := hA.hα
  have h2 := hA.hβ
  have hKsum3 : ∑ i ∈ K, (D.tile i).localAngle X = γ + γ + α + β := by
    rw [hKdef, Finset.sum_insert (by simp [n0ν, h0A, h0B]), Finset.sum_insert (by simp [hνA, hνB]),
      Finset.sum_insert (by simp [hAB]), Finset.sum_singleton, a0, aν, aA, aB]
    ring
  have hXint : X ∈ interior D.target.carrier := by
    refine interior_of_sum D.toDissection hXt K ?_
    rw [hKsum3]; linarith
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle X = 2 * Real.pi - (α + β) := by
    rw [hKsum3]; linarith
  have hΩ : ∑ i, (D.tile i).localAngle X = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq X
    rw [this, D.target.localAngle_interior hXint]
  obtain ⟨-, -, hγ0⟩ := wedge_alpha_beta S hΩ hKsum (by linarith)
  have hint := openSeg_interior D.toDissection hXint hYt
  have hP' : cross (Y - X) ((X - (Y - X)) - X) = 0 := by
    simp [cross]; ring
  have hXP : X ∈ openSegment ℝ (X - (Y - X)) Y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hclamp := clamp_prev_tile D hXY hν hWc
  have hKray : ∀ k ∈ K, k ≠ t0 → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap X Y s := by
    intro k hk hkt
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact absurd rfl hkt
    · exact rν
    · exact rA
    · exact rB
  obtain ⟨τ, hτK, k, m, n, t, hkm, hkn, hmn, hk, ht, hm, hneg, hvc⟩ :=
    filler_core S hXY hV hZ hP' hXP hint hclamp K hKray
  have hmemτ : τ ∈ Finset.univ \ K := by simp [hτK]
  have hHV : HasV D τ X ((D.tile τ).pts m) ((D.tile τ).pts n) := ⟨k, m, n, hkm, hkn, hmn, hk, rfl, rfl⟩
  have hray : ∃ s : ℝ, 0 < s ∧ (D.tile τ).pts m = AffineMap.lineMap X Y s := ⟨t, ht, hm⟩
  rcases hvc with hα' | hβ' | hγ'
  · -- alpha: the edge on the ray is `b` or `c`
    right
    refine ⟨τ, (D.tile τ).pts m, (D.tile τ).pts n, hHV, hray, hneg, ?_⟩
    obtain ⟨-, hs⟩ := sides_of_alpha S τ hkm hkn hmn (by rw [hk]; exact hα')
    rw [hk] at hs
    rcases hs with ⟨h1', -⟩ | ⟨h1', -⟩
    · exact Or.inr h1'
    · exact Or.inl h1'
  · -- beta
    obtain ⟨hopp, hs⟩ := sides_of_beta S τ hkm hkn hmn (by rw [hk]; exact hβ')
    rw [hk] at hs
    rcases hs with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · left
      exact ⟨τ, (D.tile τ).pts m, (D.tile τ).pts n, hHV, hray, hneg, hopp, h1', h2'⟩
    · right
      exact ⟨τ, (D.tile τ).pts m, (D.tile τ).pts n, hHV, hray, hneg, Or.inr h1'⟩
  · exfalso
    unfold cnt at hγ0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hγ0
    exact hγ0 hmemτ hγ'

end rl23

#print axioms clamp_prev_tile
#print axioms inner_fill_abs

end Erdos634.Draft.WGapStmt
