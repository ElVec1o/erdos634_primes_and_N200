/-
Draft/WGapRL14.lean -- written 16 November 2026 (session 12).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 steps (5), (6) at `i = 1`).
Not imported by any aggregate.  No sorry, no native_decide.
* `Tplus_core`: `sigma_Tplus` (T+ lays c [K1J] or is the strip tile) with the hypotheses it really uses: strip up to `y0`, `U(0,y0)`, `U(0,y0+1)` (no `SigmaCfg`).  Proof = the proof of `sigma_Tplus`.
* `filler_ab_left`: the LEFT filler for a wedge of size `alpha + beta`: the tile beside the ray is an `alpha`-tile or a `beta`-tile.
-/
import Erdos634.Draft.WGapRL13
import Erdos634.Draft.WGapSig13
import Erdos634.Draft.WGapSide3a

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

section rl14

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem Tplus_core (S : SetupG D e f α β γ L ax ay) {c₀ J y₀ : ℕ} (hJ : J ≤ y₀)
    (hS1 : StripTiles D e f c₀ J y₀)
    (hUy : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((0 : ℕ) : ℝ) (y₀ : ℝ))
    (hU01 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1)) :
    K1J D (e : ℝ) (f : ℝ) 1 (xo f c₀) (y₀ + 1) ∨ UTM D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 ((y₀ : ℝ) + 1) := by
  set x := xo f c₀ with hxdef
  obtain ⟨tE, hE0⟩ := hS1 y₀ hJ le_rfl
  rw [zero_add] at hE0
  obtain ⟨tU, hU⟩ := hUy
  rw [Nat.cast_zero] at hU
  obtain ⟨tU1, hU1⟩ := hU01
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hA := S.hA
  have hs2 := sMir_gt_two he0 hef
  have hsm := sMir_mul he0 hef
  have hhh := hhG_pos he0 hef
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  have hXm : mpG (e : ℝ) f 1 x 0 ((y₀ : ℝ) + 1) = lpG (e : ℝ) f 1 x 0 ((y₀ : ℝ) + 1) := mpG_eq_zero he0 hef x _
  have hP'm : mpG (e : ℝ) f 1 x 1 (y₀ : ℝ) = lpG (e : ℝ) f 1 x (-1) ((y₀ : ℝ) + sMir (e : ℝ) f * 1) := mpG_eq he0 hef x 1 _
  have hAm : mpG (e : ℝ) f 1 x 0 (y₀ : ℝ) = lpG (e : ℝ) f 1 x 0 (y₀ : ℝ) := mpG_eq_zero he0 hef x _
  set X := lpG (e : ℝ) f 1 x 0 ((y₀ : ℝ) + 1) with hXdef
  set P' := lpG (e : ℝ) f 1 x (-1) ((y₀ : ℝ) + sMir (e : ℝ) f * 1) with hP'def
  have hE' : HasV D tE (lpG (e : ℝ) f 1 x 0 (y₀ : ℝ)) P' X := hasV_congr hE0 hAm hP'm hXm
  have dEA : dist (lpG (e : ℝ) f 1 x 0 (y₀ : ℝ)) P' = (f : ℝ) ^ 2 := by
    rw [hP'def]
    refine dist_lpG he0 hef hε hf2.le ?_
    have e1 : (0 : ℝ) - (-1) = 1 := by ring
    have e2 : (y₀ : ℝ) - ((y₀ : ℝ) + sMir (e : ℝ) f * 1) = -sMir (e : ℝ) f := by ring
    rw [e1, e2]
    unfold QfG
    linear_combination (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * sMir (e : ℝ) f) * hsm
  have aE : (D.tile tE).localAngle X = γ := ((hE'.rot.rot.anglesG S.tile S.hM).2.2) dEA
  have aU : (D.tile tU).localAngle X = γ := (U_anglesG S hε hU).2.2
  have aU1 : (D.tile tU1).localAngle X = α := (U_anglesG S hε hU1).1
  have hU1y : ∀ i, ((D.tile tU).pts i) 1 ≤ ((y₀ : ℝ) + 1) * hhG (e : ℝ) (f : ℝ) :=
    hU.all (P := fun p => p 1 ≤ ((y₀ : ℝ) + 1) * hhG (e : ℝ) (f : ℝ))
      (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef le_rfl)
  have P'high : ((y₀ : ℝ) + 1) * hhG (e : ℝ) (f : ℝ) < P' 1 := lpG_y_gt he0 hef (by linarith)
  have nUE : tU ≠ tE := by
    obtain ⟨i2, hi2⟩ := hE'.idx₂
    exact ne_of_F (fun p : Plane => p 1) hU1y (i := i2) (by rw [hi2]; exact P'high)
  have hXint : X ∈ interior D.target.carrier :=
    interior_of_two_tiles D.toDissection hU.mem₃ nUE.symm aE aU
      (by have := Erdos634.Draft.WGapAngles.two_gamma_gt_pi hA; linarith)
  have hB : lpG (e : ℝ) f 1 x 0 ((y₀ : ℝ) + 1 + 1) ∈ D.target.carrier := hU1.mem₃
  have hint := openSeg_interior D.toDissection hXint hB
  -- the clamp from below: the `b`-edge of `E_{y₀}` on `ℓ`
  have hEle : ∀ i, FXG (e : ℝ) (f : ℝ) 1 ((D.tile tE).pts i) ≤ lvG (e : ℝ) (f : ℝ) 1 x 0 := by
    refine hE'.all (P := fun p => FXG (e : ℝ) (f : ℝ) 1 p ≤ lvG (e : ℝ) (f : ℝ) 1 x 0)
      (le_of_eq (FXG_lp hε _ _)) ?_ (le_of_eq (FXG_lp hε _ _))
    dsimp only
    rw [hP'def, FXG_lp hε]
    exact lvG_le he0 hef (by norm_num)
  obtain ⟨k0, m0, j0, hkm0, hkj0, hmj0, hk0, hm0, hj0⟩ := hE0
  have hcl := clamp_tile S hε (c := 0) (η := (y₀ : ℝ)) (x := x) hkj0 (by rw [hk0, hAm]) (by rw [hj0, hXm]) hEle
  have hcn := col_next S hε hU1 hint hcl
  rcases hcn with ⟨iT, k, m, t, hkm, hk, hm, ht, hlen, hle⟩ | ⟨iT, k, m, hkm, hk, hm, hle⟩
  · left
    refine ⟨iT, k, m, t, hkm, ?_, ?_, ht, hlen, hle⟩
    · rw [hk, Nat.cast_add, Nat.cast_one]
    · rw [hm, Nat.cast_add, Nat.cast_one]
  · right
    have hnγ : (D.tile iT).localAngle (lpG (e : ℝ) f 1 x ((0 : ℕ) : ℝ) ((y₀ : ℝ) + 1)) ≠ γ := by
      intro hγ0
      rw [Nat.cast_zero] at hγ0
      have nTU : iT ≠ tU := by
        obtain ⟨i2, hi2⟩ := hU.idx₂
        exact ne_of_F (FXG (e : ℝ) (f : ℝ) 1) hle (i := i2)
          (by rw [hi2, FXG_lp hε]; exact lvG_lt he0 hef (by norm_num))
      have nTE : iT ≠ tE := by
        refine HasV.ne_of_vertex hE' (X := (D.tile iT).pts m) rfl ?_ ?_ ?_ |>.symm.symm
        all_goals
          intro h
          rw [hm] at h
          have := lpG_eta_eq he0 hef h
          linarith
      obtain ⟨i3, hi3⟩ := hE'.idx₃
      have fig := fig_int S hXint hi3
      unfold FigI at fig
      have hγ3 := forall_mem3
        (P := fun i => (D.tile i).localAngle X = γ) aE aU hγ0
      have c1 := card_le_angle _ γ hγ3
      rw [card3 nUE.symm nTE.symm nTU.symm] at c1
      have hα1 := forall_mem2 (P := fun i => (D.tile i).localAngle X = α) aU1 aU1
      have c2 := card_le_angle _ α hα1
      have : ({tU1, tU1} : Finset (Fin N)).card = 1 := by simp
      rw [this] at c2
      omega
    have hmir := mirror_of_b_n S hε (n := 0) (η := (y₀ : ℝ) + 1) hkm (by rw [Nat.cast_zero]; exact hk)
      (by rw [Nat.cast_zero]; exact hm) (by rw [Nat.cast_zero]; exact hle) hnγ
    rw [shiftX_zero] at hmir
    exact (mirrorAt_iff_UTM_gen S _ _).1 hmir

/-- **LEFT filler, wedge of size `alpha + beta`**: the tile beside the ray (on its left) is an `alpha`-tile (`|PW| = a`, `{|XP|,|XW|} = {b,c}`) or a `beta`-tile (`|PW| = b`, `{|XP|,|XW|} = {a,c}`) -/
theorem filler_ab_left (S : SetupG D e f α β γ L ax ay) {X Y Z P' : Plane} {t₀ : Fin N} (hXY : X ≠ Y)
    (hV : HasV D t₀ X Y Z) (hZ : cross (Y - X) (Z - X) < 0)
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    (hint : openSegment ℝ X Y ⊆ interior D.target.carrier)
    (hclamp : ∀ ed ∈ D.lineChain (crossL (X - Y)) (cross (X - Y) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y)
    {Ω : ℝ} (hΩ : ∑ i, (D.tile i).localAngle X = Ω) (K : Finset (Fin N))
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - (α + β))
    (hKray : ∀ k ∈ K, k ≠ t₀ → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap X Y s) :
    ∃ τ : Fin N, τ ∉ K ∧ ∃ P W : Plane, HasV D τ X P W ∧ (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap X Y s) ∧
      0 < cross (Y - X) (W - X) ∧
      (((D.tile τ).localAngle X = α ∧ dist P W = (e : ℝ) * f ∧
        ((dist X P = (f : ℝ) ^ 2 ∧ dist X W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
          (dist X P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist X W = (f : ℝ) ^ 2))) ∨
       ((D.tile τ).localAngle X = β ∧ dist P W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
        ((dist X P = (e : ℝ) * f ∧ dist X W = (f : ℝ) ^ 2) ∨
          (dist X P = (f : ℝ) ^ 2 ∧ dist X W = (e : ℝ) * f)))) := by
  obtain ⟨τ, k, m, t, hτ, hkm, hk, ht, hm, hle⟩ := ray_filler_left D hXY hV hZ hP' hXP hint hclamp
  obtain ⟨n, hnk, hnm⟩ := fin3_third k m hkm
  have hkn : k ≠ n := hnk.symm
  have hmn : m ≠ n := hnm.symm
  have hτK : τ ∉ K := fun h => hKray τ h hτ m t ht hm
  have hne := tri_cross_ne (D.tile τ) hkm hkn hmn
  have hmX : (D.tile τ).pts m - (D.tile τ).pts k = t • (Y - X) := by
    rw [hm, hk, AffineMap.lineMap_apply]; simp
  have hneg : 0 < cross (Y - X) ((D.tile τ).pts n - X) := by
    rcases lt_or_eq_of_le (hle n) with h | h
    · exact h
    · exfalso; apply hne
      rw [hmX, cross_smul_left', hk, ← h]; ring
  have hvc := vertex_angle_cases S τ hkm hkn hmn
  have hA := S.hA
  have hαβπ : α + β < Real.pi := by
    have hr := hA.hrel
    have hg := hA.hγdef
    have h1 := hA.hα
    have h2 := hA.hβ
    linarith
  have hcnt := wedge_alpha_beta S hΩ hK hαβπ
  have hmemτ : τ ∈ Finset.univ \ K := by simp [hτK]
  rcases hvc with h | h | h
  · obtain ⟨hopp, hsd⟩ := sides_of_alpha S τ hkm hkn hmn h
    rw [hk] at h hsd
    refine ⟨τ, hτK, (D.tile τ).pts m, (D.tile τ).pts n, ⟨k, m, n, hkm, hkn, hmn, hk, rfl, rfl⟩,
      ⟨t, ht, hm⟩, hneg, Or.inl ⟨h, hopp, ?_⟩⟩
    rcases hsd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · obtain ⟨hopp, hsd⟩ := sides_of_beta S τ hkm hkn hmn h
    rw [hk] at h hsd
    exact ⟨τ, hτK, (D.tile τ).pts m, (D.tile τ).pts n, ⟨k, m, n, hkm, hkn, hmn, hk, rfl, rfl⟩,
      ⟨t, ht, hm⟩, hneg, Or.inr ⟨h, hopp, hsd⟩⟩
  · exfalso
    have h0 := hcnt.2.2
    unfold cnt at h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    exact h0 hmemτ (by rw [← hk]; exact h)

end rl14

#print axioms Tplus_core
#print axioms filler_ab_left

end Erdos634.Draft.WGapStmt
