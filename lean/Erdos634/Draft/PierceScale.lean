/-
Draft/PierceScale.lean -- the pierce lemma at EVERY scale.

`R1Frame` / `R1Pierce` prove the pierced corner for the `m = 1` target, where no dissection exists.  The scale
enters there only through the lengths of the target (legs `f³`, base `e (3f² − e²)`), which are used to compute where
the mismatch ray leaves the target.  Here that computation is replaced by two scale-free facts: the end `V` of
`T₂`'s `c`-edge is a vertex of a tile, hence a point of the target, so the open stretch `(A, V)` of the ray is
interior to the target; and `V` is interior because a tile edge passes through it.

Input: a congruent dissection of a triangle with a corner `3α` at vertex `k` (the apex), by the tile
`(a, b, c) = (ef, f² − e², f²)`, such that the apex flanks along the two sides are `c`-edges
(`ApexPlacement.LegFlanksC`: both sides end at the apex with a `c`-edge).  No hypothesis on the lengths of the
target.  Output (`thm_pierce_scale`): the three apex tiles `T₁`, `T₂`, `T₃`; `T₁`'s `b`-edge and `T₂`'s `c`-edge lie on
one ray from the apex; at the end `X` of the `b`-edge (distance `b`) the figure is one `α`, one `β`, one `γ` and
one straight angle (`T₁` presents `γ`, `T₂` is straight); the end `V` of the `c`-edge (distance `c = f²`) is interior to
the target, `T₂` presents `β` there, a tile edge lying on the ray, of a tile on `T₁`'s side, has `V` in its relative
interior, exactly one tile is straight at `V`, and the remaining corners at `V` sum to `π − β`.  No sorry, no native_decide.
-/
import Erdos634.Draft.R1Pierce

namespace Erdos634.Draft.PierceScale

open Erdos634.Geometry Erdos634.Placement Erdos634.TilePlacement Erdos634.WallEndpoints
  Erdos634.BridgeC Erdos634.BaseBetaWalkArith
open Erdos634.SideWall Erdos634.Draft.ApexPlacement Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.ApexLegWord Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.R1Frame
open Erdos634.CertCoord Erdos634.Draft.NearBaseVertex

variable {N : ℕ}

/-- **The apex frame, scale-free.**  `A` the apex (target vertex `k`), `uR` the unit direction of the mismatch
ray, `V = A + c·uR` the end of `T₂`'s `c`-edge, `P` the third vertex of `T₂`, `Rf` the third vertex of `T₁`, `h` a
normal functional of the ray with `T₂` on the side `h < h A` and `T₁` on the side `h > h A`. -/
structure SFrame (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) (k : Fin 3) where
  A : Plane
  V : Plane
  P : Plane
  Rf : Plane
  uR : Plane
  h : Plane →ₗ[ℝ] ℝ
  hA : A = D.target.pts k
  hco : Nat.Coprime e f
  he : 1 ≤ e
  hef : e < f
  hM : ModelDataE D e f α β γ
  hAng : MarchSlots.AngleData α β γ
  huR : ‖uR‖ = 1
  hV : V = A + ((f : ℝ) ^ 2) • uR
  hAP : dist A P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2
  hARf : dist A Rf = (f : ℝ) ^ 2
  hh0 : h ≠ 0
  hhuR : h uR = 0
  hhP : h P < h A
  hhRf : h A < h Rf
  hrint : ∀ t : ℝ, 0 < t → t < (f : ℝ) ^ 2 → A + t • uR ∈ interior D.target.carrier
  hT1 : Present D {A, A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • uR, Rf}
  hT2 : Present D {A, V, P}

/-- **The frame from a real dissection at any scale**, given that the apex flanks along the sides are `c`. -/
theorem exists_sframe (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ) (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α)
    (hlegc : LegFlanksC D k ((f : ℝ) ^ 2)) :
    Nonempty (SFrame D e f α β γ k) := by
  classical
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hlt : (e : ℝ) < f := by exact_mod_cast hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  set a : ℝ := (e : ℝ) * f with ha
  set b : ℝ := (f : ℝ) ^ 2 - (e : ℝ) ^ 2 with hb
  set c : ℝ := (f : ℝ) ^ 2 with hc
  have ha0 : a ≠ 0 := by rw [ha]; exact mul_ne_zero he0.ne' hf0.ne'
  have hb0 : 0 < b := by rw [hb]; nlinarith
  have hc0 : 0 < c := by positivity
  have hbc : b ≠ c := by rw [hb, hc]; intro h; nlinarith
  obtain ⟨L, R, G1, G3, hLR, cfg⟩ := apex_config D hM.hs0 hM.hs1 hM.hs2 ha0 hb0 hc0 hbc hAng
    hM.hα' hM.hβ' hM.hγ' k hcorner hlegc
  set A := D.target.pts k with hAdef
  have hC : ApexCone D.target A L R := cone_LR hLR
  have hRA : R ≠ A := by
    rcases hLR with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact (Erdos634.TilePlacement.pts_ne D.target ((by decide : ∀ x : Fin 3, x ≠ x + 2) k)).symm
    · exact (Erdos634.TilePlacement.pts_ne D.target ((by decide : ∀ x : Fin 3, x ≠ x + 1) k)).symm
  have hRn : 0 < ‖R - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hRA)
  have hdistA : ∀ G : Plane, dist A (A + G) = ‖G‖ := fun G => by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
  obtain ⟨s1, t1, hs1, ht1, hG1⟩ := cfg.hG1cone
  -- the normal functional of the ray
  have hside := cfg.hside
  have hcr : cross G1 (R - A) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hside; exact lt_irrefl _ hside
  set h : Plane →ₗ[ℝ] ℝ := (cross G1 (R - A)) • Erdos634.Geometry.crossL G1 with hhdef
  have happ : ∀ v, h v = cross G1 (R - A) * cross G1 v := fun v => by
    rw [hhdef, LinearMap.smul_apply, Erdos634.Geometry.crossL_apply, smul_eq_mul]
  have hG3neg : h G3 < 0 := by rw [happ, mul_comm]; exact hside
  have hRpos : 0 < h (R - A) := by
    rw [happ]; exact mul_self_pos.mpr hcr
  -- `V` is a point of the target, so the cone coefficients of the ray are small
  have hVtarget : A + (c / b) • G1 ∈ D.target.carrier := by
    obtain ⟨i, hi⟩ := cfg.hT2
    have hmem : A + (c / b) • G1 ∈ Set.range (D.tile i).pts := by
      rw [hi]; exact Or.inr (Or.inr rfl)
    obtain ⟨j, hj⟩ := hmem
    rw [← hj]
    exact Erdos634.Geometry.tile_subset_target D.toDissection i
      (subset_convexHull ℝ _ ⟨j, rfl⟩)
  have hcoef : c / b * (s1 + t1) ≤ 1 := by
    have hpt : A + (c / b) • G1 = A + ((c / b * s1) • (L - A) + (c / b * t1) • (R - A)) := by
      rw [hG1, smul_add, smul_smul, smul_smul]
    rw [hpt] at hVtarget
    have hco' := ((mem_carrier_iff _ _).mp hVtarget) k
    rw [coord_LR hLR] at hco'
    linarith
  refine ⟨{
    A := A
    V := A + ((f : ℝ) ^ 2) • ((1 / b) • G1)
    P := A + G3
    Rf := A + (c / ‖R - A‖) • (R - A)
    uR := (1 / b) • G1
    h := h
    hA := rfl
    hco := hco
    he := he
    hef := hef
    hM := hM
    hAng := hAng
    huR := ?_
    hV := rfl
    hAP := ?_
    hARf := ?_
    hh0 := ?_
    hhuR := ?_
    hhP := ?_
    hhRf := ?_
    hrint := ?_
    hT1 := ?_
    hT2 := ?_ }⟩
  · rw [norm_smul, cfg.hG1, Real.norm_of_nonneg (by positivity), one_div_mul_cancel hb0.ne']
  · rw [hdistA, cfg.hG3]
  · rw [hdistA, norm_smul, Real.norm_of_nonneg (div_pos hc0 hRn).le, div_mul_cancel₀ _ hRn.ne']
  · intro h0
    have := congrArg (fun φ : Plane →ₗ[ℝ] ℝ => φ G3) h0
    simp only [LinearMap.zero_apply] at this
    rw [this] at hG3neg; exact lt_irrefl _ hG3neg
  · rw [happ, cross_smul_right, cross_self', mul_zero, mul_zero]
  · rw [map_add]; linarith
  · rw [map_add, map_smul, smul_eq_mul]
    have : 0 < c / ‖R - A‖ * h (R - A) := mul_pos (div_pos hc0 hRn) hRpos
    linarith
  · -- the open stretch of the ray up to `V` is interior to the target
    intro τ hτ hτ2
    have hpt : A + τ • ((1 / b) • G1) = A + (τ / b) • (s1 • (L - A) + t1 • (R - A)) := by
      rw [hG1, smul_smul]; ring_nf
    rw [hpt]
    apply hC.inter s1 t1 (τ / b) hs1 ht1 (div_pos hτ hb0)
    have hst : 0 < s1 + t1 := by linarith
    have h1 : τ / b < c / b := div_lt_div_of_pos_right hτ2 hb0
    calc τ / b * (s1 + t1) < c / b * (s1 + t1) := mul_lt_mul_of_pos_right h1 hst
      _ ≤ 1 := hcoef
  · -- `T₁`
    obtain ⟨i, hi⟩ := cfg.hT1
    refine ⟨i, ?_⟩
    rw [hi, smul_smul, ← hb, mul_one_div_cancel hb0.ne', one_smul]
  · -- `T₂`
    obtain ⟨i, hi⟩ := cfg.hT2
    refine ⟨i, ?_⟩
    rw [hi, smul_smul, show (f : ℝ) ^ 2 * (1 / b) = c / b by rw [hc]; ring]
    exact congrArg (insert A) (Set.pair_comm _ _)

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {k : Fin 3}

/-- `T₂`, indexed: an edge `m` from `A` to `V` (either order) and the third vertex `P`. -/
theorem T2_indexed (F : SFrame D e f α β γ k) :
    ∃ (i2 : Fin N) (m : Fin 3),
      Set.range (D.tile i2).pts = {F.A, F.V, F.P} ∧
      (((D.tile i2).pts m = F.A ∧ (D.tile i2).pts (m + 1) = F.V) ∨
        ((D.tile i2).pts m = F.V ∧ (D.tile i2).pts (m + 1) = F.A)) ∧
      (D.tile i2).pts (m + 2) = F.P := by
  obtain ⟨i2, hi2⟩ := F.hT2
  obtain ⟨kA, hkA⟩ := MarchInduction.mem_range_of_eq hi2 (Set.mem_insert _ _)
  have hfin1 : kA + 2 + 1 = kA := by fin_cases kA <;> rfl
  have hfin2 : kA + 2 + 2 = kA + 1 := by fin_cases kA <;> rfl
  refine ⟨i2, ?_⟩
  rcases MarchInduction.vertex_data_of_range hi2 hkA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨kA, hi2, Or.inl ⟨hkA, h1⟩, h2⟩
  · exact ⟨kA + 2, hi2, Or.inr ⟨h2, by rw [hfin1, hkA]⟩, by rw [hfin2, h1]⟩

/-- **`thm:pierce` (iii), every scale: `V` is pierced** — a tile edge on the ray, of a tile on `T₁`'s side, has
`V` in its relative interior.  (Otherwise the far edges on `[A, V]` form a word of value `c` containing `T₁`'s `b`,
which `Inflation.c_side_no_b` forbids.) -/
theorem V_pierced (F : SFrame D e f α β γ k) :
    TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A)) F.V := by
  classical
  obtain ⟨i2, m2, -, hm01, -⟩ := T2_indexed F
  have hedgeAV : (D.tile i2).edge m2 = segment ℝ F.A F.V := by
    rw [Tri.edge]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    exact segment_symm ℝ _ _
  by_contra hns
  have hef := F.hef
  have he := F.he
  have hu1 : ‖F.uR‖ = 1 := F.huR
  have hu0 : F.uR ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hgd₂ : ∀ y, (-F.h) y = -(F.h F.A) ↔ F.h y = F.h F.A := TraceCovering.neg_iff
  have hh' : (-F.h : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => F.hh0 (neg_eq_zero.mp h)
  have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have heR : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hb_pos : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hc_pos : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hA0 : F.A + (0 : ℝ) • F.uR = F.A := by rw [zero_smul, add_zero]
  have ht0 : (0 : ℝ) ≤ (f : ℝ) ^ 2 := hc_pos.le
  -- (i) interior
  have hint : ∀ x ∈ Set.Ioo 0 ((f : ℝ) ^ 2), F.A + x • F.uR ∈ interior D.target.carrier :=
    fun x hx => F.hrint x hx.1 hx.2
  -- (ii) the wall: `T₂`'s `c`-edge `[A, V]`
  have hwall : ∀ x ∈ Set.Ioo 0 ((f : ℝ) ^ 2), ∀ i, F.A + x • F.uR ∉ interior (D.tile i).carrier := by
    intro x hx i
    have hmem : F.A + x • F.uR ∈ (D.tile i2).edge m2 := by
      rw [hedgeAV, F.hV]
      have hs := TraceCovering.segment_param (X := F.A) (u := F.uR) 0 ((f : ℝ) ^ 2)
      rw [hA0, min_eq_left ht0, max_eq_right ht0] at hs
      rw [hs]
      exact ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
    exact D.toDissection.edge_point_not_interior hmem i
  -- (iii) no far edge passes through the apex
  have hback : ∀ s : ℝ, s < 0 → F.A + s • F.uR ∉ D.target.carrier := by
    intro s hs
    have hv : ((f : ℝ) ^ 2 / 2) • F.uR ≠ 0 := smul_ne_zero (by positivity) hu0
    have hin : D.target.pts k + ((f : ℝ) ^ 2 / 2) • F.uR ∈ D.target.carrier := by
      rw [← F.hA]; exact interior_subset (hint ((f : ℝ) ^ 2 / 2) ⟨by positivity, by linarith⟩)
    have := TraceCovering.vertex_ray_out D.target k hv hin (t := s / ((f : ℝ) ^ 2 / 2))
      (div_neg_of_neg_of_pos hs (by positivity))
    rwa [← F.hA, smul_smul, div_mul_cancel₀ _ (by positivity)] at this
  have hstart := TraceCovering.not_straddled_of_outside_before (D := D.toDissection) (g := -F.h)
    (d := -(F.h F.A)) hgd₂ F.hh0 rfl F.hhuR hu0 (x₀ := 0) hback
  have hns' : ¬ TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A))
      (F.A + ((f : ℝ) ^ 2) • F.uR) := by rw [← F.hV]; exact hns
  -- TRACE COVERING, far side, on `[A, V]`
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hh' hgd₂ F.hh0 rfl F.hhuR hu1 ht0
    hint hwall hstart hns'
  -- `T₁`'s `b`-edge is one of them
  obtain ⟨i1, hi1⟩ := F.hT1
  set Bp := F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR with hBp
  obtain ⟨kA1, hkA1⟩ := MarchInduction.mem_range_of_eq hi1 (Set.mem_insert _ _)
  have hfin1 : kA1 + 2 + 1 = kA1 := by fin_cases kA1 <;> rfl
  have hfin2 : kA1 + 2 + 2 = kA1 + 1 := by fin_cases kA1 <;> rfl
  obtain ⟨m, hm01', hm2⟩ : ∃ m : Fin 3,
      (((D.tile i1).pts m = F.A ∧ (D.tile i1).pts (m + 1) = Bp) ∨
        ((D.tile i1).pts m = Bp ∧ (D.tile i1).pts (m + 1) = F.A)) ∧
      (D.tile i1).pts (m + 2) = F.Rf := by
    rcases MarchInduction.vertex_data_of_range hi1 hkA1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨kA1, Or.inl ⟨hkA1, h1⟩, h2⟩
    · exact ⟨kA1 + 2, Or.inr ⟨h2, by rw [hfin1, hkA1]⟩, by rw [hfin2, h1]⟩
  have hhB : F.h Bp = F.h F.A := TraceCovering.f_param rfl F.hhuR _
  have hhRf : F.h F.A < F.h F.Rf := F.hhRf
  have he1 : (i1, m) ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A)) := by
    rw [Dissection.mem_lineChain]
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    refine ⟨?_, ?_, fun i => ?_⟩
    · rcases hm01' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhB]
    · rcases hm01' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhB]
    · rcases h3 i m with rfl | rfl | rfl
      · rcases hm01' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhB]
      · rcases hm01' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhB]
      · rw [hm2]; simp only [LinearMap.neg_apply, neg_le_neg_iff]; exact hhRf.le
  have hedge1 : (D.tile i1).edge m = segment ℝ F.A Bp := by
    rw [Tri.edge]
    rcases hm01' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    exact segment_symm ℝ _ _
  have hdist1 : dist ((D.tile i1).pts m) ((D.tile i1).pts (m + 1))
      = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have hdb : dist F.A Bp = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [hBp, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one,
        Real.norm_of_nonneg hb_pos.le]
    rcases hm01' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hdb
    · rw [dist_comm]; exact hdb
  have hbt : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≤ (f : ℝ) ^ 2 := by nlinarith
  have hBseg : Bp ∈ segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + ((f : ℝ) ^ 2) • F.uR) := by
    rw [TraceCovering.segment_param, min_eq_left ht0, max_eq_right ht0]
    exact ⟨_, ⟨hb_pos.le, hbt⟩, rfl⟩
  have hAseg : F.A ∈ segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + ((f : ℝ) ^ 2) • F.uR) := by
    convert left_mem_segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + ((f : ℝ) ^ 2) • F.uR) using 1
    exact hA0.symm
  set sF := (D.toDissection.lineChain (-F.h) (-(F.h F.A))).filter
    (fun e => (D.toDissection.tile e.1).edge e.2 ⊆
      segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + ((f : ℝ) ^ 2) • F.uR)) with hsF
  have hmemF : (i1, m) ∈ sF := by
    refine Finset.mem_filter.mpr ⟨he1, ?_⟩
    show (D.tile i1).edge m ⊆ _
    rw [hedge1]
    exact (convex_segment _ _).segment_subset hAseg hBseg
  rw [← Finset.add_sum_erase sF _ hmemF] at hsum
  obtain ⟨P', Q', R', hPQR, -⟩ := sum_three_values (sF.erase (i1, m))
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = 1 * f ^ 2 := by
    have : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
        = ((1 * f ^ 2 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hee]
      simp only at hsum hdist1
      rw [hdist1] at hsum
      linarith
    exact_mod_cast this
  have := Inflation.c_side_no_b e f (f ^ 2 - e ^ 2) 1 P' (Q' + 1) R' (by omega) (by omega) F.hco
    (by omega) (by omega) hnat
  omega

/-- **The piercer.**  Some tile has `V` in the relative interior of an edge lying on the ray, with the tile on
the far side (`h ≥ h A`); it presents `π` at `V`. -/
theorem piercer (F : SFrame D e f α β γ k) :
    ∃ ε ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A)),
      F.V ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) ∧
      (D.tile ε.1).localAngle F.V = Real.pi ∧
      ∀ y ∈ (D.tile ε.1).carrier, F.h F.A ≤ F.h y := by
  obtain ⟨ε, hε, hV⟩ := V_pierced F
  refine ⟨ε, hε, hV, ?_, ?_⟩
  · have e1 : ε.2 + 2 + 1 = ε.2 := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) _
    have e2 : ε.2 + 2 + 2 = ε.2 + 1 := (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) _
    apply Erdos634.RouteOne.openSegment_localAngle_pi (D.tile ε.1) (ε.2 + 2)
    rw [e1, e2]; exact hV
  · intro y hy
    have := (D.tile ε.1).carrier_subset_halfplane (-F.h) (-(F.h F.A))
      (Dissection.mem_lineChain.mp hε).2.2 y hy
    simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
    exact this

/-- **`V` is interior to the target** (a tile edge passes through it, and the stretch before it is interior). -/
theorem V_interior (F : SFrame D e f α β γ k) : F.V ∈ interior D.target.carrier := by
  have hu0 := TraceCovering.ne_zero_of_norm F.huR
  have hgd₂ : ∀ y, (-F.h) y = -(F.h F.A) ↔ F.h y = F.h F.A := TraceCovering.neg_iff
  have hc_pos : (0 : ℝ) < (f : ℝ) ^ 2 := by
    have : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by have := F.hef; omega)
    positivity
  have hp := V_pierced F
  rw [F.hV, TraceCovering.str_iff hgd₂ F.hh0 rfl F.hhuR hu0] at hp
  obtain ⟨ε, hε, hlo, hhi⟩ := hp
  -- the far end `W` of the piercing edge is a point of the target beyond `V`
  have hW : F.A + (TraceCovering.hi D.toDissection F.A F.uR ε) • F.uR ∈ D.target.carrier := by
    have hm : F.A + (TraceCovering.hi D.toDissection F.A F.uR ε) • F.uR ∈ (D.tile ε.1).edge ε.2 :=
      (TraceCovering.mem_edge_iff hgd₂ F.hh0 rfl F.hhuR hu0 hε _).mpr ⟨by linarith, le_rfl⟩
    exact Erdos634.Geometry.tile_subset_target D.toDissection ε.1
      ((D.tile ε.1).edge_subset_carrier ε.2 hm)
  have hI := F.hrint ((f : ℝ) ^ 2 / 2) (by positivity) (by linarith)
  have hne : (f : ℝ) ^ 2 / 2 ≠ TraceCovering.hi D.toDissection F.A F.uR ε := by
    intro h; linarith
  have hVseg : F.A + ((f : ℝ) ^ 2) • F.uR ∈ openSegment ℝ (F.A + ((f : ℝ) ^ 2 / 2) • F.uR)
      (F.A + (TraceCovering.hi D.toDissection F.A F.uR ε) • F.uR) := by
    rw [TraceCovering.openSegment_param hne, min_eq_left (by linarith), max_eq_right (by linarith)]
    exact ⟨_, ⟨by linarith, hhi⟩, rfl⟩
  rw [F.hV]
  exact D.target.convex.openSegment_interior_closure_subset_interior hI (subset_closure hW) hVseg

/-- `T₂` presents `β` at `V` (`c` joins its `α` at `A` and its `β` at `V`; `|AP| = b`). -/
theorem T2_beta_at_V (F : SFrame D e f α β γ k) {i2 : Fin N}
    (h2 : Set.range (D.tile i2).pts = {F.A, F.V, F.P}) : (D.tile i2).localAngle F.V = β := by
  obtain ⟨hab, hac, hbc⟩ := sides_distinct1 F.hco F.he F.hef
  have h2' : Set.range (D.tile i2).pts = {F.V, F.A, F.P} := by
    rw [h2]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  exact (localAngle_of_rangeE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ'
    F.hM.hγ' h2').2.1 F.hAP

/-- **The census at `V`**: with the piercer (`π`) and `T₂` (`β`), exactly one tile is straight at `V`, none is
`2π`, and the other corners fill `π − β`. -/
theorem fill_at_V (F : SFrame D e f α β γ k) {k t : Fin N}
    (hk : (D.tile k).localAngle F.V = Real.pi) (ht : (D.tile t).localAngle F.V = β) :
    ({i | (D.tile i).localAngle F.V = Real.pi} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle F.V = 2 * Real.pi} : Finset (Fin N)).card = 0 ∧
    (({i | (D.tile i).localAngle F.V = α} : Finset (Fin N)).card : ℝ) * α
      + ((({i | (D.tile i).localAngle F.V = β} : Finset (Fin N)).card : ℝ) - 1) * β
      + (({i | (D.tile i).localAngle F.V = γ} : Finset (Fin N)).card : ℝ) * γ
      = Real.pi - β := by
  have hA := F.hAng
  exact ThickEFminus1Steps.corners_fill_pi_sub_beta D.toDissection hA.hγdef hA.hrel hA.hα hA.hβ
    hA.hirr (V_interior F)
    (fun i => Erdos634.Geometry.congruentDissection_localAngle_mem_all D α β γ F.hM.hα' F.hM.hβ'
      F.hM.hγ' F.V i) k t hk ht

/-- **The figures beyond the pierced corner**: the corners at `V` other than the piercer are three `α` and two
`β` (one of them `T₂`'s), or one `α`, one `β` (`T₂`'s) and one `γ`. -/
theorem fill_at_V_cases (F : SFrame D e f α β γ k) {k t : Fin N}
    (hk : (D.tile k).localAngle F.V = Real.pi) (ht : (D.tile t).localAngle F.V = β) :
    (({i | (D.tile i).localAngle F.V = α} : Finset (Fin N)).card = 3 ∧
      ({i | (D.tile i).localAngle F.V = β} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle F.V = γ} : Finset (Fin N)).card = 0) ∨
    (({i | (D.tile i).localAngle F.V = α} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle F.V = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle F.V = γ} : Finset (Fin N)).card = 1) := by
  obtain ⟨-, -, hfill⟩ := fill_at_V F hk ht
  have hA := F.hAng
  have hγd := hA.hγdef
  have hrel := hA.hrel
  have hirr := hA.hirr
  generalize ({i | (D.tile i).localAngle F.V = α} : Finset (Fin N)).card = nα at hfill ⊢
  generalize ({i | (D.tile i).localAngle F.V = β} : Finset (Fin N)).card = nβ at hfill ⊢
  generalize ({i | (D.tile i).localAngle F.V = γ} : Finset (Fin N)).card = nγ at hfill ⊢
  have e3 : (nγ : ℝ) * γ = (nγ : ℝ) * (2 * α + β) := congrArg (fun x : ℝ => (nγ : ℝ) * x) hγd
  have h : (nα : ℝ) * α + (nβ : ℝ) * β + (nγ : ℝ) * (2 * α + β)
      = ((3 : ℤ) : ℝ) * α + ((2 : ℤ) : ℝ) * β := by
    push_cast
    linarith
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr nα nβ nγ 3 2 h
  omega

/-- **The T-junction** (`thm:pierce` (i)): at `X = A + b·uR`, the end of `T₁`'s `b`-edge, the point is interior to
the target, `T₁` presents `γ`, `T₂` is straight, and the figure is one each of `α`, `β`, `γ`, `π`. -/
theorem junction_figure (F : SFrame D e f α β γ k) :
    F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR ∈ interior D.target.carrier ∧
    (∃ i1 : Fin N, Set.range (D.tile i1).pts = {F.A, F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR, F.Rf} ∧
      (D.tile i1).localAngle (F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) = γ) ∧
    (∃ i2 : Fin N, Set.range (D.tile i2).pts = {F.A, F.V, F.P} ∧
      (D.tile i2).localAngle (F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) = Real.pi) ∧
    ({i | (D.tile i).localAngle (F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) = γ} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) = Real.pi} : Finset (Fin N)).card = 1 := by
  classical
  have hef := F.hef
  have he := F.he
  have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hb_pos : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hbc : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (f : ℝ) ^ 2 := by nlinarith
  have hc_pos : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  set X := F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR with hX
  have hXint : X ∈ interior D.target.carrier := F.hrint _ hb_pos hbc
  obtain ⟨hab, hac, hbc'⟩ := sides_distinct1 F.hco F.he F.hef
  -- `T₁` presents `γ` at `X`
  obtain ⟨i1, hi1⟩ := F.hT1
  have hi1' : Set.range (D.tile i1).pts = {X, F.A, F.Rf} := by
    rw [hi1]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hγ1 : (D.tile i1).localAngle X = γ :=
    (localAngle_of_rangeE D hab hac hbc' F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ'
      hi1').2.2 F.hARf
  -- `T₂` is straight at `X`
  obtain ⟨i2, m2, hi2, hm01, -⟩ := T2_indexed F
  have hA0 : F.A + (0 : ℝ) • F.uR = F.A := by rw [zero_smul, add_zero]
  have hXseg : X ∈ openSegment ℝ F.A F.V := by
    have h := TraceCovering.openSegment_param (X := F.A) (u := F.uR) (s := 0) (t := (f : ℝ) ^ 2)
      hc_pos.ne
    rw [hA0, min_eq_left hc_pos.le, max_eq_right hc_pos.le] at h
    rw [F.hV, h]
    exact ⟨_, ⟨hb_pos, hbc⟩, rfl⟩
  have hπ2 : (D.tile i2).localAngle X = Real.pi := by
    have e1 : m2 + 2 + 1 = m2 := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) _
    have e2 : m2 + 2 + 2 = m2 + 1 := (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) _
    apply Erdos634.RouteOne.openSegment_localAngle_pi (D.tile i2) (m2 + 2)
    rw [e1, e2]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hXseg
    · rw [openSegment_symm]; exact hXseg
  -- the figure
  have hA := F.hAng
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hα2π, -, hαpos⟩ := angle_facts hA
  have hπ := Real.pi_pos
  have hβpos := hA.hβ
  have hrel := hA.hrel
  have hγd := hA.hγdef
  have hfig := Erdos634.VertexFigureReal.one_gamma_real D.toDissection hαβ hαγ hαπ hα2π hα0 hβγ hβπ
    (by intro h; linarith) hβ0 hγπ (by intro h; linarith) hγ0 (by intro h; linarith) hπ.ne'
    (by positivity) hγd hrel hA.hirr hXint
    (fun i => Erdos634.Geometry.congruentDissection_localAngle_mem_all D α β γ F.hM.hα' F.hM.hβ'
      F.hM.hγ' X i) i1 hγ1 i2 hπ2
  exact ⟨hXint, ⟨i1, hi1, hγ1⟩, ⟨i2, hi2, hπ2⟩, hfig.1, hfig.2.1, hfig.2.2.1, hfig.2.2.2.1⟩

/-- **`thm:pierce`, every scale.**  A congruent dissection, by the tile `(ef, f² − e², f²)`, of a triangle with a
corner `3α` at its vertex `k` whose two flanking sides end there with `c`-edges.  Then there are points `X`, `V` on
one ray from the apex `A`, at distances `b` and `c`, such that:
(i) at `X` the figure is one each of `α`, `β`, `γ`, `π`;
(iii) `V` is interior to the target, a tile presents `β` at `V`, a tile edge has `V` in its relative interior, and
the corners at `V` other than that tile are `3α + 2β` or `α + β + γ` (the `β` of the first tile included). -/
theorem thm_pierce_scale (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ) (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α)
    (hlegc : LegFlanksC D k ((f : ℝ) ^ 2)) :
    ∃ (u X V : Plane), ‖u‖ = 1 ∧ X = D.target.pts k + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • u ∧
      V = D.target.pts k + ((f : ℝ) ^ 2) • u ∧
      -- (i) the T-junction
      X ∈ interior D.target.carrier ∧
      ({i | (D.tile i).localAngle X = α} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle X = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle X = γ} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle X = Real.pi} : Finset (Fin N)).card = 1 ∧
      -- (iii) the pierced corner
      V ∈ interior D.target.carrier ∧
      (∃ i2 : Fin N, (D.tile i2).localAngle V = β ∧ (D.tile i2).localAngle X = Real.pi ∧
        ∃ j, (D.tile i2).pts j = D.target.pts k) ∧
      (∃ ε : Fin N × Fin 3, V ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) ∧
        (D.tile ε.1).localAngle V = Real.pi) ∧
      ({i | (D.tile i).localAngle V = Real.pi} : Finset (Fin N)).card = 1 ∧
      ((({i | (D.tile i).localAngle V = α} : Finset (Fin N)).card = 3 ∧
          ({i | (D.tile i).localAngle V = β} : Finset (Fin N)).card = 2 ∧
          ({i | (D.tile i).localAngle V = γ} : Finset (Fin N)).card = 0) ∨
        (({i | (D.tile i).localAngle V = α} : Finset (Fin N)).card = 1 ∧
          ({i | (D.tile i).localAngle V = β} : Finset (Fin N)).card = 1 ∧
          ({i | (D.tile i).localAngle V = γ} : Finset (Fin N)).card = 1)) := by
  obtain ⟨F⟩ := exists_sframe D hco he hef hM hAng k hcorner hlegc
  obtain ⟨hXint, ⟨i1, hi1, hγ1⟩, ⟨i2, hi2, hπ2⟩, c1, c2, c3, c4⟩ := junction_figure F
  obtain ⟨ε, -, hVε, hπε, -⟩ := piercer F
  have hβ2 := T2_beta_at_V F hi2
  obtain ⟨hcardπ, -, -⟩ := fill_at_V F hπε hβ2
  have hcases := fill_at_V_cases F hπε hβ2
  have hkk : F.A = D.target.pts k := F.hA
  obtain ⟨jA, hjA⟩ := MarchInduction.mem_range_of_eq hi2 (Set.mem_insert _ _)
  refine ⟨F.uR, F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR, F.V, F.huR, by rw [hkk], by rw [F.hV, hkk],
    hXint, c1, c2, c3, c4, V_interior F, ⟨i2, hβ2, hπ2, jA, by rw [hjA, hkk]⟩, ⟨ε, hVε, hπε⟩, hcardπ, hcases⟩

end Erdos634.Draft.PierceScale

#print axioms Erdos634.Draft.PierceScale.thm_pierce_scale
