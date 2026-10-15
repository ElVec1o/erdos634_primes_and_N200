/-
Draft/W2E1Last.lean -- Stage 3 of the formalization of `prop:w2e1`: the rule R-CH, i.e. the side word does not end
`(A1 or B1) C1 C1`.

Points (`c = n²`, `u`, `h` as in `W2E1Frame`; the last two base tiles are `C1` at `x = L − 2c` and at `x + c`):
`P2 = (x, 0)`, `R = (x + c, 0)`, `B = (x + 2c, 0)`, `G = (x + c − u, h)` and `G2 = (x + 2c − u, h)` the two apexes,
`E = (x + 2c − 2u, 2h)` on `BA`.  Steps, as in the paper:
 1. the corner lemma gives the partner `U = (R, G2, G)` of the last tile (`third_vertex_unique`);
 2. no tile other than `X_{n−1}` has both `G` and `P2` as vertices (vertex figure at `P2`), so some tile `φ` has `G`
    in the relative interior of an edge on the line `P2 G` (`apex_dichotomy`);
 3. the wall `[G, G2]` (an edge of `U`) is clamped by `φ` at `G` and by `BA` at `G2`; its first edge from above at
    `G` belongs to a tile `Y` which shows at most `α` at `G` (four angles at `G`), so `Y = (G, G2, E)`;
 4. the chord `[P2, E]` of length `2b` is a wall clamped by the boundary at both ends; its first edge at `P2` on the
    side away from `R` has length `b`, so a tile other than `X_{n−1}` has the vertices `P2` and `G`: contradiction
    with step 2.

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.W2E1HalfTurn

namespace Erdos634.Draft.W2E1

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Set

/-- the functional `−y` -/
theorem negy_apply (p : Plane) : crossL (mkPt (-1) 0) p = -(p 1) := by
  rw [crossL_apply]; simp only [cross, mkPt_zero, mkPt_one]; ring

theorem negy_ne : crossL (mkPt (-1) 0) ≠ 0 := by
  apply crossL_ne_zero
  intro h
  have h' := congrArg (fun p : Plane => p 0) h
  simp at h'

/-- the third vertex of a tile is off the line of the other two -/
theorem cross_ne_zero_of_tri (T : Tri) {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) :
    cross (T.pts m - T.pts k) (T.pts j - T.pts k) ≠ 0 := by
  intro h0
  have hne : T.pts m ≠ T.pts k := fun h => hkm (T.indep.injective h).symm
  refine two_vertices_on_line T (crossL (T.pts m - T.pts k)) (cross (T.pts m - T.pts k) (T.pts k))
    (crossL_ne_zero (sub_ne_zero.mpr hne)) (fun i => ?_)
  rcases fin3_cover k m j hkm hkj hmj i with h' | h' | h'
  · rw [h']; rfl
  · rw [h', crossL_apply]
    have h1 := cross_sub_right (T.pts m - T.pts k) (T.pts m) (T.pts k)
    rw [cross_self] at h1
    linarith
  · rw [h', crossL_apply]
    rw [cross_sub_right] at h0
    linarith

namespace Setup

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ : ℝ}

set_option maxHeartbeats 1600000 in
/-- **R-CH**: the side word does not end `(A1 or B1) C1 C1`.  Here `i2`, `i3`, `i4` are the last three base tiles,
at `xp`, `x = L − 2c`, `x + c`. -/
theorem rule_CH (S : Setup D n α β γ) {i2 i3 i4 : Fin N} {t' : Ty} {xp x : ℝ}
    (h2 : BaseTile D n i2 t' xp) (hxp : xp + t'.lenR n = x) (hg : t'.gR)
    (h3 : BaseTile D n i3 Ty.C1 x) (h4 : BaseTile D n i4 Ty.C1 (x + (n:ℝ) ^ 2))
    (hx : x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 = Lw n) : False := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hαβ := S.alpha_lt_beta
  have hπ := Real.pi_pos
  have hf0 := S.f0
  have hr := rt_pos S.f1.le
  have hb := S.b_pos
  have hhp := hh_pos S.f1
  have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by positivity
  have h2r := S.baseTile_range h2
  have hl := Ty.lenR_pos S.f2 t'
  have hx0 : 0 < x := by linarith [h2r.1]
  have hxL : x < Lw n := by linarith
  -- the two `C1` tiles
  obtain ⟨ka, kb, kg, hab, hag, hbg, hVa, hVb, hG, hda, hdb⟩ := S.c1_data h3
  obtain ⟨hG1, htG, hintPG⟩ := S.c1_common h3 hab hag hbg hVa hVb hG
  obtain ⟨ka', kb', kg', hab', hag', hbg', hVa', hVb', hG', hda', hdb'⟩ := S.c1_data h4
  have mG : (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) ∈ D.target.carrier := by
    rw [← hG]; exact pts_mem_target D.toDissection i3 kg
  have mG2 : (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) ∈ D.target.carrier := by
    rw [← hG']; exact pts_mem_target D.toDissection i4 kg'
  have mP2 : (mkPt x 0) ∈ D.target.carrier := by
    rw [← hVa]; exact pts_mem_target D.toDissection i3 ka
  have hGne : (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) ≠ (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) := mkPt_ne_of_fst (by intro h0; linarith)
  have hGG2 : dist (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) = (n:ℝ) ^ 2 := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg hn2.le
    rw [dist_sq_mkPt]; ring
  -- Step 1: the partner `U` of the last tile; its third vertex is `G`
  obtain ⟨u, hu4, k, m, j, hkm, hkj, hmj, hk, hm, hd1, hd2, hUang, hside⟩ := S.c1_corner h4 hx
  have e1 : cross ((mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) - (mkPt (x + (n:ℝ) ^ 2) 0)) ((mkPt (x + (n:ℝ) ^ 2) 0) - (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2) 0)) = hh n * (n:ℝ) ^ 2 := by
    simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]; ring
  have e2 : cross ((mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) - (mkPt (x + (n:ℝ) ^ 2) 0)) ((mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) - (mkPt (x + (n:ℝ) ^ 2) 0)) = hh n * (n:ℝ) ^ 2 := by
    simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]; ring
  have h5 : 0 < hh n * (n:ℝ) ^ 2 := mul_pos hhp hn2
  have hne0 := cross_ne_zero_of_tri (D.tile u) hkm hkj hmj
  rw [hk, hm] at hne0
  have hpos1 : 0 < cross ((mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) - (mkPt (x + (n:ℝ) ^ 2) 0)) ((D.tile u).pts j - (mkPt (x + (n:ℝ) ^ 2) 0)) := by
    rw [e1] at hside
    rcases lt_or_gt_of_ne hne0 with hneg | hpos
    · exfalso
      nlinarith [mul_pos (neg_pos.mpr hneg) h5]
    · exact hpos
  have hjG : (D.tile u).pts j = (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) :=
    third_vertex_unique (P := (mkPt (x + (n:ℝ) ^ 2) 0)) (Q := (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n))) (by rw [hd1, hda]) (by rw [hd2, hGG2])
      (by rw [e2]; exact mul_pos hpos1 h5)
  have hUG : (D.tile u).localAngle (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = β := by
    have h6 := (angle_at_vertex D S.f2 S.hM u (Ne.symm hkj) (Ne.symm hmj) hkm).2.1
      (by rw [hk, hm]; exact hdb')
    rw [hjG] at h6; exact h6
  obtain ⟨k₀, hk₀⟩ := (D.tile u).pair_eq_edge (Ne.symm hmj)
  rw [hjG, hm] at hk₀
  -- Step 2: no tile other than `i3` has both `G` and `P2` as vertices
  have hi2 : (D.tile i2).localAngle (mkPt x 0) = γ := by
    have h6 := (S.angles h2).2
    rw [hxp, Ty.aR_of_gR α β γ hg] at h6; exact h6
  have hi3 : (D.tile i3).localAngle (mkPt x 0) = α := (S.angles h3).1
  have nomirror : ∀ T' : Fin N, T' ≠ i3 → ∀ k m : Fin 3, k ≠ m →
      (D.tile T').pts k = (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) → (D.tile T').pts m = (mkPt x 0) → False := by
    intro T' hT k m hkm hk hm
    have hTang := S.angle_of_b_edge (i := T') hkm (by rw [hk, hm, dist_comm]; exact hdb)
    rw [hm] at hTang
    rcases hTang with h6 | h6
    · rcases (S.c1_left h3 hT h6 hk).2 i2 t' xp h2 hxp with h7 | h7
      · exact (Ty.gR_ne _ hg).1 h7
      · exact (Ty.gR_ne _ hg).2.1 h7
    · exact S.gamma_alpha_alpha hx0 hxL hi2 hi3 h6 (Ne.symm hT)
  obtain ⟨φ, hGφ, hφπ, hpush⟩ : ∃ φ : Fin N, (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) ∈ (D.tile φ).carrier ∧
      (D.tile φ).localAngle (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = Real.pi ∧
      ∀ a μ : ℝ, 0 < μ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) + ε • (a • ((mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) - (mkPt x 0)) + μ • ((mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) - (mkPt (x + (n:ℝ) ^ 2) 0))) ∈ interior (D.tile φ).carrier := by
    rcases apex_dichotomy D S.hn3 S.hM hag hab (Ne.symm hbg) hVa hG hVb
        (Or.inr (by rw [dist_comm]; exact hdb)) (by rw [openSegment_symm]; exact hintPG)
        (S.below_out (mkPt_one _ _) hG1) with h6 | ⟨T', hT, k, m, hkm, hk, hm⟩
    · exact h6
    · exact (nomirror T' hT k m hkm hk hm).elim
  -- Step 3: the tile `Y` above the wall `[G, G2]`
  have hfG : (crossL (mkPt (-1) 0)) (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = -(hh n) := by rw [negy_apply, mkPt_one]
  have hfG2 : (crossL (mkPt (-1) 0)) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) = -(hh n) := by rw [negy_apply, mkPt_one]
  obtain ⟨P', hfP', hGP', hsubφ⟩ := ext_point_of_push (crossL (mkPt (-1) 0)) hfG hfG2 hGφ (by
    obtain ⟨ε₀, hε₀, hp⟩ := hpush (-1) 1 one_pos
    have hv : (-1:ℝ) • ((mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) - (mkPt x 0)) + (1:ℝ) • ((mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) - (mkPt (x + (n:ℝ) ^ 2) 0)) = (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) - (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) := by
      apply plane_ext <;> simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
    rw [hv] at hp
    exact ⟨ε₀, hε₀, hp⟩)
  have hG2B : gBA n (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) = 0 := by
    rw [gBA_mk, hx]
    have h6 := bru S.f1
    linear_combination h6
  have hGBpos : 0 < gBA n (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) := by
    rw [gBA_mk]
    have e : Lw n - (x + (n:ℝ) ^ 2 - uu n) = (n:ℝ) ^ 2 + uu n := by linarith
    rw [e]
    have h6 := bru S.f1
    nlinarith [mul_pos (mul_pos hb hr) hn2]
  have hGQpos : 0 < gQA n (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) := by
    rw [gQA_mk]
    have h6 := ruh S.f1
    have h7 := two_hh_lt S.f1
    nlinarith [mul_pos hr hx0]
  have hint3 : openSegment ℝ (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) ⊆ interior D.target.carrier :=
    S.interior_seg mG mG2 (Or.inl hG1) (Or.inl hGQpos) (Or.inl hGBpos)
  have hwall3 : ∀ y ∈ openSegment ℝ (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)), ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy i
    refine D.edge_point_not_interior (j := u) (k := k₀) ?_ i
    rw [← hk₀]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨iy, ky, my, xx, yy, zz, hkmy, hky, hmy, hley, hsumy⟩ :=
    wall_first D S.hM (crossL (mkPt (-1) 0)) negy_ne (-(hh n)) hGne hfG hfG2 hfP' (ext_level _ hfG2 hfG 1) hGP'
      (by rw [openSegment_symm]; exact mem_openSegment_ext (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) one_pos) hint3 hwall3
      (fun e _ => not_straddles_of_interior D.toDissection hsubφ e.1 e.2)
      (clamp_out D.toDissection _ _ (S.BA_out hG2B hGBpos))
  rw [hGG2] at hsumy
  have hℓ := vertex_dist_cases D S.hM iy hkmy
  rw [hky] at hℓ
  have hnb := (first_len S.hn3 hℓ hsumy).2.2.1 rfl
  obtain ⟨jy, hjyk, hjym⟩ := fin3_third ky my hkmy
  have hhigh : ∀ i, hh n ≤ ((D.tile iy).pts i) 1 := by
    intro i
    have h6 := hley i
    rw [negy_apply] at h6
    linarith
  have hφ3 : φ ≠ i3 := by
    intro h0; rw [h0, htG] at hφπ; linarith
  have hφu : φ ≠ u := by
    intro h0; rw [h0, hUG] at hφπ; linarith
  have h3u : i3 ≠ u := by
    intro h0
    have h6 : (D.tile i3).localAngle (mkPt (x + (n:ℝ) ^ 2) 0) = β := (S.angles h3).2
    rw [h0, hUang] at h6
    linarith
  have hy3 : iy ≠ i3 := by
    intro h0
    have h6 := hhigh ka
    rw [h0, hVa, mkPt_one] at h6
    linarith
  have hyu : iy ≠ u := by
    intro h0
    have h6 := hhigh k
    rw [h0, hk, mkPt_one] at h6
    linarith
  have hAy := angle_at_vertex D S.f2 S.hM iy hkmy (Ne.symm hjyk) (Ne.symm hjym)
  rw [hky] at hAy
  have h4le : ∀ θ : ℝ, (D.tile iy).localAngle (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = θ → θ < Real.pi → θ ≤ α := by
    intro θ hθ hθπ
    have hφy : φ ≠ iy := by
      intro h0; rw [h0, hθ] at hφπ; linarith
    have h6 := four_angles_le D.toDissection (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) hφ3 hφu hφy h3u (Ne.symm hy3) (Ne.symm hyu)
    have h7 := localAngle_le_two_pi D.target (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n))
    rw [hφπ, htG, hUG, hθ] at h6
    linarith
  have hda_y : dist ((D.tile iy).pts my) ((D.tile iy).pts jy) = n := by
    rcases vertex_dist_cases D S.hM iy (Ne.symm hjym) with h6 | h6 | h6
    · exact h6
    · exfalso
      have h7 := h4le β (hAy.2.1 h6) (by linarith)
      linarith
    · exfalso
      have h7 := h4le γ (hAy.2.2 h6) hγπ
      linarith
  have hsides : dist (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) ((D.tile iy).pts my) = (n:ℝ) ^ 2 ∧
      dist (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) ((D.tile iy).pts jy) = (n:ℝ) ^ 2 - 1 := by
    rcases sides_of_a_edge D S.f2 S.hM iy (Ne.symm hjym) (Ne.symm hkmy) hjyk hda_y with
      ⟨s1, s2⟩ | ⟨s1, -⟩
    · rw [hky] at s1 s2; exact ⟨s1, s2⟩
    · rw [hky] at s1; exact absurd s1 hnb
  have hmyG2 : (D.tile iy).pts my = (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) :=
    eq_of_mem_segment_of_dist hGne hmy (right_mem_segment ℝ _ _) (by rw [hsides.1, hGG2])
  have hEG : dist (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = (n:ℝ) ^ 2 - 1 := by
    have h6 : dist (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = dist (mkPt x 0) (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) := by
      refine dist_eq_of_sq_eq ?_ dist_nonneg dist_nonneg
      rw [dist_sq_mkPt, dist_sq_mkPt]; ring
    rw [h6]; exact hdb
  have hEG2 : dist (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) = n := by
    have h6 : dist (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) = dist (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2) 0) := by
      refine dist_eq_of_sq_eq ?_ dist_nonneg dist_nonneg
      rw [dist_sq_mkPt, dist_sq_mkPt]; ring
    rw [h6]; exact hda'
  have hc : ∀ q : Plane, cross ((mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) - (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n))) (q - (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n))) = (n:ℝ) ^ 2 * (q 1 - hh n) := by
    intro q
    simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]; ring
  have hjy_ne := cross_ne_zero_of_tri (D.tile iy) hkmy (Ne.symm hjyk) (Ne.symm hjym)
  rw [hky, hmyG2, hc] at hjy_ne
  have hjy_high : hh n < ((D.tile iy).pts jy) 1 := by
    rcases lt_or_eq_of_le (hhigh jy) with h6 | h6
    · exact h6
    · exfalso
      apply hjy_ne
      rw [← h6]; ring
  have hjyG2 : dist ((D.tile iy).pts jy) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n)) = n := by
    rw [← hmyG2, dist_comm]; exact hda_y
  have hjyE : (D.tile iy).pts jy = (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) := by
    refine third_vertex_unique (P := (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n))) (Q := (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - uu n) (hh n))) (by rw [dist_comm, hsides.2, hEG])
      (by rw [hjyG2, hEG2]) ?_
    rw [hc, hc, mkPt_one]
    exact mul_pos (mul_pos hn2 (by linarith)) (mul_pos hn2 (by linarith))
  -- Step 4: the chord `[P2, E]`
  obtain ⟨w, hw0, hwG, hwb, -⟩ := exists_side_functional (T := D.tile i3) hag hab (Ne.symm hbg)
  rw [hVa, hG] at hwG
  rw [hVa, hVb] at hwb
  have hfP2 : crossL w (mkPt x 0) = cross w (mkPt x 0) := rfl
  have hEeq : (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) = (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) + (1:ℝ) • ((mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) - (mkPt x 0)) := by
    apply plane_ext <;> simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
  have hfE : crossL w (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) = cross w (mkPt x 0) := by
    rw [hEeq]; exact ext_level _ hwG hfP2 1
  have hE1 : 0 < (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) 1 := by rw [mkPt_one]; linarith
  have hP2E : (mkPt x 0) ≠ (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) := mkPt_ne_of_snd (by intro h0; linarith)
  have mE : (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) ∈ D.target.carrier := by
    rw [← hjyE]; exact pts_mem_target D.toDissection iy jy
  have hEB : gBA n (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) = 0 := by
    rw [gBA_mk]
    have e : Lw n - (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) = 2 * uu n := by linarith
    rw [e]
    have h6 := bru S.f1
    linear_combination 2 * h6
  have hP2B : 0 < gBA n (mkPt x 0) := by
    rw [gBA_mk]
    nlinarith [mul_pos (mul_pos hb hr) (show (0:ℝ) < Lw n - x by linarith)]
  have hint4 : openSegment ℝ (mkPt x 0) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) ⊆ interior D.target.carrier := by
    refine S.interior_seg mP2 mE (Or.inr hE1) (Or.inl ?_) (Or.inl hP2B)
    rw [gQA_mk]
    nlinarith [mul_pos hr hx0]
  have hGmid : (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = (1 / 2 : ℝ) • (mkPt x 0) + (1 / 2 : ℝ) • (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) := by
    apply plane_ext <;> simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
  obtain ⟨k₃, hk₃⟩ := (D.tile i3).pair_eq_edge hag
  rw [hVa, hG] at hk₃
  obtain ⟨k₄, hk₄⟩ := (D.tile iy).pair_eq_edge (Ne.symm hjyk)
  rw [hky, hjyE] at hk₄
  have hwall4 : ∀ y ∈ openSegment ℝ (mkPt x 0) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)), ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy i
    rcases segment_split_mid hGmid (openSegment_subset_segment ℝ _ _ hy) with h6 | h6
    · exact D.edge_point_not_interior (j := i3) (k := k₃) (by rw [← hk₃]; exact h6) i
    · exact D.edge_point_not_interior (j := iy) (k := k₄) (by rw [← hk₄]; exact h6) i
  obtain ⟨iT, kT, mT, x4, y4, z4, hkmT, hkT, hmT, hleT, hsumT⟩ :=
    wall_first D S.hM (crossL w) (crossL_ne_zero hw0) (cross w (mkPt x 0)) hP2E hfP2 hfE
      (ext_level _ hfP2 hfE 1) (ext_level _ hfE hfP2 1) (mem_openSegment_ext (mkPt x 0) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) one_pos)
      (by rw [openSegment_symm]; exact mem_openSegment_ext (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) (mkPt x 0) one_pos) hint4 hwall4
      (clamp_out D.toDissection _ _ (S.below_out (mkPt_one _ _) hE1))
      (clamp_out D.toDissection _ _ (S.BA_out hEB hP2B))
  have hdPE : dist (mkPt x 0) (mkPt (x + (n:ℝ) ^ 2 + (n:ℝ) ^ 2 - 2 * uu n) (2 * hh n)) = 2 * ((n:ℝ) ^ 2 - 1) := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by linarith)
    rw [dist_sq_mkPt]
    have h6 := hh_sq' S.f1
    linear_combination 4 * h6
  rw [hdPE] at hsumT
  have hℓT := vertex_dist_cases D S.hM iT hkmT
  rw [hkT] at hℓT
  have hTb := (first_len S.hn3 hℓT hsumT).2.2.2 rfl
  have hmTG : (D.tile iT).pts mT = (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) :=
    eq_of_mem_segment_of_dist hP2E hmT
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, hGmid.symm⟩ (by rw [hTb, hdb])
  have hT3 : iT ≠ i3 := by
    intro h0
    have h6 := hleT kb
    rw [h0, hVb] at h6
    exact absurd h6 (not_le.mpr hwb)
  exact nomirror iT hT3 mT kT (Ne.symm hkmT) hmTG hkT

end Setup

end Erdos634.Draft.W2E1

#print axioms Erdos634.Draft.W2E1.Setup.rule_CH
