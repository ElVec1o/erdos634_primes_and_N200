/-
Draft/WGapRL1.lean -- written 16 November 2026 (session 9).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8, steps (alpha) and (beta) of Lemma RL).
Not imported by any aggregate.  The SIGNED, general-length version of the Wall Lemma core `wl_straddle` (WGapWL1): used for the two "fault line" steps of RL
 (alpha) on `Lambda_3` : the wall tiles (the `nu(i-m',m')`, c-edges of length `u = c`) lie on the side `s * cross d . < 0`, the chain tile (of (r2), `b`-edge) on the side `s * cross > 0`;
 (beta)  on `L^(tau)`   : the wall tiles are the `b`-edges (`u = b`) of the `nu(tau,m')`, the chain tile has an edge of length `a` or `c` from `P0`.
`fault_straddle`: with unit step `d` (`||d|| = u`), `q >= 1` wall tiles `T_t` on `[P0 + t d, P0 + (t+1) d]`, `t < q`, a first wall tile `E` and a chain tile `Fo` with an edge
`[P0, P0 + lam d]` (`lam > 0` ARBITRARY), and the arithmetic hypothesis `hnon : lam*u + (x a + y b + z c) != q*u` for all naturals: some chain edge straddles `Z = P0 + q d`.
The clamp at `P0` is automatic (the straddler would overlap `Fo`).  If `lam > q` the first chain edge itself straddles `Z` (no arithmetic needed).
`fault_cover` = the same with the conclusion "a tile has `Z` in the relative interior of an edge on the line and covers the open half-disk on the chain side".
`edgecover_clash`: two such half-disk covers at one point `X`, along non-parallel directions, are impossible (the tile would contain `X` in its interior).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapWL1
import Erdos634.Draft.WGapWL2

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

section rl1

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem fault_straddle (S : SetupG D e f α β γ L ax ay) {q : ℕ} (hq1 : 1 ≤ q)
    (P0 d : Plane) (u lam s : ℝ) (hs : s = 1 ∨ s = -1) (hdn : ‖d‖ = u) (hu : 0 < u) (hlam : 0 < lam)
    (hnon : ∀ x y z : ℕ, lam * u + ((x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2) ≠ (q : ℝ) * u)
    (E : Fin N) (A0 : Plane) (hE : HasV D E P0 (P0 + d) A0) (hA0 : s * cross d (A0 - P0) < 0)
    (Fo : Fin N) (R : Plane) (hFo : HasV D Fo P0 (P0 + lam • d) R) (hR : 0 < s * cross d (R - P0))
    (hT : ∀ t : ℕ, t < q → ∃ (T : Fin N) (A : Plane),
      HasV D T (P0 + (t : ℝ) • d) (P0 + ((t : ℝ) + 1) • d) A ∧ s * cross d (A - (P0 + (t : ℝ) • d)) < 0) :
    ∃ ed ∈ D.lineChain (crossL (-(s • d))) (crossL (-(s • d)) P0),
      Straddles ((D.tile ed.1).edge ed.2) (P0 + ((q : ℝ) + 1) • d) (P0 + (q : ℝ) • d) P0 := by
  by_contra hno
  push_neg at hno
  have hf2 := S.c_pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hs0 : s ≠ 0 := by rcases hs with h | h <;> simp [h]
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at hdn; simp at hdn; linarith
  set F : Plane →ₗ[ℝ] ℝ := crossL (-(s • d)) with hFdef
  have hF : F ≠ 0 := crossL_ne_zero (neg_ne_zero.mpr (smul_ne_zero hs0 hd0))
  set cc : ℝ := F P0 with hcc
  have hFz : ∀ z : Plane, F z = cc - s * cross d (z - P0) := by
    intro z; simp only [hFdef, hcc, crossL_apply, cross, PiLp.neg_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hFl : ∀ r : ℝ, F (P0 + r • d) = cc := by
    intro r; rw [hFz]; simp only [cross, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  have hFP0 : F P0 = cc := rfl
  set Z : Plane := P0 + (q : ℝ) • d with hZ
  set Q' : Plane := P0 + ((q : ℝ) + 1) • d with hQ'def
  set P' : Plane := P0 + (-1 : ℝ) • d with hP'def
  set W : Plane := P0 + lam • d with hW
  have hPQ : P0 ≠ Z := by
    intro h
    have : (q : ℝ) • d = 0 := by
      have := congrArg (fun z => z - P0) h.symm
      simpa [hZ] using this
    rcases smul_eq_zero.mp this with h0 | h0
    · exact hqpos.ne' h0
    · exact hd0 h0
  have hfZ : F Z = cc := hFl _
  have hfP' : F P' = cc := hFl _
  have hfQ' : F Q' = cc := hFl _
  have hP' : P0 ∈ openSegment ℝ P' Z := by
    have := pt_openSeg P0 d (a := -1) (b := (q : ℝ)) (t := 0) (by norm_num) hqpos
    simpa [hP'def, hZ] using this
  have hQ' : Z ∈ openSegment ℝ P0 Q' := by
    have := pt_openSeg P0 d (a := 0) (b := (q : ℝ) + 1) (t := (q : ℝ)) hqpos (by linarith)
    simpa [hQ'def, hZ] using this
  have hS : segment ℝ P0 Z ⊆ {y | F y = cc} := Erdos634.RunPartition.CSlot.segment_subset_level F cc hFP0 hfZ
  have hall : ∀ i, F ((D.tile Fo).pts i) ≤ cc := by
    refine hFo.all (P := fun z => F z ≤ cc) (le_of_eq hFP0) (le_of_eq (hFl lam)) ?_
    show F R ≤ cc
    rw [hFz]; linarith
  have hP0t : P0 ∈ D.target.carrier := hE.mem₁
  have hZt : Z ∈ D.target.carrier := by
    obtain ⟨T, A, hTv, -⟩ := hT (q - 1) (by omega)
    have h := hTv.mem₂
    have e1 : (((q - 1 : ℕ) : ℝ) + 1) = (q : ℝ) := by rw [Nat.cast_sub hq1]; simp
    rwa [e1] at h
  -- interior point z of the first step
  set δ : ℝ := min 1 lam with hδ
  have hδ0 : 0 < δ := lt_min one_pos hlam
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδl : δ ≤ lam := min_le_right _ _
  set z : Plane := P0 + (δ / 2) • d with hz
  have hzE : z ∈ openSegment ℝ P0 (P0 + d) := by
    have := pt_openSeg P0 d (a := 0) (b := 1) (t := δ / 2) (by linarith) (by linarith)
    simpa using this
  have hzW : z ∈ openSegment ℝ P0 W := by
    have := pt_openSeg P0 d (a := 0) (b := lam) (t := δ / 2) (by linarith) (by linarith)
    simpa [hW] using this
  have hanE : (D.tile E).localAngle z = Real.pi := hasV_localAngle_pi hE.rot.rot hzE
  have hanF : (D.tile Fo).localAngle z = Real.pi := hasV_localAngle_pi hFo.rot.rot hzW
  have hne : E ≠ Fo := by
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hE
    refine (ne_of_F F hall (i := j) ?_).symm
    rw [hj, hFz]; linarith
  have hzt : z ∈ D.target.carrier := D.target.convex.openSegment_subset hE.mem₁ hE.mem₂ hzE
  have hzint : z ∈ interior D.target.carrier := by
    refine interior_of_sum D.toDissection hzt {E, Fo} ?_
    rw [Finset.sum_pair hne, hanE, hanF]
    linarith [Real.pi_pos]
  have hzr : z ∈ range (AffineMap.lineMap P0 Z : ℝ → Plane) := by
    refine ⟨δ / (2 * q), ?_⟩
    rw [hz, hZ, AffineMap.lineMap_apply]
    ext x
    simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    ring
  have hint : openSegment ℝ P0 Z ⊆ interior D.target.carrier := by
    intro y hy
    rcases openSegment_subset_union _ _ hzr hy with h | h | h
    · rw [h]; exact hzint
    · rw [openSegment_symm] at h
      exact openSeg_interior D.toDissection hzint hP0t h
    · exact openSeg_interior D.toDissection hzint hZt h
  have hwall : ∀ y ∈ openSegment ℝ P0 Z, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := chord_point_step P0 d hq1 (show y ∈ openSegment ℝ P0 (P0 + (q : ℝ) • d) from hy)
    obtain ⟨T, A, hTv, -⟩ := hT i hi
    obtain ⟨k, m', j', hkm, hkj, hmj, hk, hm', hj'⟩ := hTv
    refine seg_wall D.toDissection (t := T) hkm ?_
    rw [hk, hm']; exact hyi
  -- the clamp at P0 (automatic)
  have hP : ∀ ed ∈ D.lineChain F cc, ¬ Straddles ((D.tile ed.1).edge ed.2) P' P0 Z := by
    intro ed hed hs'
    obtain ⟨-, hang, hpush⟩ := straddle_data D.toDissection F hF cc hPQ hFP0 hfZ hfP' hP' hed hs'
    set v : Plane := (1 : ℝ) • (W - P0) + (1 : ℝ) • (R - P0) with hv
    have hFv : F v < 0 := by
      have : F v = - (s * cross d (R - P0)) := by
        simp only [hv, hW, hFdef, crossL_apply, cross, PiLp.neg_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul]
        ring
      rw [this]; linarith
    obtain ⟨ε₀, hε₀, hpe⟩ := hpush v hFv
    obtain ⟨ε₁, hε₁, hpf⟩ := hasV_push hFo (θ1 := 1) (θ2 := 1) one_pos one_pos
    set ε := min ε₀ ε₁ / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; have := lt_min hε₀ hε₁; linarith
    have hεa : ε < ε₀ := by rw [hε]; have := min_le_left ε₀ ε₁; linarith [lt_min hε₀ hε₁]
    have hεb : ε < ε₁ := by rw [hε]; have := min_le_right ε₀ ε₁; linarith [lt_min hε₀ hε₁]
    have h1 := hpe ε hε0 hεa
    have h2 := hpf ε hε0 hεb
    have hedF : ed.1 = Fo := by
      by_contra hneq
      exact Set.disjoint_left.mp (D.interiors_disjoint hneq) h1 h2
    rw [hedF] at hang
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hFo
    have h3 := Tri.localAngle_vertex (D.tile Fo) k
    have h4 := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi (D.tile Fo) k
    have h5 : (D.tile Fo).localAngle P0 = (D.tile Fo).localAngle ((D.tile Fo).pts k) := by rw [hk]
    linarith
  -- the first chain edge
  obtain ⟨k, hk, hkpts⟩ := hasV_edge_pts hFo
  have hmem : (Fo, k) ∈ D.lineChain F cc := by
    rw [Dissection.mem_lineChain]
    refine ⟨?_, ?_, hall⟩
    all_goals (rcases hkpts with ⟨h1, h2⟩ | ⟨h1, h2⟩)
    all_goals (simp only [])
    all_goals (first | (rw [h1]; first | done | exact hFP0 | exact hFl lam) | (rw [h2]; first | done | exact hFP0 | exact hFl lam))
  by_cases hlq : lam ≤ (q : ℝ)
  · have hdedge : dist ((D.tile Fo).pts k) ((D.tile Fo).pts (k + 1)) = lam * u := by
      have hdW : dist P0 W = lam * u := by
        rw [dist_eq_norm, hW, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, hdn]
      rcases hkpts with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hdW
      · rw [h1, h2, dist_comm]; exact hdW
    have hsub : (D.tile Fo).edge k ⊆ segment ℝ P0 Z := by
      rw [hk]
      refine (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) ?_
      have := pt_seg P0 d (a := 0) (b := (q : ℝ)) (t := lam) hqpos hlam.le hlq
      simpa [hW, hZ] using this
    obtain ⟨x, y, w, hxyz⟩ := wall_partitionG D S.hM F hF cc hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hno hmem hsub
    have hdPQ : dist P0 Z = (q : ℝ) * u := by
      rw [dist_eq_norm, hZ, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hqpos, hdn]
    rw [hdedge, hdPQ] at hxyz
    exact hnon x y w hxyz
  · push_neg at hlq
    refine hno (Fo, k) hmem ⟨?_, ?_⟩
    · set η : ℝ := min (lam - q) 1 / 2 with hη
      have hη0 : 0 < η := by rw [hη]; have := lt_min (sub_pos.mpr hlq) one_pos; linarith
      have hη1 : η < 1 := by rw [hη]; have := min_le_right (lam - q) 1; linarith
      have hη2 : (q : ℝ) + η < lam := by rw [hη]; have := min_le_left (lam - q) 1; have := lt_min (sub_pos.mpr hlq) one_pos; linarith
      refine ⟨P0 + ((q : ℝ) + η) • d, ?_, ?_⟩
      · rw [hk]
        have := pt_seg P0 d (a := 0) (b := lam) (t := (q : ℝ) + η) hlam (by linarith) hη2.le
        simpa [hW] using this
      · have := pt_openSeg P0 d (a := (q : ℝ)) (b := (q : ℝ) + 1) (t := (q : ℝ) + η) (by linarith) (by linarith)
        rw [openSegment_symm]
        simpa [hZ, hQ'def] using this
    · refine ⟨P0 + ((q : ℝ) / 2) • d, ?_, ?_⟩
      · rw [hk]
        have := pt_seg P0 d (a := 0) (b := lam) (t := (q : ℝ) / 2) hlam (by linarith) (by linarith)
        simpa [hW] using this
      · have := pt_openSeg P0 d (a := 0) (b := (q : ℝ)) (t := (q : ℝ) / 2) (by linarith) (by linarith)
        rw [openSegment_symm]
        simpa [hZ] using this

end rl1

end Erdos634.Draft.WGapStmt
