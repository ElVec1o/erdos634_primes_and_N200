/-
Draft/WGapWL1.lean -- written 15 November 2026 (session 6).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.2, Wall Lemma).
Not imported by any aggregate.  Module WL1: the ABSTRACT Wall Lemma `wl_straddle` (no lattice, no `mpG`): points `P0`, direction `d` (`‖d‖ = c`), a tile `E` below
(vertices `P0`, `P0 + d`, `A0`), the wall tile `Fo` above (vertices `P0`, `P0 + ν d`, `R`), tiles `T_t` below on `[P0 + t d, P0 + (t+1) d]` for `t < q`:
then some tile edge on the line (tile above, `F ≤ level` for `F = crossL (-d)`) straddles `Z = P0 + q d`.
Proof = PROOF 6.2: hint (interior of the open run) from the midpoint of `[P0, W]` (two straight angles), hwall from the below tiles, clamp at `P0` by the vertex `P0` of `Fo`
(pushes into interior of the straddling tile and of `Fo` overlap, so the tile is `Fo`, whose angle at `P0` is `< π`), `wall_partitionG` with the first edge `Fo`'s `b`-edge,
and the arithmetic `nonmem_mc_sub_b` (A5) for `q c - b`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapCase3d
import Erdos634.Draft.WGapArith

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

/-- points `P0 + t d` strictly between two of its points are in the open segment -/
theorem pt_openSeg (P0 d : Plane) {a b t : ℝ} (h1 : a < t) (h2 : t < b) :
    P0 + t • d ∈ openSegment ℝ (P0 + a • d) (P0 + b • d) := by
  have hba : 0 < b - a := by linarith
  refine ⟨(b - t) / (b - a), (t - a) / (b - a), div_pos (by linarith) hba, div_pos (by linarith) hba, ?_, ?_⟩
  · field_simp; ring
  · ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp; ring

theorem pt_seg (P0 d : Plane) {a b t : ℝ} (h0 : a < b) (h1 : a ≤ t) (h2 : t ≤ b) :
    P0 + t • d ∈ segment ℝ (P0 + a • d) (P0 + b • d) := by
  have hba : 0 < b - a := by linarith
  refine ⟨(b - t) / (b - a), (t - a) / (b - a), div_nonneg (by linarith) hba.le, div_nonneg (by linarith) hba.le, ?_, ?_⟩
  · field_simp; ring
  · ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp; ring

section wl

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem wl_straddle (S : SetupG D e f α β γ L ax ay) {q : ℕ} (hq1 : 1 ≤ q) (hqf : q ≤ f - 1)
    (P0 d : Plane) (ν : ℝ) (hdn : ‖d‖ = (f : ℝ) ^ 2) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hνb : (f : ℝ) ^ 2 * ν = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (E : Fin N) (A0 : Plane) (hE : HasV D E P0 (P0 + d) A0) (hA0 : cross d (A0 - P0) < 0)
    (Fo : Fin N) (R : Plane) (hFo : HasV D Fo P0 (P0 + ν • d) R) (hR : 0 < cross d (R - P0))
    (hT : ∀ t : ℕ, t < q → ∃ (T : Fin N) (A : Plane),
      HasV D T (P0 + (t : ℝ) • d) (P0 + ((t : ℝ) + 1) • d) A ∧ cross d (A - (P0 + (t : ℝ) • d)) < 0) :
    ∃ ed ∈ D.lineChain (crossL (-d)) (crossL (-d) P0),
      Straddles ((D.tile ed.1).edge ed.2) (P0 + ((q : ℝ) + 1) • d) (P0 + (q : ℝ) • d) P0 := by
  by_contra hno
  push_neg at hno
  have hf2 := S.c_pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at hdn; simp at hdn; linarith
  set F : Plane →ₗ[ℝ] ℝ := crossL (-d) with hFdef
  have hF : F ≠ 0 := crossL_ne_zero (neg_ne_zero.mpr hd0)
  set cc : ℝ := F P0 with hcc
  have hFz : ∀ z : Plane, F z = cc - cross d (z - P0) := by
    intro z; simp only [hFdef, hcc, crossL_apply, cross, PiLp.neg_apply, PiLp.sub_apply]; ring
  have hFl : ∀ s : ℝ, F (P0 + s • d) = cc := by
    intro s; rw [hFz]; simp only [cross, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  have hFP0 : F P0 = cc := rfl
  set Z : Plane := P0 + (q : ℝ) • d with hZ
  set Q' : Plane := P0 + ((q : ℝ) + 1) • d with hQ'def
  set P' : Plane := P0 + (-1 : ℝ) • d with hP'def
  set W : Plane := P0 + ν • d with hW
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
  -- the wall tile: all vertices have F ≤ cc
  have hall : ∀ i, F ((D.tile Fo).pts i) ≤ cc := by
    refine hFo.all (P := fun z => F z ≤ cc) (le_of_eq hFP0) (le_of_eq (hFl ν)) ?_
    show F R ≤ cc
    rw [hFz]; linarith
  -- Z and P0 are vertices (in the target)
  have hP0t : P0 ∈ D.target.carrier := hE.mem₁
  have hZt : Z ∈ D.target.carrier := by
    obtain ⟨T, A, hTv, -⟩ := hT (q - 1) (by omega)
    have h := hTv.mem₂
    have e1 : (((q - 1 : ℕ) : ℝ) + 1) = (q : ℝ) := by rw [Nat.cast_sub hq1]; simp
    rwa [e1] at h
  -- interior point z of the first b-step
  set z : Plane := P0 + (ν / 2) • d with hz
  have hzE : z ∈ openSegment ℝ P0 (P0 + d) := by
    have := pt_openSeg P0 d (a := 0) (b := 1) (t := ν / 2) (by linarith) (by linarith)
    simpa using this
  have hzW : z ∈ openSegment ℝ P0 W := by
    have := pt_openSeg P0 d (a := 0) (b := ν) (t := ν / 2) (by linarith) (by linarith)
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
    refine ⟨ν / (2 * q), ?_⟩
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
  -- the wall
  have hwall : ∀ y ∈ openSegment ℝ P0 Z, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := chord_point_step P0 d hq1 (show y ∈ openSegment ℝ P0 (P0 + (q : ℝ) • d) from hy)
    obtain ⟨T, A, hTv, -⟩ := hT i hi
    obtain ⟨k, m', j', hkm, hkj, hmj, hk, hm', hj'⟩ := hTv
    refine seg_wall D.toDissection (t := T) hkm ?_
    rw [hk, hm']; exact hyi
  -- the clamp at P0: no chain edge straddles P0
  have hP : ∀ ed ∈ D.lineChain F cc, ¬ Straddles ((D.tile ed.1).edge ed.2) P' P0 Z := by
    intro ed hed hs
    obtain ⟨-, hang, hpush⟩ := straddle_data D.toDissection F hF cc hPQ hFP0 hfZ hfP' hP' hed hs
    set v : Plane := (1 : ℝ) • (W - P0) + (1 : ℝ) • (R - P0) with hv
    have hFv : F v < 0 := by
      have : F v = - cross d (R - P0) := by
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
  -- the first edge: the b-edge of Fo
  obtain ⟨k, hk, hkpts⟩ := hasV_edge_pts hFo
  have hmem : (Fo, k) ∈ D.lineChain F cc := by
    rw [Dissection.mem_lineChain]
    refine ⟨?_, ?_, hall⟩
    all_goals (rcases hkpts with ⟨h1, h2⟩ | ⟨h1, h2⟩)
    all_goals (simp only [])
    all_goals (first | (rw [h1]; first | done | exact hFP0 | exact hFl ν) | (rw [h2]; first | done | exact hFP0 | exact hFl ν))
  have hdedge : dist ((D.tile Fo).pts k) ((D.tile Fo).pts (k + 1)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have hdW : dist P0 W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [dist_eq_norm, hW, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hν0, hdn]
      linarith
    rcases hkpts with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hdW
    · rw [h1, h2, dist_comm]; exact hdW
  have hsub : (D.tile Fo).edge k ⊆ segment ℝ P0 Z := by
    rw [hk]
    refine (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) ?_
    have := pt_seg P0 d (a := 0) (b := (q : ℝ)) (t := ν) hqpos hν0.le (by
      have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
      linarith)
    simpa [hW, hZ] using this
  obtain ⟨x, y, w, hxyz⟩ := wall_partitionG D S.hM F hF cc hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hno hmem hsub
  have hdPQ : dist P0 Z = (q : ℝ) * (f : ℝ) ^ 2 := by
    rw [dist_eq_norm, hZ, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hqpos, hdn]
  rw [hdedge, hdPQ] at hxyz
  have hZR : ((x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + w * (f : ℝ) ^ 2) =
      (q : ℝ) * (f : ℝ) ^ 2 - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by linarith
  have hZI : (x : ℤ) * ((e : ℤ) * f) + (y : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (w : ℤ) * (f : ℤ) ^ 2 =
      (q : ℤ) * (f : ℤ) ^ 2 - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) := by
    exact_mod_cast hZR
  exact Erdos634.Draft.WGapArith.nonmem_mc_sub_b S.he S.hef S.hco hq1 hqf ⟨x, y, w, hZI⟩

end wl

#print axioms wl_straddle

end Erdos634.Draft.WGapStmt
