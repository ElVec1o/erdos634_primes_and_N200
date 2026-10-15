import Mathlib.Tactic
import Erdos634.Draft.T30LL3Wit
import Erdos634.Draft.T30LL4Chain
import Erdos634.Draft.T30LL4Tri

open scoped Classical

/-!
# Witness for `chain_sum_open_end` on the N = 1440 dissection

The impossibility lemma `l4_corner` has no witness for its own (type `(b,a)`) hypotheses, so its structural ingredients are witnessed separately.
On `G3CSixtyControl.D`: the chord `[R, Z]`, `R = (33600,33600)` on the left target side, `Z = (60480,33600)` an interior point (lattice coordinates, real point `(X, Y√3)`), is the edge of the tile
`((52080,25200),(60480,33600),(33600,33600))`; the line past `Z` runs into the interior of the tile `((68400,30000),(80160,41760),(55200,36000))` for `s ∈ (0, 1/4]`.  All hypotheses of `chain_sum_open_end` are discharged.
For the chord `[R, Z₀]`, `Z₀ = (47040,33600)` the midpoint of that edge, a chain edge meets the chord and is not contained in it (the conclusion fails without `hover`).
-/

namespace Erdos634.C2Forward.Wit

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.G3CSixtyControl Erdos634.CertCoord
open Erdos634.Draft.G3CEqui60n1440 (cert cert_ok)

theorem toPt_0 (p : LP) : (toPt p) 0 = p.1 := by simp [toPt, rx]
theorem toPt_1 (p : LP) : (toPt p) 1 = p.2 * Real.sqrt 3 := by simp [toPt, ry]

noncomputable def fY : Plane →ₗ[ℝ] ℝ where
  toFun v := v 1
  map_add' := by intro a b; simp only [PiLp.add_apply]
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]

noncomputable def gL : Plane →ₗ[ℝ] ℝ where
  toFun v := v 1 - Real.sqrt 3 * v 0
  map_add' := by intro a b; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem fY_toPt (p : LP) : fY (toPt p) = p.2 * Real.sqrt 3 := toPt_1 p
theorem gL_toPt (p : LP) : gL (toPt p) = p.2 * Real.sqrt 3 - Real.sqrt 3 * p.1 := by
  show (toPt p) 1 - Real.sqrt 3 * (toPt p) 0 = _
  rw [toPt_0, toPt_1]

theorem fY_ne : fY ≠ 0 := by
  intro h
  have := congrArg (fun f => f (toPt (0, 1))) h
  simp only [fY_toPt, LinearMap.zero_apply] at this
  have h3 := s3pos
  norm_num at this

theorem tile_pts_of_mem (t : LT) (ht : t ∈ cert.leaves) :
    ∃ i : Fin cert.leaves.length, ∀ k, (D.tile i).pts k = toPt (vtx t k) := by
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp ht
  exact ⟨⟨n, hn⟩, fun k => triOf_pts _ (pos_of_mem cert_ok (List.getElem_mem hn)) k⟩

def tb : LT := ((52080, 25200), (60480, 33600), (33600, 33600))
def tu : LT := ((68400, 30000), (80160, 41760), (55200, 36000))
theorem tb_mem : tb ∈ cert.leaves := by decide +kernel
theorem tu_mem : tu ∈ cert.leaves := by decide +kernel

noncomputable def Rp : Plane := toPt (33600, 33600)
noncomputable def Zp : Plane := toPt (60480, 33600)

theorem Rp_ne_Zp : Rp ≠ Zp := by
  intro h
  have := congrArg (fun x : Plane => x 0) h
  simp only [Rp, Zp, toPt_0] at this
  norm_num at this

theorem lm0 (τ : ℝ) : (AffineMap.lineMap Rp Zp τ) 0 = 33600 + 26880 * τ := by
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul, Rp, Zp, toPt_0]
  push_cast; ring

theorem lm1 (τ : ℝ) : (AffineMap.lineMap Rp Zp τ) 1 = 33600 * Real.sqrt 3 := by
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul, Rp, Zp, toPt_1]
  push_cast; ring

theorem hover_wit : ∃ i : Fin cert.leaves.length, ∀ s : ℝ, 0 < s → s ≤ 1 / 4 →
    AffineMap.lineMap Rp Zp (1 + s) ∈ interior (D.tile i).carrier := by
  obtain ⟨i, hp⟩ := tile_pts_of_mem tu tu_mem
  refine ⟨i, fun s hs hs4 => ?_⟩
  have := interior_of_three (D.tile i) 0 (24 * s / 35 + 2 / 5) (5 * s / 7) (3 / 5 - 7 * s / 5)
    (by linarith) (by linarith) (by linarith) (by ring)
  convert this using 1
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [lm0, show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hp, hp, hp, toPt_0, toPt_0, toPt_0]
    simp [tu, vtx]
    ring
  · simp only [Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [lm1, show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hp, hp, hp, toPt_1, toPt_1, toPt_1]
    simp [tu, vtx]
    ring


theorem hint_wit : openSegment ℝ Rp Zp ⊆ interior D.target.carrier := by
  rintro y ⟨s, t, hs, ht, hst, rfl⟩
  obtain rfl : s = 1 - t := by linarith
  have := interior_of_three D.target 0 (11 / 12 - t / 30) (t / 30) (1 / 12)
    (by linarith) (by linarith) (by norm_num) (by ring)
  convert this using 1
  have h1 : D.target.pts (0 + 1) = toPt (806400, 0) := by rw [tpt]; rfl
  have h2 : D.target.pts (0 + 2) = toPt (403200, 403200) := by rw [tpt]; rfl
  have h0 : D.target.pts 0 = toPt (0, 0) := by rw [tpt]; rfl
  rw [h0, h1, h2]
  ext k
  fin_cases k
  · simp [Rp, Zp, toPt_0]; ring
  · simp [Rp, Zp, toPt_1]; ring

theorem hwall_wit : ∀ y ∈ openSegment ℝ Rp Zp, ∀ i, y ∉ interior (D.tile i).carrier := by
  obtain ⟨i, hp⟩ := tile_pts_of_mem tb tb_mem
  have h := Erdos634.ChordFar.hwall_of_tile_edge D.toDissection i 1
  have e1 : (D.tile i).pts 1 = Zp := by rw [hp]; rfl
  have e2 : (D.tile i).pts (1 + 1) = Rp := by rw [show (1 : Fin 3) + 1 = 2 from rfl, hp]; rfl
  rw [e1, e2, openSegment_symm] at h
  exact h

theorem gL_bound : ∀ y ∈ D.target.carrier, gL y ≤ 0 := by
  refine Tri.carrier_subset_halfplane D.target gL 0 ?_
  intro i
  have h3 := s3pos
  rw [tpt, gL_toPt, show cert.target = ((0, 0), (806400, 0), (403200, 403200)) from rfl]
  fin_cases i <;> simp [vtx] <;> nlinarith

/-- **Witness for `chain_sum_open_end`**: all hypotheses discharged on the real 1440-tiling. -/
theorem chain_open_end_witness :
    (∀ e ∈ D.lineChain fY (fY Rp), (∃ y, y ∈ (D.tile e.1).edge e.2 ∧ y ∈ segment ℝ Rp Zp) →
        (D.tile e.1).edge e.2 ⊆ segment ℝ Rp Zp) ∧
    ∑ e ∈ (D.lineChain fY (fY Rp)).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ Rp Zp),
        ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist Rp Zp) := by
  have h3 := s3pos
  obtain ⟨i, hi⟩ := hover_wit
  refine chain_sum_open_end D.toDissection fY fY_ne (fY Rp) Rp_ne_Zp rfl ?_ gL 0 gL_bound ?_ ?_ hint_wit
    hwall_wit ⟨1 / 4, by norm_num, fun s hs hs4 => ⟨i, hi s hs hs4⟩⟩
  · simp only [Rp, Zp, fY_toPt]
  · simp only [Rp, gL_toPt]; ring
  · simp only [Zp, gL_toPt]; push_cast; nlinarith


noncomputable def Z0p : Plane := toPt (47040, 33600)

/-- For the chord `[R, Z₀]` (`Z₀` the midpoint of the chain edge `[R, Z]`), whose end is not clamped (no tile interior ahead), a chain edge meets the chord and is not contained in it:
the conclusion of `chain_sum_open_end` is false without `hover`. -/
theorem hover_needed : ∃ e ∈ D.lineChain fY (fY Rp),
    (∃ y, y ∈ (D.tile e.1).edge e.2 ∧ y ∈ segment ℝ Rp Z0p) ∧ ¬ (D.tile e.1).edge e.2 ⊆ segment ℝ Rp Z0p := by
  have h3 := s3pos
  obtain ⟨i, hp⟩ := tile_pts_of_mem tb tb_mem
  have e1 : (D.tile i).pts 1 = Zp := by rw [hp]; rfl
  have e2 : (D.tile i).pts (1 + 1) = Rp := by rw [show (1 : Fin 3) + 1 = 2 from rfl, hp]; rfl
  have hedge : (D.tile i).edge 1 = segment ℝ Zp Rp := by
    unfold Tri.edge; rw [e1, e2]
  refine ⟨(i, 1), ?_, ⟨Rp, ?_, left_mem_segment ℝ _ _⟩, ?_⟩
  · rw [Dissection.mem_lineChain]
    refine ⟨?_, ?_, ?_⟩
    · show fY ((D.tile i).pts 1) = fY Rp
      rw [e1]; simp only [Rp, Zp, fY_toPt]
    · show fY ((D.tile i).pts (1 + 1)) = fY Rp
      rw [e2]
    · intro t
      rw [hp, fY_toPt, show fY Rp = (33600 : ℤ) * Real.sqrt 3 from fY_toPt _]
      fin_cases t <;> simp [tb, vtx] <;> nlinarith
  · show Rp ∈ (D.tile i).edge 1
    rw [hedge]; exact right_mem_segment ℝ _ _
  · intro hsub
    have hZ : Zp ∈ segment ℝ Rp Z0p := hsub (by show Zp ∈ (D.tile i).edge 1; rw [hedge]; exact left_mem_segment ℝ _ _)
    obtain ⟨a', b', ha', hb', hab', h⟩ := hZ
    have := congrArg (fun x : Plane => x 0) h
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Rp, Zp, Z0p, toPt_0] at this
    push_cast at this
    nlinarith

end Erdos634.C2Forward.Wit

#print axioms Erdos634.C2Forward.Wit.chain_open_end_witness
#print axioms Erdos634.C2Forward.Wit.hover_needed
