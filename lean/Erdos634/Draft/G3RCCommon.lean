-- Draft/G3RCCommon.lean. No sorry/native_decide/axioms.
-- Generic layer on top of G3CCert/G3RCAngles for certificates whose model is the 30-60-90 triangle
-- `((0,2),(-2,0),(0,0))` and whose leaves all have opposite squared sides a permutation of (4,12,16):
--  * model angles (1,2,3)·π/6; tile angles; any corner labelling `idx` equals the lattice labelling `midx`;
--  * `fig D idx = latFig c` (corner figures computed on the lattice, decidable);
--  * T-junction witness lemma (midpoint of an edge).
import Erdos634.Draft.G3RCAngles

namespace Erdos634.Draft.G3RCCommon

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.G3RCAngles
  Erdos634.KConj

theorem toPt_inj {p q : LP} (h : toPt p = toPt q) : p = q := by
  have h1 := dist_sq_toPt p q
  rw [h, dist_self] at h1
  have h2 : d2 p q = 0 := by
    have : ((d2 p q : ℤ) : ℝ) = 0 := by rw [← h1]; norm_num
    exact_mod_cast this
  unfold d2 at h2
  have a : (p.1 - q.1) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  have b : (p.2 - q.2) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  exact Prod.ext (by nlinarith [pow_eq_zero_iff (two_ne_zero) |>.mp a]) (by nlinarith [pow_eq_zero_iff (two_ne_zero) |>.mp b])

/-- a lattice point that is the midpoint of the lattice segment `q r` lies in the open real segment -/
theorem toPt_mem_openSegment {p q r : LP} (h1 : p.1 * 2 = q.1 + r.1) (h2 : p.2 * 2 = q.2 + r.2) :
    toPt p ∈ openSegment ℝ (toPt q) (toPt r) := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  have e1 : (p.1 : ℝ) * 2 = q.1 + r.1 := by exact_mod_cast h1
  have e2 : (p.2 : ℝ) * 2 = q.2 + r.2 := by exact_mod_cast h2
  have e3 : (p.2 : ℝ) * Real.sqrt 3 * 2 = q.2 * Real.sqrt 3 + r.2 * Real.sqrt 3 := by
    rw [mul_right_comm, e2]; ring
  unfold toPt rx ry
  ext i; fin_cases i <;> simp [Erdos634.CertCoord.mkPt] <;> linarith

/-- corner figures on the lattice -/
def latFig (c : Cert) (j l : Fin 3) : ℕ :=
  (Finset.univ.filter (fun p : Fin c.leaves.length × Fin 3 =>
    vtx (c.leaves.get p.1) p.2 = vtx c.target j ∧ midx (c.leaves.get p.1) p.2 = l)).card

section generic
variable (c : Cert) (hc : c.ok = true)

theorem tile_eq (i : Fin c.leaves.length) :
    (cd c hc).tile i = triOf (c.leaves.get i) (pos_of_mem hc (List.get_mem _ _)) := rfl

theorem model_angles (hgM : goodT c.model) (hmid : ∀ k, midx c.model k = k) (k : Fin 3) :
    (cd c hc).model.angleAt k = (![1, 2, 3] : Fin 3 → ℕ) k * Real.pi / (6 : ℕ) := by
  rw [cd_model, tile_angle _ _ hgM, hmid]

theorem hidx_lat (hg : ∀ t ∈ c.leaves, goodT t) (i : Fin c.leaves.length) (v : Fin 3) :
    ((cd c hc).tile i).angleAt v =
      (![1, 2, 3] : Fin 3 → ℕ) (midx (c.leaves.get i) v) * Real.pi / (6 : ℕ) := by
  rw [tile_eq]; exact tile_angle _ _ (hg _ (List.get_mem _ _)) v

theorem idx_eq (hg : ∀ t ∈ c.leaves, goodT t) (idx : Fin c.leaves.length → Equiv.Perm (Fin 3))
    (hidx : ∀ i v, ((cd c hc).tile i).angleAt v = (![1, 2, 3] : Fin 3 → ℕ) (idx i v) * Real.pi / (6 : ℕ))
    (i : Fin c.leaves.length) (v : Fin 3) : idx i v = midx (c.leaves.get i) v := by
  have h := (hidx i v).symm.trans (hidx_lat c hc hg i v)
  have hp : (0 : ℝ) < Real.pi / 6 := by positivity
  have h' : ((![1, 2, 3] : Fin 3 → ℕ) (idx i v) : ℝ) = ((![1, 2, 3] : Fin 3 → ℕ) (midx (c.leaves.get i) v) : ℝ) := by
    have : ((![1, 2, 3] : Fin 3 → ℕ) (idx i v) : ℝ) * (Real.pi / 6)
        = ((![1, 2, 3] : Fin 3 → ℕ) (midx (c.leaves.get i) v) : ℝ) * (Real.pi / 6) := by
      push_cast at h; linarith
    exact mul_right_cancel₀ hp.ne' this
  have h'' : (![1, 2, 3] : Fin 3 → ℕ) (idx i v) = (![1, 2, 3] : Fin 3 → ℕ) (midx (c.leaves.get i) v) := by
    exact_mod_cast h'
  generalize idx i v = x at h''
  generalize midx (c.leaves.get i) v = y at h''
  revert x y; decide

theorem fig_eq (hg : ∀ t ∈ c.leaves, goodT t) (idx : Fin c.leaves.length → Equiv.Perm (Fin 3))
    (hidx : ∀ i v, ((cd c hc).tile i).angleAt v = (![1, 2, 3] : Fin 3 → ℕ) (idx i v) * Real.pi / (6 : ℕ))
    (j l : Fin 3) : fig (cd c hc) idx j l = latFig c j l := by
  unfold fig latFig
  congr 1
  apply Finset.filter_congr
  intro p _
  rw [idx_eq c hc hg idx hidx p.1 p.2, tile_eq, cd_target]
  rw [triOf_pts, triOf_pts]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨toPt_inj h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by rw [h1], h2⟩

theorem tjunction (i j : Fin c.leaves.length) (v m : Fin 3)
    (h1 : (vtx (c.leaves.get i) v).1 * 2 = (vtx (c.leaves.get j) m).1 + (vtx (c.leaves.get j) (m + 1)).1)
    (h2 : (vtx (c.leaves.get i) v).2 * 2 = (vtx (c.leaves.get j) m).2 + (vtx (c.leaves.get j) (m + 1)).2) :
    ((cd c hc).tile i).pts v ∈ openSegment ℝ (((cd c hc).tile j).pts m) (((cd c hc).tile j).pts (m + 1)) := by
  rw [tile_eq, tile_eq, triOf_pts, triOf_pts, triOf_pts]
  exact toPt_mem_openSegment h1 h2

end generic

end Erdos634.Draft.G3RCCommon
