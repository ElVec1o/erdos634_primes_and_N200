-- Draft/ChainCover.lean -- CHAIN LEMMA, part 3: from the crossing-sum identity of a family of triangles to interior-disjointness
-- and containment in a target triangle.  UNAUDITED.  No sorry.
-- Credit: Ramanujan-rows session (chain lemma, audited SOUND-WITH-FIX 2026-10-19); the AI assistant (integer frame); Beeson-Rosu; Paliy.
import Erdos634.Draft.ChainTri

open scoped Classical Topology
namespace Erdos634.Draft.Chain

/-- a triangle given by its three vertices (to be counter-clockwise, `0 < crs a b c`). -/
structure Tri3 where
  a : ℝ × ℝ
  b : ℝ × ℝ
  c : ℝ × ℝ

theorem continuous_crs (p q : ℝ × ℝ) : Continuous (fun z : ℝ × ℝ => crs p q z) := by unfold crs; fun_prop

namespace Tri3
def pos (t : Tri3) : Prop := 0 < crs t.a t.b t.c
/-- closed triangle -/
def cl (t : Tri3) : Set (ℝ × ℝ) := {z | 0 ≤ crs t.a t.b z ∧ 0 ≤ crs t.b t.c z ∧ 0 ≤ crs t.c t.a z}
/-- open triangle -/
def op (t : Tri3) : Set (ℝ × ℝ) := {z | 0 < crs t.a t.b z ∧ 0 < crs t.b t.c z ∧ 0 < crs t.c t.a z}
/-- crossing sum -/
noncomputable def k (t : Tri3) (z : ℝ × ℝ) : ℤ := kapTri t.a t.b t.c z

theorem good (t : Tri3) (h : t.pos) (z : ℝ × ℝ) : TriGood t.a t.b t.c z := tri_good _ _ _ z h
theorem nonneg (t : Tri3) (h : t.pos) (z : ℝ × ℝ) : 0 ≤ t.k z := (t.good h z).1.1
theorem le_one (t : Tri3) (h : t.pos) (z : ℝ × ℝ) : t.k z ≤ 1 := (t.good h z).1.2
theorem one_of_op (t : Tri3) (h : t.pos) {z : ℝ × ℝ} (hz : z ∈ t.op) : t.k z = 1 := (t.good h z).2.1 hz.1 hz.2.1 hz.2.2
theorem cl_of_ne (t : Tri3) (h : t.pos) {z : ℝ × ℝ} (hz : t.k z ≠ 0) : z ∈ t.cl := (t.good h z).2.2 hz

theorem op_subset_cl (t : Tri3) : t.op ⊆ t.cl := fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩

theorem isClosed_cl (t : Tri3) : IsClosed t.cl := by
  unfold cl
  exact IsClosed.inter (isClosed_le continuous_const (continuous_crs _ _)) (IsClosed.inter (isClosed_le continuous_const (continuous_crs _ _)) (isClosed_le continuous_const (continuous_crs _ _)))

/-- the closed triangle lies in the closure of the open one -/
theorem cl_subset_closure_op (t : Tri3) (h : t.pos) : t.cl ⊆ closure t.op := by
  intro z hz
  set g : ℝ × ℝ := ((t.a.1 + t.b.1 + t.c.1) / 3, (t.a.2 + t.b.2 + t.c.2) / 3) with hg
  let f : ℝ → ℝ × ℝ := fun s => (z.1 + s * (g.1 - z.1), z.2 + s * (g.2 - z.2))
  have hf0 : f 0 = z := by simp [f]
  have hcont : Continuous f := by fun_prop
  have htend : Filter.Tendsto f (𝓝[>] (0:ℝ)) (𝓝 z) := by
    rw [← hf0]; exact tendsto_nhdsWithin_of_tendsto_nhds (hcont.tendsto 0)
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with s hs
  have hD : 0 < crs t.a t.b t.c := h
  have e1 : crs t.a t.b (f s) = (1 - s) * crs t.a t.b z + s * (crs t.a t.b t.c / 3) := by simp only [f, hg, crs]; ring
  have e2 : crs t.b t.c (f s) = (1 - s) * crs t.b t.c z + s * (crs t.a t.b t.c / 3) := by simp only [f, hg, crs]; ring
  have e3 : crs t.c t.a (f s) = (1 - s) * crs t.c t.a z + s * (crs t.a t.b t.c / 3) := by simp only [f, hg, crs]; ring
  obtain ⟨s0, s1⟩ := hs
  have hd3 : 0 < crs t.a t.b t.c / 3 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) hz.1, mul_pos s0 hd3]
  · rw [e2]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) hz.2.1, mul_pos s0 hd3]
  · rw [e3]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) hz.2.2, mul_pos s0 hd3]

theorem isOpen_op (t : Tri3) : IsOpen t.op := by
  unfold op
  exact IsOpen.inter (isOpen_lt continuous_const (continuous_crs _ _)) (IsOpen.inter (isOpen_lt continuous_const (continuous_crs _ _)) (isOpen_lt continuous_const (continuous_crs _ _)))

end Tri3

variable {ι : Type*} [Fintype ι]

/-- **Chain lemma (triangle form).**  If strictly counter-clockwise triangles `P i` and `T` satisfy the crossing-sum identity
`∑ i, κ(P i) = κ(T)` at every point (this is the statement that the boundary chains agree: it follows from antisymmetry and
collinear additivity of `kap`, with no inequality), then the open triangles `P i` are pairwise disjoint, each lies in `T`
(open in closed, hence closed in closed), and the open triangle `T` is covered by the closed `P i`. -/
theorem chain_tri (T : Tri3) (P : ι → Tri3) (hT : T.pos) (hP : ∀ i, (P i).pos)
    (h : ∀ z, ∑ i, (P i).k z = T.k z) :
    (∀ i j, i ≠ j → Disjoint (P i).op (P j).op) ∧ (∀ i, (P i).cl ⊆ T.cl) ∧ (∀ z ∈ T.op, ∃ i, z ∈ (P i).cl) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hi hj
    have h1 := (P i).one_of_op (hP i) hi
    have h2 := (P j).one_of_op (hP j) hj
    have hsub : ∑ x ∈ ({i, j} : Finset ι), (P x).k z ≤ ∑ x, (P x).k z :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => (P x).nonneg (hP x) z)
    rw [Finset.sum_pair hij, h1, h2, h] at hsub
    have := T.le_one hT z
    omega
  · intro i
    have hop : (P i).op ⊆ T.cl := by
      intro z hz
      have h1 := (P i).one_of_op (hP i) hz
      have hsub : (P i).k z ≤ ∑ x, (P x).k z :=
        Finset.single_le_sum (f := fun x => (P x).k z) (fun x _ => (P x).nonneg (hP x) z) (Finset.mem_univ i)
      rw [h] at hsub
      exact T.cl_of_ne hT (by omega)
    intro z hz
    have := (Tri3.cl_subset_closure_op _ (hP i)) hz
    exact (closure_minimal hop T.isClosed_cl) this
  · intro z hz
    have h1 := T.one_of_op hT hz
    have : ∑ i, (P i).k z ≠ 0 := by rw [h, h1]; norm_num
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero this
    exact ⟨i, (P i).cl_of_ne (hP i) hi⟩

end Erdos634.Draft.Chain

#print axioms Erdos634.Draft.Chain.chain_tri
#print axioms Erdos634.Draft.Chain.kap_add
#print axioms Erdos634.Draft.Chain.tri_good
