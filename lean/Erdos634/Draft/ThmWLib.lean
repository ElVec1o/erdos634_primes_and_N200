-- Draft/ThmWLib.lean — generic infrastructure for Theorem W (six-piece template W_M(e,f), all 2 <= e <= f-2).  UNAUDITED.
-- No sorry, no native_decide.  Parallelogram family `parFam` (cells of the Subdivision lattice inside a lattice parallelogram),
-- `preg_le_named` / `pgm_le` (half-plane bounds from named vertex values), target membership `memT`.
-- Credit: Paliy (W/beta framework), Beeson-Rosu (S2L skew frame), our template engine `bto` (template discovery);
-- builds on LadderFam / CollarLayerLib of this project.
import Erdos634.Draft.LadderFam
import Erdos634.Draft.CollarLayerLib

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.ThmW
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.LadderFam Erdos634.Subdivision
open Erdos634.Draft.CollarLayer (preg_le preg_ge mem_tri_iso)

/-- half-plane bound on a trapezoid region from named vertex values -/
theorem preg_le_named (a V1 V2 c1 c2 : ℝ × ℝ) (σ u w c : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (e1 : a.1 + σ * (V1.1 - a.1) = c1.1) (e2 : a.2 + σ * (V1.2 - a.2) = c1.2)
    (e3 : a.1 + σ * (V2.1 - a.1) = c2.1) (e4 : a.2 + σ * (V2.2 - a.2) = c2.2)
    (h1 : u * c1.1 + w * c1.2 ≤ c) (h2 : u * c2.1 + w * c2.2 ≤ c)
    (h3 : u * V1.1 + w * V1.2 ≤ c) (h4 : u * V2.1 + w * V2.2 ≤ c) :
    ∀ p ∈ Preg a V1 V2 σ, u * p.1 + w * p.2 ≤ c := by
  refine preg_le a V1 V2 σ u w c hσ0 hσ1 ?_ ?_ h3 h4
  · rw [e1, e2]; exact h1
  · rw [e3, e4]; exact h2

theorem preg_ge_named (a V1 V2 c1 c2 : ℝ × ℝ) (σ u w c : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (e1 : a.1 + σ * (V1.1 - a.1) = c1.1) (e2 : a.2 + σ * (V1.2 - a.2) = c1.2)
    (e3 : a.1 + σ * (V2.1 - a.1) = c2.1) (e4 : a.2 + σ * (V2.2 - a.2) = c2.2)
    (h1 : c ≤ u * c1.1 + w * c1.2) (h2 : c ≤ u * c2.1 + w * c2.2)
    (h3 : c ≤ u * V1.1 + w * V1.2) (h4 : c ≤ u * V2.1 + w * V2.2) :
    ∀ p ∈ Preg a V1 V2 σ, c ≤ u * p.1 + w * p.2 := by
  refine preg_ge a V1 V2 σ u w c hσ0 hσ1 ?_ ?_ h3 h4
  · rw [e1, e2]; exact h1
  · rw [e3, e4]; exact h2

/-- the lattice parallelogram `{a + α d1 + β d2 | 0 ≤ α ≤ s, 0 ≤ β ≤ x}` (steps `V1 - a`, `V2 - a`) -/
def Pgm (a V1 V2 : ℝ × ℝ) (s x : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ α β : ℝ, 0 ≤ α ∧ α ≤ s ∧ 0 ≤ β ∧ β ≤ x ∧ p = a + α • (V1 - a) + β • (V2 - a)}

theorem Pgm_convex (a V1 V2 : ℝ × ℝ) (s x : ℝ) : Convex ℝ (Pgm a V1 V2 s x) := by
  rintro p ⟨α, β, h1, h2, h3, h4, rfl⟩ p' ⟨α', β', h1', h2', h3', h4', rfl⟩ m n hm hn hmn
  have hn' : n = 1 - m := by linarith
  subst hn'
  refine ⟨m * α + (1 - m) * α', m * β + (1 - m) * β', by positivity, ?_, by positivity, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left h2 hm, mul_le_mul_of_nonneg_left h2' hn]
  · nlinarith [mul_le_mul_of_nonneg_left h4 hm, mul_le_mul_of_nonneg_left h4' hn]
  · ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub] <;> ring

/-- half-plane bound on a lattice parallelogram from the four corner values -/
theorem pgm_le (a V1 V2 p10 p01 p11 : ℝ × ℝ) (s x u w c : ℝ) (hs : 0 ≤ s) (hx : 0 ≤ x)
    (e10 : a + s • (V1 - a) = p10) (e01 : a + x • (V2 - a) = p01)
    (e11 : a + s • (V1 - a) + x • (V2 - a) = p11)
    (h00 : u * a.1 + w * a.2 ≤ c) (h10 : u * p10.1 + w * p10.2 ≤ c)
    (h01 : u * p01.1 + w * p01.2 ≤ c) (h11 : u * p11.1 + w * p11.2 ≤ c) :
    ∀ p ∈ Pgm a V1 V2 s x, u * p.1 + w * p.2 ≤ c := by
  rintro p ⟨α, β, h1, h2, h3, h4, rfl⟩
  subst e10 e01 e11
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub] at h10 h01 h11 ⊢
  set l1 := u * (V1.1 - a.1) + w * (V1.2 - a.2) with hl1
  set l2 := u * (V2.1 - a.1) + w * (V2.2 - a.2) with hl2
  set la := u * a.1 + w * a.2 with hla
  have g10 : la + s * l1 ≤ c := by simp only [hla, hl1]; nlinarith
  have g01 : la + x * l2 ≤ c := by simp only [hla, hl2]; nlinarith
  have g11 : la + s * l1 + x * l2 ≤ c := by simp only [hla, hl1, hl2]; nlinarith
  have e : u * (a.1 + α * (V1.1 - a.1) + β * (V2.1 - a.1)) + w * (a.2 + α * (V1.2 - a.2) + β * (V2.2 - a.2))
      = la + α * l1 + β * l2 := by simp only [hla, hl1, hl2]; ring
  rw [e]
  have A1 : α * l1 ≤ max 0 (s * l1) := by
    rcases le_total 0 l1 with h | h
    · exact le_trans (by nlinarith) (le_max_right _ _)
    · exact le_trans (by nlinarith) (le_max_left _ _)
  have A2 : β * l2 ≤ max 0 (x * l2) := by
    rcases le_total 0 l2 with h | h
    · exact le_trans (by nlinarith) (le_max_right _ _)
    · exact le_trans (by nlinarith) (le_max_left _ _)
  have h00' : la ≤ c := h00
  rcases max_cases 0 (s * l1) with ⟨m1, _⟩ | ⟨m1, _⟩ <;> rcases max_cases 0 (x * l2) with ⟨m2, _⟩ | ⟨m2, _⟩ <;>
    rw [m1] at A1 <;> rw [m2] at A2 <;> linarith

theorem pgm_ge (a V1 V2 p10 p01 p11 : ℝ × ℝ) (s x u w c : ℝ) (hs : 0 ≤ s) (hx : 0 ≤ x)
    (e10 : a + s • (V1 - a) = p10) (e01 : a + x • (V2 - a) = p01)
    (e11 : a + s • (V1 - a) + x • (V2 - a) = p11)
    (h00 : c ≤ u * a.1 + w * a.2) (h10 : c ≤ u * p10.1 + w * p10.2)
    (h01 : c ≤ u * p01.1 + w * p01.2) (h11 : c ≤ u * p11.1 + w * p11.2) :
    ∀ p ∈ Pgm a V1 V2 s x, c ≤ u * p.1 + w * p.2 := by
  intro p hp
  have := pgm_le a V1 V2 p10 p01 p11 s x (-u) (-w) (-c) hs hx e10 e01 e11 (by linarith) (by linarith) (by linarith)
    (by linarith) p hp
  linarith

/-- lattice points of the parallelogram lie in the (image) region -/
theorem P_eq1 {f : ℝ} (a V1 V2 : ℝ × ℝ) (i j : ℕ) :
    P (Phi f a) (Phi f V1) (Phi f V2) i j = Phi f (a + (i : ℝ) • (V1 - a) + (j : ℝ) • (V2 - a)) := by
  unfold P
  rw [← PhiL_eq, ← PhiL_eq, ← PhiL_eq, ← PhiL_eq]
  simp only [map_add, map_smul, map_sub]

theorem cell_subP {f : ℝ} (a V1 V2 : ℝ × ℝ) (s x : ℕ)
    (hind : AffineIndependent ℝ ![Phi f a, Phi f V1, Phi f V2])
    (t : Bool) (i j : ℕ) (hi : i < s) (hj : j < x) :
    (cellOf _ _ _ hind (t, i, j)).carrier ⊆ Phi f '' Pgm a V1 V2 (s : ℝ) (x : ℝ) := by
  have hRconv : Convex ℝ (Phi f '' Pgm a V1 V2 (s : ℝ) (x : ℝ)) :=
    (Pgm_convex a V1 V2 _ _).linear_image (PhiL f)
  have key : ∀ i' j' : ℕ, i' ≤ s → j' ≤ x →
      P (Phi f a) (Phi f V1) (Phi f V2) i' j' ∈ Phi f '' Pgm a V1 V2 (s : ℝ) (x : ℝ) := by
    intro i' j' h1 h2
    rw [P_eq1]
    exact ⟨_, ⟨(i' : ℝ), (j' : ℝ), by positivity, by exact_mod_cast h1, by positivity, by exact_mod_cast h2, rfl⟩, rfl⟩
  cases t
  · simp only [cellOf, Bool.false_eq_true, if_false]
    show convexHull ℝ (Set.range (cellDown _ _ _ hind i j).pts) ⊆ _
    refine convexHull_min ?_ hRconv
    rintro _ ⟨m, rfl⟩
    fin_cases m
    · exact key (i + 1) j (by omega) (by omega)
    · exact key i (j + 1) (by omega) (by omega)
    · exact key (i + 1) (j + 1) (by omega) (by omega)
  · simp only [cellOf, if_true]
    show convexHull ℝ (Set.range (cellUp _ _ _ hind i j).pts) ⊆ _
    refine convexHull_min ?_ hRconv
    rintro _ ⟨m, rfl⟩
    fin_cases m
    · exact key i j (by omega) (by omega)
    · exact key (i + 1) j (by omega) (by omega)
    · exact key i (j + 1) (by omega) (by omega)

theorem card_parIdx (s x : ℕ) :
    ((Finset.univ : Finset Bool) ×ˢ (Finset.range s ×ˢ Finset.range x)).card = 2 * s * x := by
  simp [Finset.card_product]; ring

/-- **Parallelogram family.**  The `2 s x` cells of the lattice `(a; V1-a, V2-a)` inside the lattice parallelogram. -/
noncomputable def parFam (f : ℝ) (hf : 1 < f) (a V1 V2 : ℝ × ℝ) (s x : ℕ)
    (h : (V1.1 - a.1) * (V2.2 - a.2) - (V2.1 - a.1) * (V1.2 - a.2) ≠ 0) (M : Tri)
    (hc : (triC f hf a V1 V2 h).Congruent M) :
    TFam (Phi f '' Pgm a V1 V2 (s : ℝ) (x : ℝ)) M (2 * s * x) := by
  have hind : AffineIndependent ℝ ![Phi f a, Phi f V1, Phi f V2] := by
    have := (triC f hf a V1 V2 h).indep
    simpa only [triC_pts] using this
  have hbase : (⟨![Phi f a, Phi f V1, Phi f V2], hind⟩ : Tri) = triC f hf a V1 V2 h :=
    Erdos634.Draft.S2L.tri_eq_of_pts (by simp only [triC_pts])
  let S : Finset (Bool × ℕ × ℕ) := (Finset.univ : Finset Bool) ×ˢ (Finset.range s ×ˢ Finset.range x)
  let e : Fin (2 * s * x) ≃ S := (finCongr (card_parIdx s x).symm).trans S.equivFin.symm
  refine { tile := fun n => cellOf _ _ _ hind ((e n : Bool × ℕ × ℕ)), sub := ?_, disj := ?_, cong := ?_ }
  · intro n
    obtain ⟨⟨t, i, j⟩, hp⟩ := e n
    simp only [S, Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and] at hp
    exact cell_subP a V1 V2 s x hind t i j hp.1 hp.2
  · intro n m hnm
    exact cellOf_disjoint _ _ _ hind _ _ (fun h => hnm (e.injective (Subtype.ext h)))
  · intro n
    obtain ⟨⟨t, i, j⟩, hp⟩ := e n
    rcases t <;> simp only [cellOf, Bool.false_eq_true, if_false, if_true]
    · exact ((cellDown_congruent _ _ _ hind i j).symm.trans (by rw [hbase]; exact hc))
    · exact ((cellUp_congruent _ _ _ hind i j).symm.trans (by rw [hbase]; exact hc))

/-- membership in the target triangle `(0,0),(B,0),(xA,yA)` with the two slanted conditions scaled by `f > 0` -/
theorem memT {f B xA yA X Y : ℝ} (hf : 0 < f) (hB : 0 < B) (hy : 0 < yA) (h1 : 0 ≤ Y)
    (h2 : 0 ≤ f * (yA * X - xA * Y)) (h3 : 0 ≤ f * (yA * (B - X) - (B - xA) * Y)) :
    (X, Y) ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (B, 0), (xA, yA)} : Set (ℝ × ℝ)) :=
  mem_tri_iso hB hy h1 (nonneg_of_mul_nonneg_right h2 hf) (nonneg_of_mul_nonneg_right h3 hf)

end Erdos634.Draft.ThmW
