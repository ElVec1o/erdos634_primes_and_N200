-- Draft/ThetaNotchBase.lean -- generic tools for the NOTCH SEED family: lattice parallelogram families, joins of families,
-- the apex-unit frame `cH`.  INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
**Theorem N (notch seed family)**, formalisation, layer 0.  Credit: Paliy (annulus / band steps on a seed; the 48-tile seed
for the tile `(2,3,4)` is Beeson's), Laczkovich (classification, Lemma 2.2), Zhang (the families), Beeson-Rosu (skew frame),
the project (`ThetaUnit*`, `LadderFam`).  The hand proof is `internal working notes` section 2.1; the
exact generator `rust/audit_notch_20261114` is the specification of the pieces.

This file: (1) the closed parallelogram `Par a v1 v2 p q = a + [0,p] v1 + [0,q] v2` in skew coordinates and the tile family
`parFam` of its `2 p q` lattice cells (needs `|v1|, |v2|, |v1-v2|` to be the three sides of the tile); (2) `TFam.join`, the union of
a finite family of tile families with pairwise interior-disjoint regions; (3) the APEX-UNIT FRAME: a point `(x,y)` of the
apex frame of `theta_t` (`theta_t = {x,y >= 0, x+y <= t}`, legs along the axes) is the point `cH (x,y) = (f b (s-x-y), e b x)`
of the skew frame `Phi_phi`, `phi = f/e`; this is the frame of the `ThetaUnit` pieces at the base vertex `(0,s)`.
INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaUnitStep

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.LadderFam Erdos634.Draft.CollarFam
open Erdos634.Draft.S2L (baseTri tri_eq_of_pts)
open Erdos634.Subdivision

/-! ### the closed parallelogram -/

/-- `a + [0,p] v1 + [0,q] v2` -/
def Par (a v1 v2 : ℝ × ℝ) (p q : ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ α β : ℝ, 0 ≤ α ∧ α ≤ p ∧ 0 ≤ β ∧ β ≤ q ∧ x = a + α • v1 + β • v2}

theorem Par_convex (a v1 v2 : ℝ × ℝ) (p q : ℝ) : Convex ℝ (Par a v1 v2 p q) := by
  rintro x ⟨α, β, hα, hα', hβ, hβ', rfl⟩ y ⟨α', β', hα2, hα2', hβ2, hβ2', rfl⟩ s t hs ht hst
  have ht' : t = 1 - s := by linarith
  subst ht'
  refine ⟨s * α + (1 - s) * α', s * β + (1 - s) * β', by positivity, ?_, by positivity, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hα' hs, mul_le_mul_of_nonneg_left hα2' ht]
  · nlinarith [mul_le_mul_of_nonneg_left hβ' hs, mul_le_mul_of_nonneg_left hβ2' ht]
  · ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- linear bound on the parallelogram from its four corners -/
theorem Par_le (a v1 v2 : ℝ × ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (u w c : ℝ)
    (h00 : u * a.1 + w * a.2 ≤ c)
    (h10 : u * (a + p • v1).1 + w * (a + p • v1).2 ≤ c)
    (h01 : u * (a + q • v2).1 + w * (a + q • v2).2 ≤ c)
    (h11 : u * (a + p • v1 + q • v2).1 + w * (a + p • v1 + q • v2).2 ≤ c) :
    ∀ x ∈ Par a v1 v2 p q, u * x.1 + w * x.2 ≤ c := by
  rintro x ⟨α, β, hα, hα', hβ, hβ', rfl⟩
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
  obtain ⟨r, hr⟩ : ∃ r, α = r * p := ⟨α / p, by field_simp⟩
  obtain ⟨s, hs⟩ : ∃ s, β = s * q := ⟨β / q, by field_simp⟩
  have hr0 : 0 ≤ r := by rw [hr] at hα; exact nonneg_of_mul_nonneg_left hα hp
  have hs0 : 0 ≤ s := by rw [hs] at hβ; exact nonneg_of_mul_nonneg_left hβ hq
  have hr1 : r ≤ 1 := by rw [hr] at hα'; nlinarith
  have hs1 : s ≤ 1 := by rw [hs] at hβ'; nlinarith
  subst hr; subst hs
  have e1 := mul_nonneg (mul_nonneg hr0 hs0) (sub_nonneg.2 h11)
  have e2 := mul_nonneg (mul_nonneg hr0 (sub_nonneg.2 hs1)) (sub_nonneg.2 h10)
  have e3 := mul_nonneg (mul_nonneg (sub_nonneg.2 hr1) hs0) (sub_nonneg.2 h01)
  have e4 := mul_nonneg (mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hs1)) (sub_nonneg.2 h00)
  nlinarith [e1, e2, e3, e4]

theorem P_par (f : ℝ) (a v1 v2 : ℝ × ℝ) (i j : ℕ) :
    P (Phi f a) (Phi f (a + v1)) (Phi f (a + v2)) i j = Phi f (a + (i : ℝ) • v1 + (j : ℝ) • v2) := by
  unfold P
  rw [← PhiL_eq, ← PhiL_eq, ← PhiL_eq, ← PhiL_eq]
  simp only [map_add, map_smul, map_sub]
  module

/-- **The lattice parallelogram family**: the `2 p q` cells of the lattice `a + i v1 + j v2` inside `Par a v1 v2 p q`
(each cell is cut by the diagonal `v1 - v2`); congruent to `M` as soon as the cell `a, a+v1, a+v2` is. -/
noncomputable def parFam (f : ℝ) (hf : 1 < f) (a v1 v2 : ℝ × ℝ) (p q : ℕ)
    (h : ((a + v1).1 - a.1) * ((a + v2).2 - a.2) - ((a + v2).1 - a.1) * ((a + v1).2 - a.2) ≠ 0) (M : Erdos634.Geometry.Tri)
    (hc : (triC f hf a (a + v1) (a + v2) h).Congruent M) :
    TFam (Phi f '' Par a v1 v2 (p : ℝ) (q : ℝ)) M (2 * p * q) := by
  have hind : AffineIndependent ℝ ![Phi f a, Phi f (a + v1), Phi f (a + v2)] := by
    have := (triC f hf a (a + v1) (a + v2) h).indep
    simpa only [triC_pts] using this
  have hbase : (⟨![Phi f a, Phi f (a + v1), Phi f (a + v2)], hind⟩ : Erdos634.Geometry.Tri) = triC f hf a (a + v1) (a + v2) h :=
    tri_eq_of_pts (by simp only [triC_pts])
  have hRconv : Convex ℝ (Phi f '' Par a v1 v2 (p : ℝ) (q : ℝ)) :=
    (Par_convex a v1 v2 _ _).linear_image (PhiL f)
  let Cs : Finset (Bool × ℕ × ℕ) := Finset.univ ×ˢ (Finset.range p ×ˢ Finset.range q)
  have hcard : Cs.card = 2 * p * q := by
    simp only [Cs, Finset.card_product, Finset.card_univ, Fintype.card_bool, Finset.card_range]; ring
  let e : Fin (2 * p * q) ≃ Cs := (finCongr hcard.symm).trans Cs.equivFin.symm
  have key : ∀ i j : ℕ, i ≤ p → j ≤ q →
      P (Phi f a) (Phi f (a + v1)) (Phi f (a + v2)) i j ∈ Phi f '' Par a v1 v2 (p : ℝ) (q : ℝ) := by
    intro i j hi hj
    rw [P_par]
    exact ⟨_, ⟨(i : ℝ), (j : ℝ), by positivity, by exact_mod_cast hi, by positivity, by exact_mod_cast hj, rfl⟩, rfl⟩
  refine { tile := fun n => cellOf _ _ _ hind ((e n : Bool × ℕ × ℕ)), sub := ?_, disj := ?_, cong := ?_ }
  · intro n
    obtain ⟨⟨t, i, j⟩, hp⟩ := e n
    simp only [Cs, Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and] at hp
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
  · intro n m hnm
    exact cellOf_disjoint _ _ _ hind _ _ (fun h => hnm (e.injective (Subtype.ext h)))
  · intro n
    obtain ⟨⟨t, i, j⟩, hp⟩ := e n
    rcases t <;> simp only [cellOf, Bool.false_eq_true, if_false, if_true]
    · exact ((cellDown_congruent _ _ _ hind i j).symm.trans (by rw [hbase]; exact hc))
    · exact ((cellUp_congruent _ _ _ hind i j).symm.trans (by rw [hbase]; exact hc))

/-! ### joins -/

open MeasureTheory in
/-- Join of finitely many tile families with pairwise interior-disjoint regions, all inside `S`. -/
noncomputable def TFam.join {m : ℕ} {M : Erdos634.Geometry.Tri} (S : Set Plane) (Sa : Fin m → Set Plane) (n : Fin m → ℕ)
    (R : ∀ a, TFam (Sa a) M (n a)) (hSa : ∀ a, Sa a ⊆ S)
    (hd : ∀ a b, a ≠ b → Disjoint (interior (Sa a)) (interior (Sa b))) : TFam S M (∑ a, n a) := by
  classical
  refine
    { tile := fun e => (R (finSigmaFinEquiv.symm e).1).tile (finSigmaFinEquiv.symm e).2
      sub := fun e => ((R _).sub _).trans (hSa _)
      disj := ?_
      cong := fun e => (R _).cong _ }
  have key : ∀ (p q : (a : Fin m) × Fin (n a)), p ≠ q →
      Disjoint (interior ((R p.1).tile p.2).carrier) (interior ((R q.1).tile q.2).carrier) := by
    rintro ⟨a, x⟩ ⟨b, y⟩ hne
    by_cases hab : a = b
    · subst hab
      have : x ≠ y := fun h => hne (by rw [h])
      exact (R a).disj this
    · exact (hd a b hab).mono (interior_mono ((R a).sub x)) (interior_mono ((R b).sub y))
  intro i j hij
  exact key _ _ (fun h => hij (finSigmaFinEquiv.symm.injective h))

end

end Erdos634.Draft.ThetaNotch
