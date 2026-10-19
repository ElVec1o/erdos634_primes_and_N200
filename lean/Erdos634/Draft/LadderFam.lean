-- Draft/LadderFam.lean — generic "ladder subfamily" tiling of a triangle or a trapezoid in the skew frame Φ_f.
-- Statement-match audited internally (2026-10-19); no outside reader.  Built for TileCount 11625.  No sorry, no native_decide.
--
-- For a scale-`k` triangle `a,V1,V2` (skew coordinates) whose base tile is congruent to a model `M`, and `sp ≤ k`:
-- the cells of `Subdivision.cellOf` indexed by `cellSet k \ cellSet sp` form `k² - sp²` tiles congruent to `M`,
-- pairwise interior-disjoint, all inside the region `Φ_f '' Preg a V1 V2 (sp/k)` (the triangle itself for `sp = 0`,
-- the trapezoid `T(k) \ T(sp)` otherwise).  This is the trapezoid analogue of `S2L.scaledRT` (= `ladderDissection`
-- in skew coordinates); no covering statement is claimed (the covering is derived downstream by area).
-- Ingredients credited: Subdivision/CellCoord ladder (project), S2L layer (Beeson III Thm 10 reconstruction).
import Erdos634.Draft.S2LCore

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.LadderFam
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.S2L (baseTri)
open Erdos634.Subdivision

/-- Tiles in a region: containment, disjoint interiors, congruence (no covering). -/
structure TFam (S : Set Plane) (M : Tri) (n : ℕ) where
  tile : Fin n → Tri
  sub : ∀ i, (tile i).carrier ⊆ S
  disj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)
  cong : ∀ i, (tile i).Congruent M

/-- The region `{a + α(V1-a) + β(V2-a) | α,β ≥ 0, σ ≤ α+β ≤ 1}`. -/
def Preg (a V1 V2 : ℝ × ℝ) (σ : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ σ ≤ α + β ∧ α + β ≤ 1 ∧ p = a + α • (V1 - a) + β • (V2 - a)}

theorem Preg_convex (a V1 V2 : ℝ × ℝ) (σ : ℝ) : Convex ℝ (Preg a V1 V2 σ) := by
  rintro x ⟨α, β, hα, hβ, h1, h2, rfl⟩ y ⟨α', β', hα', hβ', h1', h2', rfl⟩ s t hs ht hst
  have ht' : t = 1 - s := by linarith
  subst ht'
  refine ⟨s * α + (1 - s) * α', s * β + (1 - s) * β', by positivity, by positivity, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h1' ht]
  · nlinarith [mul_le_mul_of_nonneg_left h2 hs, mul_le_mul_of_nonneg_left h2' ht]
  · ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub] <;> ring

theorem mem_cellSet {k : ℕ} {t : Bool} {i j : ℕ} :
    (t, i, j) ∈ cellSet k ↔ (t = true ∧ i + j + 1 ≤ k) ∨ (t = false ∧ i + j + 2 ≤ k) := by
  simp only [cellSet, Finset.mem_union, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro (⟨q, hq, h1, h2⟩ | ⟨q, hq, h1, h2⟩)
    · subst h2; subst h1
      exact Or.inl ⟨rfl, mem_upSet.mp hq⟩
    · subst h2; subst h1
      exact Or.inr ⟨rfl, mem_downSet.mp hq⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact Or.inl ⟨(i, j), mem_upSet.mpr h, rfl, rfl⟩
    · exact Or.inr ⟨(i, j), mem_downSet.mpr h, rfl, rfl⟩

theorem cellSet_mono {sp k : ℕ} (h : sp ≤ k) : cellSet sp ⊆ cellSet k := by
  rintro ⟨t, i, j⟩ hp
  rw [mem_cellSet] at hp ⊢
  cases t <;> simp at hp ⊢ <;> omega

theorem card_ladder (k sp : ℕ) (h : sp ≤ k) : (cellSet k \ cellSet sp).card = k * k - sp * sp := by
  rw [Finset.card_sdiff_of_subset (cellSet_mono h), card_cellSet, card_cellSet]

/-- A lattice point of the ladder lies in the region. -/
theorem lattice_mem {f : ℝ} (a V1 V2 : ℝ × ℝ) (k sp i j : ℕ) (hk : 0 < k)
    (h1 : sp ≤ i + j) (h2 : i + j ≤ k) :
    Phi f (a + ((i : ℝ) / k) • (V1 - a) + ((j : ℝ) / k) • (V2 - a)) ∈
      Phi f '' Preg a V1 V2 ((sp : ℝ) / k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨_, ⟨(i : ℝ) / k, (j : ℝ) / k, by positivity, by positivity, ?_, ?_, rfl⟩, rfl⟩
  · rw [← add_div]; exact div_le_div_of_nonneg_right (by exact_mod_cast h1) hk'.le
  · rw [← add_div, div_le_one hk']; exact_mod_cast h2

theorem P_eq {f : ℝ} (a V1 V2 : ℝ × ℝ) (k : ℕ) (hk : 0 < k) (i j : ℕ) :
    P (Phi f a) (Phi f (a + (1 / (k : ℝ)) • (V1 - a))) (Phi f (a + (1 / (k : ℝ)) • (V2 - a))) i j
      = Phi f (a + ((i : ℝ) / k) • (V1 - a) + ((j : ℝ) / k) • (V2 - a)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold P
  rw [← PhiL_eq, ← PhiL_eq, ← PhiL_eq, ← PhiL_eq]
  simp only [map_add, map_smul, map_sub]
  have e1 : ((i : ℝ) / k) = (i : ℝ) * (1 / k) := by ring
  have e2 : ((j : ℝ) / k) = (j : ℝ) * (1 / k) := by ring
  rw [e1, e2]
  module



open Erdos634.Draft.S2L (tri_eq_of_pts)

theorem cell_sub {f : ℝ} (a V1 V2 : ℝ × ℝ) (k sp : ℕ) (hk : 0 < k)
    (hind : AffineIndependent ℝ ![Phi f a, Phi f (a + (1 / (k : ℝ)) • (V1 - a)),
      Phi f (a + (1 / (k : ℝ)) • (V2 - a))])
    (t : Bool) (i j : ℕ) (hp : (t, i, j) ∈ cellSet k) (hq : (t, i, j) ∉ cellSet sp) :
    (cellOf _ _ _ hind (t, i, j)).carrier ⊆ Phi f '' Preg a V1 V2 ((sp : ℝ) / k) := by
  have hRconv : Convex ℝ (Phi f '' Preg a V1 V2 ((sp : ℝ) / k)) :=
    (Preg_convex a V1 V2 _).linear_image (PhiL f)
  rw [mem_cellSet] at hp
  rw [mem_cellSet] at hq
  have key : ∀ i' j' : ℕ, sp ≤ i' + j' → i' + j' ≤ k →
      P (Phi f a) (Phi f (a + (1 / (k : ℝ)) • (V1 - a))) (Phi f (a + (1 / (k : ℝ)) • (V2 - a))) i' j'
        ∈ Phi f '' Preg a V1 V2 ((sp : ℝ) / k) := by
    intro i' j' h1 h2
    rw [P_eq a V1 V2 k hk]
    exact lattice_mem a V1 V2 k sp i' j' hk h1 h2
  cases t
  · simp only [cellOf, Bool.false_eq_true, if_false]
    show convexHull ℝ (Set.range (cellDown _ _ _ hind i j).pts) ⊆ _
    refine convexHull_min ?_ hRconv
    rintro _ ⟨m, rfl⟩
    simp at hp hq
    fin_cases m
    · exact key (i + 1) j (by omega) (by omega)
    · exact key i (j + 1) (by omega) (by omega)
    · exact key (i + 1) (j + 1) (by omega) (by omega)
  · simp only [cellOf, if_true]
    show convexHull ℝ (Set.range (cellUp _ _ _ hind i j).pts) ⊆ _
    refine convexHull_min ?_ hRconv
    rintro _ ⟨m, rfl⟩
    simp at hp hq
    fin_cases m
    · exact key i j (by omega) (by omega)
    · exact key (i + 1) j (by omega) (by omega)
    · exact key i (j + 1) (by omega) (by omega)

noncomputable def ladderFam (f : ℝ) (hf : 1 < f) (a V1 V2 : ℝ × ℝ) (k sp : ℕ) (hk : 0 < k) (hsp : sp ≤ k)
    (h : (V1.1 - a.1) * (V2.2 - a.2) - (V2.1 - a.1) * (V1.2 - a.2) ≠ 0) (M : Tri)
    (hc : (baseTri f hf a V1 V2 k hk h).Congruent M) :
    TFam (Phi f '' Preg a V1 V2 ((sp : ℝ) / k)) M (k * k - sp * sp) := by
  have hind : AffineIndependent ℝ ![Phi f a, Phi f (a + (1 / (k : ℝ)) • (V1 - a)),
      Phi f (a + (1 / (k : ℝ)) • (V2 - a))] := by
    have := (baseTri f hf a V1 V2 k hk h).indep
    simpa only [baseTri, triC_pts] using this
  have hbase : (⟨![Phi f a, Phi f (a + (1 / (k : ℝ)) • (V1 - a)),
      Phi f (a + (1 / (k : ℝ)) • (V2 - a))], hind⟩ : Tri) = baseTri f hf a V1 V2 k hk h :=
    tri_eq_of_pts (by simp only [baseTri, triC_pts])
  let e : Fin (k * k - sp * sp) ≃ (cellSet k \ cellSet sp : Finset (Bool × ℕ × ℕ)) :=
    (finCongr (card_ladder k sp hsp).symm).trans (cellSet k \ cellSet sp).equivFin.symm
  refine { tile := fun n => cellOf _ _ _ hind ((e n : Bool × ℕ × ℕ)), sub := ?_, disj := ?_, cong := ?_ }
  · intro n
    obtain ⟨⟨t, i, j⟩, hp⟩ := e n
    rw [Finset.mem_sdiff] at hp
    exact cell_sub a V1 V2 k sp hk hind t i j hp.1 hp.2
  · intro n m hnm
    exact cellOf_disjoint _ _ _ hind _ _ (fun h => hnm (e.injective (Subtype.ext h)))
  · intro n
    obtain ⟨⟨t, i, j⟩, hp⟩ := e n
    rcases t <;> simp only [cellOf, Bool.false_eq_true, if_false, if_true]
    · exact ((cellDown_congruent _ _ _ hind i j).symm.trans (by rw [hbase]; exact hc))
    · exact ((cellUp_congruent _ _ _ hind i j).symm.trans (by rw [hbase]; exact hc))



open MeasureTheory in
/-- **Packing lemma for tile families** (variant of `S2L.pack_exists` that needs only containment, not covering,
of each region: the covering of `T` is derived from the area identity by `ConvexCover.ofCertificate`). -/
theorem pack_exists' {m : ℕ} {M T : Tri} (S : Fin m → Set Plane) (n : Fin m → ℕ)
    (R : ∀ a, TFam (S a) M (n a))
    (hS : ∀ a b, a ≠ b → Disjoint (interior (S a)) (interior (S b)))
    (hsub : ∀ a, S a ⊆ T.carrier)
    (hvol : ((∑ a, n a : ℕ) : ENNReal) * volume M.carrier = volume T.carrier) :
    ∃ D : CongruentDissection (∑ a, n a), D.model = M ∧ D.target = T := by
  classical
  let tile : Fin (∑ a, n a) → Tri := fun e =>
    (R (finSigmaFinEquiv.symm e).1).tile (finSigmaFinEquiv.symm e).2
  have tsub : ∀ (p : (a : Fin m) × Fin (n a)), ((R p.1).tile p.2).carrier ⊆ S p.1 :=
    fun p => (R p.1).sub p.2
  have hsub' : ∀ e, (tile e).carrier ⊆ T.carrier := fun e => (tsub _).trans (hsub _)
  have key : ∀ (p q : (a : Fin m) × Fin (n a)), p ≠ q →
      Disjoint (interior ((R p.1).tile p.2).carrier) (interior ((R q.1).tile q.2).carrier) := by
    rintro ⟨a, x⟩ ⟨b, y⟩ hne
    by_cases hab : a = b
    · subst hab
      have : x ≠ y := fun h => hne (by rw [h])
      exact (R a).disj this
    · exact (hS a b hab).mono (interior_mono (tsub ⟨a, x⟩)) (interior_mono (tsub ⟨b, y⟩))
  have hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier) :=
    fun i j hij => key _ _ (fun h => hij (finSigmaFinEquiv.symm.injective h))
  have hcong : ∀ e, (tile e).Congruent M := fun e => (R _).cong _
  have hvol' : ∑ e, volume (tile e).carrier = volume T.carrier := by
    rw [Finset.sum_congr rfl (fun e _ => Erdos634.CongruentArea.volume_congruent (hcong e))]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hvol
  exact ⟨{ Erdos634.ConvexCover.ofCertificate T tile hsub' hdisj hvol' with
           model := M
           tiles_congruent := hcong }, rfl, rfl⟩

end Erdos634.Draft.LadderFam
