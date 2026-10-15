/-
Draft/LayerE1Chord.lean  In `AllThreshold`.

The forward half of the reframing statement (b).  The layer of `LayerE1` (`T_M(1,f) → T_{M+1}(1,f)`, `f ≤ 2M`)
builds the dissection of `T_{M+1}` from nine region tilings, and the chord `x = A₀ M` (the line of the base of the
translate of `T_M`) separates the nine regions (`Y0` on one side, `Y1`, `Y2` and the six cap pieces on the other).
`S2L.pack_exists` does not say which region a tile came from; here

    pack_exists_tracked      -- same hypotheses and proof as `S2L.pack_exists`; extra conclusion: every tile of the
                             --   dissection lies in one of the regions
    skewX F                  -- the linear form "first frame coordinate" of the frame `Φ_F`: `skewX F (Φ_F p) = p.1`
    layer_real_chord         -- `LayerE1.layer_real` with the extra conclusion
                             --   `straddlers D.toDissection (skewX (d+2)) (cA d * t) = ∅`
    layer_chord_at           -- the frame-level statement for naturals: `TClosed (g+2) _ M`, `g+2 ≤ 2M`  ⟹  a congruent
                             --   dissection `D` of `DeltaTri (g+2) _ (M+1) _` with model `MF` and the chord
                             --   `x = A₀ M` uncrossed (`A₀ = f (f²−1)`)
    layer_chord              -- the forward half of (b): `BetaTilable 1 f (f−1)` ⟹ a congruent dissection `D` of
                             --   `DeltaTri f _ f _` with model `MF f` and `straddlers D (skewX f) (A₀ (f−1)) = ∅`

Non-vacuity.
  * `layer_chord_at` has witnesses: its hypothesis `TClosed (g+2) _ M` holds for every `M ≥ g + 2` (D. Paliy's construction,
    `CollarE1.betaTilable_e1` through `TClosed_of_betaTilable`); the `example` at the foot instantiates it at `g = 0`, `M = 2`
    (`f = 2`, the chord of `T_3(1,2)` at the height of `T_2`).
  * `layer_chord` has no known witness.  Its hypothesis is `BetaTilable 1 f (f−1)`.  For `f = 2` it is false
    (`SideRun.not_betaTilable_e1_le_half 2 1`), so the theorem is vacuous there.  For `f = 3` it is false
    (`E1ScaleTwo.not_betaTilable_1_3_2`; it says `¬ BetaTilable 1 3 2`).  For `f ≥ 4` it is the open question
    whether `T_{f−1}(1,f)` has a tiling: no witness of the hypothesis is known.  `layer_chord` is an
    implication; what is not vacuous is the construction (`layer_chord_at`).
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.LayerE1
import Erdos634.Draft.ChordCut

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.LayerE1Chord
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (disjoint_image')
open Erdos634.Draft.WtoDeltaF (DS DeltaTri DTriR)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap congruent_of_hasSides')
open Erdos634.Draft.UniformThreshold (BetaTilable)
open Erdos634.Draft.CollarE1
open Erdos634.Draft.LayerE1
open Erdos634.ChordTraceReal (straddlers)

/-! ## The first frame coordinate as a linear form -/

/-- `q ↦ q₀ − q₁ / sD F`: the first skew coordinate of the frame `Φ_F` (`= (Psi F q).1`) -/
noncomputable def skewX (F : ℝ) : Plane →ₗ[ℝ] ℝ where
  toFun q := q 0 - q 1 / sD F
  map_add' := by intro a b; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem skewX_apply (F : ℝ) (q : Plane) : skewX F q = q 0 - q 1 / sD F := rfl

theorem skewX_Phi {F : ℝ} (hF : 1 < F) (p : ℝ × ℝ) : skewX F (Phi F p) = p.1 := by
  calc skewX F (Phi F p) = (Psi F (Phi F p)).1 := rfl
    _ = p.1 := by rw [Psi_Phi hF p]

theorem skewX_ne_zero {F : ℝ} (hF : 1 < F) : skewX F ≠ 0 := by
  intro h
  have h1 := skewX_Phi hF (1, 0)
  rw [h] at h1
  simp at h1

/-- a dissection no tile of which has points strictly on both sides of a line: `straddlers = ∅` -/
theorem straddlers_empty_of_sides {N : ℕ} (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (h : ∀ e, (∀ x ∈ (D.tile e).carrier, g x ≤ c) ∨ (∀ x ∈ (D.tile e).carrier, c ≤ g x)) :
    straddlers D g c = ∅ := by
  by_contra hne
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  simp only [straddlers, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hi
  have hmem : ∀ k, (D.tile i).pts k ∈ (D.tile i).carrier := fun k => subset_convexHull ℝ _ ⟨k, rfl⟩
  rcases h i with h1 | h1
  · exact absurd (h1 _ (hmem b)) (not_le.mpr hb)
  · exact absurd (h1 _ (hmem a)) (not_le.mpr ha)

/-! ## The tracked packing lemma -/

open MeasureTheory in
/-- **`S2L.pack_exists`, with the region of each tile.**  Same hypotheses and the same proof; the extra conclusion says
that every tile of the resulting dissection is contained in one of the regions. -/
theorem pack_exists_tracked {m : ℕ} {M T : Erdos634.Geometry.Tri} (S : Fin m → Set Plane) (n : Fin m → ℕ)
    (R : ∀ a, RTiling (S a) M (n a))
    (hS : ∀ a b, a ≠ b → Disjoint (interior (S a)) (interior (S b)))
    (hsub : ∀ a, S a ⊆ T.carrier)
    (hvol : ((∑ a, n a : ℕ) : ENNReal) * volume M.carrier = volume T.carrier) :
    ∃ D : CongruentDissection (∑ a, n a), D.model = M ∧ D.target = T ∧
      ∀ e, ∃ a, (D.tile e).carrier ⊆ S a := by
  classical
  let tile : Fin (∑ a, n a) → Erdos634.Geometry.Tri := fun e =>
    (R (finSigmaFinEquiv.symm e).1).tile (finSigmaFinEquiv.symm e).2
  have tsub : ∀ (p : (a : Fin m) × Fin (n a)), ((R p.1).tile p.2).carrier ⊆ S p.1 := by
    intro p x hx
    rw [← (R p.1).covers]
    exact Set.mem_iUnion.mpr ⟨_, hx⟩
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
  refine ⟨{ Erdos634.ConvexCover.ofCertificate T tile hsub' hdisj hvol' with
           model := M
           tiles_congruent := hcong }, rfl, rfl, ?_⟩
  intro e
  exact ⟨(finSigmaFinEquiv.symm e).1, tsub (finSigmaFinEquiv.symm e)⟩

/-! ## The nine regions and the line `x = A₀ t` -/

theorem Yf_side {d t : ℝ} (hd : 0 ≤ d) : ∀ a : Fin 9,
    (∀ p ∈ Yf d t a, p.1 ≤ cA d * t) ∨ (∀ p ∈ Yf d t a, cA d * t ≤ p.1) := fun a => match a with
  | ⟨0, _⟩ => Or.inl (x_le_Y0 d t)
  | ⟨1, _⟩ => Or.inr (x_ge_Y1 d t)
  | ⟨2, _⟩ => Or.inr (x_ge_Y2 hd t)
  | ⟨3, _⟩ => Or.inr (xgY3 hd t)
  | ⟨4, _⟩ => Or.inr (xgY4 hd t)
  | ⟨5, _⟩ => Or.inr (xgY5 hd t)
  | ⟨6, _⟩ => Or.inr (xgY6 hd t)
  | ⟨7, _⟩ => Or.inr (xgY7 hd t)
  | ⟨8, _⟩ => Or.inr (xgY8 hd t)
  | ⟨k + 9, h⟩ => absurd h (by omega)

/-- **The layer step with the chord uncrossed (real parameters).**  `LayerE1.layer_real`, with the extra conclusion that no
tile of the dissection of `T_{t+1}` has points strictly on both sides of the line `x = A₀ t` (the base of the translate
of `T_t`). -/
theorem layer_real_chord {d t : ℝ} (hd : 0 ≤ d) (h2t : d + 2 ≤ 2 * t) (n0 k1 l1 k2 l2 k3 k4 k6 l6 k7 : ℕ)
    (hn0 : (n0 : ℝ) = cC d * t ^ 2)
    (hk1 : (k1 : ℝ) + 1 = d + 2) (hl1 : (l1 : ℝ) + 1 = xa d t)
    (hk2 : (k2 : ℝ) + 1 = (d + 2) ^ 2 - 1) (hl2 : (l2 : ℝ) + 1 = t + 1)
    (hk30 : 0 < k3) (hk3 : (k3 : ℝ) = d + 2) (hk40 : 0 < k4) (hk4 : (k4 : ℝ) = d + 1)
    (hk6 : (k6 : ℝ) + 1 = (d + 2) * (d + 1)) (hl6 : (l6 : ℝ) + 1 = d + 1) (hk7 : (k7 : ℝ) + 1 = d + 1)
    (R0 : RTiling (Phi (d + 2) '' DS (cA d * t) (cB d * t) (cC d * t)) (Mod hd) n0) :
    ∃ (N : ℕ) (D : CongruentDissection N), (N : ℝ) = cC d * (t + 1) ^ 2 ∧ D.model = Mod hd ∧
      D.target = tgtT hd h2t ∧ straddlers D.toDissection (skewX (d + 2)) (cA d * t) = ∅ := by
  have h0 : (0 : ℝ) ≤ 0 := le_refl 0
  obtain ⟨S6, ⟨R6⟩, h6⟩ := shift_sub_exists (vsh d t) (RT6 hd h0 k6 l6 hk6 hl6)
  obtain ⟨S7, ⟨R7⟩, h7⟩ := shift_sub_exists (vsh d t) (RT7 hd h0 k7 hk7)
  have R0s : RTiling (Phi (d + 2) '' Y0 d t) (Mod hd) n0 := shiftR R0 (0, cB d)
  have Rall : ∀ a : Fin 9, RTiling (regionL d t S6 S7 a) (Mod hd)
      (cnt n0 (2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k3 * k3)
        (k4 * k4) (k4 * k4) (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a) := fun a => match a with
    | ⟨0, _⟩ => R0s
    | ⟨1, _⟩ => RY1 hd h2t k1 l1 k2 l2 hk1 hl1 hk2 hl2
    | ⟨2, _⟩ => RY2 hd t k3 hk30 hk3
    | ⟨3, _⟩ => shiftR (RT3 hd h0 k3 hk30 hk3) (vsh d t)
    | ⟨4, _⟩ => shiftR (RT4 hd h0 k4 hk40 hk4) (vsh d t)
    | ⟨5, _⟩ => shiftR (RT5 hd h0 k4 hk40 hk4) (vsh d t)
    | ⟨6, _⟩ => R6
    | ⟨7, _⟩ => R7
    | ⟨8, _⟩ => shiftR (RT8 hd h0 k4 hk40 hk4) (vsh d t)
    | ⟨k + 9, h⟩ => absurd h (by omega)
  have sub_all : ∀ a : Fin 9, regionL d t S6 S7 a ⊆ Phi (d + 2) '' Yf d t a := fun a => match a with
    | ⟨0, _⟩ => subset_rfl
    | ⟨1, _⟩ => subset_rfl
    | ⟨2, _⟩ => subset_rfl
    | ⟨3, _⟩ => subset_rfl
    | ⟨4, _⟩ => subset_rfl
    | ⟨5, _⟩ => subset_rfl
    | ⟨6, _⟩ => h6
    | ⟨7, _⟩ => h7
    | ⟨8, _⟩ => subset_rfl
    | ⟨k + 9, h⟩ => absurd h (by omega)
  have hS_all : ∀ a b : Fin 9, a ≠ b →
      Disjoint (interior (regionL d t S6 S7 a)) (interior (regionL d t S6 S7 b)) := fun a b hab =>
    (disjoint_image' (hfr hd) (dY_all hd h2t a b hab)).mono (interior_mono (sub_all a)) (interior_mono (sub_all b))
  have hsub_all : ∀ a : Fin 9, regionL d t S6 S7 a ⊆ (tgtT hd h2t).carrier := fun a => by
    rw [carrier_tgtT hd h2t]
    exact (sub_all a).trans (Set.image_mono (Yf_sub hd h2t a))
  have hsumR : ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k3 * k3)
        (k4 * k4) (k4 * k4) (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a : ℕ) : ℝ)
      = cC d * (t + 1) ^ 2 := by
    rw [sum_cnt]
    push_cast
    rw [hn0, hk1, hl1, hk2, hl2, hk3, hk4, hk6, hl6, hk7]
    simp only [cC, xa]; ring
  have hvol : ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k3 * k3)
        (k4 * k4) (k4 * k4) (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a : ℕ) : ENNReal)
        * MeasureTheory.volume (Mod hd).carrier
      = MeasureTheory.volume (tgtT hd h2t).carrier := by
    have hNR : (0 : ℝ) ≤ ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1) + 2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k3 * k3)
        (k4 * k4) (k4 * k4) (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    rw [volMod hd h0, vol_tgtT hd h2t, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNR, hsumR]
    congr 2
    simp only [cA, cC]; ring
  obtain ⟨D, hM, hT, htr⟩ := pack_exists_tracked (M := Mod hd) (T := tgtT hd h2t) (regionL d t S6 S7) _
    Rall hS_all hsub_all hvol
  refine ⟨_, D, hsumR, hM, hT, ?_⟩
  apply straddlers_empty_of_sides
  intro e
  obtain ⟨a, ha⟩ := htr e
  rcases Yf_side (t := t) hd a with h | h
  · left
    intro x hx
    obtain ⟨p, hp, rfl⟩ := sub_all a (ha hx)
    rw [skewX_Phi (oneF hd)]
    exact h p hp
  · right
    intro x hx
    obtain ⟨p, hp, rfl⟩ := sub_all a (ha hx)
    rw [skewX_Phi (oneF hd)]
    exact h p hp

/-! ## The natural-number form -/

/-- `DTriR` depends only on the values of its parameters -/
theorem DTriR_congr {F F' u u' v v' w w' : ℝ} {hF1 : 1 < F} {hF1' : 1 < F'} {hu : 0 < u} {hu' : 0 < u'}
    {hw : 0 < w} {hw' : 0 < w'} (hF : F = F') (h1 : u = u') (h2 : v = v') (h3 : w = w') :
    DTriR F hF1 u v w hu hw = DTriR F' hF1' u' v' w' hu' hw' := by
  subst hF h1 h2 h3
  rfl

/-- **The layer step with the chord uncrossed, for the member `(1, g+2)`** (frame level).  A tiling of `T_M` (`TClosed`),
with `g + 2 ≤ 2M`, gives a congruent dissection `D` of `T_{M+1}` (`DeltaTri (g+2) _ (M+1) _`) with the model `MF (g+2)` in
which no tile has points strictly on both sides of the line `x = A₀ M`, `A₀ = (g+2)((g+2)²−1)`: the chord parallel to the
base at the height of `T_1`.  The hypothesis holds for every `M ≥ g + 2` (`betaTilable_e1`). -/
theorem layer_chord_at (g M : ℕ) (hM : g + 2 ≤ 2 * M) (hT : TClosed (g + 2) (by omega) M) :
    ∃ (N : ℕ) (D : CongruentDissection N),
      D.target = DeltaTri (g + 2) (by omega) (M + 1) (by omega) ∧
      D.model = Erdos634.Draft.WBrickF.MF ((g + 2 : ℕ) : ℝ) (Erdos634.Draft.WPgramF.hF (g + 2) (by omega)) ∧
      straddlers D.toDissection (skewX ((g + 2 : ℕ) : ℝ))
        (((g + 2 : ℕ) : ℝ) * (((g + 2 : ℕ) : ℝ) ^ 2 - 1) * (M : ℝ)) = ∅ := by
  obtain ⟨R⟩ := hT
  have hd : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg _
  have h2t : (g : ℝ) + 2 ≤ 2 * (M : ℝ) := by exact_mod_cast hM
  have h0 : (0 : ℝ) ≤ 0 := le_refl 0
  have hf : 2 ≤ g + 2 := by omega
  have hFr := Erdos634.Draft.WPgramF.hF (g + 2) hf
  have eF : ((g + 2 : ℕ) : ℝ) = (g : ℝ) + 2 := by push_cast; ring
  have hS : Phi ((g + 2 : ℕ) : ℝ) '' DS (((g + 2 : ℕ) : ℝ) * (((g + 2 : ℕ) : ℝ) ^ 2 - 1) * (M : ℝ))
      ((2 * ((g + 2 : ℕ) : ℝ) ^ 2 - 1) * (M : ℝ)) ((3 * ((g + 2 : ℕ) : ℝ) ^ 2 - 1) * (M : ℝ))
      = Phi ((g : ℝ) + 2) '' DS (cA (g : ℝ) * (M : ℝ)) (cB (g : ℝ) * (M : ℝ)) (cC (g : ℝ) * (M : ℝ)) := by
    simp only [cA, cB, cC]; push_cast; rfl
  obtain ⟨m1, m2, m3⟩ := Erdos634.Draft.WPgramWrap.MF_sides hFr
  obtain ⟨s1, s2, s3⟩ := Mod_sides hd h0
  have hMF0 : HasSides (Erdos634.Draft.WBrickF.MF ((g + 2 : ℕ) : ℝ) hFr) ((g + 2 : ℕ) : ℝ)
      (((g + 2 : ℕ) : ℝ) ^ 2) (((g + 2 : ℕ) : ℝ) ^ 2 - 1) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; exact m2,
      by simp only [Equiv.refl_apply]; rw [dist_comm]; exact m3, by simp only [Equiv.refl_apply]; exact m1⟩
  have hMF : (Erdos634.Draft.WBrickF.MF ((g + 2 : ℕ) : ℝ) hFr).Congruent (Mod hd) :=
    congruent_of_hasSides' (hasSides_rot (hasSides_rot (hasSides_swap hMF0)))
      (by rw [s1, eF]) (by rw [s2, eF]) (by rw [s3, eF])
  have h1 : 1 ≤ 3 * (g + 2) ^ 2 := by nlinarith
  have R0 : RTiling (Phi ((g : ℝ) + 2) '' DS (cA (g : ℝ) * (M : ℝ)) (cB (g : ℝ) * (M : ℝ)) (cC (g : ℝ) * (M : ℝ)))
      (Mod hd) ((3 * (g + 2) ^ 2 - 1) * M ^ 2) := RegionTiling.remodel (RTiling.cast hS R) hMF
  have hn0 : (((3 * (g + 2) ^ 2 - 1) * M ^ 2 : ℕ) : ℝ) = cC (g : ℝ) * (M : ℝ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_sub h1]; simp only [cC]; push_cast; ring
  obtain ⟨k2, hk2n⟩ : ∃ k2, k2 + 1 = (g + 2) ^ 2 - 1 :=
    ⟨(g + 2) ^ 2 - 1 - 1, Nat.sub_add_cancel (Nat.le_sub_of_add_le (by nlinarith))⟩
  obtain ⟨k6, hk6n⟩ : ∃ k6, k6 + 1 = (g + 2) * (g + 1) :=
    ⟨(g + 2) * (g + 1) - 1, Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))⟩
  have hl1 : ((((2 * M - (g + 2)) * (g + 2) : ℕ)) : ℝ) + 1 = xa (g : ℝ) (M : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hM]; simp only [xa]; push_cast; ring
  have hk2 : (k2 : ℝ) + 1 = ((g : ℝ) + 2) ^ 2 - 1 := by
    have h4 : 1 ≤ (g + 2) ^ 2 := by nlinarith
    have h := congrArg (Nat.cast : ℕ → ℝ) hk2n
    rw [Nat.cast_sub h4] at h
    push_cast at h; linarith
  have hk6 : (k6 : ℝ) + 1 = ((g : ℝ) + 2) * ((g : ℝ) + 1) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hk6n
    push_cast at h; linarith
  obtain ⟨N, D, hN, hMd, hTd, hstr⟩ := layer_real_chord hd h2t _ (g + 1)
    ((2 * M - (g + 2)) * (g + 2)) k2 M (g + 2) (g + 1)
    k6 g g hn0 (by push_cast; ring) hl1 hk2 rfl (by omega) (by push_cast; ring) (by omega) (by push_cast; ring)
    hk6 rfl rfl R0
  have hTT : tgtT hd h2t = DeltaTri (g + 2) hf (M + 1) (by omega) :=
    DTriR_congr (by first | (push_cast; ring) | push_cast)
      (by simp only [cA]; first | (push_cast; ring) | push_cast)
      (by simp only [cB]; first | (push_cast; ring) | push_cast)
      (by simp only [cC]; first | (push_cast; ring) | push_cast)
  have hcMod : ∀ i, (D.tile i).Congruent (Mod hd) := fun i => by
    have := D.tiles_congruent i
    rwa [hMd] at this
  have key : straddlers D.toDissection (skewX ((g + 2 : ℕ) : ℝ))
      (((g + 2 : ℕ) : ℝ) * (((g + 2 : ℕ) : ℝ) ^ 2 - 1) * (M : ℝ)) = ∅ := by
    rw [eF]
    exact hstr
  let D' : CongruentDissection N :=
    { toDissection := D.toDissection
      model := Erdos634.Draft.WBrickF.MF ((g + 2 : ℕ) : ℝ) hFr
      tiles_congruent := fun i => (hcMod i).trans hMF.symm }
  exact ⟨N, D', hTd.trans hTT, rfl, key⟩

/-- **(b), forward half.**  If the base-β target `T_{f−1}(1,f)` has a tiling, then `T_f(1,f)` has a congruent
dissection `D` (target `DeltaTri f _ f _`, model `MF f`) in which no tile has points strictly on both sides of the line
`x = A₀ (f−1)` (`A₀ = f (f²−1)`), the chord parallel to the base at the height of `T_1`: the layer of `prop:layer` laid
over the tiling of `T_{f−1}`.

No witness of the hypothesis is known.  `BetaTilable 1 f (f − 1)` is false for `f = 2`
(`SideRun.not_betaTilable_e1_le_half 2 1`; the theorem is vacuous there), false for `f = 3`
(`E1ScaleTwo.not_betaTilable_1_3_2`), and for `f ≥ 4` it is the open question (whether `T_{f−1}(1,f)` has a tiling).  What
is not vacuous is the construction: `layer_chord_at` has hypotheses that hold for all `M ≥ f`. -/
theorem layer_chord (f : ℕ) (hf : 2 ≤ f) (h : BetaTilable 1 f (f - 1)) :
    ∃ (N : ℕ) (D : CongruentDissection N), D.target = DeltaTri f hf f (by omega) ∧
      D.model = Erdos634.Draft.WBrickF.MF (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf) ∧
      straddlers D.toDissection (skewX (f : ℝ))
        ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * ((f - 1 : ℕ) : ℝ)) = ∅ := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  have e : g + 2 - 1 = g + 1 := by omega
  rw [e] at h
  have hT : TClosed (g + 2) hf (g + 1) := TClosed_of_betaTilable (g + 2) hf (g + 1) (by omega) h
  obtain ⟨N, D, h1, h2, h3⟩ := layer_chord_at g (g + 1) (by omega) hT
  rw [e]
  exact ⟨N, D, h1, h2, h3⟩

/-- **Non-vacuity of the construction**: the layer with the chord uncrossed at `g = 0`, `M = 2` (the member `(1, 2)`: the
chord of `T_3(1,2)` at the height of `T_2`); the tiling of `T_2(1,2)` is `CollarE1.betaTilable_e1`. -/
example : ∃ (N : ℕ) (D : CongruentDissection N), straddlers D.toDissection (skewX ((0 + 2 : ℕ) : ℝ))
    (((0 + 2 : ℕ) : ℝ) * (((0 + 2 : ℕ) : ℝ) ^ 2 - 1) * ((2 : ℕ) : ℝ)) = ∅ := by
  obtain ⟨N, D, -, -, h⟩ := layer_chord_at 0 2 (by norm_num)
    (TClosed_of_betaTilable (0 + 2) (by norm_num) 2 (by norm_num)
      (Erdos634.Draft.CollarE1.betaTilable_e1 (0 + 2) (by norm_num) 2 (by norm_num)))
  exact ⟨N, D, h⟩

end Erdos634.Draft.LayerE1Chord

#print axioms Erdos634.Draft.LayerE1Chord.pack_exists_tracked
#print axioms Erdos634.Draft.LayerE1Chord.layer_real_chord
#print axioms Erdos634.Draft.LayerE1Chord.layer_chord_at
#print axioms Erdos634.Draft.LayerE1Chord.layer_chord
