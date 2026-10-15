/-
Basic facts about the base-β model (`BaseBetaModel`, `BaseBetaShape`) and the flanks of the corner tile.
The architecture follows the γ = 2α and π/3 cases.

Adapted (copied, with a header line naming the source) from:
  Draft/R1Frame.lean            sides_distinct1            -> sidesDistinct
  Draft/HalfTurnR3R4Glue.lean   localAngle_of_oppSideE     -> localAngle_of_oppSide
  CornerBaseEdgesReal.lean      tail of congruentDissection_base_corner_edges -> beta_vertex_flanks
Imported and applied:
  BaseBetaCorners.lean          b_unsplittable (scaled by s>0)  -> hword_b
  TileAt.lean                   congruentDissection_{base_corner_counts, apex_counts, base_corner_tile_vertex}
                                -> no_gamma_at_target_vertex, base_corner_tile_flanks
-/
import Erdos634.TileAt
import Erdos634.CornerBaseEdgesReal
import Erdos634.EdgeWordConversion
import Erdos634.BaseBetaCorners
import Erdos634.MarchSlots

/-!
# Scale-free base-β model data and the arithmetic/angle lemmas for the corner parallelogram

Adapts the corner pipeline of the γ = 2α and π/3 cases to the base-β tile.  `R1Frame` and `HalfTurnR3R4Glue` are
not imported, to keep the import cone of this module small; the lemmas taken from them are copied (see the
header of the file).

Contents:
* `BaseBetaModel`, `BaseBetaShape`;
* `angleFacts`, `sidesDistinct`, `BaseBetaModel.scalene`;
* `hword_b`, `BaseBetaModel.sideLen_mem`;
* `localAngle_of_oppSide` (local copy), `BaseBetaModel.localAngle_of_oppSide`;
* `no_gamma_at_target_vertex`, `not_vertex_of_gamma`;
* `beta_vertex_flanks`, `base_corner_tile_flanks` (`TileAt`'s corner tile together with `beta_vertex_flanks`);
* numeric checks at `(e, f, s) = (1, 2, 8)` (the N = 44 tiling `D44`: sides 16, 24, 32) and at
  `(e, f, s) = (2, 3, 1)` (sides 6, 5, 9), and a counterexample showing that `hword_b` is specific to the chord `b`.

The structures `BaseBetaModel` / `BaseBetaShape` are witnessed at the N = 44 tiling (`Tiling44Bridge.D44`,
`(e, f, s) = (1, 2, 8)`) in the modules `Draft/CornerParaWitnessAux` (`D44_model`, `D44_shape`).  The pure arithmetic
of the fields is checked in this file (`arith_witness_*`, `hword_b_instances`, `hword_b_not_for_c`).
-/

namespace Erdos634.CornerPara

open Erdos634.Geometry Erdos634.TilePlacement

/-! ## The scale-free model data and the target shape -/

/-- Base-β model data at an arbitrary positive scale `s` (`HalfTurnR3R4Glue.ModelDataE` is `s = 1`; the real
N = 44 tiling `D44` is `s = 8` at `(e, f) = (1, 2)`).  Model vertices `0 / 1 / 2` carry `α / β / γ`;
`sideOpp D.model j` is the side OPPOSITE vertex `j`, so `a = sideOpp 0`, `b = sideOpp 1`, `c = sideOpp 2`. -/
structure BaseBetaModel {N : ℕ} (D : CongruentDissection N) (e f : ℕ) (s α β γ : ℝ) : Prop where
  hs : 0 < s
  hs0 : sideOpp D.model 0 = s * ((e : ℝ) * f)
  hs1 : sideOpp D.model 1 = s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
  hs2 : sideOpp D.model 2 = s * (f : ℝ) ^ 2
  hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α
  hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β
  hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ

/-- Base-β shape of the target: every corner is `3α` or `β` (the `htarget` hypothesis of the vertex census). -/
def BaseBetaShape (T : Tri) (α β : ℝ) : Prop :=
  ∀ m : Fin 3, cornerAngle (T.pts (m + 1)) (T.pts m) (T.pts (m + 2)) = 3 * α ∨
    cornerAngle (T.pts (m + 1)) (T.pts m) (T.pts (m + 2)) = β

/-! ## A0: distinctness facts and scalene sides (M2) -/

/-- **The ten `≠` facts that `TileAt`'s corner/boundary census consumes, and `β ≠ 2π`**, from the angle bundle
(`MarchKillsFan.distinct_of_pos_ne` for the ten; `3α + 2β = π`, `α > 0` for `β ≠ 2π`). -/
theorem angleFacts {α β γ : ℝ} (hA : MarchSlots.AngleData α β γ) :
    (α ≠ β ∧ α ≠ γ ∧ α ≠ Real.pi ∧ α ≠ 0 ∧ β ≠ γ ∧ β ≠ Real.pi ∧ β ≠ 0 ∧ γ ≠ Real.pi ∧ γ ≠ 0 ∧
      Real.pi ≠ 0) ∧ β ≠ 2 * Real.pi := by
  refine ⟨Erdos634.MarchKillsFan.distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel, ?_⟩
  intro h
  have hpi := Real.pi_pos
  have h1 := hA.hrel
  have h2 := hA.hα
  linarith

/-- COPY of `Draft/R1Frame.lean:31 sides_distinct1`, so as not to import `R1Frame` (its cone contains
`ApexLegWord`): the base-β side values `ef`, `f² - e²`, `f²` are pairwise distinct at every coprime member
`1 ≤ e < f` (`HalfTurnR3R4Glue.sides_distinct` needs `2 ≤ e`; at `e = 1`, `a = b` would be `f + 1 = f²`). -/
theorem sidesDistinct {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) :
    ((e : ℝ) * f ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧ ((e : ℝ) * f ≠ (f : ℝ) ^ 2) ∧
      ((f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≠ (f : ℝ) ^ 2) := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hN : e * f + e ^ 2 = f ^ 2 := by
      have : ((e * f + e ^ 2 : ℕ) : ℝ) = ((f ^ 2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hdvd : e ∣ f ^ 2 := ⟨f + e, by rw [← hN]; ring⟩
    have he1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 hco) hdvd
    subst he1
    have hf2 : 2 ≤ f := by omega
    nlinarith
  · have hf : (0 : ℝ) < f := by linarith
    have : (e : ℝ) = f := by
      have h' : (e : ℝ) * f = f * f := by rw [h]; ring
      exact mul_right_cancel₀ hf.ne' h'
    linarith
  · have : (e : ℝ) ^ 2 = 0 := by linarith
    have : (e : ℝ) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith

/-- **M2.**  The three model sides are pairwise distinct (scalene tile), at every coprime member `1 ≤ e < f` and
every scale `s > 0`. -/
theorem BaseBetaModel.scalene {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) :
    ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m' := by
  obtain ⟨hab, hac, hbc⟩ := sidesDistinct hco he hef
  have hs := hM.hs.ne'
  have h01 : sideOpp D.model 0 ≠ sideOpp D.model 1 := by
    rw [hM.hs0, hM.hs1]; exact fun h => hab (mul_left_cancel₀ hs h)
  have h02 : sideOpp D.model 0 ≠ sideOpp D.model 2 := by
    rw [hM.hs0, hM.hs2]; exact fun h => hac (mul_left_cancel₀ hs h)
  have h12 : sideOpp D.model 1 ≠ sideOpp D.model 2 := by
    rw [hM.hs1, hM.hs2]; exact fun h => hbc (mul_left_cancel₀ hs h)
  intro m m' hmm'
  fin_cases m <;> fin_cases m' <;>
    first
      | exact absurd rfl hmm'
      | exact h01 | exact h02 | exact h12
      | exact h01.symm | exact h02.symm | exact h12.symm

/-! ## M3: the word lemma for the `b`-chord, at scale `s` -/

/-- **M3** (scale-free `BaseBetaCorners.b_unsplittable`).  The `b`-chord is a single edge: if
`x·(s·ef) + y·(s·(f² - e²)) + z·(s·f²) = s·(f² - e²)` over `ℕ`-multiplicities then `x + y + z = 1`.
This is the shape of the `hword` hypothesis of `far_chain_single_gen` (`s0 = s·ef`, `s1 = s·(f² - e²)`,
`s2 = s·f²`, `L = s·(f² - e²)`).  Cancels `s > 0`, and uses `Nat.cast_sub` with `e² ≤ f²` to pass from the real
`f² - e²` to the natural `b` with `b + e² = f²` that `b_unsplittable` takes. -/
theorem hword_b {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) {s : ℝ} (hs : 0 < s) :
    ∀ x y z : ℕ, (x : ℝ) * (s * ((e : ℝ) * f)) + y * (s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
        + z * (s * (f : ℝ) ^ 2) = s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) → x + y + z = 1 := by
  intro x y z h
  have hle : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  have hb : (f ^ 2 - e ^ 2) + e ^ 2 = f ^ 2 := Nat.sub_add_cancel hle
  have hbR : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub hle]; push_cast; ring
  have h' : (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2
      = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have h1 : s * ((x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2)
        = s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by linear_combination h
    exact mul_left_cancel₀ hs.ne' h1
  have hN : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = f ^ 2 - e ^ 2 := by
    have h2 : ((x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 : ℕ) : ℝ)
        = (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) := by
      push_cast
      rw [hbR]
      linear_combination h'
    exact_mod_cast h2
  obtain ⟨h1, h2, h3⟩ :=
    Erdos634.BaseBetaCorners.b_unsplittable e f (f ^ 2 - e ^ 2) x y z he hef hco hb hN
  omega

/-! ## M4: every model side is one of `s·ef`, `s·(f² - e²)`, `s·f²` -/

/-- **M4.**  `EdgeWordConversion.sideLen D i = dist (model.pts i) (model.pts (i+1)) = sideOpp D.model (i+2)`
(NB the indexing differs from `sideOpp`: `sideLen 0 = c`, `sideLen 1 = a`, `sideLen 2 = b`), so each is one of
the three base-β side values at scale `s`.  This is the `hsides` hypothesis of `far_chain_single_gen`. -/
theorem BaseBetaModel.sideLen_mem {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (i : Fin 3) :
    EdgeWordConversion.sideLen D i = s * ((e : ℝ) * f) ∨
      EdgeWordConversion.sideLen D i = s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
      EdgeWordConversion.sideLen D i = s * (f : ℝ) ^ 2 := by
  have h0 : EdgeWordConversion.sideLen D 0 = sideOpp D.model 2 := rfl
  have h1 : EdgeWordConversion.sideLen D 1 = sideOpp D.model 0 := rfl
  have h2 : EdgeWordConversion.sideLen D 2 = sideOpp D.model 1 := rfl
  fin_cases i
  · right; right; exact h0.trans hM.hs2
  · left; exact h1.trans hM.hs0
  · right; left; exact h2.trans hM.hs1

/-! ## A4: a local angle read off the opposite side (LOCAL COPY) -/

/-- Local copy of `localAngle_of_oppSideE` from `Draft/HalfTurnR3R4Glue.lean` (restated here to keep the
import cone small): with the model's opposite sides `a, b, c` pairwise distinct,
a tile's local angle at a vertex is read off the opposite side. -/
theorem localAngle_of_oppSide {N : ℕ} (D : CongruentDissection N) {a b c α β γ : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs0 : sideOpp D.model 0 = a) (hs1 : sideOpp D.model 1 = b) (hs2 : sideOpp D.model 2 = c)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (i : Fin N) (j : Fin 3) :
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = a →
      (D.tile i).localAngle ((D.tile i).pts j) = α) ∧
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = b →
      (D.tile i).localAngle ((D.tile i).pts j) = β) ∧
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = c →
      (D.tile i).localAngle ((D.tile i).pts j) = γ) := by
  rw [Tri.localAngle_vertex]
  obtain ⟨k, hk, hd⟩ :=
    Erdos634.CornerBaseEdgesReal.congruent_opposite_side (D.tiles_congruent i).symm j
  rw [hk]
  simp only [sideOpp] at hs0 hs1 hs2
  fin_cases k <;> simp at hd hs0 hs1 hs2 ⊢
  · refine ⟨fun _ => hα', fun h => ?_, fun h => ?_⟩
    · exact absurd (hs0.symm.trans (hd.trans h)) hab
    · exact absurd (hs0.symm.trans (hd.trans h)) hac
  · refine ⟨fun h => ?_, fun _ => hβ', fun h => ?_⟩
    · exact absurd (hs1.symm.trans (hd.trans h)) hab.symm
    · exact absurd (hs1.symm.trans (hd.trans h)) hbc
  · refine ⟨fun h => ?_, fun h => ?_, fun _ => hγ'⟩
    · exact absurd (hs2.symm.trans (hd.trans h)) hac.symm
    · exact absurd (hs2.symm.trans (hd.trans h)) hbc.symm

/-- `localAngle_of_oppSide` for the base-β model data (opposite sides stated as `sideOpp D.model 0/1/2`):
a vertex of a tile whose opposite side is `a` (resp. `b`, `c`) has local angle `α` (resp. `β`, `γ`). -/
theorem BaseBetaModel.localAngle_of_oppSide {N : ℕ} {D : CongruentDissection N} {e f : ℕ}
    {s α β γ : ℝ} (hM : BaseBetaModel D e f s α β γ) (hco : Nat.Coprime e f) (he : 1 ≤ e)
    (hef : e < f) (i : Fin N) (j : Fin 3) :
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = sideOpp D.model 0 →
      (D.tile i).localAngle ((D.tile i).pts j) = α) ∧
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = sideOpp D.model 1 →
      (D.tile i).localAngle ((D.tile i).pts j) = β) ∧
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = sideOpp D.model 2 →
      (D.tile i).localAngle ((D.tile i).pts j) = γ) :=
  Erdos634.CornerPara.localAngle_of_oppSide D (hM.scalene hco he hef 0 1 (by decide))
    (hM.scalene hco he hef 0 2 (by decide)) (hM.scalene hco he hef 1 2 (by decide)) rfl rfl rfl
    hM.hα' hM.hβ' hM.hγ' i j

/-! ## M5 / A6: no `γ` at a target vertex, hence a `γ`-presenting point is not a target vertex -/

/-- **No `γ` at a target vertex.**  With the base-β shape of the target (every corner is `3α` or `β`; used for all three
vertices, not only the apex), no tile presents `γ` at any target vertex: at a `β`-corner the census is `{β}`
(`congruentDissection_base_corner_counts`), at a `3α`-corner it is `{3α}` (`congruentDissection_apex_counts`). -/
theorem no_gamma_at_target_vertex {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (m : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts m) ≠ γ := by
  obtain ⟨⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩, -⟩ := angleFacts hA
  intro hi
  have hmem : i ∈ ({j | (D.tile j).localAngle (D.target.pts m) = γ} : Finset (Fin N)) := by
    simpa using hi
  rcases hshape m with h3 | hb
  · obtain ⟨-, -, hc, -⟩ := Erdos634.Geometry.Dissection.congruentDissection_apex_counts D α β γ
      hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hA.hγdef hA.hrel hA.hirr hM.hα' hM.hβ' hM.hγ' m h3
    exact Finset.card_ne_zero_of_mem hmem hc
  · obtain ⟨-, -, hc, -⟩ := Erdos634.Geometry.Dissection.congruentDissection_base_corner_counts D α β γ
      hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hA.hγdef hA.hrel hA.hirr hM.hα' hM.hβ' hM.hγ' m hb
    exact Finset.card_ne_zero_of_mem hmem hc

/-- **A6.**  A point at which some tile presents `γ` is not a target vertex. -/
theorem not_vertex_of_gamma {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) {i : Fin N} {P : Plane}
    (h : (D.tile i).localAngle P = γ) : P ∉ Set.range D.target.pts := by
  rintro ⟨m, rfl⟩
  exact no_gamma_at_target_vertex hM hA hshape m i h

/-! ## M6: the flanks of a `β`-corner of ANY tile, and its opposite side -/

/-- **M6** (the tail of `CornerBaseEdgesReal.congruentDissection_base_corner_edges` (`:102`), un-specialized to
the target).  If a tile `i` has a `β`-corner at its vertex `j` then its two edges at `j` are `{a, c}` (in one
order or the other) and the opposite side `[j+1, j+2]` is `b`.  `hopp` is not exported by the original. -/
theorem beta_vertex_flanks {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ) (i : Fin N) (j : Fin 3)
    (h : cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = β) :
    ((dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = sideOpp D.model 2 ∧
        dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = sideOpp D.model 0) ∨
      (dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = sideOpp D.model 0 ∧
        dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = sideOpp D.model 2)) ∧
    dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = sideOpp D.model 1 := by
  classical
  obtain ⟨⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩, -⟩ := angleFacts hA
  obtain ⟨k0, hk0angle, hk0side⟩ :=
    Erdos634.CornerBaseEdgesReal.congruent_opposite_side (D.tiles_congruent i).symm j
  rw [h] at hk0angle
  have hk0eq : k0 = 1 := by
    fin_cases k0
    · exact absurd (hk0angle.trans hM.hα') hαβ.symm
    · rfl
    · exact absurd (hk0angle.trans hM.hγ') hβγ
  subst hk0eq
  have hopp : dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = sideOpp D.model 1 := by
    rw [← hk0side]; unfold sideOpp; norm_num
  refine ⟨?_, hopp⟩
  have hb : sideOpp D.model 1 ≠ 0 :=
    (dist_pos.mpr (pts_ne D.model (by decide : (2 : Fin 3) ≠ 0))).ne'
  have hmulti := (D.tiles_congruent i).sideMultiset_eq
  have hshift := Tri.sideMultiset_shift (D.tile i) j
  have hmul : ({dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)),
      dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j),
      dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2))} : Multiset ℝ)
      = {sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} := by
    rw [hshift, hmulti]
    simp only [sideOpp, show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl,
      show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
      show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
  rcases corner_tile_edges (D.tile i) j (sideOpp D.model 2) (sideOpp D.model 1)
      (sideOpp D.model 0) hb hopp hmul with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-! ## A1 + A3 assembled: the unique tile at a base corner, with its flanks `{a, c}` and opposite side `b` -/

/-- **A1 + A3.**  At a base corner `A = D.target.pts k` (corner angle `β`) of a base-β dissection there is a tile
`i` with `A` as its vertex `j`, presenting `β` there, which is the ONLY tile whose carrier contains `A`
(`TileAt.congruentDissection_base_corner_tile_vertex`), whose two edges at `A` have lengths `{a, c}` in one order or
the other and whose opposite side is the `b`-edge (`beta_vertex_flanks`). -/
theorem base_corner_tile_flanks {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ) (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ∃ (i : Fin N) (j : Fin 3), D.target.pts k = (D.tile i).pts j ∧
      (D.tile i).localAngle (D.target.pts k) = β ∧
      (∀ i' : Fin N, D.target.pts k ∈ (D.tile i').carrier → i' = i) ∧
      ((dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = sideOpp D.model 2 ∧
          dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = sideOpp D.model 0) ∨
        (dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = sideOpp D.model 0 ∧
          dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = sideOpp D.model 2)) ∧
      dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = sideOpp D.model 1 := by
  obtain ⟨⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩, hβ2π⟩ := angleFacts hA
  obtain ⟨i, j, hij, hangle, huniq⟩ :=
    Erdos634.Geometry.Dissection.congruentDissection_base_corner_tile_vertex D α β γ hαβ hαγ hαπ hα0
      hβγ hβπ hβ0 hβ2π hγπ hγ0 hπ0 hA.hγdef hA.hrel hA.hirr hM.hα' hM.hβ' hM.hγ' k hcorner
  have hc : cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = β := by
    rw [← Tri.localAngle_vertex, ← hij]; exact hangle
  obtain ⟨hfl, hopp⟩ := beta_vertex_flanks hM hA i j hc
  exact ⟨i, j, hij, hangle, huniq, hfl, hopp⟩

/-! ## Numerical checks of the arithmetic, and a counterexample for the chord `c`

The structures are witnessed on a tiling in the modules `Draft/CornerParaWitnessAux` / `Draft/CornerParaWitness`
(N = 44 tiling, `(e, f, s) = (1, 2, 8)`).
Here: the field arithmetic at two sample points. -/

/-- `(e, f, s) = (1, 2, 8)` (real N = 44 tiling `D44`): sides `a, b, c = 16, 24, 32`; pairwise distinct;
`hword_b`'s hypotheses hold and its equation has the solution `(0, 1, 0)`. -/
theorem arith_witness_1_2_8 :
    (8 : ℝ) * (((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) = 16 ∧
    (8 : ℝ) * (((2 : ℕ) : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2) = 24 ∧
    (8 : ℝ) * ((2 : ℕ) : ℝ) ^ 2 = 32 ∧
    Nat.Coprime 1 2 ∧ 1 ≤ 1 ∧ 1 < 2 ∧
    ((0 : ℕ) : ℝ) * (8 * (((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ))) +
      ((1 : ℕ) : ℝ) * (8 * (((2 : ℕ) : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2)) +
      ((0 : ℕ) : ℝ) * (8 * ((2 : ℕ) : ℝ) ^ 2) = 8 * (((2 : ℕ) : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, le_rfl, by norm_num, by norm_num⟩

/-- `(e, f, s) = (2, 3, 1)` (thick member, `β < α`): sides `a, b, c = 6, 5, 9`; pairwise distinct;
`hword_b`'s equation has the solution `(0, 1, 0)`. -/
theorem arith_witness_2_3_1 :
    (1 : ℝ) * (((2 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 6 ∧
    (1 : ℝ) * (((3 : ℕ) : ℝ) ^ 2 - ((2 : ℕ) : ℝ) ^ 2) = 5 ∧
    (1 : ℝ) * ((3 : ℕ) : ℝ) ^ 2 = 9 ∧
    Nat.Coprime 2 3 ∧ 1 ≤ 2 ∧ 2 < 3 ∧
    ((0 : ℕ) : ℝ) * (1 * (((2 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))) +
      ((1 : ℕ) : ℝ) * (1 * (((3 : ℕ) : ℝ) ^ 2 - ((2 : ℕ) : ℝ) ^ 2)) +
      ((0 : ℕ) : ℝ) * (1 * ((3 : ℕ) : ℝ) ^ 2) = 1 * (((3 : ℕ) : ℝ) ^ 2 - ((2 : ℕ) : ℝ) ^ 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, by norm_num, by norm_num, by norm_num⟩

/-- **`hword_b` does not hold for the chord `c`.**  The single-edge conclusion is specific to the chord length `b`: for the
chord of length `c` (`= s f²`) at `(e, f, s) = (1, 2, 8)` the same word equation has the solution `(2, 0, 0)`
(`2·16 = 32`) with `x + y + z = 2 ≠ 1`.  So `hword_b` is not an instance of a statement true of every
tile length. -/
theorem hword_b_not_for_c :
    ∃ x y z : ℕ, (x : ℝ) * (8 * (((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ))) +
        y * (8 * (((2 : ℕ) : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2)) + z * (8 * ((2 : ℕ) : ℝ) ^ 2)
          = 8 * ((2 : ℕ) : ℝ) ^ 2 ∧ x + y + z ≠ 1 :=
  ⟨2, 0, 0, by norm_num, by norm_num⟩

/-- Instances of `hword_b` and `sidesDistinct` at the two sanity points (so the lemmas are applied, not just
stated): `(e, f, s) = (1, 2, 8)` and `(2, 3, 1)`. -/
theorem hword_b_instances :
    (∀ x y z : ℕ, (x : ℝ) * (8 * (((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ))) +
        y * (8 * (((2 : ℕ) : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2)) + z * (8 * ((2 : ℕ) : ℝ) ^ 2)
          = 8 * (((2 : ℕ) : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2) → x + y + z = 1) ∧
    (∀ x y z : ℕ, (x : ℝ) * (1 * (((2 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))) +
        y * (1 * (((3 : ℕ) : ℝ) ^ 2 - ((2 : ℕ) : ℝ) ^ 2)) + z * (1 * ((3 : ℕ) : ℝ) ^ 2)
          = 1 * (((3 : ℕ) : ℝ) ^ 2 - ((2 : ℕ) : ℝ) ^ 2) → x + y + z = 1) :=
  ⟨hword_b (by decide) le_rfl (by norm_num) (by norm_num),
    hword_b (by decide) (by norm_num) (by norm_num) (by norm_num)⟩

end Erdos634.CornerPara

#print axioms Erdos634.CornerPara.BaseBetaModel
#print axioms Erdos634.CornerPara.BaseBetaShape
#print axioms Erdos634.CornerPara.angleFacts
#print axioms Erdos634.CornerPara.sidesDistinct
#print axioms Erdos634.CornerPara.BaseBetaModel.scalene
#print axioms Erdos634.CornerPara.hword_b
#print axioms Erdos634.CornerPara.BaseBetaModel.sideLen_mem
#print axioms Erdos634.CornerPara.localAngle_of_oppSide
#print axioms Erdos634.CornerPara.BaseBetaModel.localAngle_of_oppSide
#print axioms Erdos634.CornerPara.no_gamma_at_target_vertex
#print axioms Erdos634.CornerPara.not_vertex_of_gamma
#print axioms Erdos634.CornerPara.beta_vertex_flanks
#print axioms Erdos634.CornerPara.base_corner_tile_flanks
#print axioms Erdos634.CornerPara.arith_witness_1_2_8
#print axioms Erdos634.CornerPara.arith_witness_2_3_1
#print axioms Erdos634.CornerPara.hword_b_not_for_c
#print axioms Erdos634.CornerPara.hword_b_instances
