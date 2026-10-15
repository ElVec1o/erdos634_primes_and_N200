/-
Draft/WStrip.lean  In `AllThreshold`.  Strip step for `prop:wstrip`.

Statement.  `prop:wstrip` (a): "Let `M ≥ 2`, and let `z` be an integer with `z ≡ Mf (mod e)`, `f ≤ z ≤ Mb/f`.  Then `x = (Mb − zf)/e` is a non-negative integer, and the trapezoid `AQQ₁A₁`, which is the part of `W_M(e, f)` outside the copy of `W_{M−1}` at
the corner `B`, can be cut into `(2M − 1)(2f² − e²)` copies of the tile, in the five lattice pieces (1)-(5) of the proof.  The side `AQ` then reads `C₁^z A₂^x`."  And (c), first statement: "if `M(f − e) ≥ f` and `W_{M−1}(e, f)` has a tiling, then `W_M(e, f)` has a tiling."

Proved here (the geometry is `Draft/WStripGeom.lean`, a generated file; the frame is that of `CollarG`, `u = e`, `g = f − e`, `F = f / e`).
* `pgram_rt`: a grid of cells of one frame, carried into a parallelogram of another frame, with the degenerate cases `n = 0` or `m = 0` (the empty tiling): the form needed for the pieces whose cell counts `z − f`, `x` can be `0`;
* `RTw1`, `RTw2`, `RTw5` (the three triangles: scale `f`, `f`, `e`), `RTw3`, `RTw4`, `RTw6` (the three parallelograms: `f × (z − f)` cells, `x × e` cells, `(M − 1) f × f` cells);
* `skewY`: the second skew coordinate of the frame as a linear form of the plane (`skewY F (Φ_F p) = p.2`), for the chord;
* `strip_real`: the strip step with real parameters: a tiling of `W_{M−1}` by `n₀` tiles gives a dissection of `W_M`, `M = (z f + x e)/b`, `z = f + s`, `s, x ≥ 0`, in which no tile crosses the chord `y = V − cB` (`straddlers = ∅`: the tiles of
  the copy of `W_{M−1}` lie below it, the tiles of the five pieces above it);
* `strip_nat_dis`, `strip_nat`: for natural numbers, `WTilable u (u + g) (M − 1)` with `f ≤ z`, `x u + z f = M b`, `M ≥ 2` give a dissection of the frame triangle `W_M` with the chord uncrossed, and `WTilable u (u + g) M`;
* `wstrip_step`: in the notation of the paper (`e`, `f`): `z ≡ M f (mod e)`, `f ≤ z`, `z f ≤ M b`, `M ≥ 2` give the natural number `x = (M b − z f)/e` with `x e + z f = M b`, and `WTilable e f (M − 1)` gives `WTilable e f M`.
The tile counts are those of the paper: `cQ (M − 1)² + f² + f² + 2 f s + 2 x e + e² + 2 (M − 1) f² = cQ M²`, so the strip has `(2M − 1)(2f² − e²)` tiles.
Not proved here: that the five pieces form a single tiling of the trapezoid `AQQ₁A₁` as a set (a packing lemma for a quadrilateral target; `S2L.pack_exists` is for triangles): they are tiled, pairwise interior-disjoint and contained in the trapezoid, and together with the
copy of `W_{M−1}` they fill the triangle `W_M`; the types of the tiles on `AQ` (`C₁^z A₂^x`) are not stated.

No sorry, no native_decide.
-/
import Erdos634.Draft.WStripGeom
import Erdos634.Draft.LayerE1Chord

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.WStripG
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (triC triC_pts carrier_triC brickL brickU brick_rt cong_U_cell grid scaledRT baseTri
  baseTri_cong vol_triC sq_Phi' dPhi' disjoint_image' f_ne)
open Erdos634.Draft.BrickGridF (shift_rect)
open Erdos634.Draft.WAddF (Wt)
open Erdos634.Draft.WtoDeltaF (WS QS DS DS_eq hull_QS DTriR carrier_DTriR WS_eq)
open Erdos634.Draft.WClosedBase (WTriR carrier_WTriR WTriR_sq hull_WS)
open Erdos634.Draft.CollarE1 (mapped_grid dPhi2 cong_swap)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap congruent_of_hasSides')
open Erdos634.Draft.UniformThreshold (BetaTilable ThresholdAt hasSides_congr)
open Erdos634.Draft.CollarG (gF φβ hF1 hfr hvpos hapos hbpos hPpos hφβ Mod hab_id cellA cellB cellC volMod ca cb cQ cA cB
  cApos cBpos Pg WTilable wTilable_iff_frame pred_cast)
open Erdos634.Draft.LayerE1Chord (pack_exists_tracked straddlers_empty_of_sides)
open Erdos634.ChordTraceReal (straddlers)

/-- `q ↦ q₁ (2F) / sD F`: the second skew coordinate of the frame `Φ_F` (`= (Psi F q).2`) -/
noncomputable def skewY (F : ℝ) : Plane →ₗ[ℝ] ℝ where
  toFun q := q 1 * (2 * F) / sD F
  map_add' := by intro a b; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem skewY_Phi {F : ℝ} (hF : 1 < F) (p : ℝ × ℝ) : skewY F (Phi F p) = p.2 := by
  calc skewY F (Phi F p) = (Psi F (Phi F p)).2 := rfl
    _ = p.2 := by rw [Psi_Phi hF p]

theorem skewY_ne_zero {F : ℝ} (hF : 1 < F) : skewY F ≠ 0 := by
  intro h
  have h1 := skewY_Phi hF (0, 1)
  rw [h] at h1
  simp at h1

/-- the empty tiling -/
def emptyRT (M : Erdos634.Geometry.Tri) {N : ℕ} (hN : N = 0) : RTiling (∅ : Set Plane) M N where
  tile := fun i => absurd i.2 (by omega)
  covers := Set.iUnion_eq_empty.mpr (fun i => absurd i.2 (by omega))
  disj := fun i => absurd i.2 (by omega)
  cong := fun i => absurd i.2 (by omega)

/-- **A grid of one frame, carried into a parallelogram of another frame; `n` or `m` may be `0`.** -/
theorem pgram_rt {φ F : ℝ} (hφ : 1 < 4 * φ ^ 2) (hF : 1 < 4 * F ^ 2) {α1 α2 : ℝ} (h1 : 0 < α1) (h2 : 0 < α2)
    {M : Erdos634.Geometry.Tri} {n0 : ℕ} (Rb : RTiling (Phi φ '' Rect 0 α1 0 α2) M n0) (n m : ℕ)
    (P0 e1 e2 : ℝ × ℝ) (hdet : e1.1 * e2.2 - e2.1 * e1.2 ≠ 0)
    (H1 : e1.1 ^ 2 + e1.2 ^ 2 + e1.1 * e1.2 / F = α1 ^ 2)
    (H2 : e2.1 ^ 2 + e2.2 ^ 2 + e2.1 * e2.2 / F = α2 ^ 2)
    (H12 : (e2.1 - e1.1) ^ 2 + (e2.2 - e1.2) ^ 2 + (e2.1 - e1.1) * (e2.2 - e1.2) / F
      = α1 ^ 2 + α2 ^ 2 - α1 * α2 / φ) :
    ∃ S : Set Plane, Nonempty (RTiling S M (n0 * n * m)) ∧ S ⊆ Phi F '' Pg P0 ((n : ℝ) • e1) ((m : ℝ) • e2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, ⟨emptyRT M (by simp)⟩, Set.empty_subset _⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨∅, ⟨emptyRT M (by simp)⟩, Set.empty_subset _⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  obtain ⟨S, hS, hsub⟩ := mapped_grid hφ hF h1 h2 Rb k l P0 e1 e2 hdet H1 H2 H12
  refine ⟨S, hS, ?_⟩
  rw [Nat.cast_succ, Nat.cast_succ]
  exact hsub

section pieces
variable {u g s x : ℝ} (hu : 0 < u) (hg : 0 < g) (hs : 0 ≤ s) (hx : 0 ≤ x)
include hu hg

/-- the triangle `A₁ G A` is the tile at scale `f` -/
noncomputable def RTw1 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = u + g) :
    RTiling (Phi (gF u g) '' Z1 u g s x) (Mod hu hg) (k * k) :=
  scaledRT (gF u g) (hfr hu hg) (wpA1 u g s x) (wpG u g s x) (wpA u g s x) k hk0
    (by
      have h1 : u ≠ 0 := hu.ne'
      have hE : ((wpG u g s x).1 - (wpA1 u g s x).1) * ((wpA u g s x).2 - (wpA1 u g s x).2)
          - ((wpA u g s x).1 - (wpA1 u g s x).1) * ((wpG u g s x).2 - (wpA1 u g s x).2)
          = (u + g) * (g * (2 * u + g)) * (u * (u + g) ^ 2) := by
        simp only [wpG, wpA, wpA1]; ring
      rw [hE]; positivity)
    _
    (baseTri_cong _ _ (ca u g) (cb u g) (((u + g) ^ 2) ^ 2) (hapos hu hg) (hbpos hu hg) (hab_id hu hg) _ _ _
      k hk0 _
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]; simp only [wpA1, wpG, wpA, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]; simp only [wpA1, wpG, wpA, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]; simp only [wpA1, wpG, wpA, ca, cb, gF]; field_simp; ring))

/-- the triangle `F₀ G A` is the tile at scale `f` -/
noncomputable def RTw2 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = u + g) :
    RTiling (Phi (gF u g) '' Z2 u g s x) (Mod hu hg) (k * k) :=
  scaledRT (gF u g) (hfr hu hg) (wpF0 u g s x) (wpG u g s x) (wpA u g s x) k hk0
    (by
      have hE : ((wpG u g s x).1 - (wpF0 u g s x).1) * ((wpA u g s x).2 - (wpF0 u g s x).2)
          - ((wpA u g s x).1 - (wpF0 u g s x).1) * ((wpG u g s x).2 - (wpF0 u g s x).2)
          = -((u + g) * (u + g) ^ 2 * (g * (2 * u + g)) * u) := by
        simp only [wpG, wpA, wpF0]; ring
      rw [hE]
      exact neg_ne_zero.mpr (by positivity))
    _
    (baseTri_cong _ _ (ca u g) (cb u g) (((u + g) ^ 2) ^ 2) (hapos hu hg) (hbpos hu hg) (hab_id hu hg) _ _ _
      k hk0 _
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]; simp only [wpF0, wpG, wpA, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]; simp only [wpF0, wpG, wpA, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]; simp only [wpF0, wpG, wpA, ca, cb, gF]; field_simp; ring))

/-- the triangle `Q_a Q_b Q` is the tile at scale `e = u` -/
noncomputable def RTw5 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = u) :
    RTiling (Phi (gF u g) '' Z5 u g s x) (Mod hu hg) (k * k) :=
  scaledRT (gF u g) (hfr hu hg) (wpQa u g s x) (wpQb u g s x) (wpQ u g s x) k hk0
    (by
      have hE : ((wpQb u g s x).1 - (wpQa u g s x).1) * ((wpQ u g s x).2 - (wpQa u g s x).2)
          - ((wpQ u g s x).1 - (wpQa u g s x).1) * ((wpQb u g s x).2 - (wpQa u g s x).2)
          = (u ^ 2 * (u + g)) * (u * (g * (2 * u + g))) := by
        simp only [wpQa, wpQb, wpQ]; ring
      rw [hE]; positivity)
    _
    (baseTri_cong _ _ (ca u g) (cb u g) (((u + g) ^ 2) ^ 2) (hapos hu hg) (hbpos hu hg) (hab_id hu hg) _ _ _
      k hk0 _
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]; simp only [wpQa, wpQb, wpQ, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]; simp only [wpQa, wpQb, wpQ, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
          rw [hk]; simp only [wpQa, wpQb, wpQ, ca, cb, gF]; field_simp; ring))

/-- `Z3`: the parallelogram `F₀ G Z_f Z₀`, `(u + g) × s` cells (`f × (z − f)`), cell type `C` -/
theorem RTw3 (n m : ℕ) (hn : (n : ℝ) = u + g) (hm : (m : ℝ) = s) :
    ∃ S : Set Plane, Nonempty (RTiling S (Mod hu hg) (2 * n * m)) ∧ S ⊆ Phi (gF u g) '' Z3 u g s x := by
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
  have h3 : 3 * (u + g) ^ 2 - u ^ 2 ≠ 0 := (hPpos hu hg).ne'
  have h := pgram_rt (hφβ hu hg) (hfr hu hg) (hapos hu hg) (pow_pos (hvpos hu hg) 2) (cellC hu hg) n m
    (wpF0 u g s x) (wve1 u g) (wve2 u g)
    (by have hE : (wve1 u g).1 * (wve2 u g).2 - (wve2 u g).1 * (wve1 u g).2
            = (u + g) * (2 * u ^ 2 * g + u * g ^ 2) := by
          simp only [wve1, wve2]; field_simp; ring
        rw [hE]; positivity)
    (by simp only [wve1, ca, gF]; field_simp; ring) (by simp only [wve2]; ring)
    (by simp only [wve1, wve2, ca, gF, φβ]; field_simp; ring)
  rw [hn, hm] at h
  exact h

/-- `Z4`: the parallelogram `Z₀ Q Q_a Z_f`, `x × u` cells (`x × e`), cell type `C` -/
theorem RTw4 (n m : ℕ) (hn : (n : ℝ) = x) (hm : (m : ℝ) = u) :
    ∃ S : Set Plane, Nonempty (RTiling S (Mod hu hg) (2 * n * m)) ∧ S ⊆ Phi (gF u g) '' Z4 u g s x := by
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
  have h3 : 3 * (u + g) ^ 2 - u ^ 2 ≠ 0 := (hPpos hu hg).ne'
  have h := pgram_rt (hφβ hu hg) (hfr hu hg) (hapos hu hg) (pow_pos (hvpos hu hg) 2) (cellC hu hg) n m
    (wpZ0 u g s x) (wvc1 u g) (wvc2 u g)
    (by have hE : (wvc1 u g).1 * (wvc2 u g).2 - (wvc2 u g).1 * (wvc1 u g).2
            = -((u ^ 2 + u * g) * (2 * u * g + g ^ 2)) := by
          simp only [wvc1, wvc2]; ring
        rw [hE]; exact neg_ne_zero.mpr (by positivity))
    (by simp only [wvc1, ca, gF]; field_simp; ring) (by simp only [wvc2, gF]; field_simp; ring)
    (by simp only [wvc1, wvc2, ca, gF, φβ]; field_simp; ring)
  rw [hn, hm] at h
  exact h

/-- `Z6`: the rectangle `A₁ Q₅ Q_b G`, `(M − 1) f × f` cells, cell type `A` -/
theorem RTw6 (n m : ℕ) (hn : (n : ℝ) = (wmM u g s x - 1) * (u + g)) (hm : (m : ℝ) = u + g) :
    ∃ S : Set Plane, Nonempty (RTiling S (Mod hu hg) (2 * n * m)) ∧ S ⊆ Phi (gF u g) '' Z6 u g s x := by
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + g ≠ 0 := (hvpos hu hg).ne'
  have h := pgram_rt (hfr hu hg) (hfr hu hg) (hbpos hu hg) (hapos hu hg) (cellA hu hg) n m
    (wpA1 u g s x) (wvr1 u g) (wvr2 u g)
    (by have hE : (wvr1 u g).1 * (wvr2 u g).2 - (wvr2 u g).1 * (wvr1 u g).2
            = (2 * u * g + g ^ 2) * (u ^ 2 + u * g) := by
          simp only [wvr1, wvr2]; ring
        rw [hE]; positivity)
    (by simp only [wvr1, cb, gF]; field_simp; ring) (by simp only [wvr2, ca, gF]; field_simp; ring)
    (by simp only [wvr1, wvr2, ca, cb, gF]; field_simp; ring)
  rw [hn, hm] at h
  exact h

end pieces

/-! ## Assembly: the seven regions fill `W_M` -/

/-- the seven regions in the plane; the three parallelograms are given as sets -/
noncomputable def wregionOf (u g s x : ℝ) (S3 S4 S6 : Set Plane) : Fin 7 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi (gF u g) '' Z0 u g s x
  | ⟨1, _⟩ => Phi (gF u g) '' Z1 u g s x
  | ⟨2, _⟩ => Phi (gF u g) '' Z2 u g s x
  | ⟨3, _⟩ => S3
  | ⟨4, _⟩ => S4
  | ⟨5, _⟩ => Phi (gF u g) '' Z5 u g s x
  | ⟨6, _⟩ => S6
  | ⟨k + 7, h⟩ => absurd h (by omega)

/-- the tile counts of the seven regions -/
def wcnt (n0 kf ks kx ku kM : ℕ) : Fin 7 → ℕ := fun i => match i with
  | ⟨0, _⟩ => n0
  | ⟨1, _⟩ => kf * kf
  | ⟨2, _⟩ => kf * kf
  | ⟨3, _⟩ => 2 * kf * ks
  | ⟨4, _⟩ => 2 * kx * ku
  | ⟨5, _⟩ => ku * ku
  | ⟨6, _⟩ => 2 * kM * kf
  | ⟨k + 7, h⟩ => absurd h (by omega)

theorem sum_wcnt (n0 kf ks kx ku kM : ℕ) :
    ∑ a, wcnt n0 kf ks kx ku kM a = n0 + kf * kf + kf * kf + 2 * kf * ks + 2 * kx * ku + ku * ku + 2 * kM * kf := by
  rw [Fin.sum_univ_seven]
  rfl

section assemble
variable {u g s x : ℝ} (hu : 0 < u) (hg : 0 < g) (hs : 0 ≤ s) (hx : 0 ≤ x)
include hu hg hs hx

/-- the target `W_M` -/
noncomputable def tgtW : Erdos634.Geometry.Tri :=
  WTriR (gF u g) (hF1 hu hg) (wU u g s x) (wV u g s x) (wU_pos hu hg hs hx) (wV_pos hu hg hs hx)

theorem carrier_tgtW : (tgtW hu hg hs hx).carrier = Phi (gF u g) '' ZT u g s x :=
  carrier_WTriR _ _ _ _ _ _

open MeasureTheory in
theorem vol_tgtW : volume (tgtW hu hg hs hx).carrier
    = ENNReal.ofReal (|sD (gF u g) / (2 * gF u g)| * (wU u g s x * wV u g s x))
      * volume Erdos634.AreaDet.stdCarrier := by
  have hu0 := wU_pos hu hg hs hx
  have hv0 := wV_pos hu hg hs hx
  have hdet : (((wU u g s x, wV u g s x) : ℝ × ℝ).1 - ((wU u g s x, (0 : ℝ)) : ℝ × ℝ).1)
        * ((((0 : ℝ), wV u g s x) : ℝ × ℝ).2 - ((wU u g s x, (0 : ℝ)) : ℝ × ℝ).2)
      - ((((0 : ℝ), wV u g s x) : ℝ × ℝ).1 - ((wU u g s x, (0 : ℝ)) : ℝ × ℝ).1)
        * (((wU u g s x, wV u g s x) : ℝ × ℝ).2 - ((wU u g s x, (0 : ℝ)) : ℝ × ℝ).2)
      = wU u g s x * wV u g s x := by ring
  have hne : (((wU u g s x, wV u g s x) : ℝ × ℝ).1 - ((wU u g s x, (0 : ℝ)) : ℝ × ℝ).1)
        * ((((0 : ℝ), wV u g s x) : ℝ × ℝ).2 - ((wU u g s x, (0 : ℝ)) : ℝ × ℝ).2)
      - ((((0 : ℝ), wV u g s x) : ℝ × ℝ).1 - ((wU u g s x, (0 : ℝ)) : ℝ × ℝ).1)
        * (((wU u g s x, wV u g s x) : ℝ × ℝ).2 - ((wU u g s x, (0 : ℝ)) : ℝ × ℝ).2)
      ≠ 0 := by rw [hdet]; exact (mul_pos hu0 hv0).ne'
  have hc : (tgtW hu hg hs hx).carrier
      = (triC (gF u g) (hfr hu hg) (wU u g s x, 0) (wU u g s x, wV u g s x) (0, wV u g s x) hne).carrier := by
    rw [carrier_tgtW, carrier_triC]
    show Phi (gF u g) '' WS _ _ = _
    rw [← hull_WS _ _ hu0 hv0]
  rw [hc, vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  rw [hdet, abs_of_pos (mul_pos hu0 hv0)]

/-- **The strip step, real parameters.**  A tiling of `W_{M−1}` by `n₀` tiles gives a dissection of `W_M`
(`M = wmM u g s x = (z f + x e)/b`, `z = f + s`). -/
theorem strip_real (n0 kf ks kx ku kM : ℕ)
    (hn0 : (n0 : ℝ) = cQ u g * (wmM u g s x - 1) ^ 2)
    (hkf0 : 0 < kf) (hkf : (kf : ℝ) = u + g) (hks : (ks : ℝ) = s) (hkx : (kx : ℝ) = x)
    (hku0 : 0 < ku) (hku : (ku : ℝ) = u) (hkM : (kM : ℝ) = (wmM u g s x - 1) * (u + g))
    (R0 : RTiling (Phi (gF u g) '' Wt (cA u g) (cB u g) (wmM u g s x - 1)) (Mod hu hg) n0) :
    ∃ (N : ℕ) (D : CongruentDissection N), (N : ℝ) = cQ u g * wmM u g s x ^ 2 ∧ D.model = Mod hu hg ∧
      D.target = tgtW hu hg hs hx ∧
      straddlers D.toDissection (skewY (gF u g)) (wV u g s x - cB u g) = ∅ := by
  obtain ⟨S3, ⟨R3⟩, h3⟩ := RTw3 hu hg kf ks hkf hks
  obtain ⟨S4, ⟨R4⟩, h4⟩ := RTw4 hu hg kx ku hkx hku
  obtain ⟨S6, ⟨R6⟩, h6⟩ := RTw6 hu hg kM kf hkM hkf
  have R0s : RTiling (Phi (gF u g) '' Z0 u g s x) (Mod hu hg) n0 := shiftR R0 (cA u g, 0)
  have Rall : ∀ a : Fin 7, RTiling (wregionOf u g s x S3 S4 S6 a) (Mod hu hg) (wcnt n0 kf ks kx ku kM a) :=
    fun a => match a with
    | ⟨0, _⟩ => R0s
    | ⟨1, _⟩ => RTw1 hu hg kf hkf0 hkf
    | ⟨2, _⟩ => RTw2 hu hg kf hkf0 hkf
    | ⟨3, _⟩ => R3
    | ⟨4, _⟩ => R4
    | ⟨5, _⟩ => RTw5 hu hg ku hku0 hku
    | ⟨6, _⟩ => R6
    | ⟨k + 7, h⟩ => absurd h (by omega)
  have sub_all : ∀ a : Fin 7, wregionOf u g s x S3 S4 S6 a ⊆ Phi (gF u g) '' Wf u g s x a := fun a => match a with
    | ⟨0, _⟩ => subset_rfl
    | ⟨1, _⟩ => subset_rfl
    | ⟨2, _⟩ => subset_rfl
    | ⟨3, _⟩ => h3
    | ⟨4, _⟩ => h4
    | ⟨5, _⟩ => subset_rfl
    | ⟨6, _⟩ => h6
    | ⟨k + 7, h⟩ => absurd h (by omega)
  have hS_all : ∀ a b : Fin 7, a ≠ b →
      Disjoint (interior (wregionOf u g s x S3 S4 S6 a)) (interior (wregionOf u g s x S3 S4 S6 b)) :=
    fun a b hab => (disjoint_image' (hfr hu hg) (dW_all hu hg hs hx a b hab)).mono (interior_mono (sub_all a))
      (interior_mono (sub_all b))
  have hsub_all : ∀ a : Fin 7, wregionOf u g s x S3 S4 S6 a ⊆ (tgtW hu hg hs hx).carrier := fun a => by
    rw [carrier_tgtW]
    exact (sub_all a).trans (Set.image_mono (Wf_sub hu hg hs hx a))
  have hsumR : ((∑ a, wcnt n0 kf ks kx ku kM a : ℕ) : ℝ) = cQ u g * wmM u g s x ^ 2 := by
    rw [sum_wcnt]
    push_cast
    rw [hn0, hkf, hks, hkx, hku, hkM]
    have h : g * (2 * u + g) ≠ 0 := by positivity
    simp only [cQ, wmM]
    field_simp
    ring
  have hvol : ((∑ a, wcnt n0 kf ks kx ku kM a : ℕ) : ENNReal) * MeasureTheory.volume (Mod hu hg).carrier
      = MeasureTheory.volume (tgtW hu hg hs hx).carrier := by
    have hNR : (0 : ℝ) ≤ ((∑ a, wcnt n0 kf ks kx ku kM a : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [volMod hu hg, vol_tgtW hu hg hs hx, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNR, hsumR]
    congr 2
    rw [← cA_eq hu hg hs hx, ← cB_eq hu hg hs hx]
    simp only [cQ, cA, cB, ca, cb]; ring
  obtain ⟨D, hM, hT, hreg⟩ := pack_exists_tracked (M := Mod hu hg) (T := tgtW hu hg hs hx)
    (wregionOf u g s x S3 S4 S6) _ Rall hS_all hsub_all hvol
  have hside : ∀ e, (∀ y ∈ (D.tile e).carrier, skewY (gF u g) y ≤ wV u g s x - cB u g) ∨
      (∀ y ∈ (D.tile e).carrier, wV u g s x - cB u g ≤ skewY (gF u g) y) := by
    intro e
    obtain ⟨a, ha⟩ := hreg e
    have key : ∀ y ∈ (D.tile e).carrier, ∃ p ∈ Wf u g s x a, Phi (gF u g) p = y := fun y hy => sub_all a (ha hy)
    match a, key with
    | ⟨0, _⟩, key =>
      left; intro y hy; obtain ⟨p, hp, rfl⟩ := key y hy
      rw [skewY_Phi (hF1 hu hg)]; exact y_ge_Z0 hu hg hs hx p hp
    | ⟨1, _⟩, key =>
      right; intro y hy; obtain ⟨p, hp, rfl⟩ := key y hy
      rw [skewY_Phi (hF1 hu hg)]; exact yc_1 hu hg hs hx p hp
    | ⟨2, _⟩, key =>
      right; intro y hy; obtain ⟨p, hp, rfl⟩ := key y hy
      rw [skewY_Phi (hF1 hu hg)]; exact yc_2 hu hg hs hx p hp
    | ⟨3, _⟩, key =>
      right; intro y hy; obtain ⟨p, hp, rfl⟩ := key y hy
      rw [skewY_Phi (hF1 hu hg)]; exact yc_3 hu hg hs hx p hp
    | ⟨4, _⟩, key =>
      right; intro y hy; obtain ⟨p, hp, rfl⟩ := key y hy
      rw [skewY_Phi (hF1 hu hg)]; exact yc_4 hu hg hs hx p hp
    | ⟨5, _⟩, key =>
      right; intro y hy; obtain ⟨p, hp, rfl⟩ := key y hy
      rw [skewY_Phi (hF1 hu hg)]; exact yc_5 hu hg hs hx p hp
    | ⟨6, _⟩, key =>
      right; intro y hy; obtain ⟨p, hp, rfl⟩ := key y hy
      rw [skewY_Phi (hF1 hu hg)]; exact yc_6 hu hg hs hx p hp
    | ⟨k + 7, h⟩, _ => exact absurd h (by omega)
  exact ⟨_, D, hsumR, hM, hT, straddlers_empty_of_sides D.toDissection _ _ hside⟩

end assemble

/-! ## The natural-number step -/

/-- the target `W_M` of the strip step is the frame triangle `W_T` of `CollarG` at `T = M = wmM u g s x` -/
theorem WTriR_congr {F : ℝ} (hF : 1 < F) {A A' B B' : ℝ} (hA : 0 < A) (hB : 0 < B) (hA' : 0 < A') (hB' : 0 < B')
    (h1 : A = A') (h2 : B = B') : WTriR F hF A B hA hB = WTriR F hF A' B' hA' hB' := by
  subst h1; subst h2; rfl

theorem tgtW_eq_WT {u g s x : ℝ} (hu : 0 < u) (hg : 0 < g) (hs : 0 ≤ s) (hx : 0 ≤ x) (M : ℝ)
    (hMR : wmM u g s x = M) (hM : 0 < M) :
    tgtW hu hg hs hx = Erdos634.Draft.CollarG.WT hu hg M hM := by
  unfold tgtW Erdos634.Draft.CollarG.WT
  have e1 : wU u g s x = cA u g * M := by rw [← hMR]; exact (cA_eq hu hg hs hx).symm
  have e2 : wV u g s x = cB u g * M := by rw [← hMR]; exact (cB_eq hu hg hs hx).symm
  exact WTriR_congr _ _ _ _ _ e1 e2

/-- **The strip step for naturals, as a dissection with the chord uncrossed**: `W_{M−1}` of the member `(u, u + g)` has a tiling, `f = u + g ≤ z`, `x u + z f = M b`
(`b = f² − u²`), `M ≥ 2`; then the frame triangle `W_M` has a congruent dissection (with the model `Mod`) in which no tile has points strictly on both sides of the
chord `y = cB (M − 1)` (the chord `A₁ Q₁`, the line that cuts off the copy of `W_{M−1}` at the corner `B`). -/
theorem strip_nat_dis (u g M z x : ℕ) (hu : 0 < u) (hg : 0 < g) (hz : u + g ≤ z) (hM : 2 ≤ M)
    (heq : x * u + z * (u + g) = M * ((u + g) ^ 2 - u ^ 2)) (h : WTilable u (u + g) (M - 1)) :
    ∃ D : CongruentDissection ((2 * (u + g) ^ 2 - u ^ 2) * M ^ 2),
      D.model = Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg) ∧
      D.target = Erdos634.Draft.CollarG.WT (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg)
        (M : ℝ) (Nat.cast_pos.mpr (by omega)) ∧
      straddlers D.toDissection (skewY (gF (u : ℝ) (g : ℝ))) (cB (u : ℝ) (g : ℝ) * ((M : ℝ) - 1)) = ∅ := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  obtain ⟨s, hs⟩ : ∃ s, z = u + g + s := ⟨z - (u + g), by omega⟩
  subst hs
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hbR : (((u + g) ^ 2 - u ^ 2 : ℕ) : ℝ) = (g : ℝ) * (2 * (u : ℝ) + g) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left (by omega) 2)]; push_cast; ring
  have hMR : wmM (u : ℝ) (g : ℝ) (s : ℝ) (x : ℝ) = (M : ℝ) := by
    have hb : (g : ℝ) * (2 * (u : ℝ) + g) ≠ 0 := by positivity
    have h1 := congrArg (Nat.cast : ℕ → ℝ) heq
    push_cast [hbR] at h1
    simp only [wmM]
    rw [div_eq_iff hb]
    linarith
  have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨R⟩ := (wTilable_iff_frame u g (M - 1) hu hg (by omega)).mp h
  have R0 : RTiling (Phi (gF (u : ℝ) (g : ℝ)) '' Wt (cA (u : ℝ) (g : ℝ)) (cB (u : ℝ) (g : ℝ))
      (wmM (u : ℝ) (g : ℝ) (s : ℝ) (x : ℝ) - 1)) (Mod hu' hg') ((2 * (u + g) ^ 2 - u ^ 2) * (M - 1) ^ 2) :=
    RTiling.cast (by rw [hMR, hM1]) R
  have h1 : u ^ 2 ≤ 2 * (u + g) ^ 2 := by nlinarith [Nat.zero_le g, Nat.zero_le u]
  have hn0 : (((2 * (u + g) ^ 2 - u ^ 2) * (M - 1) ^ 2 : ℕ) : ℝ)
      = cQ (u : ℝ) (g : ℝ) * (wmM (u : ℝ) (g : ℝ) (s : ℝ) (x : ℝ) - 1) ^ 2 := by
    have h2 : (((2 * (u + g) ^ 2 - u ^ 2) * (M - 1) ^ 2 : ℕ) : ℝ)
        = (2 * ((u : ℝ) + g) ^ 2 - (u : ℝ) ^ 2) * ((M : ℝ) - 1) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_sub h1]; push_cast [hM1]; ring
    rw [h2, hMR]; simp only [cQ]
  obtain ⟨N, D, hN, hMd, hT, hst⟩ := strip_real hu' hg' hs0 hx0 ((2 * (u + g) ^ 2 - u ^ 2) * (M - 1) ^ 2) (u + g) s x u
    ((M - 1) * (u + g)) hn0 (by omega) (Nat.cast_add u g) rfl rfl hu rfl
    (by rw [hMR, Nat.cast_mul, hM1, Nat.cast_add]) R0
  have hNn : N = (2 * (u + g) ^ 2 - u ^ 2) * M ^ 2 := by
    have : (N : ℝ) = (((2 * (u + g) ^ 2 - u ^ 2) * M ^ 2 : ℕ) : ℝ) := by
      rw [hN, hMR, Nat.cast_mul, Nat.cast_sub h1]; simp only [cQ]; push_cast; ring
    exact_mod_cast this
  subst hNn
  refine ⟨D, hMd, by rw [hT]; exact tgtW_eq_WT hu' hg' hs0 hx0 (M : ℝ) hMR hMpos, ?_⟩
  have hc : wV (u : ℝ) (g : ℝ) (s : ℝ) (x : ℝ) - cB (u : ℝ) (g : ℝ) = cB (u : ℝ) (g : ℝ) * ((M : ℝ) - 1) := by
    rw [← cB_eq hu' hg' hs0 hx0, hMR]; ring
  rw [hc] at hst
  exact hst

/-- **The strip step for naturals**: `W_{M−1}` of the member `(u, u + g)` has a tiling, `f = u + g ≤ z`, `x u + z f = M b`
(`b = f² − u²`), `M ≥ 2`; then `W_M` has a tiling. -/
theorem strip_nat (u g M z x : ℕ) (hu : 0 < u) (hg : 0 < g) (hz : u + g ≤ z) (hM : 2 ≤ M)
    (heq : x * u + z * (u + g) = M * ((u + g) ^ 2 - u ^ 2)) (h : WTilable u (u + g) (M - 1)) :
    WTilable u (u + g) M := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨D, hMd, hT, -⟩ := strip_nat_dis u g M z x hu hg hz hM heq h
  have hc : D.target.carrier = Phi (gF (u : ℝ) (g : ℝ)) '' Wt (cA (u : ℝ) (g : ℝ)) (cB (u : ℝ) (g : ℝ)) (M : ℝ) := by
    rw [hT]; exact Erdos634.Draft.CollarG.carrier_WT hu' hg' (M : ℝ) hMpos
  exact (wTilable_iff_frame u g M hu hg (by omega)).mpr
    ⟨RegionTiling.remodel (RTiling.cast hc (ofCD D)) (by rw [hMd]; exact Erdos634.Geometry.Tri.Congruent.refl _)⟩

/-! ## The strip step in the notation of the paper -/

/-- **`prop:wstrip` (c), first statement, and the existence in (a)** in the notation of the paper (`e`, `f`, `b = f² − e²`): let `M ≥ 2` and let `z` be a natural number with `z ≡ M f (mod e)`, `f ≤ z`, `z f ≤ M b`.  Then `x = (M b − z f)/e` is a natural number
with `x e + z f = M b`, and if `W_{M−1}(e, f)` has a tiling then so has `W_M(e, f)` (the strip of the five lattice pieces and the copy of `W_{M−1}` at the corner `B`). -/
theorem wstrip_step (e f M z : ℕ) (he : 1 ≤ e) (hef : e < f) (hM : 2 ≤ M) (hmod : z ≡ M * f [MOD e])
    (hz : f ≤ z) (hzM : z * f ≤ M * (f ^ 2 - e ^ 2)) (h : WTilable e f (M - 1)) :
    ∃ x : ℕ, x * e + z * f = M * (f ^ 2 - e ^ 2) ∧ WTilable e f M := by
  -- `e ∣ M b - z f`: `z ≡ M f` and `b = f² - e²`
  have hdivN : e ∣ M * (f ^ 2 - e ^ 2) - z * f := by
    have h1 : (e : ℤ) ∣ (M : ℤ) * f - z := by
      have := (Nat.modEq_iff_dvd.mp hmod)
      push_cast at this
      exact this
    have hb : (((f ^ 2 - e ^ 2 : ℕ)) : ℤ) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
      rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2)]; push_cast; ring
    have h2 : (e : ℤ) ∣ ((M * (f ^ 2 - e ^ 2) - z * f : ℕ) : ℤ) := by
      have h3 : ((M * (f ^ 2 - e ^ 2) - z * f : ℕ) : ℤ) = f * ((M : ℤ) * f - z) - M * (e : ℤ) ^ 2 := by
        rw [Nat.cast_sub hzM]; push_cast [hb]; ring
      rw [h3]
      exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right (dvd_pow_self (e : ℤ) two_ne_zero) _)
    exact Int.natCast_dvd_natCast.mp h2
  obtain ⟨x, hx⟩ := hdivN
  have hxeq : x * e + z * f = M * (f ^ 2 - e ^ 2) := by
    have h4 := Nat.sub_add_cancel hzM
    rw [hx] at h4
    linarith [mul_comm x e]
  obtain ⟨g, rfl⟩ : ∃ g, f = e + g := ⟨f - e, by omega⟩
  have hg : 0 < g := by omega
  exact ⟨x, hxeq, strip_nat e g M z x he hg hz hM hxeq h⟩

end Erdos634.Draft.WStripG

#print axioms Erdos634.Draft.WStripG.skewY_Phi
#print axioms Erdos634.Draft.WStripG.pgram_rt
#print axioms Erdos634.Draft.WStripG.strip_real
#print axioms Erdos634.Draft.WStripG.strip_nat_dis
#print axioms Erdos634.Draft.WStripG.strip_nat
#print axioms Erdos634.Draft.WStripG.wstrip_step
