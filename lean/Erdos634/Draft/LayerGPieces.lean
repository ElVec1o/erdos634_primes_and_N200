/-
Draft/LayerGPieces.lean  In `AllThreshold`.

PAPER.  `prop:layerall` (b): the trapezoid cut from `T_M(e, f)` by the line parallel to the base at the height `eH₁` "can be cut into `(2Me − e²)(3f² − e²)` copies of the tile", by the layout
(the tile at scale `ef`; `x_a` columns of `ef` parallelograms `a × b`; `eM` columns of `b` parallelograms `b × a`; the six pieces of Paliy's cap).

WHAT IS PROVED HERE.  `Draft/LayerG.lean` proves the layer as a step between triangles (`layer_real`: a tiling of the translate of `T_{M−e}` together with the nine pieces gives a tiling of `T_M`).  Here the nine pieces alone:
* `unionFam`: the union of region tilings with pairwise disjoint interiors is a tiling of the union (the tiles are the tiles of the pieces), with the sum of the counts;
* `layer_pieces`: **the layer of `prop:layerall` (b) as a tiling of the union of its nine pieces.**  For the member `(u, u + g)` and a real scale `M` with `x_a ≥ 0` (`2f(M − e) ≥ b`), the nine pieces `LS1, LRa, LRb, Z3, …, Z8` (the tile at scale `ef`, the rectangle of
  `ef × x_a` cells, the rectangle of `b × eM` cells, the six pieces of the cap) are tiled by `(2 M e − e²)(3f² − e²)` copies of the tile; the union `Λ` of the tiled pieces lies in the trapezoid `T_M ∩ {x ≥ A (M − e)}` of the frame.

NOT PROVED HERE: that `Λ` is the whole trapezoid as a set (the library's covering lemma, `ConvexCover.covers_of_volume`, is for a triangle as target).  The trapezoid is filled in the sense of `LayerG.layer_real`: the nine pieces together with a tiling of the translate of `T_{M−e}` fill the triangle `T_M`
(there the covering follows from the area identity).

No sorry, no native_decide.
-/
import Erdos634.Draft.LayerG

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.LayerG
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (disjoint_image')
open Erdos634.Draft.CollarG (gF hF1 hfr Mod ca cb cA cB cC Z3 Z4 Z5 Z8 RT3 RT4 RT5 RT6 RT7 RT8)
open Erdos634.Draft.LayerE1 (shift_sub_exists)

/-! ## The union of region tilings -/

/-- the tile of the family `R` indexed by a pair (region, tile of the region) -/
def tileOf {m : ℕ} {M : Erdos634.Geometry.Tri} {S : Fin m → Set Plane} {n : Fin m → ℕ}
    (R : ∀ a, RTiling (S a) M (n a)) (p : (a : Fin m) × Fin (n a)) : Erdos634.Geometry.Tri := (R p.1).tile p.2

theorem tileOf_sub {m : ℕ} {M : Erdos634.Geometry.Tri} {S : Fin m → Set Plane} {n : Fin m → ℕ}
    (R : ∀ a, RTiling (S a) M (n a)) (p : (a : Fin m) × Fin (n a)) : (tileOf R p).carrier ⊆ S p.1 := by
  intro x hx
  rw [← (R p.1).covers]
  exact Set.mem_iUnion.mpr ⟨_, hx⟩

theorem tileOf_disj {m : ℕ} {M : Erdos634.Geometry.Tri} {S : Fin m → Set Plane} {n : Fin m → ℕ}
    (R : ∀ a, RTiling (S a) M (n a)) (hS : ∀ a b, a ≠ b → Disjoint (interior (S a)) (interior (S b)))
    (p q : (a : Fin m) × Fin (n a)) (hne : p ≠ q) :
    Disjoint (interior (tileOf R p).carrier) (interior (tileOf R q).carrier) := by
  obtain ⟨a, x⟩ := p
  obtain ⟨b, y⟩ := q
  by_cases hab : a = b
  · subst hab
    have : x ≠ y := fun h => hne (by rw [h])
    exact (R a).disj this
  · exact (hS a b hab).mono (interior_mono (tileOf_sub R ⟨a, x⟩)) (interior_mono (tileOf_sub R ⟨b, y⟩))

/-- **The union of region tilings with pairwise disjoint interiors is a tiling of the union.** -/
noncomputable def unionFam {m : ℕ} {M : Erdos634.Geometry.Tri} (S : Fin m → Set Plane) (n : Fin m → ℕ)
    (R : ∀ a, RTiling (S a) M (n a)) (hS : ∀ a b, a ≠ b → Disjoint (interior (S a)) (interior (S b))) :
    RTiling (⋃ a, S a) M (∑ a, n a) where
  tile := fun e => tileOf R (finSigmaFinEquiv.symm e)
  covers := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨e, hx⟩
      exact ⟨(finSigmaFinEquiv.symm e).1, tileOf_sub R _ hx⟩
    · rintro ⟨a, hx⟩
      rw [← (R a).covers] at hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      refine ⟨finSigmaFinEquiv ⟨a, j⟩, ?_⟩
      show x ∈ (tileOf R (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩))).carrier
      rw [Equiv.symm_apply_apply]
      exact hj
  disj := fun i j hij =>
    tileOf_disj R hS _ _ (fun h => hij (finSigmaFinEquiv.symm.injective h))
  cong := fun e => (R _).cong _

/-! ## The nine pieces of the layer -/

/-- the count of the nine pieces -/
theorem sum_lcnt9 (n0 k3 k4 nA mA nB mB k6 l6 k7 l7 : ℕ) :
    ∑ i : Fin 9, lcnt n0 k3 k4 nA mA nB mB k6 l6 k7 l7 i.succ
      = k3 * k3 + (2 * nA * mA + 2 * nB * mB + k3 * k3 + k4 * k4 + k4 * k4 + 2 * (k6 + 1) * (l6 + 1)
          + 2 * (k7 + 1) * (l7 + 1) + k4 * k4) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_eight]
  rfl

/-- the family of the nine tilings of the layer -/
noncomputable def Rfam9 {u g M : ℝ} (hu : 0 < u) (hg : 0 < g) (n0 k3 k4 nA mA nB mB k6 l6 k7 l7 : ℕ)
    {Sa Sb S6 S7 : Set Plane}
    (R1 : RTiling (Phi (gF u g) '' LS1 u g M) (Mod hu hg) (k3 * k3))
    (Ra : RTiling Sa (Mod hu hg) (2 * nA * mA)) (Rb : RTiling Sb (Mod hu hg) (2 * nB * mB))
    (R3 : RTiling (Phi (gF u g) '' Sh (lvsh u g M) (Z3 u g 1)) (Mod hu hg) (k3 * k3))
    (R4 : RTiling (Phi (gF u g) '' Sh (lvsh u g M) (Z4 u g 1)) (Mod hu hg) (k4 * k4))
    (R5 : RTiling (Phi (gF u g) '' Sh (lvsh u g M) (Z5 u g 1)) (Mod hu hg) (k4 * k4))
    (R6 : RTiling S6 (Mod hu hg) (2 * (k6 + 1) * (l6 + 1)))
    (R7 : RTiling S7 (Mod hu hg) (2 * (k7 + 1) * (l7 + 1)))
    (R8 : RTiling (Phi (gF u g) '' Sh (lvsh u g M) (Z8 u g 1)) (Mod hu hg) (k4 * k4)) :
    ∀ i : Fin 9, RTiling (regionL u g M Sa Sb S6 S7 i.succ) (Mod hu hg)
      (lcnt n0 k3 k4 nA mA nB mB k6 l6 k7 l7 i.succ) :=
  fun i => match i with
  | ⟨0, _⟩ => R1
  | ⟨1, _⟩ => Ra
  | ⟨2, _⟩ => Rb
  | ⟨3, _⟩ => R3
  | ⟨4, _⟩ => R4
  | ⟨5, _⟩ => R5
  | ⟨6, _⟩ => R6
  | ⟨7, _⟩ => R7
  | ⟨8, _⟩ => R8
  | ⟨k + 9, h⟩ => absurd h (by omega)

section assemble
variable {u g M : ℝ} (hu : 0 < u) (hg : 0 < g) (hx : 0 ≤ lxa u g M)
include hu hg hx

/-- **`prop:layerall` (b): the layer as a tiling of its nine pieces.**  Member `(u, u + g)`, real scale `M` with `x_a ≥ 0`.  The tile at scale `ef`, the rectangle of `ef × x_a` cells `b × a`, the rectangle of `b × eM` cells `a × b` and the six pieces of the cap
(`Z3, …, Z8` of `CollarGGeom` at `σ = 1`, translated by `(A (M − f − 1), 0)`) are tiled by `(2 M e − e²)(3f² − e²)` copies of the tile; the union `Λ` of the nine tiled pieces lies in the trapezoid `T_M ∩ {x ≥ A (M − e)}`. -/
theorem layer_pieces (k3 k4 nA mA nB mB k6 l6 k7 l7 : ℕ)
    (hk30 : 0 < k3) (hk3 : (k3 : ℝ) = ca u g) (hk40 : 0 < k4) (hk4 : (k4 : ℝ) = u * g)
    (hnA : (nA : ℝ) = u * (u + g)) (hmA : (mA : ℝ) = lxa u g M) (hnB : (nB : ℝ) = cb u g)
    (hmB : (mB : ℝ) = u * M)
    (hk6 : (k6 : ℝ) + 1 = g * (u + g)) (hl6 : (l6 : ℝ) + 1 = u * g) (hk7 : (k7 : ℝ) + 1 = u * g)
    (hl7 : (l7 : ℝ) + 1 = u ^ 2) :
    ∃ (Λ : Set Plane) (N : ℕ) (R : RTiling Λ (Mod hu hg) N),
      Λ ⊆ Phi (gF u g) '' (LT u g M ∩ {p | lX0 u g M ≤ p.1}) ∧ (N : ℝ) = (2 * M * u - u ^ 2) * cP u g := by
  obtain ⟨Sa, ⟨Ra⟩, ha⟩ := RLa hu hg nA mA hnA hmA
  obtain ⟨Sb, ⟨Rb⟩, hb⟩ := RLb hu hg nB mB hnB hmB
  obtain ⟨S6, ⟨R6⟩, h6⟩ := shift_sub_exists (lvsh u g M) (RT6 hu hg (one_pos : (0 : ℝ) < 1) k6 l6 hk6 hl6)
  obtain ⟨S7, ⟨R7⟩, h7⟩ := shift_sub_exists (lvsh u g M) (RT7 hu hg (one_pos : (0 : ℝ) < 1) k7 l7 hk7 hl7)
  have sub_all : ∀ a : Fin 10, regionL u g M Sa Sb S6 S7 a ⊆ Phi (gF u g) '' Lf u g M a := fun a => match a with
    | ⟨0, _⟩ => subset_rfl
    | ⟨1, _⟩ => subset_rfl
    | ⟨2, _⟩ => ha
    | ⟨3, _⟩ => hb
    | ⟨4, _⟩ => subset_rfl
    | ⟨5, _⟩ => subset_rfl
    | ⟨6, _⟩ => subset_rfl
    | ⟨7, _⟩ => h6
    | ⟨8, _⟩ => h7
    | ⟨9, _⟩ => subset_rfl
    | ⟨k + 10, h⟩ => absurd h (by omega)
  have hS9 : ∀ i j : Fin 9, i ≠ j →
      Disjoint (interior (regionL u g M Sa Sb S6 S7 i.succ)) (interior (regionL u g M Sa Sb S6 S7 j.succ)) :=
    fun i j hij => (disjoint_image' (hfr hu hg) (dL_all hu hg hx i.succ j.succ
      (fun h => hij (Fin.succ_injective _ h)))).mono (interior_mono (sub_all i.succ)) (interior_mono (sub_all j.succ))
  refine ⟨_, _, unionFam (fun i : Fin 9 => regionL u g M Sa Sb S6 S7 i.succ)
    (fun i : Fin 9 => lcnt 0 k3 k4 nA mA nB mB k6 l6 k7 l7 i.succ)
    (Rfam9 hu hg 0 k3 k4 nA mA nB mB k6 l6 k7 l7 (RLs1 hu hg k3 hk30 hk3)
      Ra Rb (shiftR (RT3 hu hg (one_pos : (0 : ℝ) < 1) k3 hk30 hk3) (lvsh u g M))
      (shiftR (RT4 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M))
      (shiftR (RT5 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M)) R6 R7
      (shiftR (RT8 hu hg (one_pos : (0 : ℝ) < 1) k4 hk40 hk4) (lvsh u g M))) hS9, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    obtain ⟨p, hp, rfl⟩ := sub_all i.succ hi
    exact ⟨p, ⟨Lf_sub hu hg hx i.succ hp, Lf_right hu hg hx i.succ (Fin.succ_ne_zero i) p hp⟩, rfl⟩
  · show ((∑ i : Fin 9, lcnt 0 k3 k4 nA mA nB mB k6 l6 k7 l7 i.succ : ℕ) : ℝ) = (2 * M * u - u ^ 2) * cP u g
    rw [sum_lcnt9]
    push_cast
    rw [hk3, hk4, hnA, hmA, hnB, hmB, hk6, hl6, hk7, hl7]
    simp only [cP, lxa, ca, cb]; ring

end assemble

end Erdos634.Draft.LayerG

#print axioms Erdos634.Draft.LayerG.unionFam
#print axioms Erdos634.Draft.LayerG.layer_pieces
