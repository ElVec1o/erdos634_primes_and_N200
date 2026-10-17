/-
Draft/HerdtBase.lean — generic lemmas for the Herdt 11-piece family (Lead 1 of private/ROOM/DISCOVERY/leads6.md):
the linear map `kap r (X,Y) = (-X + r Y, Y)` (the frame image of the reflection `x ↦ -x` of the plane, `refl_Phi`),
half-plane / containment lemmas for the sets `Rect a b c d` and `kap r '' Rect a b c d`, and membership in the
target triangle `hull {(0,0), (Cx,0), (0,-By)}`.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.LaczTile
import Erdos634.MarchCompose

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Rect RTiling.cast interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.HerdtFamily
open Erdos634.Draft.LaczFamily
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G
open Erdos634.Draft.S2L (rect_subset mem_hull3')

/-- `(X,Y) ↦ (-X + r Y, Y)`. -/
def kap (r : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (-q.1 + r * q.2, q.2)

/-- `kap r` as a linear map. -/
def kapL (r : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := kap r
  map_add' := by
    intro p q
    simp only [kap, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    ext <;> simp <;> ring
  map_smul' := by
    intro c p
    simp only [kap, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, Prod.smul_mk]
    ext <;> simp <;> ring

theorem convex_kap_pre (r : ℝ) {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) : Convex ℝ {q | kap r q ∈ K} :=
  hK.linear_preimage (kapL r)

theorem par_subset {r : ℝ} {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) {a b c d : ℝ} (h0 : a < b) (h1 : c < d)
    (c00 : kap r (a, c) ∈ K) (c10 : kap r (b, c) ∈ K) (c01 : kap r (a, d) ∈ K) (c11 : kap r (b, d) ∈ K) :
    kap r '' Rect a b c d ⊆ K := by
  rintro _ ⟨q, hq, rfl⟩
  exact rect_subset (K := {q | kap r q ∈ K}) (convex_kap_pre r hK) h0 h1 c00 c10 c01 c11 hq

/-- half-plane side of a `Rect`. -/
theorem rect_side {a b c d : ℝ} (h0 : a < b) (h1 : c < d) (X Y : ℝ × ℝ) (s : ℝ)
    (c00 : 0 ≤ s * cross X Y (a, c)) (c10 : 0 ≤ s * cross X Y (b, c))
    (c01 : 0 ≤ s * cross X Y (a, d)) (c11 : 0 ≤ s * cross X Y (b, d)) :
    ∀ p ∈ Rect a b c d, 0 ≤ s * cross X Y p := fun _ hp =>
  rect_subset (K := {p : ℝ × ℝ | 0 ≤ s * cross X Y p}) (convex_cross X Y s) h0 h1 c00 c10 c01 c11 hp

/-- half-plane side of a `kap`-parallelogram. -/
theorem par_side {r a b c d : ℝ} (h0 : a < b) (h1 : c < d) (X Y : ℝ × ℝ) (s : ℝ)
    (c00 : 0 ≤ s * cross X Y (kap r (a, c))) (c10 : 0 ≤ s * cross X Y (kap r (b, c)))
    (c01 : 0 ≤ s * cross X Y (kap r (a, d))) (c11 : 0 ≤ s * cross X Y (kap r (b, d))) :
    ∀ p ∈ kap r '' Rect a b c d, 0 ≤ s * cross X Y p := fun _ hp =>
  par_subset (K := {p : ℝ × ℝ | 0 ≤ s * cross X Y p}) (convex_cross X Y s) h0 h1 c00 c10 c01 c11 hp

/-- the target `hull {(0,0), (Cx,0), (0,-By)}`: membership. -/
theorem mem_tri0 {Cx By : ℝ} (hC : 0 < Cx) (hB : 0 < By) {p : ℝ × ℝ} (h1 : 0 ≤ p.1) (h2 : 0 ≤ -p.2)
    (h3 : p.1 * By + (-p.2) * Cx ≤ Cx * By) :
    p ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (Cx, 0), (0, -By)} : Set (ℝ × ℝ)) := by
  refine mem_hull3' (A := ((0 : ℝ), (0 : ℝ))) (B := (Cx, 0)) (C := (0, -By)) (Cx * By)
    (Cx * By - p.1 * By - (-p.2) * Cx) (p.1 * By) ((-p.2) * Cx) (mul_pos hC hB) (by linarith)
    (mul_nonneg h1 hB.le) (mul_nonneg h2 hC.le) (by ring) p ?_ ?_
  · simp only; ring
  · simp only; ring

theorem rect_sub_tri0 {Cx By : ℝ} (hC : 0 < Cx) (hB : 0 < By) {a b c d : ℝ} (h0 : a < b) (h1 : c < d)
    (K : Set (ℝ × ℝ)) (hK : K = convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (Cx, 0), (0, -By)} : Set (ℝ × ℝ)))
    (c00 : (a, c) ∈ K) (c10 : (b, c) ∈ K) (c01 : (a, d) ∈ K) (c11 : (b, d) ∈ K) : Rect a b c d ⊆ K := by
  subst hK
  exact rect_subset (convex_convexHull ℝ _) h0 h1 c00 c10 c01 c11

theorem sub_tri3 {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) {a b c : ℝ × ℝ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) ⊆ K := by
  refine convexHull_min ?_ hK
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

/-! ### the reflection `x ↦ -x` of the plane in skew coordinates -/

theorem Phi_eq_mkPt {f : ℝ} (p : ℝ × ℝ) :
    Phi f p = mkPt (p.1 + p.2 / (2 * f)) (p.2 * (sD f / (2 * f))) := by
  ext i; fin_cases i <;> simp [Phi_apply0, Phi_apply1]

theorem refl_Phi {f : ℝ} (hf : f ≠ 0) (p : ℝ × ℝ) :
    Erdos634.MarchCompose.reflX 0 (Phi f p) = Phi f (kap (-1 / f) p) := by
  rw [Phi_eq_mkPt p, Phi_eq_mkPt (kap (-1 / f) p), Erdos634.MarchCompose.reflX_apply]
  simp only [kap]
  congr 1
  · field_simp; ring

theorem image_refl_Phi {f : ℝ} (hf : f ≠ 0) (S : Set (ℝ × ℝ)) :
    (Erdos634.MarchCompose.reflX 0).toIsometryEquiv '' (Phi f '' S) = Phi f '' (kap (-1 / f) '' S) := by
  rw [← Set.image_comp, ← Set.image_comp]
  congr 1
  funext p
  simp only [Function.comp, AffineIsometryEquiv.coe_toIsometryEquiv]
  exact refl_Phi hf p

noncomputable def reflTiling {f : ℝ} (hf : f ≠ 0) {S : Set (ℝ × ℝ)} {M : Tri} {N : ℕ}
    (R : RTiling (Phi f '' S) M N) : RTiling (Phi f '' (kap (-1 / f) '' S)) M N :=
  RTiling.cast (image_refl_Phi hf S) (RegionTiling.map R (Erdos634.MarchCompose.reflX 0).toIsometryEquiv)

end Erdos634.Draft.HerdtFamily
