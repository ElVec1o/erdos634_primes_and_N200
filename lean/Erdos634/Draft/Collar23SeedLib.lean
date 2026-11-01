-- Draft/Collar23SeedLib.lean -- scale-8 bridge from a checked integer table (vertices in (1/8) Z^2) to `Tile23 12`:
-- hulls are (1/8)-dilates of the integer hulls (separation transfers), congruence to M23 from scaled squared sides, and the
-- covering from AREA (`ConvexCover.covers_of_volume`: containment + disjoint interiors + total |det|), never pointwise.
-- UNAUDITED.  No sorry, no native_decide.  NOT imported by All.  Credit: B. Herdt (the 720-layout), Beeson-Rosu, Paliy.
import Erdos634.Draft.Collar23E
import Erdos634.Draft.Collar23SeedChk
import Erdos634.ConvexCover
import Erdos634.AreaDet

open scoped Classical Pointwise
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling
open Erdos634.Draft.CollarParam (RTiling.cast RTiling.castN)

namespace Erdos634.Draft.Collar23

/-- the real point of an integer pair at scale 8. -/
noncomputable def ptd (p : ZP) : ℝ × ℝ := ((p.1 : ℝ) / 8, (p.2 : ℝ) / 8)

theorem ptd_eq (p : ZP) : ptd p = (1 / 8 : ℝ) • pt p := by
  ext <;> simp [ptd, pt] <;> ring

def Hd (t : ZT) : Set (ℝ × ℝ) := convexHull ℝ ({ptd t.a, ptd t.b, ptd t.c} : Set (ℝ × ℝ))

theorem Hd_eq (t : ZT) : Hd t = (1 / 8 : ℝ) • t.H := by
  unfold Hd ZT.H H3
  rw [← convexHull_smul]
  congr 1
  simp only [Set.smul_set_insert, Set.smul_set_singleton, ptd_eq]

theorem sepd_sound (s t : ZT) (hs : s.nd) (ht : t.nd) (h : sep s t) :
    Disjoint (interior (Hd s)) (interior (Hd t)) := by
  have h0 := sep_sound s t hs ht h
  rw [Hd_eq, Hd_eq, interior_smul₀ (by norm_num), interior_smul₀ (by norm_num)]
  simp only [← Set.image_smul]
  exact (Set.disjoint_image_iff (smul_right_injective (ℝ × ℝ) (by norm_num : (1 / 8 : ℝ) ≠ 0))).mpr h0

theorem crd (o p q : ZP) : cr (ptd o) (ptd p) (ptd q) = (zcr o p q : ℝ) / 64 := by
  simp only [cr, zcr, ptd]; push_cast; ring

theorem crd_ne (t : ZT) (h : t.nd) : cr (ptd t.a) (ptd t.b) (ptd t.c) ≠ 0 := by
  rw [crd]
  have : (zcr t.a t.b t.c : ℝ) ≠ 0 := by exact_mod_cast h
  exact div_ne_zero this (by norm_num)

noncomputable def ZT.trid (t : ZT) (h : t.nd) : Tri := TT (ptd t.a) (ptd t.b) (ptd t.c) (crd_ne t h)

theorem ZT.trid_carrier (t : ZT) (h : t.nd) : (t.trid h).carrier = Phi '' Hd t := by
  unfold ZT.trid Hd
  exact TT_carrier _ _ _ _

theorem sq8 (p q : ZP) :
    ((ptd p).1 - (ptd q).1) ^ 2 + 3 / 2 * ((ptd p).1 - (ptd q).1) * ((ptd p).2 - (ptd q).2)
      + ((ptd p).2 - (ptd q).2) ^ 2 = (zq p q : ℝ) / 128 := by
  simp only [ptd, zq]; push_cast; ring

theorem sq1 (p q : ZP) :
    ((pt p).1 - (pt q).1) ^ 2 + 3 / 2 * ((pt p).1 - (pt q).1) * ((pt p).2 - (pt q).2)
      + ((pt p).2 - (pt q).2) ^ 2 = (zq p q : ℝ) / 2 := by
  simp only [pt, zq]; push_cast; ring

theorem ZT.congrd (t : ZT) (h : t.nd) (hm : Pm8 t) : (t.trid h).Congruent M23 := by
  obtain ⟨e1, e2, e3⟩ := hm
  have f1 : (zq t.a t.b : ℝ) = 3200 := by exact_mod_cast e1
  have f2 : (zq t.b t.c : ℝ) = 4608 := by exact_mod_cast e2
  have f3 : (zq t.c t.a : ℝ) = 2048 := by exact_mod_cast e3
  have m1 : (zq modelZT.a modelZT.b : ℝ) = 50 := by exact_mod_cast (by decide : zq modelZT.a modelZT.b = 50)
  have m2 : (zq modelZT.b modelZT.c : ℝ) = 72 := by exact_mod_cast (by decide : zq modelZT.b modelZT.c = 72)
  have m3 : (zq modelZT.c modelZT.a : ℝ) = 32 := by exact_mod_cast (by decide : zq modelZT.c modelZT.a = 32)
  unfold ZT.trid M23 ZT.tri
  refine TT_congruent _ _ _ _ _ _ _ _ ?_ ?_ ?_
  · rw [sq8, sq1, f1, m1]; norm_num
  · rw [sq8, sq1, f2, m2]; norm_num
  · rw [sq8, sq1, f3, m3]; norm_num

theorem detTri_TT (p q r : ℝ × ℝ) (h : cr p q r ≠ 0) :
    Erdos634.AreaDet.detTri (TT p q r h) = s7 / 4 * cr p q r := by
  unfold TT
  rw [detTri_mkTri, det3_Phi]

theorem detTri_trid (t : ZT) (h : t.nd) :
    Erdos634.AreaDet.detTri (t.trid h) = s7 / 4 * ((zcr t.a t.b t.c : ℝ) / 64) := by
  unfold ZT.trid
  rw [detTri_TT, crd]

theorem ptd_mem (p : ZP) (h : In8 p) : ptd p ∈ Tset23 ((12 : ℕ) : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := h
  have r1 : (0 : ℝ) ≤ p.1 := by exact_mod_cast h1
  have r2 : (0 : ℝ) ≤ p.2 := by exact_mod_cast h2
  have r3 : 2 * (p.1 : ℝ) + 3 * (p.2 : ℝ) ≤ 2880 := by exact_mod_cast h3
  refine ⟨?_, ?_, ?_⟩
  · simp only [ptd]; linarith
  · simp only [ptd]; linarith
  · simp only [ptd]; push_cast; linarith

theorem Hd_sub (t : ZT) (h : Good8 t) : Hd t ⊆ Tset23 ((12 : ℕ) : ℝ) := by
  obtain ⟨-, -, ha, hb, hc⟩ := h
  refine convexHull_min ?_ (Tset23_convex _)
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact ptd_mem _ ha
  · exact ptd_mem _ hb
  · exact ptd_mem _ hc

/-- **The seed theorem.**  A list of 720 integer-scale-8 tiles passing the four checks (`Good8` on each tile, pairwise `sep`, total
twice-area `1382400 = 64 * 21600`) is a tiling of `T(12)` by the tile (4,5,6). -/
theorem seedRT (L : List ZT) (hlen : L.length = 720) (hg : ∀ t ∈ L, Good8 t) (hs : L.Pairwise sep)
    (ha : (L.map fun t => |zcr t.a t.b t.c|).sum = 1382400) : Tile23 12 := by
  have hpos : (0 : ℝ) < ((12 : ℕ) : ℝ) := by norm_num
  set T0 : Tri := tri23 ((12 : ℕ) : ℝ) hpos with hT0
  let tab : Fin L.length → ZT := fun i => L.get i
  have hmem : ∀ i, tab i ∈ L := fun i => List.get_mem _ _
  have hnd : ∀ i, (tab i).nd := fun i => (hg _ (hmem i)).2.1
  let tl : Fin L.length → Tri := fun i => (tab i).trid (hnd i)
  have hcar : ∀ i, (tl i).carrier = Phi '' Hd (tab i) := fun i => ZT.trid_carrier _ _
  have hsub : ∀ i, (tl i).carrier ⊆ T0.carrier := by
    intro i
    rw [hcar, hT0, tri23_carrier]
    exact Set.image_mono (Hd_sub _ (hg _ (hmem i)))
  have hsep : ∀ i j : Fin L.length, i < j → sep (tab i) (tab j) := fun i j hij =>
    List.pairwise_iff_get.mp hs i j hij
  have hdisj : Pairwise fun i j => Disjoint (interior (tl i).carrier) (interior (tl j).carrier) := by
    intro i j hij
    rw [hcar, hcar]
    rcases lt_or_gt_of_ne hij with h | h
    · exact disjoint_image (sepd_sound _ _ (hnd i) (hnd j) (hsep i j h))
    · exact (disjoint_image (sepd_sound _ _ (hnd j) (hnd i) (hsep j i h))).symm
  have hdetT : |Erdos634.AreaDet.detTri T0| = s7 / 4 * 21600 := by
    rw [hT0]; unfold tri23
    rw [detTri_TT]
    have : cr ((0 : ℝ), (0 : ℝ)) (15 * ((12 : ℕ) : ℝ), 0) (0, 10 * ((12 : ℕ) : ℝ)) = 21600 := by
      simp only [cr]; push_cast; ring
    rw [this, abs_of_nonneg (by have := s7_pos; positivity)]
  have hsum : ∑ i, |Erdos634.AreaDet.detTri (tl i)| = s7 / 4 * 21600 := by
    have e1 : ∀ i, |Erdos634.AreaDet.detTri (tl i)| = s7 / 4 / 64 * ((|zcr (tab i).a (tab i).b (tab i).c| : ℤ) : ℝ) := by
      intro i
      show |Erdos634.AreaDet.detTri ((tab i).trid (hnd i))| = _
      rw [detTri_trid, abs_mul, abs_of_pos (by have := s7_pos; positivity : (0 : ℝ) < s7 / 4), abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 64)]
      push_cast
      ring
    simp only [e1]
    rw [← Finset.mul_sum]
    have e2 : ∑ i : Fin L.length, |zcr (tab i).a (tab i).b (tab i).c| = 1382400 := by
      have : L.map (fun t => |zcr t.a t.b t.c|) = List.ofFn (fun i : Fin L.length => |zcr (tab i).a (tab i).b (tab i).c|) := by
        apply List.ext_getElem
        · simp
        · intro k h1 h2; simp [tab]
      rw [← List.sum_ofFn, ← this]; exact ha
    have e3 : ∑ i : Fin L.length, ((|zcr (tab i).a (tab i).b (tab i).c| : ℤ) : ℝ) = 1382400 := by
      rw [← Int.cast_sum, e2]; norm_num
    rw [e3]; ring
  have hvol : ∑ i, MeasureTheory.volume (tl i).carrier = MeasureTheory.volume T0.carrier :=
    Erdos634.AreaDet.area_identity_of_det T0 tl (by rw [hsum, hdetT])
  have hcov : (⋃ i, (tl i).carrier) = Phi '' Tset23 ((12 : ℕ) : ℝ) := by
    rw [Erdos634.ConvexCover.covers_of_volume T0 tl hsub hdisj hvol, hT0, tri23_carrier]
  let R : RTiling (Phi '' Tset23 ((12 : ℕ) : ℝ)) M23 L.length :=
    { tile := tl, covers := hcov, disj := hdisj
      cong := fun i => ZT.congrd _ _ (hg _ (hmem i)).1 }
  exact ⟨RTiling.castN (by omega) R⟩

end Erdos634.Draft.Collar23
