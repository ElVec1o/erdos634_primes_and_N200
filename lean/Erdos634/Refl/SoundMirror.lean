import Erdos634.Refl.SoundN
import Erdos634.NormalPosition
import Erdos634.SssCongruent

/-! Refl/SoundMirror.lean -- a mirror symmetry of the target halves a refutation certificate.

If the target `A B C` of an instance has `|AB| = |AC|`, the reflection `g` that fixes `A` and exchanges `B`, `C`
maps the target onto itself and every dissection of it onto a dissection of it.  So a configuration `[t]` is refuted
as soon as its mirror image `[t']` is:

    theorem sound_mirror : mirIso I = true → mirTri I t t' = true → Sound Dn I M [t'] → Sound Dn I M [t]

`mirIso` and `mirTri` are exact integer tests (`decide +kernel` in the generated certificates): `mirIso` is
`|AB|² = |AC|²`, and `mirTri I t t'` says that the vertices of `t'` are the images of the vertices of `t` under the
affine map `A + s (B − A) + u (C − A) ↦ A + s (C − A) + u (B − A)` (the second and third vertex exchanged, so that
`t'` is again counter-clockwise).

Use (rust/certgenx, mirror mode): at the root corner `A` a certificate needs subtrees only for the root placements
of one half; a root placement `t` of the other half is refuted through the configuration `[t']`, whose refutation is
one node with two stubs.  No sorry, no native_decide. -/

open Erdos634.CertNode Erdos634.SssCongruent
open Erdos634.Geometry (Plane)

namespace Refl

/-- `|AB|² = |AC|²` for the target `A B C` (exact) -/
def mirIso (I : Inst) : Bool :=
  ((I.tgt.b.x * I.tgt.a.w - I.tgt.a.x * I.tgt.b.w) ^ 2
      + I.Dn * (I.tgt.b.y * I.tgt.a.w - I.tgt.a.y * I.tgt.b.w) ^ 2) * I.tgt.c.w ^ 2
    == ((I.tgt.c.x * I.tgt.a.w - I.tgt.a.x * I.tgt.c.w) ^ 2
      + I.Dn * (I.tgt.c.y * I.tgt.a.w - I.tgt.a.y * I.tgt.c.w) ^ 2) * I.tgt.b.w ^ 2

/-- `q` is the image of `p` under the affine map that fixes `A` and exchanges `B`, `C` -/
def mirPt (A B C p q : Pt) : Bool :=
  (det3 A q C * B.w * p.w == det3 A B p * C.w * q.w) && (det3 A B q * C.w * p.w == det3 A p C * B.w * q.w)

/-- `t'` is the mirror image of `t` (vertices `a ↦ a`, `b ↦ c`, `c ↦ b`) -/
def mirTri (I : Inst) (t t' : _root_.Tri) : Bool :=
  mirPt I.tgt.a I.tgt.b I.tgt.c t.a t'.a && mirPt I.tgt.a I.tgt.b I.tgt.c t.b t'.c &&
    mirPt I.tgt.a I.tgt.b I.tgt.c t.c t'.b

/-- Cramer's rule in the rescaled coordinates -/
theorem rp_bary (Dn x0 y0 x1 y1 x2 y2 X Y : ℝ) (hE : ef x0 y0 x1 y1 x2 y2 ≠ 0) :
    rp Dn X Y = rp Dn x0 y0 + (ef x0 y0 X Y x2 y2 / ef x0 y0 x1 y1 x2 y2) • (rp Dn x1 y1 - rp Dn x0 y0)
      + (ef x0 y0 x1 y1 X Y / ef x0 y0 x1 y1 x2 y2) • (rp Dn x2 y2 - rp Dn x0 y0) := by
  refine Erdos634.PlacementCompleteness.plane_ext ?_ ?_
  · simp
    field_simp
    unfold ef; ring
  · simp
    field_simp
    unfold ef; ring

/-- the SSS isometry in barycentric form -/
theorem sssIso_bary {T U : Erdos634.Geometry.Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) (s u : ℝ) :
    sssIso hd (T.pts 0 + s • (T.pts 1 - T.pts 0) + u • (T.pts 2 - T.pts 0))
      = U.pts 0 + s • (U.pts 1 - U.pts 0) + u • (U.pts 2 - U.pts 0) := by
  rw [sssIso_apply]
  have e : T.pts 0 + s • (T.pts 1 - T.pts 0) + u • (T.pts 2 - T.pts 0) + -T.pts 0
      = s • ev T 0 + u • ev T 1 := by
    simp only [ev, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    abel
  rw [e, map_add, map_smul, map_smul, evMap_basis, evMap_basis]
  simp only [ev, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  abel

theorem mirIso_dist (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (ha : 0 < I.tgt.a.w) (hb : 0 < I.tgt.b.w) (hc : 0 < I.tgt.c.w) (h : mirIso I = true) :
    dist (I.tgt.a.re Dn) (I.tgt.b.re Dn) = dist (I.tgt.a.re Dn) (I.tgt.c.re Dn) := by
  simp only [mirIso, beq_iff_eq] at h
  have key := congrArg (Int.cast : ℤ → ℝ) h
  push_cast at key
  rw [hDn] at key
  have wa := Pt.w_ne _ ha
  have wb := Pt.w_ne _ hb
  have wc := Pt.w_ne _ hc
  refine dist_of_sq ?_
  rw [_root_.Pt.re, _root_.Pt.re, _root_.Pt.re, dist_rp_sq Dn hD, dist_rp_sq Dn hD]
  have eB : (I.tgt.a.X - I.tgt.b.X) ^ 2 + Dn * (I.tgt.a.Y - I.tgt.b.Y) ^ 2
      = (((I.tgt.b.x : ℝ) * I.tgt.a.w - I.tgt.a.x * I.tgt.b.w) ^ 2
          + Dn * ((I.tgt.b.y : ℝ) * I.tgt.a.w - I.tgt.a.y * I.tgt.b.w) ^ 2) / ((I.tgt.a.w : ℝ) * I.tgt.b.w) ^ 2 := by
    unfold _root_.Pt.X _root_.Pt.Y
    field_simp
    ring
  have eC : (I.tgt.a.X - I.tgt.c.X) ^ 2 + Dn * (I.tgt.a.Y - I.tgt.c.Y) ^ 2
      = (((I.tgt.c.x : ℝ) * I.tgt.a.w - I.tgt.a.x * I.tgt.c.w) ^ 2
          + Dn * ((I.tgt.c.y : ℝ) * I.tgt.a.w - I.tgt.a.y * I.tgt.c.w) ^ 2) / ((I.tgt.a.w : ℝ) * I.tgt.c.w) ^ 2 := by
    unfold _root_.Pt.X _root_.Pt.Y
    field_simp
    ring
  rw [eB, eC, div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero wa wb)) (pow_ne_zero 2 (mul_ne_zero wa wc))]
  linear_combination ((I.tgt.a.w : ℝ) ^ 2) * key

theorem mirPt_ef (A B C p q : Pt) (hA : 0 < A.w) (hB : 0 < B.w) (hC : 0 < C.w) (hp : 0 < p.w) (hq : 0 < q.w)
    (h : mirPt A B C p q = true) :
    ef A.X A.Y q.X q.Y C.X C.Y = ef A.X A.Y B.X B.Y p.X p.Y ∧
    ef A.X A.Y B.X B.Y q.X q.Y = ef A.X A.Y p.X p.Y C.X C.Y := by
  simp only [mirPt, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  have h1R := congrArg (Int.cast : ℤ → ℝ) h1
  have h2R := congrArg (Int.cast : ℤ → ℝ) h2
  push_cast at h1R h2R
  have wA := Pt.w_ne _ hA
  have wB := Pt.w_ne _ hB
  have wC := Pt.w_ne _ hC
  have wp := Pt.w_ne _ hp
  have wq := Pt.w_ne _ hq
  rw [det3_ef _ _ _ wA wq wC, det3_ef _ _ _ wA wB wp] at h1R
  rw [det3_ef _ _ _ wA wB wq, det3_ef _ _ _ wA wp wC] at h2R
  have P : (0 : ℝ) < A.w * B.w * C.w * p.w * q.w :=
    mul_pos (mul_pos (mul_pos (mul_pos (Pt.w_pos _ hA) (Pt.w_pos _ hB)) (Pt.w_pos _ hC)) (Pt.w_pos _ hp))
      (Pt.w_pos _ hq)
  constructor
  · have e : ((A.w : ℝ) * B.w * C.w * p.w * q.w)
        * (ef A.X A.Y q.X q.Y C.X C.Y - ef A.X A.Y B.X B.Y p.X p.Y) = 0 := by linear_combination h1R
    rcases mul_eq_zero.mp e with h | h
    · exact absurd h P.ne'
    · linarith
  · have e : ((A.w : ℝ) * B.w * C.w * p.w * q.w)
        * (ef A.X A.Y B.X B.Y q.X q.Y - ef A.X A.Y p.X p.Y C.X C.Y) = 0 := by linear_combination h2R
    rcases mul_eq_zero.mp e with h | h
    · exact absurd h P.ne'
    · linarith

/-- the isometry that maps the triangle `A B C` to `A C B` maps `p` to its mirror image `q` -/
theorem mir_re (Dn : ℝ) (A B C : Pt) (hE : ef A.X A.Y B.X B.Y C.X C.Y ≠ 0) (T U : Erdos634.Geometry.Tri)
    (hT0 : T.pts 0 = rp Dn A.X A.Y) (hT1 : T.pts 1 = rp Dn B.X B.Y) (hT2 : T.pts 2 = rp Dn C.X C.Y)
    (hU0 : U.pts 0 = rp Dn A.X A.Y) (hU1 : U.pts 1 = rp Dn C.X C.Y) (hU2 : U.pts 2 = rp Dn B.X B.Y)
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j))
    (p q : Pt) (h1 : ef A.X A.Y q.X q.Y C.X C.Y = ef A.X A.Y B.X B.Y p.X p.Y)
    (h2 : ef A.X A.Y B.X B.Y q.X q.Y = ef A.X A.Y p.X p.Y C.X C.Y) :
    sssIso hd (rp Dn p.X p.Y) = rp Dn q.X q.Y := by
  have ep := rp_bary Dn A.X A.Y B.X B.Y C.X C.Y p.X p.Y hE
  have eq := rp_bary Dn A.X A.Y B.X B.Y C.X C.Y q.X q.Y hE
  have e : rp Dn p.X p.Y = T.pts 0
      + (ef A.X A.Y p.X p.Y C.X C.Y / ef A.X A.Y B.X B.Y C.X C.Y) • (T.pts 1 - T.pts 0)
      + (ef A.X A.Y B.X B.Y p.X p.Y / ef A.X A.Y B.X B.Y C.X C.Y) • (T.pts 2 - T.pts 0) := by
    rw [hT0, hT1, hT2]; exact ep
  rw [e, sssIso_bary hd, hU0, hU1, hU2, eq, h1, h2]
  abel

/-- **A configuration is refuted if its mirror image is.** -/
theorem sound_mirror (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn) (M : Erdos634.Geometry.Tri)
    (htok : I.tgt.ok = true) (hiso : mirIso I = true) (t t' : _root_.Tri) (ht : t.ok = true)
    (ht' : t'.ok = true) (hm : mirTri I t t' = true) (h : Sound Dn I M [t']) : Sound Dn I M [t] := by
  intro N D htg hmod hreal
  obtain ⟨hp, hcarr⟩ := Tri.ok_sem Dn hD I.tgt htok
  have hok := htok
  simp only [_root_.Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, -⟩ := hok
  simp only [_root_.Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at ht ht'
  obtain ⟨⟨⟨hta, htb⟩, htc⟩, -⟩ := ht
  obtain ⟨⟨⟨hta', htb'⟩, htc'⟩, -⟩ := ht'
  simp only [mirTri, Bool.and_eq_true] at hm
  obtain ⟨⟨hma, hmb⟩, hmc⟩ := hm
  -- the target and its relabelling
  let T0 : Erdos634.Geometry.Tri :=
    rtri Dn hD I.tgt.a.X I.tgt.a.Y I.tgt.b.X I.tgt.b.Y I.tgt.c.X I.tgt.c.Y hp
  let U0 : Erdos634.Geometry.Tri := Erdos634.NormalPosition.relabelTri T0 (Equiv.swap 1 2)
  have s0 : U0.pts 0 = T0.pts 0 := by
    show T0.pts (Equiv.swap 1 2 0) = _
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  have s1 : U0.pts 1 = T0.pts 2 := by
    show T0.pts (Equiv.swap 1 2 1) = _
    rw [Equiv.swap_apply_left]
  have s2 : U0.pts 2 = T0.pts 1 := by
    show T0.pts (Equiv.swap 1 2 2) = _
    rw [Equiv.swap_apply_right]
  have hab : dist (T0.pts 0) (T0.pts 1) = dist (T0.pts 0) (T0.pts 2) :=
    mirIso_dist Dn hD I hDn ha hb hc hiso
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  have hd : ∀ i j : Fin 3, dist (T0.pts i) (T0.pts j) = dist (U0.pts i) (U0.pts j) := by
    intro i j
    rcases htri i with rfl | rfl | rfl <;> rcases htri j with rfl | rfl | rfl <;>
      simp only [s0, s1, s2, dist_self] <;>
      first
        | exact hab
        | exact hab.symm
        | exact dist_comm _ _
        | (rw [dist_comm (T0.pts 1) (T0.pts 0), dist_comm (T0.pts 2) (T0.pts 0)]; exact hab)
        | (rw [dist_comm (T0.pts 2) (T0.pts 0), dist_comm (T0.pts 1) (T0.pts 0)]; exact hab.symm)
  let g : Plane ≃ᵢ Plane := sssIso hd
  have E0 : ef I.tgt.a.X I.tgt.a.Y I.tgt.b.X I.tgt.b.Y I.tgt.c.X I.tgt.c.Y ≠ 0 := hp.ne'
  have im : ∀ p q : Pt, 0 < p.w → 0 < q.w → mirPt I.tgt.a I.tgt.b I.tgt.c p q = true →
      g (p.re Dn) = q.re Dn := by
    intro p q hpw hqw hpq
    obtain ⟨h1, h2⟩ := mirPt_ef _ _ _ p q ha hb hc hpw hqw hpq
    exact mir_re Dn I.tgt.a I.tgt.b I.tgt.c E0 T0 U0 rfl rfl rfl s0 s1 s2 hd p q h1 h2
  have g0 : g (T0.pts 0) = U0.pts 0 := by simpa using sssIso_bary hd 0 0
  have g1 : g (T0.pts 1) = U0.pts 1 := by simpa using sssIso_bary hd 1 0
  have g2 : g (T0.pts 2) = U0.pts 2 := by simpa using sssIso_bary hd 0 1
  -- the mirrored dissection
  let D' : Erdos634.Geometry.CongruentDissection N :=
    Erdos634.NormalPosition.normalizeC D g (Equiv.refl _)
  have htg' : D'.target.carrier = I.tgt.carr Dn := by
    have e1 : D'.target = Erdos634.DissectionMap.mapTri (Erdos634.Ladder.isoAff g)
        (Erdos634.NormalPosition.relabelTri D.target (Equiv.refl _).symm) := rfl
    rw [e1, Erdos634.DissectionMap.mapTri_carrier, Erdos634.NormalPosition.relabelTri_carrier, htg, hcarr]
    have e2 : (Erdos634.DissectionMap.mapTri (Erdos634.Ladder.isoAff g) T0).pts = U0.pts := by
      funext k
      rcases htri k with rfl | rfl | rfl
      · exact g0
      · exact g1
      · exact g2
    have e3 : (Erdos634.DissectionMap.mapTri (Erdos634.Ladder.isoAff g) T0).carrier = U0.carrier := by
      show convexHull ℝ (Set.range _) = convexHull ℝ (Set.range _)
      rw [e2]
    rw [← Erdos634.DissectionMap.mapTri_carrier, e3]
    exact Erdos634.NormalPosition.relabelTri_carrier T0 _
  obtain ⟨i, hi⟩ := hreal t (by simp)
  refine h D' htg' hmod (fun t'' ht'' => ?_)
  simp only [List.mem_singleton] at ht''
  subst ht''
  refine ⟨i, ?_⟩
  have e4 : (D'.tile i).carrier = g '' (D.tile i).carrier :=
    Erdos634.NormalPosition.normalize_tile_carrier D.toDissection g _ i
  rw [e4, hi]
  have himg : (g : Plane → Plane) '' convexHull ℝ {t.a.re Dn, t.b.re Dn, t.c.re Dn}
      = convexHull ℝ ((g : Plane → Plane) '' {t.a.re Dn, t.b.re Dn, t.c.re Dn}) :=
    AffineMap.image_convexHull (𝕜 := ℝ) (Erdos634.Ladder.isoAff g).toAffineMap _
  show (g : Plane → Plane) '' convexHull ℝ {t.a.re Dn, t.b.re Dn, t.c.re Dn}
    = convexHull ℝ {t''.a.re Dn, t''.b.re Dn, t''.c.re Dn}
  rw [himg, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    im t.a t''.a hta hta' hma, im t.b t''.c htb htc' hmb, im t.c t''.b htc htb' hmc]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

#print axioms Refl.sound_mirror

end Refl
