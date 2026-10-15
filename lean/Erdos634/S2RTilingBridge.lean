import Erdos634.S2RTiling
import Erdos634.S2RPairsDefs
import Erdos634.S2RPairs0
import Erdos634.S2RPairs1
import Erdos634.S2RPairs2
import Erdos634.S2RPairs3
import Erdos634.S2RPairs4
import Erdos634.S2RPairs5
import Erdos634.S2RPairs6
import Erdos634.S2RPairs7
import Erdos634.S2RPairs8
import Erdos634.S2RPairs9
import Erdos634.S2RPairs10
import Erdos634.S2RPairs11
import Erdos634.S2RPairs12
import Erdos634.S2RPairs13
import Erdos634.Z2Real
import Erdos634.CertGeom
import Erdos634.SssCongruent
import Erdos634.Ladder
import Erdos634.Tiling44Bridge

/-!
# `S2RTiling`, assembled into a genuine `CongruentDissection`

Erdős #634. The `cor:elevenm` half needing `S2RTiling` as a positive witness (`3 ∈ S`). Same
pattern that closed `thm:44`/`thm:63` (`Erdos634.Tiling44Bridge`/`Erdos634.CevianTiling63Bridge`):
`S2RTiling`'s `Z2`/`Pt`/`cross`/`dist2`/`znonneg` are literally `Z2Real`'s through `toZPt`, so
every general lemma applies unchanged. `S2RTiling` has a named `target` field, like `Tiling44`. N=322 tile count: target (126,81,115) scalene, tile (6,5,9). Copy of R126TilingBridge (Z[√2]); target (126,81,115), tile (6,5,9). Not a paper-row flip.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.S2RTilingBridge

open Erdos634.Z2Real Erdos634.Geometry
open Erdos634.Tiling44Bridge (affNeg_apply lineFun_ne_zero_of_sq_ne)


/-- **The real determinant of a `S2RTiling.Tri`'s three vertices**, transferred from its `ℤ[√2]`
cross product. -/
theorem det3_eq_toR_cross (t : S2RTiling.Tri) :
    Erdos634.CertCoord.det3
      (toR (zx (toZPt (S2RTiling.t1 t)))) (toR (zy (toZPt (S2RTiling.t1 t))))
      (toR (zx (toZPt (S2RTiling.t2 t)))) (toR (zy (toZPt (S2RTiling.t2 t))))
      (toR (zx (toZPt (S2RTiling.t3 t)))) (toR (zy (toZPt (S2RTiling.t3 t))))
    = toR (zcross (toZPt (S2RTiling.t1 t)) (toZPt (S2RTiling.t2 t)) (toZPt (S2RTiling.t3 t))) :=
  toR_zcross _ _ _

/-- **The target's determinant is `target_det`**, positive. -/
theorem target_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (S2RTiling.t1 S2RTiling.target))))
      (toR (zy (toZPt (S2RTiling.t1 S2RTiling.target))))
      (toR (zx (toZPt (S2RTiling.t2 S2RTiling.target))))
      (toR (zy (toZPt (S2RTiling.t2 S2RTiling.target))))
      (toR (zx (toZPt (S2RTiling.t3 S2RTiling.target))))
      (toR (zy (toZPt (S2RTiling.t3 S2RTiling.target)))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (S2RTiling.t1 S2RTiling.target))
    (toZPt (S2RTiling.t2 S2RTiling.target)) (toZPt (S2RTiling.t3 S2RTiling.target))) (by decide)

/-- **The target, as a real `Tri`.** -/
noncomputable def targetTri : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (S2RTiling.t1 S2RTiling.target))))
    (toR (zy (toZPt (S2RTiling.t1 S2RTiling.target))))
    (toR (zx (toZPt (S2RTiling.t2 S2RTiling.target))))
    (toR (zy (toZPt (S2RTiling.t2 S2RTiling.target))))
    (toR (zx (toZPt (S2RTiling.t3 S2RTiling.target))))
    (toR (zy (toZPt (S2RTiling.t3 S2RTiling.target))))
    target_det_pos.ne'

/-- **The first piece's determinant is positive**, positive — a smaller instance of the same
computation, confirming the pattern generalizes piece-by-piece. -/
theorem piece0_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (S2RTiling.t1 (S2RTiling.tiles.headI)))))
      (toR (zy (toZPt (S2RTiling.t1 (S2RTiling.tiles.headI)))))
      (toR (zx (toZPt (S2RTiling.t2 (S2RTiling.tiles.headI)))))
      (toR (zy (toZPt (S2RTiling.t2 (S2RTiling.tiles.headI)))))
      (toR (zx (toZPt (S2RTiling.t3 (S2RTiling.tiles.headI)))))
      (toR (zy (toZPt (S2RTiling.t3 (S2RTiling.tiles.headI))))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (S2RTiling.t1 (S2RTiling.tiles.headI)))
    (toZPt (S2RTiling.t2 (S2RTiling.tiles.headI))) (toZPt (S2RTiling.t3 (S2RTiling.tiles.headI))))
    (by decide)

-- Every one of the 322 pieces is positively oriented.
set_option maxRecDepth 4000 in
theorem all_pieces_pos :
    ∀ t ∈ S2RTiling.tiles,
      zpos (zcross (toZPt (S2RTiling.t1 t)) (toZPt (S2RTiling.t2 t)) (toZPt (S2RTiling.t3 t)))
        = true := by
  decide

/-- **Every piece, as a real `Tri`**, uniformly — the general form `thm:44`'s data entry needs,
combining `all_pieces_pos` with `det3_eq_toR_cross` instead of writing 44 separate constructions. -/
noncomputable def pieceTri {t : S2RTiling.Tri} (ht : t ∈ S2RTiling.tiles) : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (S2RTiling.t1 t)))) (toR (zy (toZPt (S2RTiling.t1 t))))
    (toR (zx (toZPt (S2RTiling.t2 t)))) (toR (zy (toZPt (S2RTiling.t2 t))))
    (toR (zx (toZPt (S2RTiling.t3 t)))) (toR (zy (toZPt (S2RTiling.t3 t))))
    (by
      rw [det3_eq_toR_cross]
      exact (toR_pos (all_pieces_pos t ht)).ne')

/-- **The `lineFun` of a certificate edge is nonconstant**, for two *concrete* endpoints `P ≠ Q`
whose real coordinates differ — resolved via `Z2Real.toR_ne_zero_of_sq_ne` rather than injectivity
of `toR` (which this project deliberately never proves). `hx`/`hy` are the decidable `ℤ[√2]`
side conditions (`zx Q - zx P` resp. `zy Q - zy P` squared-nonequal to `2 * (other coord)²`); one
of the two always holds for a genuine edge, matching whichever coordinate actually differs. -/
theorem lineFun_ne_zero_of_sq_ne {P Q : ZPt}
    (h : (zsub (zx P) (zx Q)).1 ^ 2 ≠ 2 * (zsub (zx P) (zx Q)).2 ^ 2
       ∨ (zsub (zy P) (zy Q)).1 ^ 2 ≠ 2 * (zsub (zy P) (zy Q)).2 ^ 2) :
    (Erdos634.CertGeom.lineFun (toR (zx P)) (toR (zy P)) (toR (zx Q)) (toR (zy Q))).linear ≠ 0 := by
  apply Erdos634.CertGeom.lineFun_linear_ne_zero
  rcases h with h | h
  · exact Or.inl (sub_ne_zero.mp (by rw [← toR_sub]; exact toR_ne_zero_of_sq_ne h))
  · exact Or.inr (sub_ne_zero.mp (by rw [← toR_sub]; exact toR_ne_zero_of_sq_ne h))

/-- Pointwise negation of an affine map into `ℝ`. -/
theorem affNeg_apply (g : Plane →ᵃ[ℝ] ℝ) (p : Plane) : (-g) p = -(g p) := by
  have := congrFun (AffineMap.coe_neg g) p
  simpa using this

/-- `S2RTiling.cross` is literally `Z2Real.zcross` read through `toZPt` — the two files define the
same operations on the same underlying type, so this is `rfl`. -/
theorem cross_eq_zcross (o a b : S2RTiling.Pt) :
    S2RTiling.cross o a b = zcross (toZPt o) (toZPt a) (toZPt b) := rfl

/-- `S2RTiling.dist2` is literally `Z2Real.zdist2` read through `toZPt` — again `rfl`. -/
theorem dist2_eq_zdist2 (p q : S2RTiling.Pt) :
    S2RTiling.dist2 p q = zdist2 (toZPt p) (toZPt q) := rfl

/-- **A piece's vertex, named by index.** -/
def vertexOf (t : S2RTiling.Tri) (i : Fin 3) : S2RTiling.Pt :=
  ![S2RTiling.t1 t, S2RTiling.t2 t, S2RTiling.t3 t] i

/-- **`pieceTri`'s vertices are exactly `vertexOf`, read as real points.** -/
theorem pieceTri_pts (t : S2RTiling.Tri) (ht : t ∈ S2RTiling.tiles) (i : Fin 3) :
    (pieceTri ht).pts i
      = Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i)))) := by
  fin_cases i <;> rfl

/-- **Squared distances between a piece's vertices, transferred to `ℝ` from the certificate's own
`dist2`.** -/
theorem pieceTri_dist_sq (t : S2RTiling.Tri) (ht : t ∈ S2RTiling.tiles) (i j : Fin 3) :
    dist ((pieceTri ht).pts i) ((pieceTri ht).pts j) ^ 2 = toR (S2RTiling.dist2 (vertexOf t i) (vertexOf t j)) := by
  rw [pieceTri_pts t ht i, pieceTri_pts t ht j, Erdos634.CertCoord.dist_sq_mkPt,
    dist2_eq_zdist2]
  exact toR_zdist2 _ _

/-- **A single `sepBy`-true witness gives a genuine separating affine functional** between two
pieces, read as real `Tri` objects — the assembly step `CertGeom.pairwise_disjoint_of_separating`
needs, for one pair. `hPQ` is `lineFun_ne_zero_of_sq_ne`'s decidable side condition on the edge
`(P, Q)`; the certificate's own `sepBy` supplies which sign pattern holds. -/
theorem sep_of_sepBy {P Q : S2RTiling.Pt} {A B : S2RTiling.Tri}
    (hPQ : (zsub (zx (toZPt P)) (zx (toZPt Q))).1 ^ 2
             ≠ 2 * (zsub (zx (toZPt P)) (zx (toZPt Q))).2 ^ 2
         ∨ (zsub (zy (toZPt P)) (zy (toZPt Q))).1 ^ 2
             ≠ 2 * (zsub (zy (toZPt P)) (zy (toZPt Q))).2 ^ 2)
    (hsep : S2RTiling.sepBy P Q A B = true) (hA : A ∈ S2RTiling.tiles) (hB : B ∈ S2RTiling.tiles) :
    ∃ (f : Plane →ᵃ[ℝ] ℝ) (_ : f.linear ≠ 0) (c : ℝ),
      (∀ x ∈ (pieceTri hA).carrier, f x ≤ c) ∧ (∀ x ∈ (pieceTri hB).carrier, c ≤ f x) := by
  set f : Plane →ᵃ[ℝ] ℝ :=
    Erdos634.CertGeom.lineFun (toR (zx (toZPt P))) (toR (zy (toZPt P)))
      (toR (zx (toZPt Q))) (toR (zy (toZPt Q))) with hfdef
  have hflin : f.linear ≠ 0 := lineFun_ne_zero_of_sq_ne hPQ
  have hfval : ∀ v : S2RTiling.Pt,
      f (Erdos634.CertCoord.mkPt (toR (zx (toZPt v))) (toR (zy (toZPt v))))
        = toR (S2RTiling.cross P Q v) := by
    intro v
    rw [hfdef, Erdos634.CertGeom.lineFun_apply, Erdos634.CertCoord.mkPt_zero,
      Erdos634.CertCoord.mkPt_one, cross_eq_zcross]
    exact toR_zcross _ _ _
  have hpts : ∀ (t : S2RTiling.Tri) (ht : t ∈ S2RTiling.tiles) (k : Fin 3),
      (pieceTri ht).pts k
        = Erdos634.CertCoord.mkPt (toR (zx (toZPt (![S2RTiling.t1 t, S2RTiling.t2 t, S2RTiling.t3 t] k))))
            (toR (zy (toZPt (![S2RTiling.t1 t, S2RTiling.t2 t, S2RTiling.t3 t] k)))) := by
    intro t ht k; fin_cases k <;> rfl
  simp only [S2RTiling.sepBy, List.all_eq_true, List.mem_cons, Bool.and_eq_true,
    Bool.or_eq_true, List.map, forall_eq_or_imp] at hsep
  rcases hsep with ⟨hsA, hsB⟩ | ⟨hsA, hsB⟩
  · -- A's vertices have cross ≥ 0, B's have cross ≤ 0 (znonpos)
    refine ⟨-f, neg_ne_zero.mpr hflin, 0, ?_, ?_⟩
    · exact Erdos634.CertGeom.le_of_forall_pts_le (-f) (t := pieceTri hA) (c := 0)
        (fun k => by
          rw [affNeg_apply, hpts A hA k, hfval, neg_le, neg_zero]
          fin_cases k <;> first | exact Erdos634.Z2Real.toR_nonneg hsA.1 | exact Erdos634.Z2Real.toR_nonneg hsA.2.1 | exact Erdos634.Z2Real.toR_nonneg hsA.2.2.1)
    · intro x hx
      have hb := Erdos634.CertGeom.le_of_forall_pts_le f (t := pieceTri hB) (c := 0)
        (fun k => by
          rw [hpts B hB k, hfval]
          fin_cases k <;> first | exact Erdos634.Z2Real.toR_nonpos hsB.1 | exact Erdos634.Z2Real.toR_nonpos hsB.2.1 | exact Erdos634.Z2Real.toR_nonpos hsB.2.2.1)
      have := hb x hx
      rw [affNeg_apply]
      linarith
  · -- A's vertices have cross ≤ 0 (znonpos), B's have cross ≥ 0
    refine ⟨f, hflin, 0, ?_, ?_⟩
    · exact Erdos634.CertGeom.le_of_forall_pts_le f (t := pieceTri hA) (c := 0)
        (fun k => by
          rw [hpts A hA k, hfval]
          fin_cases k <;> first | exact Erdos634.Z2Real.toR_nonpos hsA.1 | exact Erdos634.Z2Real.toR_nonpos hsA.2.1 | exact Erdos634.Z2Real.toR_nonpos hsA.2.2.1)
    · intro x hx
      have hb := Erdos634.CertGeom.le_of_forall_pts_le (-f) (t := pieceTri hB) (c := 0)
        (fun k => by
          rw [affNeg_apply, hpts B hB k, hfval, neg_le, neg_zero]
          fin_cases k <;> first | exact Erdos634.Z2Real.toR_nonneg hsB.1 | exact Erdos634.Z2Real.toR_nonneg hsB.2.1 | exact Erdos634.Z2Real.toR_nonneg hsB.2.2.1)
      have := hb x hx
      rw [affNeg_apply] at this
      linarith

/-! ## Every pair of distinct pieces is separated — the 322-piece pair assembly, decided at once

Rather than unpacking `Tiling44.wit`/`checkPairs`'s exact witness list (946 individual
extractions), it is far cheaper to `decide` the *existence* of a separating edge candidate per
pair directly: for each of the 322×322 ordered pairs, some one of the 6 candidate edges (3 from each
triangle) both separates them (`sepBy`) and satisfies `sep_of_sepBy`'s decidable side condition
(`sqCond`). This one `decide` (~12s) replaces per-pair data entry entirely. -/

set_option maxRecDepth 8192 in
theorem tiles_eq_chunks : S2RTiling.tiles = chunk 0 ++ chunk 1 ++ chunk 2 ++ chunk 3 ++ chunk 4 ++ chunk 5 ++ chunk 6 ++ chunk 7 ++ chunk 8 ++ chunk 9 ++ chunk 10 ++ chunk 11 ++ chunk 12 ++ chunk 13 := by
  decide +kernel

/-- Every one of the 322*322 ordered pairs of distinct pieces has a working separating edge
(assembled from the chunk theorems `pairs_chunk_k`, each its own module). -/
theorem all_pairs_ok : ∀ A ∈ S2RTiling.tiles, ∀ B ∈ S2RTiling.tiles, A ≠ B → pairOK A B = true := by
  intro A hA
  rw [tiles_eq_chunks] at hA
  simp only [List.mem_append] at hA
  rcases hA with ((((((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h
  · exact pairs_chunk_0 A h
  · exact pairs_chunk_1 A h
  · exact pairs_chunk_2 A h
  · exact pairs_chunk_3 A h
  · exact pairs_chunk_4 A h
  · exact pairs_chunk_5 A h
  · exact pairs_chunk_6 A h
  · exact pairs_chunk_7 A h
  · exact pairs_chunk_8 A h
  · exact pairs_chunk_9 A h
  · exact pairs_chunk_10 A h
  · exact pairs_chunk_11 A h
  · exact pairs_chunk_12 A h
  · exact pairs_chunk_13 A h

/-- `sqCond`'s `Bool` and `sep_of_sepBy`'s `Prop` side condition agree. -/
theorem sqCond_iff (pq : S2RTiling.Pt × S2RTiling.Pt) :
    sqCond pq = true ↔
      (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).1 ^ 2 ≠ 2 * (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).2 ^ 2
        ∨ (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).1 ^ 2
            ≠ 2 * (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).2 ^ 2 := by
  rw [sqCond, decide_eq_true_iff]

/-- **Every two distinct pieces of `Tiling44` have disjoint interiors, as real `Tri` objects.**
This is (C3) fully assembled: existence of the separating edge (`all_pairs_ok`), transferred to a
genuine affine functional bounded on the whole carrier (`sep_of_sepBy`). -/
theorem pieces_interiors_disjoint {A B : S2RTiling.Tri} (hA : A ∈ S2RTiling.tiles)
    (hB : B ∈ S2RTiling.tiles) (hne : A ≠ B) :
    Disjoint (interior (pieceTri hA).carrier) (interior (pieceTri hB).carrier) := by
  have hok := all_pairs_ok A hA B hB hne
  simp only [pairOK, List.any_eq_true] at hok
  obtain ⟨pq, hmem, hsep⟩ := hok
  rw [Bool.and_eq_true] at hsep
  obtain ⟨hsepBy, hsq⟩ := hsep
  obtain ⟨f, hf, c, h1, h2⟩ := sep_of_sepBy ((sqCond_iff pq).mp hsq) hsepBy hA hB
  exact Erdos634.CertGeom.interiors_disjoint_of_separating f hf c h1 h2

/-! ## (C1): every piece is congruent to a fixed model — the first piece, decided at once -/

/-- **The model tile**: `Tiling44`'s first certificate piece. Any piece works as the model since
all are mutually congruent; picking one already in `tiles` avoids naming new coordinates. -/
theorem headI_mem_tiles : S2RTiling.tiles.headI ∈ S2RTiling.tiles := by decide

/-- **Some permutation matches a piece's squared side lengths to the model's, positionally.**
`decide` over the `Fintype (Equiv.Perm (Fin 3))` (6 elements) × 44 pieces × 9 pairs — cheap. -/
def congOK' (t : S2RTiling.Tri) : Bool :=
  decide (∃ σ : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
    S2RTiling.dist2 (vertexOf t i) (vertexOf t j)
      = S2RTiling.dist2 (vertexOf S2RTiling.tiles.headI (σ i)) (vertexOf S2RTiling.tiles.headI (σ j)))

-- Every one of the 322 pieces has a matching permutation.
set_option maxRecDepth 4000 in
theorem all_pieces_cong : ∀ t ∈ S2RTiling.tiles, congOK' t = true := by decide

/-- **(C1) fully assembled**: every piece of `Tiling44`, as a real `Tri`, is congruent to the
model tile. -/
theorem pieceTri_congruent {t : S2RTiling.Tri} (ht : t ∈ S2RTiling.tiles) :
    (pieceTri ht).Congruent (pieceTri headI_mem_tiles) := by
  have hex := all_pieces_cong t ht
  simp only [congOK', decide_eq_true_eq] at hex
  obtain ⟨σ, hσ⟩ := hex
  refine Erdos634.SssCongruent.congruent_of_sq_dist_perm σ (fun i j => ?_)
  rw [pieceTri_dist_sq t ht, pieceTri_dist_sq S2RTiling.tiles.headI headI_mem_tiles]
  exact congrArg Erdos634.Z2Real.toR (hσ i j)

/-! ## (C2) containment: every piece lies in the target — the part `all_pieces_pos` skipped

`all_pieces_pos` only captured orientation (`insideOK`'s first conjunct); this is the actual
vertex-in-target containment, `insideOK`'s second conjunct. -/

/-- **Cyclic invariance of `cross`**: `cross o a b = cross a b o`. Twice the signed area of a
triangle does not depend on which vertex is named first, only the cyclic order. Needed to match
`insideOK`'s three checks (each anchored at a different target edge) against
`CertCoord.mem_carrier_of_dets`'s fixed vertex-0/1/2 convention. -/
theorem cross_cyclic (o a b : S2RTiling.Pt) : S2RTiling.cross o a b = S2RTiling.cross a b o := by
  simp only [S2RTiling.cross, S2RTiling.zsub, S2RTiling.zmul, S2RTiling.px, S2RTiling.py, Prod.ext_iff]
  constructor <;> ring

-- Every one of the 322 pieces' vertices lies in the closed target.
set_option maxRecDepth 4000 in
theorem all_pieces_inside : ∀ t ∈ S2RTiling.tiles, S2RTiling.insideOK t = true := by decide

/-- Abbreviations for the target's three vertices. -/
theorem insideOK_vertex {t : S2RTiling.Tri} (ht : t ∈ S2RTiling.tiles) (i : Fin 3) :
    S2RTiling.znonneg (S2RTiling.cross (S2RTiling.t1 S2RTiling.target) (S2RTiling.t2 S2RTiling.target)
        (vertexOf t i)) = true
    ∧ S2RTiling.znonneg (S2RTiling.cross (S2RTiling.t2 S2RTiling.target) (S2RTiling.t3 S2RTiling.target)
        (vertexOf t i)) = true
    ∧ S2RTiling.znonneg (S2RTiling.cross (S2RTiling.t3 S2RTiling.target) (S2RTiling.t1 S2RTiling.target)
        (vertexOf t i)) = true := by
  have hins := all_pieces_inside t ht
  simp only [S2RTiling.insideOK, Bool.and_eq_true, List.all_eq_true] at hins
  have hv : vertexOf t i ∈ ([S2RTiling.t1 t, S2RTiling.t2 t, S2RTiling.t3 t] : List S2RTiling.Pt) := by
    fin_cases i <;> simp [vertexOf]
  have h3 := hins.2 (vertexOf t i) hv
  simp only [Bool.and_eq_true] at h3
  exact ⟨h3.1.1, h3.1.2, h3.2⟩

/-- **The target, real vertex-by-vertex, matches `mem_carrier_of_dets`'s convention.** -/
theorem vertexOf_mem_targetTri {t : S2RTiling.Tri} (ht : t ∈ S2RTiling.tiles) (i : Fin 3) :
    Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i))))
      ∈ targetTri.carrier := by
  obtain ⟨h1, h2, h3⟩ := insideOK_vertex ht i
  refine Erdos634.CertCoord.mem_carrier_of_dets (x₀ := toR (zx (toZPt (S2RTiling.t1 S2RTiling.target))))
    (y₀ := toR (zy (toZPt (S2RTiling.t1 S2RTiling.target))))
    (x₁ := toR (zx (toZPt (S2RTiling.t2 S2RTiling.target))))
    (y₁ := toR (zy (toZPt (S2RTiling.t2 S2RTiling.target))))
    (x₂ := toR (zx (toZPt (S2RTiling.t3 S2RTiling.target))))
    (y₂ := toR (zy (toZPt (S2RTiling.t3 S2RTiling.target))))
    target_det_pos ?_ ?_ ?_
  · -- h0 : 0 ≤ det3 a b x1 y1 x2 y2 = cross(v, T2, T3) = cross(T2, T3, v) [cyclic]
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i))))
        (toR (zx (toZPt (S2RTiling.t2 S2RTiling.target)))) (toR (zy (toZPt (S2RTiling.t2 S2RTiling.target))))
        (toR (zx (toZPt (S2RTiling.t3 S2RTiling.target)))) (toR (zy (toZPt (S2RTiling.t3 S2RTiling.target))))
      = toR (zcross (toZPt (vertexOf t i)) (toZPt (S2RTiling.t2 S2RTiling.target))
          (toZPt (S2RTiling.t3 S2RTiling.target))) from toR_zcross _ _ _,
      ← cross_eq_zcross, cross_cyclic (vertexOf t i) (S2RTiling.t2 S2RTiling.target) (S2RTiling.t3 S2RTiling.target)]
    exact Erdos634.Z2Real.toR_nonneg h2
  · -- h1 : 0 ≤ det3 x0 y0 a b x2 y2 = cross(T1, v, T3) = cross(T3, T1, v) [two cyclic rotations]
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (S2RTiling.t1 S2RTiling.target))))
        (toR (zy (toZPt (S2RTiling.t1 S2RTiling.target)))) (toR (zx (toZPt (vertexOf t i))))
        (toR (zy (toZPt (vertexOf t i)))) (toR (zx (toZPt (S2RTiling.t3 S2RTiling.target))))
        (toR (zy (toZPt (S2RTiling.t3 S2RTiling.target))))
      = toR (zcross (toZPt (S2RTiling.t1 S2RTiling.target)) (toZPt (vertexOf t i))
          (toZPt (S2RTiling.t3 S2RTiling.target))) from toR_zcross _ _ _,
      ← cross_eq_zcross,
      cross_cyclic (S2RTiling.t1 S2RTiling.target) (vertexOf t i) (S2RTiling.t3 S2RTiling.target),
      cross_cyclic (vertexOf t i) (S2RTiling.t3 S2RTiling.target) (S2RTiling.t1 S2RTiling.target)]
    exact Erdos634.Z2Real.toR_nonneg h3
  · -- h2 : 0 ≤ det3 x0 y0 x1 y1 a b = cross(T1, T2, v), direct match
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (S2RTiling.t1 S2RTiling.target))))
        (toR (zy (toZPt (S2RTiling.t1 S2RTiling.target)))) (toR (zx (toZPt (S2RTiling.t2 S2RTiling.target))))
        (toR (zy (toZPt (S2RTiling.t2 S2RTiling.target)))) (toR (zx (toZPt (vertexOf t i))))
        (toR (zy (toZPt (vertexOf t i))))
      = toR (zcross (toZPt (S2RTiling.t1 S2RTiling.target)) (toZPt (S2RTiling.t2 S2RTiling.target))
          (toZPt (vertexOf t i))) from toR_zcross _ _ _,
      ← cross_eq_zcross]
    exact Erdos634.Z2Real.toR_nonneg h1

/-- **(C2) fully assembled**: every piece of `Tiling44`, as a real `Tri`, lies in the target. -/
theorem pieceTri_subset_target {t : S2RTiling.Tri} (ht : t ∈ S2RTiling.tiles) :
    (pieceTri ht).carrier ⊆ targetTri.carrier :=
  Erdos634.CertGeom.carrier_subset_of_pts_mem (fun k => by
    rw [pieceTri_pts t ht k]; exact vertexOf_mem_targetTri ht k)

/-! ## (C4): the area sum, and the assembled `CongruentDissection`

`Tiling44`'s own `checkAll` already checks `zsum (tiles.map area2) == area2 target`; this section
transfers that Bool equality to the real determinant sum `AreaDet.area_identity_of_det` needs. -/

/-- Every piece of `Tiling44`, indexed by `Fin S2RTiling.tiles.length` (rather than a fixed literal
`44`, so no length-cast bookkeeping is needed anywhere in this section). -/
noncomputable def pieceAt (i : Fin S2RTiling.tiles.length) : Tri :=
  pieceTri (t := S2RTiling.tiles[i.val]) (List.getElem_mem i.isLt)

theorem detTri_pieceAt (i : Fin S2RTiling.tiles.length) :
    Erdos634.AreaDet.detTri (pieceAt i) = toR (S2RTiling.area2 (S2RTiling.tiles[i.val])) := by
  unfold pieceAt pieceTri
  rw [Erdos634.CertCoord.detTri_mkTri, det3_eq_toR_cross]
  rfl

theorem foldl_zadd_eq (l : List S2RTiling.Z2) (acc : S2RTiling.Z2) :
    l.foldl S2RTiling.zadd acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [ih]; apply Prod.ext <;> simp [S2RTiling.zadd] <;> ring

theorem zsum_eq_sum (l : List S2RTiling.Z2) : S2RTiling.zsum l = l.sum := by
  simp only [S2RTiling.zsum]; rw [foldl_zadd_eq]; simp

theorem tiling322_zadd_eq_zreal (u v : S2RTiling.Z2) : S2RTiling.zadd u v = zadd u v := rfl

theorem toR_list_sum (l : List S2RTiling.Z2) : toR l.sum = (l.map toR).sum := by
  induction l with
  | nil => simp [toR]
  | cons a t ih =>
    simp only [List.sum_cons, List.map_cons]
    show toR (a + t.sum) = toR a + (List.map toR t).sum
    rw [show (a + t.sum : S2RTiling.Z2) = S2RTiling.zadd a t.sum from rfl,
      tiling322_zadd_eq_zreal, toR_add, ih]

set_option maxRecDepth 100000 in
theorem area_sum_transfer :
    ∑ i : Fin S2RTiling.tiles.length, toR (S2RTiling.area2 (S2RTiling.tiles[i.val]))
      = toR (S2RTiling.zsum (S2RTiling.tiles.map S2RTiling.area2)) := by
  rw [zsum_eq_sum, toR_list_sum, List.map_map,
    ← List.ofFn_getElem_eq_map S2RTiling.tiles (toR ∘ S2RTiling.area2)]
  rfl

/-- **The (C4) area sum, transferred to `ℝ`** — matching `Tiling44`'s own `checkAll` equality. -/
theorem area_sum_eq_target :
    ∑ i : Fin S2RTiling.tiles.length, toR (S2RTiling.area2 (S2RTiling.tiles[i.val]))
      = toR (S2RTiling.area2 S2RTiling.target) := by
  rw [area_sum_transfer]
  apply congrArg toR
  have h := S2RTiling.tiling322_certificate
  simp only [S2RTiling.checkAll, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- **(C4) fully assembled**, with absolute values — every piece is positively oriented
(`all_pieces_pos`) and so is the target (`target_det_pos`), so `|det| = det` throughout. -/
theorem abs_detTri_sum_eq_target :
    ∑ i : Fin S2RTiling.tiles.length, |Erdos634.AreaDet.detTri (pieceAt i)|
      = |Erdos634.AreaDet.detTri targetTri| := by
  have htarget : Erdos634.AreaDet.detTri targetTri = toR (S2RTiling.area2 S2RTiling.target) := by
    unfold targetTri
    rw [Erdos634.CertCoord.detTri_mkTri, det3_eq_toR_cross]
    rfl
  have htpos : (0:ℝ) < Erdos634.AreaDet.detTri targetTri := by
    unfold targetTri; rw [Erdos634.CertCoord.detTri_mkTri]; exact target_det_pos
  rw [htarget, abs_of_pos (htarget ▸ htpos)]
  rw [← area_sum_eq_target]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [detTri_pieceAt]
  exact abs_of_pos (toR_pos (all_pieces_pos _ (List.getElem_mem i.isLt)))

-- S2RTiling's certificate, assembled into a genuine CongruentDissection.
set_option maxRecDepth 8192 in
theorem tiles_nodup : S2RTiling.tiles.Nodup := by decide +kernel

theorem tiles_getElem_inj : ∀ i j : Fin S2RTiling.tiles.length, i ≠ j →
    S2RTiling.tiles[i.val] ≠ S2RTiling.tiles[j.val] := by
  intro i j hij h
  exact hij (Fin.ext ((List.Nodup.getElem_inj_iff tiles_nodup).mp h))

noncomputable def dissection : CongruentDissection S2RTiling.tiles.length where
  toDissection := Erdos634.AreaDet.ofDetCertificate targetTri pieceAt
    (fun i => pieceTri_subset_target (List.getElem_mem i.isLt))
    (fun i j hij => pieces_interiors_disjoint (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)
      (tiles_getElem_inj i j hij))
    abs_detTri_sum_eq_target
  model := pieceTri headI_mem_tiles
  tiles_congruent := fun i => pieceTri_congruent (List.getElem_mem i.isLt)

/-! ## Checking `dissection`'s shape

The isosceles triangle with sides `(16,16,22)` is tiled by 44 congruent copies of the `(2,3,4)`
triangle. Consequently `44m²` is a tile count for every `m ≥ 1`. Only the first clause is checked
here. -/

/-- **`dissection`'s target has sides in ratio `126:81:115`**. -/
theorem targetTri_pts_eq (k : Fin 3) :
    targetTri.pts k = Erdos634.CertCoord.mkPt
      (toR (zx (toZPt (![S2RTiling.t1 S2RTiling.target, S2RTiling.t2 S2RTiling.target,
        S2RTiling.t3 S2RTiling.target] k))))
      (toR (zy (toZPt (![S2RTiling.t1 S2RTiling.target, S2RTiling.t2 S2RTiling.target,
        S2RTiling.t3 S2RTiling.target] k)))) := by
  fin_cases k <;> rfl

theorem targetTri_dist_sq (i j : Fin 3) :
    dist (targetTri.pts i) (targetTri.pts j) ^ 2
      = toR (S2RTiling.dist2
          (![S2RTiling.t1 S2RTiling.target, S2RTiling.t2 S2RTiling.target, S2RTiling.t3 S2RTiling.target] i)
          (![S2RTiling.t1 S2RTiling.target, S2RTiling.t2 S2RTiling.target, S2RTiling.t3 S2RTiling.target] j)) := by
  rw [targetTri_pts_eq i, targetTri_pts_eq j, Erdos634.CertCoord.dist_sq_mkPt, dist2_eq_zdist2]
  exact toR_zdist2 _ _

theorem targetTri_sides :
    dist (targetTri.pts 0) (targetTri.pts 1) ^ 2 = 3486784401
    ∧ dist (targetTri.pts 1) (targetTri.pts 2) ^ 2 = 8437157316
    ∧ dist (targetTri.pts 2) (targetTri.pts 0) ^ 2 = 7028307225 := by
  have e01 : S2RTiling.dist2 (S2RTiling.t1 S2RTiling.target) (S2RTiling.t2 S2RTiling.target)
      = ((3486784401:ℤ),(0:ℤ)) := by decide
  have e12 : S2RTiling.dist2 (S2RTiling.t2 S2RTiling.target) (S2RTiling.t3 S2RTiling.target)
      = ((8437157316:ℤ),(0:ℤ)) := by decide
  have e20 : S2RTiling.dist2 (S2RTiling.t3 S2RTiling.target) (S2RTiling.t1 S2RTiling.target)
      = ((7028307225:ℤ),(0:ℤ)) := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [targetTri_dist_sq 0 1]; simp; rw [e01]; simp [toR]
  · rw [targetTri_dist_sq 1 2]; simp; rw [e12]; simp [toR]
  · rw [targetTri_dist_sq 2 0]; simp; rw [e20]; simp [toR]

/-- **The model tile's sides are in ratio `6:5:9`** (squared `36:25:81`, scaled by `729²`:
`19131876:13286025:43046721`). -/
theorem model_sides :
    (dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 19131876
      ∨ dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 13286025
      ∨ dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 43046721)
    ∧ (dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 19131876
      ∨ dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 13286025
      ∨ dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 43046721)
    ∧ (dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 19131876
      ∨ dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 13286025
      ∨ dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 43046721) := by
  have e01 : S2RTiling.dist2 (vertexOf S2RTiling.tiles.headI 0) (vertexOf S2RTiling.tiles.headI 1)
      = ((43046721:ℤ),(0:ℤ)) := by decide
  have e12 : S2RTiling.dist2 (vertexOf S2RTiling.tiles.headI 1) (vertexOf S2RTiling.tiles.headI 2)
      = ((19131876:ℤ),(0:ℤ)) := by decide
  have e20 : S2RTiling.dist2 (vertexOf S2RTiling.tiles.headI 2) (vertexOf S2RTiling.tiles.headI 0)
      = ((13286025:ℤ),(0:ℤ)) := by decide
  refine ⟨Or.inr (Or.inr ?_), Or.inl ?_, Or.inr (Or.inl ?_)⟩
  · rw [pieceTri_dist_sq _ headI_mem_tiles 0 1, e01]; norm_num [toR]
  · rw [pieceTri_dist_sq _ headI_mem_tiles 1 2, e12]; norm_num [toR]
  · rw [pieceTri_dist_sq _ headI_mem_tiles 2 0, e20]; norm_num [toR]

/-! ## Clause 2 of `thm:44`: "consequently `44m²` is a tile count for every `m ≥ 1`"

Composing `dissection` with `Ladder.ladder` for arbitrary `m` scales the target by `m` in each
direction, multiplying the piece count by `m²`. -/

theorem targetTri_eq_mkTri :
    targetTri = Erdos634.CertCoord.mkTri
      (toR (zx (toZPt (S2RTiling.t1 S2RTiling.target)))) (toR (zy (toZPt (S2RTiling.t1 S2RTiling.target))))
      (toR (zx (toZPt (S2RTiling.t2 S2RTiling.target)))) (toR (zy (toZPt (S2RTiling.t2 S2RTiling.target))))
      (toR (zx (toZPt (S2RTiling.t3 S2RTiling.target)))) (toR (zy (toZPt (S2RTiling.t3 S2RTiling.target))))
      target_det_pos.ne' := rfl

/-- **Clause 2 of `thm:44`**: for every `m ≥ 1`, there is a `CongruentDissection` with `44 * m * m`
pieces, all congruent to the `(2,3,4)`-shaped model tile, of the `m`-times-enlarged target. This is
`Ladder.ladder` applied to `dissection`. -/
theorem exists_dissection_mul_sq (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (m * m * S2RTiling.tiles.length), E.model = pieceTri headI_mem_tiles :=
  ⟨(Erdos634.Ladder.ladder
      (A := Erdos634.CertCoord.mkPt (toR (zx (toZPt (S2RTiling.t1 S2RTiling.target))))
        (toR (zy (toZPt (S2RTiling.t1 S2RTiling.target)))))
      (B := Erdos634.CertCoord.mkPt (toR (zx (toZPt (S2RTiling.t2 S2RTiling.target))))
        (toR (zy (toZPt (S2RTiling.t2 S2RTiling.target)))))
      (C := Erdos634.CertCoord.mkPt (toR (zx (toZPt (S2RTiling.t3 S2RTiling.target))))
        (toR (zy (toZPt (S2RTiling.t3 S2RTiling.target)))))
      targetTri.indep dissection targetTri_eq_mkTri m hm).choose,
    (Erdos634.Ladder.ladder
      (A := Erdos634.CertCoord.mkPt (toR (zx (toZPt (S2RTiling.t1 S2RTiling.target))))
        (toR (zy (toZPt (S2RTiling.t1 S2RTiling.target)))))
      (B := Erdos634.CertCoord.mkPt (toR (zx (toZPt (S2RTiling.t2 S2RTiling.target))))
        (toR (zy (toZPt (S2RTiling.t2 S2RTiling.target)))))
      (C := Erdos634.CertCoord.mkPt (toR (zx (toZPt (S2RTiling.t3 S2RTiling.target))))
        (toR (zy (toZPt (S2RTiling.t3 S2RTiling.target)))))
      targetTri.indep dissection targetTri_eq_mkTri m hm).choose_spec.2⟩

set_option maxRecDepth 100000 in
theorem tiles_length_eq_322 : S2RTiling.tiles.length = 322 := by decide

/-- **Clause 2, restated in the paper's own numeral form**: `322 * m ^ 2` is a tile count for every
`m ≥ 1`. -/
theorem exists_dissection_322_mul_sq (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (322 * m ^ 2), E.model = pieceTri headI_mem_tiles := by
  obtain ⟨E, hE⟩ := exists_dissection_mul_sq m hm
  have hnum : m * m * S2RTiling.tiles.length = 322 * m ^ 2 := by
    rw [tiles_length_eq_322]; ring
  exact hnum ▸ ⟨E, hE⟩


/-- **`Nonempty (CongruentDissection 322)`**: the triangle (126,81,115) is dissected into 322 triangles
congruent to the (6,5,9) tile (cos 7/9 angle). -/
theorem s2r_nonempty_congruentDissection : Nonempty (CongruentDissection 322) := by
  obtain ⟨E, _⟩ := exists_dissection_322_mul_sq 1 one_pos
  exact ⟨by simpa using E⟩

#print axioms s2r_nonempty_congruentDissection

end Erdos634.S2RTilingBridge
