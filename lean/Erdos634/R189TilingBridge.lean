import Erdos634.R189Tiling
import Erdos634.Z15Real
import Erdos634.CertGeom
import Erdos634.SssCongruent
import Erdos634.Ladder
import Erdos634.Tiling44Bridge

/-!
# `R189Tiling`, assembled into a genuine `CongruentDissection`

Erdős #634. `189` is a tile count (the base-α target of the tile (2,3,4) at scale 3). Same
pattern that closed `thm:44`/`thm:63` (`Erdos634.Tiling44Bridge`/`Erdos634.CevianTiling63Bridge`):
`R189Tiling`'s `Z15`/`Pt`/`cross`/`dist2`/`znonneg` are literally `Z15Real`'s through `toZPt`, so
every general lemma applies unchanged. `R189Tiling` has a named `target` field, like the certificate.

Not a paper-row flip until checked against `cor:elevenm`'s exact statement.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.R189TilingBridge

open Erdos634.Z15Real Erdos634.Geometry
open Erdos634.Tiling44Bridge (affNeg_apply lineFun_ne_zero_of_sq_ne)

def toZPt (p : R189Tiling.Pt) : ZPt := p

/-- **The real determinant of a `R189Tiling.Tri`'s three vertices**, transferred from its `ℤ[√15]`
cross product. -/
theorem det3_eq_toR_cross (t : R189Tiling.Tri) :
    Erdos634.CertCoord.det3
      (toR (zx (toZPt (R189Tiling.t1 t)))) (toR (zy (toZPt (R189Tiling.t1 t))))
      (toR (zx (toZPt (R189Tiling.t2 t)))) (toR (zy (toZPt (R189Tiling.t2 t))))
      (toR (zx (toZPt (R189Tiling.t3 t)))) (toR (zy (toZPt (R189Tiling.t3 t))))
    = toR (zcross (toZPt (R189Tiling.t1 t)) (toZPt (R189Tiling.t2 t)) (toZPt (R189Tiling.t3 t))) :=
  toR_zcross _ _ _

/-- **The target's determinant is `18144√15`**, positive. -/
theorem target_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (R189Tiling.t1 R189Tiling.target))))
      (toR (zy (toZPt (R189Tiling.t1 R189Tiling.target))))
      (toR (zx (toZPt (R189Tiling.t2 R189Tiling.target))))
      (toR (zy (toZPt (R189Tiling.t2 R189Tiling.target))))
      (toR (zx (toZPt (R189Tiling.t3 R189Tiling.target))))
      (toR (zy (toZPt (R189Tiling.t3 R189Tiling.target)))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (R189Tiling.t1 R189Tiling.target))
    (toZPt (R189Tiling.t2 R189Tiling.target)) (toZPt (R189Tiling.t3 R189Tiling.target))) (by decide)

/-- **The target, as a real `Tri`.** -/
noncomputable def targetTri : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (R189Tiling.t1 R189Tiling.target))))
    (toR (zy (toZPt (R189Tiling.t1 R189Tiling.target))))
    (toR (zx (toZPt (R189Tiling.t2 R189Tiling.target))))
    (toR (zy (toZPt (R189Tiling.t2 R189Tiling.target))))
    (toR (zx (toZPt (R189Tiling.t3 R189Tiling.target))))
    (toR (zy (toZPt (R189Tiling.t3 R189Tiling.target))))
    target_det_pos.ne'

/-- **The first piece's determinant is `48√15`**, positive — a smaller instance of the same
computation, confirming the pattern generalizes piece-by-piece. -/
theorem piece0_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (R189Tiling.t1 (R189Tiling.tiles.headI)))))
      (toR (zy (toZPt (R189Tiling.t1 (R189Tiling.tiles.headI)))))
      (toR (zx (toZPt (R189Tiling.t2 (R189Tiling.tiles.headI)))))
      (toR (zy (toZPt (R189Tiling.t2 (R189Tiling.tiles.headI)))))
      (toR (zx (toZPt (R189Tiling.t3 (R189Tiling.tiles.headI)))))
      (toR (zy (toZPt (R189Tiling.t3 (R189Tiling.tiles.headI))))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (R189Tiling.t1 (R189Tiling.tiles.headI)))
    (toZPt (R189Tiling.t2 (R189Tiling.tiles.headI))) (toZPt (R189Tiling.t3 (R189Tiling.tiles.headI))))
    (by decide)

-- Every one of the 189 pieces is positively oriented.
set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem all_pieces_pos :
    ∀ t ∈ R189Tiling.tiles,
      zpos (zcross (toZPt (R189Tiling.t1 t)) (toZPt (R189Tiling.t2 t)) (toZPt (R189Tiling.t3 t)))
        = true := by
  decide +kernel

/-- **Every piece, as a real `Tri`**, uniformly — the general form `thm:44`'s data entry needs,
combining `all_pieces_pos` with `det3_eq_toR_cross` instead of writing 44 separate constructions. -/
noncomputable def pieceTri {t : R189Tiling.Tri} (ht : t ∈ R189Tiling.tiles) : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (R189Tiling.t1 t)))) (toR (zy (toZPt (R189Tiling.t1 t))))
    (toR (zx (toZPt (R189Tiling.t2 t)))) (toR (zy (toZPt (R189Tiling.t2 t))))
    (toR (zx (toZPt (R189Tiling.t3 t)))) (toR (zy (toZPt (R189Tiling.t3 t))))
    (by
      rw [det3_eq_toR_cross]
      exact (toR_pos (all_pieces_pos t ht)).ne')

/-- **The `lineFun` of a certificate edge is nonconstant**, for two *concrete* endpoints `P ≠ Q`
whose real coordinates differ — resolved via `Z15Real.toR_ne_zero_of_sq_ne` rather than injectivity
of `toR` (which this project deliberately never proves). `hx`/`hy` are the decidable `ℤ[√15]`
side conditions (`zx Q - zx P` resp. `zy Q - zy P` squared-nonequal to `15 * (other coord)²`); one
of the two always holds for a genuine edge, matching whichever coordinate actually differs. -/
theorem lineFun_ne_zero_of_sq_ne {P Q : ZPt}
    (h : (zsub (zx P) (zx Q)).1 ^ 2 ≠ 15 * (zsub (zx P) (zx Q)).2 ^ 2
       ∨ (zsub (zy P) (zy Q)).1 ^ 2 ≠ 15 * (zsub (zy P) (zy Q)).2 ^ 2) :
    (Erdos634.CertGeom.lineFun (toR (zx P)) (toR (zy P)) (toR (zx Q)) (toR (zy Q))).linear ≠ 0 := by
  apply Erdos634.CertGeom.lineFun_linear_ne_zero
  rcases h with h | h
  · exact Or.inl (sub_ne_zero.mp (by rw [← toR_sub]; exact toR_ne_zero_of_sq_ne h))
  · exact Or.inr (sub_ne_zero.mp (by rw [← toR_sub]; exact toR_ne_zero_of_sq_ne h))

/-- Pointwise negation of an affine map into `ℝ`. -/
theorem affNeg_apply (g : Plane →ᵃ[ℝ] ℝ) (p : Plane) : (-g) p = -(g p) := by
  have := congrFun (AffineMap.coe_neg g) p
  simpa using this

/-- `R189Tiling.cross` is literally `Z15Real.zcross` read through `toZPt` — the two files define the
same operations on the same underlying type, so this is `rfl`. -/
theorem cross_eq_zcross (o a b : R189Tiling.Pt) :
    R189Tiling.cross o a b = zcross (toZPt o) (toZPt a) (toZPt b) := rfl

/-- `R189Tiling.dist2` is literally `Z15Real.zdist2` read through `toZPt` — again `rfl`. -/
theorem dist2_eq_zdist2 (p q : R189Tiling.Pt) :
    R189Tiling.dist2 p q = zdist2 (toZPt p) (toZPt q) := rfl

/-- **A piece's vertex, named by index.** -/
def vertexOf (t : R189Tiling.Tri) (i : Fin 3) : R189Tiling.Pt :=
  ![R189Tiling.t1 t, R189Tiling.t2 t, R189Tiling.t3 t] i

/-- **`pieceTri`'s vertices are exactly `vertexOf`, read as real points.** -/
theorem pieceTri_pts (t : R189Tiling.Tri) (ht : t ∈ R189Tiling.tiles) (i : Fin 3) :
    (pieceTri ht).pts i
      = Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i)))) := by
  fin_cases i <;> rfl

/-- **Squared distances between a piece's vertices, transferred to `ℝ` from the certificate's own
`dist2`.** -/
theorem pieceTri_dist_sq (t : R189Tiling.Tri) (ht : t ∈ R189Tiling.tiles) (i j : Fin 3) :
    dist ((pieceTri ht).pts i) ((pieceTri ht).pts j) ^ 2 = toR (R189Tiling.dist2 (vertexOf t i) (vertexOf t j)) := by
  rw [pieceTri_pts t ht i, pieceTri_pts t ht j, Erdos634.CertCoord.dist_sq_mkPt,
    dist2_eq_zdist2]
  exact toR_zdist2 _ _

/-- **A single `sepBy`-true witness gives a genuine separating affine functional** between two
pieces, read as real `Tri` objects — the assembly step `CertGeom.pairwise_disjoint_of_separating`
needs, for one pair. `hPQ` is `lineFun_ne_zero_of_sq_ne`'s decidable side condition on the edge
`(P, Q)`; the certificate's own `sepBy` supplies which sign pattern holds. -/
theorem sep_of_sepBy {P Q : R189Tiling.Pt} {A B : R189Tiling.Tri}
    (hPQ : (zsub (zx (toZPt P)) (zx (toZPt Q))).1 ^ 2
             ≠ 15 * (zsub (zx (toZPt P)) (zx (toZPt Q))).2 ^ 2
         ∨ (zsub (zy (toZPt P)) (zy (toZPt Q))).1 ^ 2
             ≠ 15 * (zsub (zy (toZPt P)) (zy (toZPt Q))).2 ^ 2)
    (hsep : R189Tiling.sepBy P Q A B = true) (hA : A ∈ R189Tiling.tiles) (hB : B ∈ R189Tiling.tiles) :
    ∃ (f : Plane →ᵃ[ℝ] ℝ) (_ : f.linear ≠ 0) (c : ℝ),
      (∀ x ∈ (pieceTri hA).carrier, f x ≤ c) ∧ (∀ x ∈ (pieceTri hB).carrier, c ≤ f x) := by
  set f : Plane →ᵃ[ℝ] ℝ :=
    Erdos634.CertGeom.lineFun (toR (zx (toZPt P))) (toR (zy (toZPt P)))
      (toR (zx (toZPt Q))) (toR (zy (toZPt Q))) with hfdef
  have hflin : f.linear ≠ 0 := lineFun_ne_zero_of_sq_ne hPQ
  have hfval : ∀ v : R189Tiling.Pt,
      f (Erdos634.CertCoord.mkPt (toR (zx (toZPt v))) (toR (zy (toZPt v))))
        = toR (R189Tiling.cross P Q v) := by
    intro v
    rw [hfdef, Erdos634.CertGeom.lineFun_apply, Erdos634.CertCoord.mkPt_zero,
      Erdos634.CertCoord.mkPt_one, cross_eq_zcross]
    exact toR_zcross _ _ _
  have hpts : ∀ (t : R189Tiling.Tri) (ht : t ∈ R189Tiling.tiles) (k : Fin 3),
      (pieceTri ht).pts k
        = Erdos634.CertCoord.mkPt (toR (zx (toZPt (![R189Tiling.t1 t, R189Tiling.t2 t, R189Tiling.t3 t] k))))
            (toR (zy (toZPt (![R189Tiling.t1 t, R189Tiling.t2 t, R189Tiling.t3 t] k)))) := by
    intro t ht k; fin_cases k <;> rfl
  simp only [R189Tiling.sepBy, List.all_eq_true, List.mem_cons, Bool.and_eq_true,
    Bool.or_eq_true, List.map, forall_eq_or_imp] at hsep
  rcases hsep with ⟨hsA, hsB⟩ | ⟨hsA, hsB⟩
  · -- A's vertices have cross ≥ 0, B's have cross ≤ 0 (znonpos)
    refine ⟨-f, neg_ne_zero.mpr hflin, 0, ?_, ?_⟩
    · exact Erdos634.CertGeom.le_of_forall_pts_le (-f) (t := pieceTri hA) (c := 0)
        (fun k => by
          rw [affNeg_apply, hpts A hA k, hfval, neg_le, neg_zero]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonneg hsA.1 | exact Erdos634.Z15Real.toR_nonneg hsA.2.1 | exact Erdos634.Z15Real.toR_nonneg hsA.2.2.1)
    · intro x hx
      have hb := Erdos634.CertGeom.le_of_forall_pts_le f (t := pieceTri hB) (c := 0)
        (fun k => by
          rw [hpts B hB k, hfval]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonpos hsB.1 | exact Erdos634.Z15Real.toR_nonpos hsB.2.1 | exact Erdos634.Z15Real.toR_nonpos hsB.2.2.1)
      have := hb x hx
      rw [affNeg_apply]
      linarith
  · -- A's vertices have cross ≤ 0 (znonpos), B's have cross ≥ 0
    refine ⟨f, hflin, 0, ?_, ?_⟩
    · exact Erdos634.CertGeom.le_of_forall_pts_le f (t := pieceTri hA) (c := 0)
        (fun k => by
          rw [hpts A hA k, hfval]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonpos hsA.1 | exact Erdos634.Z15Real.toR_nonpos hsA.2.1 | exact Erdos634.Z15Real.toR_nonpos hsA.2.2.1)
    · intro x hx
      have hb := Erdos634.CertGeom.le_of_forall_pts_le (-f) (t := pieceTri hB) (c := 0)
        (fun k => by
          rw [affNeg_apply, hpts B hB k, hfval, neg_le, neg_zero]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonneg hsB.1 | exact Erdos634.Z15Real.toR_nonneg hsB.2.1 | exact Erdos634.Z15Real.toR_nonneg hsB.2.2.1)
      have := hb x hx
      rw [affNeg_apply] at this
      linarith

/-! ## Every pair of distinct pieces is separated — decided by the kernel in chunks

Rather than unpacking an explicit witness list, it is cheaper to `decide` the *existence* of a separating edge candidate per
pair directly: for each of the ordered pairs, some one of the 6 candidate edges (3 from each
triangle) both separates them (`sepBy`) and satisfies `sep_of_sepBy`'s decidable side condition
(`sqCond`). This one `decide` (~12s) replaces per-pair data entry entirely. -/

/-- The 6 candidate separating edges for a pair: each triangle's own 3 edges. -/
def edgeCands (A B : R189Tiling.Tri) : List (R189Tiling.Pt × R189Tiling.Pt) :=
  [R189Tiling.edgeOf A 0, R189Tiling.edgeOf A 1, R189Tiling.edgeOf A 2,
   R189Tiling.edgeOf B 0, R189Tiling.edgeOf B 1, R189Tiling.edgeOf B 2]

/-- The decidable side condition `sep_of_sepBy` needs for an edge `(P, Q)`, as a `Bool` — a direct
`decide` of the exact `Prop` `sep_of_sepBy` wants, so `sqCond_iff` is immediate. -/
def sqCond (pq : R189Tiling.Pt × R189Tiling.Pt) : Bool :=
  decide ((zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).1 ^ 2
             ≠ 15 * (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).2 ^ 2
         ∨ (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).1 ^ 2
             ≠ 15 * (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).2 ^ 2)

/-- Some candidate edge both separates `A` and `B` and satisfies the side condition. -/
def pairOK (A B : R189Tiling.Tri) : Bool :=
  (edgeCands A B).any (fun pq => R189Tiling.sepBy pq.1 pq.2 A B && sqCond pq)

-- Every one of the 189*189 ordered pairs of distinct pieces has a working separating edge.
-- (R84TilingBridge decides the `∀ A ∈ tiles, ∀ B ∈ tiles` statement in one `decide`; at 189 tiles that needs more
-- than 10 GB, so here the check is a Bool function evaluated by the kernel on 7 chunks of 27 tiles.)

/-- `pairOK A B` for every `A` of `L` and every tile `B ≠ A`, as a `Bool` -/
def pairsOK (L : List R189Tiling.Tri) : Bool :=
  L.all (fun A => R189Tiling.tiles.all (fun B => decide (A = B) || pairOK A B))

/-- the `k`-th block of 27 tiles -/
def chunk (k : Nat) : List R189Tiling.Tri := (R189Tiling.tiles.drop (27 * k)).take 27

set_option maxRecDepth 400000 in
theorem pairs_ok_0 : pairsOK (chunk 0) = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem pairs_ok_1 : pairsOK (chunk 1) = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem pairs_ok_2 : pairsOK (chunk 2) = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem pairs_ok_3 : pairsOK (chunk 3) = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem pairs_ok_4 : pairsOK (chunk 4) = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem pairs_ok_5 : pairsOK (chunk 5) = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem pairs_ok_6 : pairsOK (chunk 6) = true := by decide +kernel

set_option maxRecDepth 400000 in
theorem tiles_eq_chunks : R189Tiling.tiles =
    chunk 0 ++ chunk 1 ++ chunk 2 ++ chunk 3 ++ chunk 4 ++ chunk 5 ++ chunk 6 := by decide +kernel

theorem all_pairs_ok : ∀ A ∈ R189Tiling.tiles, ∀ B ∈ R189Tiling.tiles, A ≠ B → pairOK A B = true := by
  intro A hA B hB hne
  have key : ∀ k, pairsOK (chunk k) = true → A ∈ chunk k → pairOK A B = true := by
    intro k hk hAk
    have h1 := List.all_eq_true.mp hk A hAk
    have h2 := List.all_eq_true.mp h1 B hB
    rcases (Bool.or_eq_true _ _).mp h2 with h | h
    · exact absurd (of_decide_eq_true h) hne
    · exact h
  rw [tiles_eq_chunks] at hA
  simp only [List.mem_append] at hA
  rcases hA with (((((h | h) | h) | h) | h) | h) | h
  · exact key 0 pairs_ok_0 h
  · exact key 1 pairs_ok_1 h
  · exact key 2 pairs_ok_2 h
  · exact key 3 pairs_ok_3 h
  · exact key 4 pairs_ok_4 h
  · exact key 5 pairs_ok_5 h
  · exact key 6 pairs_ok_6 h

/-- `sqCond`'s `Bool` and `sep_of_sepBy`'s `Prop` side condition agree. -/
theorem sqCond_iff (pq : R189Tiling.Pt × R189Tiling.Pt) :
    sqCond pq = true ↔
      (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).1 ^ 2 ≠ 15 * (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).2 ^ 2
        ∨ (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).1 ^ 2
            ≠ 15 * (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).2 ^ 2 := by
  rw [sqCond, decide_eq_true_iff]

/-- **Every two distinct pieces of the certificate have disjoint interiors, as real `Tri` objects.**
This is (C3) fully assembled: existence of the separating edge (`all_pairs_ok`), transferred to a
genuine affine functional bounded on the whole carrier (`sep_of_sepBy`). -/
theorem pieces_interiors_disjoint {A B : R189Tiling.Tri} (hA : A ∈ R189Tiling.tiles)
    (hB : B ∈ R189Tiling.tiles) (hne : A ≠ B) :
    Disjoint (interior (pieceTri hA).carrier) (interior (pieceTri hB).carrier) := by
  have hok := all_pairs_ok A hA B hB hne
  simp only [pairOK, List.any_eq_true] at hok
  obtain ⟨pq, hmem, hsep⟩ := hok
  rw [Bool.and_eq_true] at hsep
  obtain ⟨hsepBy, hsq⟩ := hsep
  obtain ⟨f, hf, c, h1, h2⟩ := sep_of_sepBy ((sqCond_iff pq).mp hsq) hsepBy hA hB
  exact Erdos634.CertGeom.interiors_disjoint_of_separating f hf c h1 h2

/-! ## (C1): every piece is congruent to a fixed model — the first piece, decided at once -/

/-- **The model tile**: the certificate's first certificate piece. Any piece works as the model since
all are mutually congruent; picking one already in `tiles` avoids naming new coordinates. -/
theorem headI_mem_tiles : R189Tiling.tiles.headI ∈ R189Tiling.tiles := by decide +kernel

/-- **Some permutation matches a piece's squared side lengths to the model's, positionally.**
`decide` over the `Fintype (Equiv.Perm (Fin 3))` (6 elements) × 189 pieces × 9 pairs. -/
def congOK' (t : R189Tiling.Tri) : Bool :=
  decide (∃ σ : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
    R189Tiling.dist2 (vertexOf t i) (vertexOf t j)
      = R189Tiling.dist2 (vertexOf R189Tiling.tiles.headI (σ i)) (vertexOf R189Tiling.tiles.headI (σ j)))

-- Every one of the 189 pieces has a matching permutation.
set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem all_pieces_cong : ∀ t ∈ R189Tiling.tiles, congOK' t = true := by decide +kernel

/-- **(C1) fully assembled**: every piece of the certificate, as a real `Tri`, is congruent to the
model tile. -/
theorem pieceTri_congruent {t : R189Tiling.Tri} (ht : t ∈ R189Tiling.tiles) :
    (pieceTri ht).Congruent (pieceTri headI_mem_tiles) := by
  have hex := all_pieces_cong t ht
  simp only [congOK', decide_eq_true_eq] at hex
  obtain ⟨σ, hσ⟩ := hex
  refine Erdos634.SssCongruent.congruent_of_sq_dist_perm σ (fun i j => ?_)
  rw [pieceTri_dist_sq t ht, pieceTri_dist_sq R189Tiling.tiles.headI headI_mem_tiles]
  exact congrArg Erdos634.Z15Real.toR (hσ i j)

/-! ## (C2) containment: every piece lies in the target — the part `all_pieces_pos` skipped

`all_pieces_pos` only captured orientation (`insideOK`'s first conjunct); this is the actual
vertex-in-target containment, `insideOK`'s second conjunct. -/

/-- **Cyclic invariance of `cross`**: `cross o a b = cross a b o`. Twice the signed area of a
triangle does not depend on which vertex is named first, only the cyclic order. Needed to match
`insideOK`'s three checks (each anchored at a different target edge) against
`CertCoord.mem_carrier_of_dets`'s fixed vertex-0/1/2 convention. -/
theorem cross_cyclic (o a b : R189Tiling.Pt) : R189Tiling.cross o a b = R189Tiling.cross a b o := by
  simp only [R189Tiling.cross, R189Tiling.zsub, R189Tiling.zmul, R189Tiling.px, R189Tiling.py, Prod.ext_iff]
  constructor <;> ring

-- Every one of the 189 pieces' vertices lies in the closed target.
set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem all_pieces_inside : ∀ t ∈ R189Tiling.tiles, R189Tiling.insideOK t = true := by decide +kernel

/-- Abbreviations for the target's three vertices. -/
theorem insideOK_vertex {t : R189Tiling.Tri} (ht : t ∈ R189Tiling.tiles) (i : Fin 3) :
    R189Tiling.znonneg (R189Tiling.cross (R189Tiling.t1 R189Tiling.target) (R189Tiling.t2 R189Tiling.target)
        (vertexOf t i)) = true
    ∧ R189Tiling.znonneg (R189Tiling.cross (R189Tiling.t2 R189Tiling.target) (R189Tiling.t3 R189Tiling.target)
        (vertexOf t i)) = true
    ∧ R189Tiling.znonneg (R189Tiling.cross (R189Tiling.t3 R189Tiling.target) (R189Tiling.t1 R189Tiling.target)
        (vertexOf t i)) = true := by
  have hins := all_pieces_inside t ht
  simp only [R189Tiling.insideOK, Bool.and_eq_true, List.all_eq_true] at hins
  have hv : vertexOf t i ∈ ([R189Tiling.t1 t, R189Tiling.t2 t, R189Tiling.t3 t] : List R189Tiling.Pt) := by
    fin_cases i <;> simp [vertexOf]
  have h3 := hins.2 (vertexOf t i) hv
  simp only [Bool.and_eq_true] at h3
  exact ⟨h3.1.1, h3.1.2, h3.2⟩

/-- **The target, real vertex-by-vertex, matches `mem_carrier_of_dets`'s convention.** -/
theorem vertexOf_mem_targetTri {t : R189Tiling.Tri} (ht : t ∈ R189Tiling.tiles) (i : Fin 3) :
    Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i))))
      ∈ targetTri.carrier := by
  obtain ⟨h1, h2, h3⟩ := insideOK_vertex ht i
  refine Erdos634.CertCoord.mem_carrier_of_dets (x₀ := toR (zx (toZPt (R189Tiling.t1 R189Tiling.target))))
    (y₀ := toR (zy (toZPt (R189Tiling.t1 R189Tiling.target))))
    (x₁ := toR (zx (toZPt (R189Tiling.t2 R189Tiling.target))))
    (y₁ := toR (zy (toZPt (R189Tiling.t2 R189Tiling.target))))
    (x₂ := toR (zx (toZPt (R189Tiling.t3 R189Tiling.target))))
    (y₂ := toR (zy (toZPt (R189Tiling.t3 R189Tiling.target))))
    target_det_pos ?_ ?_ ?_
  · -- h0 : 0 ≤ det3 a b x1 y1 x2 y2 = cross(v, T2, T3) = cross(T2, T3, v) [cyclic]
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i))))
        (toR (zx (toZPt (R189Tiling.t2 R189Tiling.target)))) (toR (zy (toZPt (R189Tiling.t2 R189Tiling.target))))
        (toR (zx (toZPt (R189Tiling.t3 R189Tiling.target)))) (toR (zy (toZPt (R189Tiling.t3 R189Tiling.target))))
      = toR (zcross (toZPt (vertexOf t i)) (toZPt (R189Tiling.t2 R189Tiling.target))
          (toZPt (R189Tiling.t3 R189Tiling.target))) from toR_zcross _ _ _,
      ← cross_eq_zcross, cross_cyclic (vertexOf t i) (R189Tiling.t2 R189Tiling.target) (R189Tiling.t3 R189Tiling.target)]
    exact Erdos634.Z15Real.toR_nonneg h2
  · -- h1 : 0 ≤ det3 x0 y0 a b x2 y2 = cross(T1, v, T3) = cross(T3, T1, v) [two cyclic rotations]
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (R189Tiling.t1 R189Tiling.target))))
        (toR (zy (toZPt (R189Tiling.t1 R189Tiling.target)))) (toR (zx (toZPt (vertexOf t i))))
        (toR (zy (toZPt (vertexOf t i)))) (toR (zx (toZPt (R189Tiling.t3 R189Tiling.target))))
        (toR (zy (toZPt (R189Tiling.t3 R189Tiling.target))))
      = toR (zcross (toZPt (R189Tiling.t1 R189Tiling.target)) (toZPt (vertexOf t i))
          (toZPt (R189Tiling.t3 R189Tiling.target))) from toR_zcross _ _ _,
      ← cross_eq_zcross,
      cross_cyclic (R189Tiling.t1 R189Tiling.target) (vertexOf t i) (R189Tiling.t3 R189Tiling.target),
      cross_cyclic (vertexOf t i) (R189Tiling.t3 R189Tiling.target) (R189Tiling.t1 R189Tiling.target)]
    exact Erdos634.Z15Real.toR_nonneg h3
  · -- h2 : 0 ≤ det3 x0 y0 x1 y1 a b = cross(T1, T2, v), direct match
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (R189Tiling.t1 R189Tiling.target))))
        (toR (zy (toZPt (R189Tiling.t1 R189Tiling.target)))) (toR (zx (toZPt (R189Tiling.t2 R189Tiling.target))))
        (toR (zy (toZPt (R189Tiling.t2 R189Tiling.target)))) (toR (zx (toZPt (vertexOf t i))))
        (toR (zy (toZPt (vertexOf t i))))
      = toR (zcross (toZPt (R189Tiling.t1 R189Tiling.target)) (toZPt (R189Tiling.t2 R189Tiling.target))
          (toZPt (vertexOf t i))) from toR_zcross _ _ _,
      ← cross_eq_zcross]
    exact Erdos634.Z15Real.toR_nonneg h1

/-- **(C2) fully assembled**: every piece of the certificate, as a real `Tri`, lies in the target. -/
theorem pieceTri_subset_target {t : R189Tiling.Tri} (ht : t ∈ R189Tiling.tiles) :
    (pieceTri ht).carrier ⊆ targetTri.carrier :=
  Erdos634.CertGeom.carrier_subset_of_pts_mem (fun k => by
    rw [pieceTri_pts t ht k]; exact vertexOf_mem_targetTri ht k)

/-! ## (C4): the area sum, and the assembled `CongruentDissection`

the certificate's own `checkAll` already checks `zsum (tiles.map area2) == area2 target`; this section
transfers that Bool equality to the real determinant sum `AreaDet.area_identity_of_det` needs. -/

/-- Every piece of the certificate, indexed by `Fin R189Tiling.tiles.length` (rather than a fixed literal
`44`, so no length-cast bookkeeping is needed anywhere in this section). -/
noncomputable def pieceAt (i : Fin R189Tiling.tiles.length) : Tri :=
  pieceTri (t := R189Tiling.tiles[i.val]) (List.getElem_mem i.isLt)

theorem detTri_pieceAt (i : Fin R189Tiling.tiles.length) :
    Erdos634.AreaDet.detTri (pieceAt i) = toR (R189Tiling.area2 (R189Tiling.tiles[i.val])) := by
  unfold pieceAt pieceTri
  rw [Erdos634.CertCoord.detTri_mkTri, det3_eq_toR_cross]
  rfl

theorem foldl_zadd_eq (l : List R189Tiling.Z15) (acc : R189Tiling.Z15) :
    l.foldl R189Tiling.zadd acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [ih]; apply Prod.ext <;> simp [R189Tiling.zadd] <;> ring

theorem zsum_eq_sum (l : List R189Tiling.Z15) : R189Tiling.zsum l = l.sum := by
  simp only [R189Tiling.zsum]; rw [foldl_zadd_eq]; simp

theorem tiling189_zadd_eq_zreal (u v : R189Tiling.Z15) : R189Tiling.zadd u v = zadd u v := rfl

theorem toR_list_sum (l : List R189Tiling.Z15) : toR l.sum = (l.map toR).sum := by
  induction l with
  | nil => simp [toR]
  | cons a t ih =>
    simp only [List.sum_cons, List.map_cons]
    show toR (a + t.sum) = toR a + (List.map toR t).sum
    rw [show (a + t.sum : R189Tiling.Z15) = R189Tiling.zadd a t.sum from rfl,
      tiling189_zadd_eq_zreal, toR_add, ih]

set_option maxRecDepth 100000 in
theorem area_sum_transfer :
    ∑ i : Fin R189Tiling.tiles.length, toR (R189Tiling.area2 (R189Tiling.tiles[i.val]))
      = toR (R189Tiling.zsum (R189Tiling.tiles.map R189Tiling.area2)) := by
  rw [zsum_eq_sum, toR_list_sum, List.map_map,
    ← List.ofFn_getElem_eq_map R189Tiling.tiles (toR ∘ R189Tiling.area2)]
  rfl

/-- **The (C4) area sum, transferred to `ℝ`** — matching the certificate's own `checkAll` equality. -/
theorem area_sum_eq_target :
    ∑ i : Fin R189Tiling.tiles.length, toR (R189Tiling.area2 (R189Tiling.tiles[i.val]))
      = toR (R189Tiling.area2 R189Tiling.target) := by
  rw [area_sum_transfer]
  apply congrArg toR
  have h := R189Tiling.tiling189_certificate
  simp only [R189Tiling.checkAll, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- **(C4) fully assembled**, with absolute values — every piece is positively oriented
(`all_pieces_pos`) and so is the target (`target_det_pos`), so `|det| = det` throughout. -/
theorem abs_detTri_sum_eq_target :
    ∑ i : Fin R189Tiling.tiles.length, |Erdos634.AreaDet.detTri (pieceAt i)|
      = |Erdos634.AreaDet.detTri targetTri| := by
  have htarget : Erdos634.AreaDet.detTri targetTri = toR (R189Tiling.area2 R189Tiling.target) := by
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

-- R189Tiling's certificate, assembled into a genuine CongruentDissection.
/-- no repetition in a list, as a `Bool` -/
def nodupB : List R189Tiling.Tri → Bool
  | [] => true
  | a :: r => !(r.any (fun b => decide (a = b))) && nodupB r

theorem nodupB_sound : ∀ l : List R189Tiling.Tri, nodupB l = true → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a r ih =>
    intro h
    have h1 : r.any (fun b => decide (a = b)) = false := by
      cases hh : r.any (fun b => decide (a = b))
      · rfl
      · simp [nodupB, hh] at h
    have h2 : nodupB r = true := by
      simp only [nodupB, h1, Bool.not_false, Bool.true_and] at h
      exact h
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih h2⟩
    have h3 : r.any (fun b => decide (a = b)) = true := List.any_eq_true.mpr ⟨a, hmem, by simp⟩
    rw [h1] at h3
    exact Bool.false_ne_true h3

set_option maxRecDepth 400000 in
theorem tiles_nodup : R189Tiling.tiles.Nodup := nodupB_sound _ (by decide +kernel)

theorem tiles_getElem_inj : ∀ i j : Fin R189Tiling.tiles.length, i ≠ j →
    R189Tiling.tiles[i.val] ≠ R189Tiling.tiles[j.val] := by
  intro i j hij h
  exact hij (Fin.ext ((List.Nodup.getElem_inj_iff tiles_nodup).mp h))

noncomputable def dissection : CongruentDissection R189Tiling.tiles.length where
  toDissection := Erdos634.AreaDet.ofDetCertificate targetTri pieceAt
    (fun i => pieceTri_subset_target (List.getElem_mem i.isLt))
    (fun i j hij => pieces_interiors_disjoint (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)
      (tiles_getElem_inj i j hij))
    abs_detTri_sum_eq_target
  model := pieceTri headI_mem_tiles
  tiles_congruent := fun i => pieceTri_congruent (List.getElem_mem i.isLt)

/-! ## The shape of `dissection`

The target is the isosceles triangle `(63, 36, 36)` at scale 8 and the tile is `(2,3,4)` at scale 8. -/

/-- the corners of `dissection`'s target, read from the certificate -/
theorem targetTri_pts_eq (k : Fin 3) :
    targetTri.pts k = Erdos634.CertCoord.mkPt
      (toR (zx (toZPt (![R189Tiling.t1 R189Tiling.target, R189Tiling.t2 R189Tiling.target,
        R189Tiling.t3 R189Tiling.target] k))))
      (toR (zy (toZPt (![R189Tiling.t1 R189Tiling.target, R189Tiling.t2 R189Tiling.target,
        R189Tiling.t3 R189Tiling.target] k)))) := by
  fin_cases k <;> rfl

theorem targetTri_dist_sq (i j : Fin 3) :
    dist (targetTri.pts i) (targetTri.pts j) ^ 2
      = toR (R189Tiling.dist2
          (![R189Tiling.t1 R189Tiling.target, R189Tiling.t2 R189Tiling.target, R189Tiling.t3 R189Tiling.target] i)
          (![R189Tiling.t1 R189Tiling.target, R189Tiling.t2 R189Tiling.target, R189Tiling.t3 R189Tiling.target] j)) := by
  rw [targetTri_pts_eq i, targetTri_pts_eq j, Erdos634.CertCoord.dist_sq_mkPt, dist2_eq_zdist2]
  exact toR_zdist2 _ _

theorem targetTri_sides :
    dist (targetTri.pts 0) (targetTri.pts 1) ^ 2 = 254016
    ∧ dist (targetTri.pts 1) (targetTri.pts 2) ^ 2 = 82944
    ∧ dist (targetTri.pts 2) (targetTri.pts 0) ^ 2 = 82944 := by
  have e01 : R189Tiling.dist2 (R189Tiling.t1 R189Tiling.target) (R189Tiling.t2 R189Tiling.target)
      = ((254016:ℤ),(0:ℤ)) := by decide
  have e12 : R189Tiling.dist2 (R189Tiling.t2 R189Tiling.target) (R189Tiling.t3 R189Tiling.target)
      = ((82944:ℤ),(0:ℤ)) := by decide
  have e20 : R189Tiling.dist2 (R189Tiling.t3 R189Tiling.target) (R189Tiling.t1 R189Tiling.target)
      = ((82944:ℤ),(0:ℤ)) := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [targetTri_dist_sq 0 1]; simp; rw [e01]; simp [toR]
  · rw [targetTri_dist_sq 1 2]; simp; rw [e12]; simp [toR]
  · rw [targetTri_dist_sq 2 0]; simp; rw [e20]; simp [toR]

/-- **The model tile has sides `32, 16, 24`** (squared `1024, 256, 576`): the triangle `(2,3,4)` at the certificate's
scale `8`. -/
theorem model_sides :
    dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 1024
    ∧ dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 256
    ∧ dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 576 := by
  have e01 : R189Tiling.dist2 (vertexOf R189Tiling.tiles.headI 0) (vertexOf R189Tiling.tiles.headI 1)
      = ((1024:ℤ),(0:ℤ)) := by decide
  have e12 : R189Tiling.dist2 (vertexOf R189Tiling.tiles.headI 1) (vertexOf R189Tiling.tiles.headI 2)
      = ((256:ℤ),(0:ℤ)) := by decide
  have e20 : R189Tiling.dist2 (vertexOf R189Tiling.tiles.headI 2) (vertexOf R189Tiling.tiles.headI 0)
      = ((576:ℤ),(0:ℤ)) := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [pieceTri_dist_sq _ headI_mem_tiles 0 1, e01]; norm_num [toR]
  · rw [pieceTri_dist_sq _ headI_mem_tiles 1 2, e12]; norm_num [toR]
  · rw [pieceTri_dist_sq _ headI_mem_tiles 2 0, e20]; norm_num [toR]

/-- transport of a dissection along an equality of the number of tiles -/
theorem exists_cast {n m : ℕ} (h : n = m) (D : CongruentDissection n) :
    ∃ D' : CongruentDissection m, D'.target = D.target ∧ D'.model = D.model := by
  subst h; exact ⟨D, rfl, rfl⟩

/-- **The 189-tiling with its shape, in one statement**: there is a dissection into 189 congruent triangles whose target
has sides `504, 288, 288` (the triangle `(63, 36, 36)` at scale `8`) and whose tile has sides `32, 16, 24` (the triangle
`(4, 2, 3)` at scale `8`). -/
theorem r189_dissection_shape :
    ∃ D : CongruentDissection 189,
      dist (D.target.pts 0) (D.target.pts 1) ^ 2 = 254016 ∧ dist (D.target.pts 1) (D.target.pts 2) ^ 2 = 82944 ∧
      dist (D.target.pts 2) (D.target.pts 0) ^ 2 = 82944 ∧
      dist (D.model.pts 0) (D.model.pts 1) ^ 2 = 1024 ∧ dist (D.model.pts 1) (D.model.pts 2) ^ 2 = 256 ∧
      dist (D.model.pts 2) (D.model.pts 0) ^ 2 = 576 := by
  obtain ⟨D, hT, hM⟩ := exists_cast (by decide +kernel : R189Tiling.tiles.length = 189) dissection
  have hT' : D.target = targetTri := hT
  have hM' : D.model = pieceTri headI_mem_tiles := hM
  obtain ⟨t1, t2, t3⟩ := targetTri_sides
  obtain ⟨m1, m2, m3⟩ := model_sides
  exact ⟨D, by rw [hT']; exact t1, by rw [hT']; exact t2, by rw [hT']; exact t3,
    by rw [hM']; exact m1, by rw [hM']; exact m2, by rw [hM']; exact m3⟩

/-! ## Consequence: `189 m²` is a tile count for every `m ≥ 1`

Composing `dissection` with `Ladder.ladder` for arbitrary `m` scales the target by `m` in each
direction, multiplying the piece count by `m²`. -/

theorem targetTri_eq_mkTri :
    targetTri = Erdos634.CertCoord.mkTri
      (toR (zx (toZPt (R189Tiling.t1 R189Tiling.target)))) (toR (zy (toZPt (R189Tiling.t1 R189Tiling.target))))
      (toR (zx (toZPt (R189Tiling.t2 R189Tiling.target)))) (toR (zy (toZPt (R189Tiling.t2 R189Tiling.target))))
      (toR (zx (toZPt (R189Tiling.t3 R189Tiling.target)))) (toR (zy (toZPt (R189Tiling.t3 R189Tiling.target))))
      target_det_pos.ne' := rfl

/-- for every `m ≥ 1`, there is a `CongruentDissection` with `189 * m * m`
pieces, all congruent to the `(2,3,4)`-shaped model tile, of the `m`-times-enlarged target. This is
`Ladder.ladder` applied to `dissection`. -/
theorem exists_dissection_mul_sq (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (m * m * R189Tiling.tiles.length), E.model = pieceTri headI_mem_tiles :=
  ⟨(Erdos634.Ladder.ladder
      (A := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R189Tiling.t1 R189Tiling.target))))
        (toR (zy (toZPt (R189Tiling.t1 R189Tiling.target)))))
      (B := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R189Tiling.t2 R189Tiling.target))))
        (toR (zy (toZPt (R189Tiling.t2 R189Tiling.target)))))
      (C := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R189Tiling.t3 R189Tiling.target))))
        (toR (zy (toZPt (R189Tiling.t3 R189Tiling.target)))))
      targetTri.indep dissection targetTri_eq_mkTri m hm).choose,
    (Erdos634.Ladder.ladder
      (A := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R189Tiling.t1 R189Tiling.target))))
        (toR (zy (toZPt (R189Tiling.t1 R189Tiling.target)))))
      (B := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R189Tiling.t2 R189Tiling.target))))
        (toR (zy (toZPt (R189Tiling.t2 R189Tiling.target)))))
      (C := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R189Tiling.t3 R189Tiling.target))))
        (toR (zy (toZPt (R189Tiling.t3 R189Tiling.target)))))
      targetTri.indep dissection targetTri_eq_mkTri m hm).choose_spec.2⟩

theorem tiles_length_eq_189 : R189Tiling.tiles.length = 189 := by decide +kernel

/-- **Clause 2, restated in numeral form**: `189 * m ^ 2` is a tile count for every
`m ≥ 1`. -/
theorem exists_dissection_189_mul_sq (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (189 * m ^ 2), E.model = pieceTri headI_mem_tiles := by
  obtain ⟨E, hE⟩ := exists_dissection_mul_sq m hm
  have hnum : m * m * R189Tiling.tiles.length = 189 * m ^ 2 := by
    rw [tiles_length_eq_189]; ring
  exact hnum ▸ ⟨E, hE⟩


/-- **`Nonempty (CongruentDissection 189)`**: the triangle (36,36,63) is dissected into 189 triangles
congruent to the (2,3,4) tile (target sides 288:288:504 = 36:36:63 and model sides 16:24:32 = 2:3:4: `r189_dissection_shape`).  A 189-tiling of this target is due to J. P. Harries (2026, unrefereed); this certificate was found
independently. no sorry, no native_decide. -/
theorem r189_nonempty_congruentDissection : Nonempty (CongruentDissection 189) := by
  obtain ⟨E, _⟩ := exists_dissection_189_mul_sq 1 one_pos
  exact ⟨by simpa using E⟩

#print axioms r189_nonempty_congruentDissection

end Erdos634.R189TilingBridge
