/-
The forward tile at the ends of the corner chord, part 2 of 2.  Adapts `GLCForward` (γ = 2α) and `T30LC2Forward` (π/3)
to the base-β tile.  The architecture and proof skeleton are redone for the base-β tile; the files below are not imported,
to keep the import cone small.

Adapted from:
  Draft/GLCForward.lean:61-197    forward_tile_2a   (the forward tile at a non-vertex frontier point)
                                                    -> forward_tile_core (symmetric core), via the lemmas of
                                                       Draft/CornerParaForwardAux.lean (forward_cover, edge_on_ray,
                                                       third_presents_beta)
  Draft/T30LC2Forward.lean:88-218 C2Forward.forward_tile (same, pi/3)
  Draft/GLCG1.lean:44-205         aux_G1, tail (the forward points are in neither the corner tile nor its reflection;
                                  the two calls of `forward_tile_2a`)  -> forward_tile_P, forward_tile_Q (the forward range is the whole
                                  segment `[X, V]`, by convexity; the two tiles are handled
                                  at once through the parallelogram `T_A u T_3`, `fwd_not_mem_tiles`)
Imported and applied:
  Draft/CornerParaForwardAux.lean  (forward_cover, edge_on_ray, third_presents_beta, unique_beta_presenter, fwd_not_mem_hull)
  Draft/CornerParaHalfTurn.lean    (corner_chord_parallelogram, corner_chord_sides_strict)
  Draft/CornerParaPartner.lean     (corner_chord_partner)
  Draft/CornerParaCornerAux.lean   (CornerChord.{vertex, angP, angQ, P_frontier, Q_frontier, P_notvert})
  Draft/CornerParaCorner.lean      (CornerChord, param_le_one)
  Draft/CornerParaClamp.lean       (supp_pair)
  Draft/CornerParaBase.lean        (BaseBetaModel, angleFacts, beta_vertex_flanks)
-/
import Erdos634.Draft.CornerParaForwardAux

/-!
# The forward tile at the ends `P`, `Q` of the corner chord, part 2 of 2

Part 1 is `Draft/CornerParaForwardAux.lean`.  Adapts `GLCForward.forward_tile_2a` (γ = 2α) and
`T30LC2Forward.forward_tile` (π/3) to the base-β tile.

Setting.  `hC : CornerChord D α β γ k iA P Q` is the corner chord of the corner tile `T_A` at the base corner `A = D.target.pts k`,
`i3` its partner (`T_3` is the half-turn image of `T_A` about the midpoint of `[P, Q]`).  `P`, `Q` are strictly inside
the two target sides at `A` (`corner_chord_sides_strict`): `P = (1-p) A + p V_w`, `Q = (1-r) A + r V_z`, `0 < p, r < 1`.
At `P` the tiles `T_A`, `T_3` present `γ`, `α`; at `Q` they present `α`, `γ`.

Contents.
* `ForwardTile D β X V K`: the forward tile at the frontier point `X` toward the target vertex `V`.  `K` presents `β` at `X`
  (and is the only tile that does), has a vertex `j` at `X` and an edge `[X, pts m]`, `m ∈ {j+1, j+2}`, along the target side:
  `pts m = X + t (V - X)`, `0 < t ≤ 1` (so the edge is a subsegment of `[X, V]`); that edge is an edge of `K`; its length is `a` or
  `c` (`beta_vertex_flanks`: the two edges of a `β`-corner are `{a, c}`, the opposite side is `b`); and `K` contains the whole
  initial piece `X + ε (V - X)`, `0 ≤ ε ≤ t`, of the ray.
* `forward_tile_core`: the symmetric core.  At a non-vertex frontier point `X = (1-σ) A + σ V` of a target
  side (`A`, `V` target vertices, `0 < σ < 1`) where two tiles `i1`, `i2` present `α` and `γ` (either order) and neither contains
  the forward points `X + δ (X - A)`, `δ > 0`, there is a tile `K ≠ i1, i2` with `ForwardTile D β X V K`.
* `CornerChord.exists_psi`, `fwd_not_mem_tiles`: the affine functional of the corner tile's barycentric coordinate that puts
  the forward points outside the parallelogram `T_A ∪ T_3 = hull {A, P, R, Q}`, hence outside both tiles.
* `forward_tile_P`, `forward_tile_Q`: the two instances of the core at the ends of the corner chord;
  `corner_forward_tiles`: both at once, with the barycentric data; `corner_forward_tiles_of_chord`: from `hC` alone (the partner
  is obtained from `corner_chord_partner`).

At the N = 44 tiling `D44` (`(e, f, s) = (1, 2, 8)`, base corners `0, 1`) the hypotheses are instantiated by the modules
`Draft/CornerParaWitnessAux` (the four forward-edge pins `D44_pin_P0 / Q0 / P1 / Q1`) and `Draft/CornerParaWitness`.
-/

namespace Erdos634.CornerPara

open Erdos634.Geometry Erdos634.TilePlacement

/-! ## 1. The forward tile -/

/-- **The forward tile at the frontier point `X` toward the target vertex `V`.**  `K` presents `β` at `X` and is the only tile
that does; it has a vertex `j` at `X` and an edge `[X, pts m]` (`m = j + 1` or `m = j + 2`) running along the ray from `X`
toward `V`: `pts m = X + t (V - X)` with `0 < t ≤ 1`, so the edge is a subsegment of the side `[X, V]`; the edge is an edge of
`K`, a subsegment of `[X, V]`; its length is `a` or `c` (`sideOpp D.model 0` / `2`); `K` contains the whole initial piece of
the ray, `X + ε (V - X)`, `0 ≤ ε ≤ t`. -/
structure ForwardTile {N : ℕ} (D : CongruentDissection N) (β : ℝ) (X V : Plane) (K : Fin N) : Prop where
  /-- `K` presents `β` at `X`. -/
  ang : (D.tile K).localAngle X = β
  /-- `K` is the only tile presenting `β` at `X`. -/
  uniq : ∀ K' : Fin N, (D.tile K').localAngle X = β → K' = K
  /-- the edge of `K` at `X` along the side toward `V`. -/
  edge : ∃ (j m : Fin 3) (t : ℝ), (D.tile K).pts j = X ∧ (m = j + 1 ∨ m = j + 2) ∧ 0 < t ∧ t ≤ 1 ∧
    (D.tile K).pts m = X + t • (V - X) ∧ segment ℝ X ((D.tile K).pts m) ⊆ segment ℝ X V ∧
    (∃ e : Fin 3, (D.tile K).edge e = segment ℝ X ((D.tile K).pts m) ∧
      (((D.tile K).pts e = X ∧ (D.tile K).pts (e + 1) = (D.tile K).pts m) ∨
        ((D.tile K).pts e = (D.tile K).pts m ∧ (D.tile K).pts (e + 1) = X))) ∧
    (dist X ((D.tile K).pts m) = sideOpp D.model 0 ∨ dist X ((D.tile K).pts m) = sideOpp D.model 2) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε ≤ t → X + ε • (V - X) ∈ (D.tile K).carrier)

/-! ## 2. The symmetric core (M12) -/

/-- **M12, the symmetric core** (port of `GLCForward.forward_tile_2a:61-197` / `C2Forward.forward_tile`; plan D0 + D1 + D2).  Let
`X = (1-σ) A + σ V` be a point strictly inside the target side `[A, V]` (`A = pts k`, `V = pts w`, `0 < σ < 1`; `z` is the third
vertex, used only to take the supporting functional of the side), a frontier non-vertex point.  Suppose two tiles `i1`, `i2` present
`α` and `γ` at `X` (in either order) and neither contains a forward point `X + δ (X - A)`, `δ > 0`.  Then some tile `K ≠ i1, i2`
is the forward tile at `X` toward `V` (`ForwardTile D β X V K`), and the tiles containing `X` are exactly `i1`, `i2`, `K`.

Proof: some tile `K0` contains `X` and a forward point (`forward_cover`); `K0 ≠ i1, i2`; the figure at `X` is `{α, β, γ}`
(`gamma_boundary_figure_real`), so `K0` presents `β` (`third_presents_beta`), has `X` as a vertex, and by the cone argument
(`edge_on_ray`) one of its edges at `X` is a positive multiple of `V - X`; that multiple is `≤ 1` because the edge's far end is
in the target; the edge lengths are `{a, c}` (`beta_vertex_flanks`). -/
theorem forward_tile_core {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    {k w z : Fin 3} (hkw : k ≠ w) (hkz : k ≠ z) (hwz : w ≠ z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {X : Plane} (hX : X = (1 - σ) • D.target.pts k + σ • D.target.pts w)
    (hXfr : X ∈ frontier D.target.carrier) (hXnv : X ∉ Set.range D.target.pts) {i1 i2 : Fin N}
    (h12 : ((D.tile i1).localAngle X = α ∧ (D.tile i2).localAngle X = γ) ∨
      ((D.tile i1).localAngle X = γ ∧ (D.tile i2).localAngle X = α))
    (hn1 : ∀ δ : ℝ, 0 < δ → X + δ • (X - D.target.pts k) ∉ (D.tile i1).carrier)
    (hn2 : ∀ δ : ℝ, 0 < δ → X + δ • (X - D.target.pts k) ∉ (D.tile i2).carrier) :
    ∃ K : Fin N, K ≠ i1 ∧ K ≠ i2 ∧ ForwardTile D β X (D.target.pts w) K ∧
      ∀ K' : Fin N, X ∈ (D.tile K').carrier → K' = i1 ∨ K' = i2 ∨ K' = K := by
  classical
  obtain ⟨⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩, hβ2π⟩ := angleFacts hA
  have hβlt : β < Real.pi := by
    have := hA.hrel; have := hA.hα; have := Real.pi_pos; linarith
  have hσne : σ ≠ 0 := hσ0.ne'
  -- the target side `[A, V]` with `X` strictly inside it
  have hAmem : D.target.pts k ∈ D.target.carrier := subset_convexHull ℝ _ ⟨k, rfl⟩
  have hVmem : D.target.pts w ∈ D.target.carrier := subset_convexHull ℝ _ ⟨w, rfl⟩
  have hXmem : X ∈ D.target.carrier := by
    rw [hX]; exact D.target.convex hAmem hVmem (by linarith) hσ0.le (by ring)
  have hu : D.target.pts w - X ≠ 0 := sub_ne_zero.mpr (fun h => hXnv ⟨w, h⟩)
  -- the supporting functional of the side `[A, V]`
  obtain ⟨g, cg, hg0, hg, hgA, hgV, -⟩ := supp_pair D.target k w z hkw hkz hwz
  have hgX : g X = cg := by
    rw [hX, map_add, map_smul, map_smul, hgA, hgV]; simp only [smul_eq_mul]; ring
  have hgu : g (D.target.pts w - X) = 0 := by rw [map_sub, hgV, hgX]; ring
  -- the forward range is the whole segment `[X, V]`
  have hin : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → X + ε • (D.target.pts w - X) ∈ D.target.carrier :=
    fun ε hε hε1 => D.target.convex.add_smul_sub_mem hXmem hVmem ⟨hε.le, hε1⟩
  obtain ⟨K0, ε, hε0, hε1, hXK0, hyK0⟩ := forward_cover D.toDissection hu one_pos hin
  -- `V - X` is a positive multiple of `X - A`, so the forward point is one of the points excluded by `hn1`, `hn2`
  have hkey : ε • (D.target.pts w - X) = (ε * (1 - σ) / σ) • (X - D.target.pts k) := by
    have h1 : D.target.pts w - X = (1 - σ) • (D.target.pts w - D.target.pts k) := by rw [hX]; module
    have h2 : X - D.target.pts k = σ • (D.target.pts w - D.target.pts k) := by rw [hX]; module
    rw [h1, h2, smul_smul, smul_smul]; congr 1; field_simp
  have hδpos : 0 < ε * (1 - σ) / σ := by
    have : 0 < 1 - σ := by linarith
    positivity
  have hyδ : X + (ε * (1 - σ) / σ) • (X - D.target.pts k) ∈ (D.tile K0).carrier := by
    rw [← hkey]; exact hyK0
  have hK01 : K0 ≠ i1 := fun h => hn1 _ hδpos (h ▸ hyδ)
  have hK02 : K0 ≠ i2 := fun h => hn2 _ hδpos (h ▸ hyδ)
  -- D0: `K0` presents `β` at `X`, so `X` is a vertex of `K0`
  have hβK0 : (D.tile K0).localAngle X = β := third_presents_beta hM hA hXfr hXnv h12 hXK0 hK01 hK02
  obtain ⟨l, hl⟩ := Erdos634.Geometry.vertex_of_localAngle_corner (D.tile K0) hβK0 hβ0 hβπ hβ2π
  have hcorner : cornerAngle ((D.tile K0).pts (l + 1)) ((D.tile K0).pts l) ((D.tile K0).pts (l + 2)) = β := by
    rw [← Tri.localAngle_vertex, hl]; exact hβK0
  -- D1: one edge of `K0` at `X` is a positive multiple of `V - X`
  have hray := edge_on_ray D.toDissection hu g hg0 cg hg hgX hgu hl hA.hβ hβlt hcorner hε0 hyK0
  obtain ⟨m, hm, t, ht0, hpm⟩ : ∃ m : Fin 3, (m = l + 1 ∨ m = l + 2) ∧ ∃ t : ℝ, 0 < t ∧
      (D.tile K0).pts m - X = t • (D.target.pts w - X) := by
    rcases hray with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
    · exact ⟨l + 1, Or.inl rfl, t, ht, h⟩
    · exact ⟨l + 2, Or.inr rfl, t, ht, h⟩
  have hpm' : (D.tile K0).pts m = X + t • (D.target.pts w - X) := by rw [← hpm]; abel
  have hmK0 : (D.tile K0).pts m ∈ (D.tile K0).carrier := subset_convexHull ℝ _ ⟨m, rfl⟩
  -- the far end of the edge is in the target, so `t ≤ 1`
  have ht1 : t ≤ 1 := by
    have hmT : (D.tile K0).pts m ∈ D.target.carrier :=
      Erdos634.BaseSelection.tile_subset_target D.toDissection K0 hmK0
    have hform : (D.tile K0).pts m = (1 - (σ + t * (1 - σ))) • D.target.pts k +
        (σ + t * (1 - σ)) • D.target.pts w := by
      rw [hpm', hX]; module
    have hle := param_le_one D.target hkw hmT hform
    by_contra hlt
    push Not at hlt
    nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 hσ1)]
  -- D2: the edge length is `a` or `c`
  obtain ⟨hfl, -⟩ := beta_vertex_flanks hM hA K0 l hcorner
  have hlen : dist X ((D.tile K0).pts m) = sideOpp D.model 0 ∨
      dist X ((D.tile K0).pts m) = sideOpp D.model 2 := by
    rcases hm with rfl | rfl
    · rw [← hl]
      rcases hfl with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inr h1
      · exact Or.inl h1
    · rw [← hl, dist_comm]
      rcases hfl with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact Or.inl h2
      · exact Or.inr h2
  have hedge : ∃ ed : Fin 3, (D.tile K0).edge ed = segment ℝ X ((D.tile K0).pts m) ∧
      (((D.tile K0).pts ed = X ∧ (D.tile K0).pts (ed + 1) = (D.tile K0).pts m) ∨
        ((D.tile K0).pts ed = (D.tile K0).pts m ∧ (D.tile K0).pts (ed + 1) = X)) := by
    rcases hm with rfl | rfl
    · exact ⟨l, by rw [Tri.edge, hl], Or.inl ⟨hl, rfl⟩⟩
    · have e3 : l + 2 + 1 = l := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) l
      refine ⟨l + 2, ?_, Or.inr ⟨rfl, by rw [e3]; exact hl⟩⟩
      rw [Tri.edge, e3, hl, segment_symm]
  -- the edge is a subsegment of the side `[X, V]`
  have hmV : (D.tile K0).pts m ∈ segment ℝ X (D.target.pts w) :=
    ⟨1 - t, t, by linarith, ht0.le, by ring, by rw [hpm']; module⟩
  have hsub : segment ℝ X ((D.tile K0).pts m) ⊆ segment ℝ X (D.target.pts w) :=
    (convex_segment X (D.target.pts w)).segment_subset (left_mem_segment ℝ _ _) hmV
  refine ⟨K0, hK01, hK02, ⟨hβK0, fun K' hK' => (unique_beta_presenter hM hA hXfr hXnv h12 hβK0 hK').symm,
    l, m, t, hl, hm, ht0, ht1, hpm', hsub, hedge, hlen, ?_⟩, ?_⟩
  · intro ε' hε'0 hε't
    have hmem := (D.tile K0).convex.add_smul_sub_mem hXK0 hmK0 (t := ε' / t)
      ⟨div_nonneg hε'0 ht0.le, (div_le_one ht0).2 hε't⟩
    rw [hpm, smul_smul, div_mul_cancel₀ _ ht0.ne'] at hmem
    exact hmem
  · -- the star of `X` is `{i1, i2, K0}`: every other tile containing `X` presents `β`
    intro K' hK'
    by_cases h1 : K' = i1
    · exact Or.inl h1
    by_cases h2 : K' = i2
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (unique_beta_presenter hM hA hXfr hXnv h12
      (third_presents_beta hM hA hXfr hXnv h12 hK' h1 h2) hβK0))

/-! ## 3. The forward points are outside `T_A` and `T_3` -/

namespace CornerChord

variable {N : ℕ} {D : CongruentDissection N} {α β γ : ℝ} {k : Fin 3} {iA : Fin N} {P Q : Plane}

/-- **The barycentric functionals of the corner tile at `P` and at `Q`.**  `T_A = hull {A, P, Q}` is a nondegenerate triangle; the
barycentric coordinate of the vertex `P` (resp. `Q`) is an affine functional that is `1` at `P` (resp. `Q`) and `0` at the other
two vertices. -/
theorem exists_psi (hC : CornerChord D α β γ k iA P Q) :
    (∃ ψ : Plane →ᵃ[ℝ] ℝ, ψ (D.target.pts k) = 0 ∧ ψ P = 1 ∧ ψ Q = 0) ∧
    (∃ ψ : Plane →ᵃ[ℝ] ℝ, ψ (D.target.pts k) = 0 ∧ ψ P = 0 ∧ ψ Q = 1) := by
  obtain ⟨j, hjA, hvert⟩ := hC.vertex
  have hcd : ∀ m n : Fin 3, (D.tile iA).basis.coord m ((D.tile iA).pts n) = if m = n then 1 else 0 :=
    fun m n => AffineBasis.coord_apply (D.tile iA).basis m n
  have n10 : j + 1 ≠ j := (by decide : ∀ x : Fin 3, x + 1 ≠ x) j
  have n20 : j + 2 ≠ j := (by decide : ∀ x : Fin 3, x + 2 ≠ x) j
  have n12 : j + 1 ≠ j + 2 := (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) j
  rcases hvert with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · refine ⟨⟨(D.tile iA).basis.coord (j + 1), ?_, ?_, ?_⟩, ⟨(D.tile iA).basis.coord (j + 2), ?_, ?_, ?_⟩⟩
    · rw [hjA, hcd, if_neg n10]
    · rw [hP, hcd, if_pos rfl]
    · rw [hQ, hcd, if_neg n12]
    · rw [hjA, hcd, if_neg n20]
    · rw [hP, hcd, if_neg n12.symm]
    · rw [hQ, hcd, if_pos rfl]
  · refine ⟨⟨(D.tile iA).basis.coord (j + 2), ?_, ?_, ?_⟩, ⟨(D.tile iA).basis.coord (j + 1), ?_, ?_, ?_⟩⟩
    · rw [hjA, hcd, if_neg n20]
    · rw [hP, hcd, if_pos rfl]
    · rw [hQ, hcd, if_neg n12.symm]
    · rw [hjA, hcd, if_neg n10]
    · rw [hP, hcd, if_neg n12]
    · rw [hQ, hcd, if_pos rfl]

end CornerChord

/-- **The forward points at a vertex `X` of a parallelogram `hull {A, X, R, Y}`, `R = X + Y - A`, lie in neither of the two
sets whose union is the parallelogram** (`fwd_not_mem_hull`, applied to the union). -/
theorem fwd_not_mem_tiles (ψ : Plane →ᵃ[ℝ] ℝ) {A X Y R : Plane} (hA : ψ A = 0) (hX : ψ X = 1) (hY : ψ Y = 0)
    (hR : R = X + Y - A) {T1 T2 : Set Plane} (hU : T1 ∪ T2 = convexHull ℝ {A, X, R, Y}) {δ : ℝ}
    (hδ : 0 < δ) : X + δ • (X - A) ∉ T1 ∧ X + δ • (X - A) ∉ T2 := by
  have h := fwd_not_mem_hull ψ hA hX hY hδ
  rw [← hR, ← hU] at h
  exact ⟨fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩

/-! ## 4. The two instances of the core: the forward tiles at `P` and at `Q` -/

/-- **The forward tile at `P`** (instance of `forward_tile_core` at `X = P`, `i1 = iA` (presents `γ`), `i2 = i3` (presents `α`)).
`P = (1-p) A + p V_w` with `0 < p < 1`; `z` is the other target index at `A`.  The forward points `P + δ (P - A)` are outside the
parallelogram `T_A ∪ T_3` (CP-3's `corner_chord_parallelogram`, M11, and `fwd_not_mem_hull`). -/
theorem forward_tile_P {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q)
    {i3 : Fin N} (hne : i3 ≠ iA) {k3 : Fin 3} (h3 : (D.tile i3).edge k3 = segment ℝ P Q)
    {w z : Fin 3} (hkw : w ≠ k) (hkz : z ≠ k) (hwz : w ≠ z) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hP : P = (1 - p) • D.target.pts k + p • D.target.pts w) :
    ∃ K : Fin N, K ≠ iA ∧ K ≠ i3 ∧ ForwardTile D β P (D.target.pts w) K ∧
      ∀ K' : Fin N, P ∈ (D.tile K').carrier → K' = iA ∨ K' = i3 ∨ K' = K := by
  obtain ⟨hαP, hγQ, hQnv, R, hR, hrange, hβR, hPR, hQR, hhull⟩ :=
    corner_chord_parallelogram hM hA hshape hco he hef hC hne h3
  obtain ⟨⟨ψ, hψA, hψP, hψQ⟩, -⟩ := hC.exists_psi
  have hn := fun (δ : ℝ) (hδ : 0 < δ) => fwd_not_mem_tiles ψ hψA hψP hψQ hR hhull hδ
  exact forward_tile_core hM hA hkw.symm hkz.symm hwz hp0 hp1 hP hC.P_frontier hC.P_notvert
    (Or.inr ⟨hC.angP, hαP⟩) (fun δ hδ => (hn δ hδ).1) (fun δ hδ => (hn δ hδ).2)

/-- **The forward tile at `Q`** (instance of `forward_tile_core` at `X = Q`, `i1 = iA` (presents `α`), `i2 = i3` (presents `γ`)).
`Q = (1-r) A + r V_z` with `0 < r < 1` (`Q` is not a target vertex: `corner_chord_Q_not_vertex`).  The forward points `Q + δ (Q - A)`
are outside the parallelogram `T_A ∪ T_3 = hull {A, Q, R, P}`. -/
theorem forward_tile_Q {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q)
    {i3 : Fin N} (hne : i3 ≠ iA) {k3 : Fin 3} (h3 : (D.tile i3).edge k3 = segment ℝ P Q)
    {w z : Fin 3} (hkw : w ≠ k) (hkz : z ≠ k) (hwz : w ≠ z) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hQ : Q = (1 - r) • D.target.pts k + r • D.target.pts z) :
    ∃ K : Fin N, K ≠ iA ∧ K ≠ i3 ∧ ForwardTile D β Q (D.target.pts z) K ∧
      ∀ K' : Fin N, Q ∈ (D.tile K').carrier → K' = iA ∨ K' = i3 ∨ K' = K := by
  obtain ⟨hαP, hγQ, hQnv, R, hR, hrange, hβR, hPR, hQR, hhull⟩ :=
    corner_chord_parallelogram hM hA hshape hco he hef hC hne h3
  obtain ⟨-, ⟨ψ, hψA, hψP, hψQ⟩⟩ := hC.exists_psi
  have hR' : R = Q + P - D.target.pts k := by rw [hR]; abel
  have hset : ({D.target.pts k, P, R, Q} : Set Plane) = {D.target.pts k, Q, R, P} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hhull' : (D.tile iA).carrier ∪ (D.tile i3).carrier = convexHull ℝ {D.target.pts k, Q, R, P} := by
    rw [hhull, hset]
  have hn := fun (δ : ℝ) (hδ : 0 < δ) => fwd_not_mem_tiles ψ hψA hψQ hψP hR' hhull' hδ
  exact forward_tile_core hM hA hkz.symm hkw.symm hwz.symm hr0 hr1 hQ hC.Q_frontier hQnv
    (Or.inl ⟨hC.angQ, hγQ⟩) (fun δ hδ => (hn δ hδ).1) (fun δ hδ => (hn δ hδ).2)

/-! ## 5. The export for the chain bridge (CP-5) -/

/-- **Both forward tiles of the corner chord** (plan D0-D2, M12; the statement CP-5's chain bridge consumes).  Let `hC` be the
corner chord and `T_3 = D.tile i3`, `i3 ≠ iA`, a tile whose edge `k3` is the chord (CP-3: unique).  There are target indices
`w, z` (the two sides at `A`) and `p, r ∈ (0, 1)` with `P = (1-p) A + p V_w`, `Q = (1-r) A + r V_z`, and tiles `K_P`, `K_Q` other than
`T_A`, `T_3` with `ForwardTile D β P V_w K_P` and `ForwardTile D β Q V_z K_Q`: each presents `β` at its end of the chord, has an edge
along the side starting there, forward from the corner (so `K_P`'s edge lies in `[P, V_w]`, `K_Q`'s in `[Q, V_z]`), of length
`a` or `c`. -/
theorem corner_forward_tiles {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q)
    {i3 : Fin N} (hne : i3 ≠ iA) {k3 : Fin 3} (h3 : (D.tile i3).edge k3 = segment ℝ P Q) :
    ∃ w z : Fin 3, w ≠ k ∧ z ≠ k ∧ w ≠ z ∧
      (∃ p : ℝ, 0 < p ∧ p < 1 ∧ P = (1 - p) • D.target.pts k + p • D.target.pts w) ∧
      (∃ r : ℝ, 0 < r ∧ r < 1 ∧ Q = (1 - r) • D.target.pts k + r • D.target.pts z) ∧
      (∃ K : Fin N, K ≠ iA ∧ K ≠ i3 ∧ ForwardTile D β P (D.target.pts w) K ∧
        ∀ K' : Fin N, P ∈ (D.tile K').carrier → K' = iA ∨ K' = i3 ∨ K' = K) ∧
      (∃ K : Fin N, K ≠ iA ∧ K ≠ i3 ∧ ForwardTile D β Q (D.target.pts z) K ∧
        ∀ K' : Fin N, Q ∈ (D.tile K').carrier → K' = iA ∨ K' = i3 ∨ K' = K) := by
  obtain ⟨w, z, hkw, hkz, hwz, p, r, hp0, hp1, hr0, hr1, hP, hQ⟩ :=
    corner_chord_sides_strict hM hA hshape hco he hef hC
  exact ⟨w, z, hkw, hkz, hwz, ⟨p, hp0, hp1, hP⟩, ⟨r, hr0, hr1, hQ⟩,
    forward_tile_P hM hA hshape hco he hef hC hne h3 hkw hkz hwz hp0 hp1 hP,
    forward_tile_Q hM hA hshape hco he hef hC hne h3 hkw hkz hwz hr0 hr1 hQ⟩

/-- **The same, from the corner chord alone**: the partner `i3` (CP-3's `corner_chord_partner`) is produced inside. -/
theorem corner_forward_tiles_of_chord {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {s α β γ : ℝ}
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    {k : Fin 3} {iA : Fin N} {P Q : Plane} (hC : CornerChord D α β γ k iA P Q) :
    ∃ i3 : Fin N, i3 ≠ iA ∧ (∃ k3 : Fin 3, (D.tile i3).edge k3 = segment ℝ P Q) ∧
      ∃ w z : Fin 3, w ≠ k ∧ z ≠ k ∧ w ≠ z ∧
        (∃ p : ℝ, 0 < p ∧ p < 1 ∧ P = (1 - p) • D.target.pts k + p • D.target.pts w) ∧
        (∃ r : ℝ, 0 < r ∧ r < 1 ∧ Q = (1 - r) • D.target.pts k + r • D.target.pts z) ∧
        (∃ K : Fin N, K ≠ iA ∧ K ≠ i3 ∧ ForwardTile D β P (D.target.pts w) K ∧
          ∀ K' : Fin N, P ∈ (D.tile K').carrier → K' = iA ∨ K' = i3 ∨ K' = K) ∧
        (∃ K : Fin N, K ≠ iA ∧ K ≠ i3 ∧ ForwardTile D β Q (D.target.pts z) K ∧
          ∀ K' : Fin N, Q ∈ (D.tile K').carrier → K' = iA ∨ K' = i3 ∨ K' = K) := by
  obtain ⟨i3, ⟨hne, k3, h3⟩, -⟩ := corner_chord_partner hM hco he hef hC
  exact ⟨i3, hne, ⟨k3, h3⟩, corner_forward_tiles hM hA hshape hco he hef hC hne h3⟩

end Erdos634.CornerPara

#print axioms Erdos634.CornerPara.ForwardTile
#print axioms Erdos634.CornerPara.forward_tile_core
#print axioms Erdos634.CornerPara.CornerChord.exists_psi
#print axioms Erdos634.CornerPara.fwd_not_mem_tiles
#print axioms Erdos634.CornerPara.forward_tile_P
#print axioms Erdos634.CornerPara.forward_tile_Q
#print axioms Erdos634.CornerPara.corner_forward_tiles
#print axioms Erdos634.CornerPara.corner_forward_tiles_of_chord
