/-
Wrapper for the corner step lemma, a corollary of the master theorem `CornerPara.corner_parallelogram`.
Applies (does not copy): Draft/CornerParaMaster.lean (`corner_chord_b_edge`), Draft/CornerParaChain.lean
(`corner_first_two_edges_sides`), Draft/CornerParaPartner.lean (`corner_chord_partner`), Draft/CornerParaHalfTurn.lean
(`corner_chord_parallelogram`), Draft/CornerParaCorner.lean (`corner_chord_data`), CornerAnglePermTarget.lean.
-/
import Erdos634.Draft.CornerParaMaster

/-!
# The corner step (unconditional at every member), as a corollary of the corner-parallelogram statement

The statement:

> Let a base corner tile lay `a` on the base. It presents `γ` at the far end of that `a`-edge, where the junction is straight, so the
> remainder is `α+β` with the unique fill `{α,β}`. The corner tile's `b`-edge joins a base vertex to a side vertex, so both of its ends
> lie on the boundary and the tile across it lays a whole `b`; that tile presents `α` at the junction, since a straight junction carries
> at most one `γ`. Hence the `α`-tile is adjacent to the corner tile and the `β`-tile is adjacent to the base, and the second base edge,
> lying among the `β`-tile's flanks, is an `a` or a `c`.

Reading, clause by clause (the Lean names are the conjuncts of `corner_step_base`, whose conclusion lists them in this order).

* "Let a base corner tile lay `a` on the base" — hypotheses: `k` is a base corner (angle `β`; `k ∈ {apex + 1, apex + 2}`), `wl` is the
  base side from `A = D.target.pts k` to the other base corner `V_v` (`v ≠ k`, `v ≠ apex`), `E` its chain of tile edges (the tile edges
  lying on the base, in order, the first starting at `A`; `GLI.IsChain`), and the first edge has length `a`:
  `len (E 0) = sideOpp D.model 0` (`hlay`).  Conclusion `(E 0).1 = iA`: the tile laying it is THE corner tile `T_A` (unique tile at `A`).
* "It presents `γ` at the far end of that `a`-edge, where the junction is straight":  `edgeEast (E 0) = P = edgeWest (E 1)` (the far end
  of the `a`-edge is the chord end `P`; the junction of the chain), `P` lies strictly inside the base side (`P ∈ openSegment ℝ wl.a wl.b`),
  and `(D.tile iA).localAngle P = γ`.
* "so the remainder is `α+β` with the unique fill `{α,β}`" — `π − γ = α + β` and every `p α + q β + r γ = α + β` (`p q r ∈ ℕ`) has
  `(p, q, r) = (1, 1, 0)` (`fill_alpha_beta_unique`, pure arithmetic from `MarchSlots.AngleData`); the geometric content, the
  tiles at `P` are exactly `T_A` (`γ`), the tile across the chord (`α`) and the owner of `E 1` (`β`), is the conjunct
  `∀ K, P ∈ carrier K → K = iA ∨ K = i3 ∨ K = (E 1).1`.
* "The corner tile's `b`-edge joins a base vertex to a side vertex, so both of its ends lie on the boundary": `T_A` has an edge of length
  `b` equal to the segment `[P, Q]`; `P` is strictly inside the base side, `Q = (1 − r) A + r V_z` with `0 < r < 1` on the OTHER side at
  `A` (`z ≠ k`, `z ≠ v`; in the isosceles setting `z` is the apex), and both are in `frontier D.target.carrier`.
* "the tile across it lays a whole `b`": `i3 ≠ iA` is the unique tile other than `T_A` with an edge equal, as a set, to `[P, Q]`
  (the tiling need not be edge-to-edge).
* "that tile presents `α` at the junction": `(D.tile i3).localAngle P = α`.
* "the `α`-tile is adjacent to the corner tile": it shares the whole edge `[P, Q]` with `T_A` (the conjunct above); "the `β`-tile is
  adjacent to the base": it is the owner `(E 1).1` of the second base edge, it differs from `T_A` and from `i3`, and presents `β` at `P`.
* "the second base edge ... is an `a` or a `c`": the base has at least two tile edges (`2 ≤ n`, so `E 1` is the second one) and
  `len (E 1) ∈ {sideOpp D.model 0, sideOpp D.model 2}`.

Generality (every deviation from the paper's setting).  As in `corner_parallelogram`: any scale `s > 0` and any coprime `1 ≤ e < f`
(`m` is not needed), `N` free; extra hypotheses the angle bundle `MarchSlots.AngleData α β γ`, `BaseBetaModel`, `BaseBetaShape`.
`AngleData` holds at every member for the canonical angles (`Draft.ApexWitness44.angleData_member`, Niven for `α ∉ ℚπ`); it is a hypothesis
here only to keep this module's import cone light, and the identification of the model's corner angles with those canonical values is
part of `BaseBetaModel`, witnessed at `(1, 2)` by `D44_angleData`/`D44_hα`/`D44_hβ`/`D44_hγ` (not derived from the side lengths in Lean).
`corner_step` is the engine and drops the isosceles reading: `wl` is ANY side at `A` along which the first tile edge has length `a`
(by `corner_parallelogram` this is the side through the `γ`-corner `P`; the side along which the first edge has length `c` is the other
one).  `corner_step_base` is the paper's setting: apex index `a`, base corners `a + 1`, `a + 2`, the base is `[A, V_v]` with `v` the
other base corner.

Not claimed: that a corner tile laying `a` on the base occurs at every member or in every tiling (it is a hypothesis; at the real
`N = 44` tiling it holds at both base corners, `Draft/CornerStepWitness.lean`), and nothing is claimed for the orientation in which the
corner tile lays `c` on the base (there the same proof gives the `Q`-side statement of `corner_first_two_edges_sides`).
-/

namespace Erdos634.CornerPara

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

set_option synthInstance.maxSize 1024 in
/-- Three distinct indices `k, w, z` of `Fin 3` exhaust it: a `v` different from `k` and `w` is `z`. -/
theorem fin3_third (k v w z : Fin 3) (hv : v ≠ k) (hw : w ≠ k) (hz : z ≠ k) (hwz : w ≠ z) (hvw : v ≠ w) :
    v = z := by
  revert k v w z; decide

set_option synthInstance.maxSize 1024 in
/-- The apex index `a` is the only index different from the base corners `a + 1`, `a + 2`. -/
theorem fin3_apex (a k v z : Fin 3) (hk : k = a + 1 ∨ k = a + 2) (hvk : v ≠ k) (hva : v ≠ a)
    (hzk : z ≠ k) (hzv : z ≠ v) : z = a := by
  revert a k v z; decide

/-- **The unique fill** (`lem:cornerstep`, arithmetic clause): after `γ` a straight angle `π` leaves `α + β`, and `α + β` is built from
the three tile angles `α, β, γ` in exactly one way, one `α` and one `β`. -/
theorem fill_alpha_beta_unique {α β γ : ℝ} (hA : MarchSlots.AngleData α β γ) :
    Real.pi - γ = α + β ∧
    ∀ p q r : ℕ, (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = α + β → p = 1 ∧ q = 1 ∧ r = 0 := by
  refine ⟨by linarith [hA.hrel, hA.hγdef], fun p q r h => ?_⟩
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((1 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * β := by
    rw [← hA.hγdef]; push_cast; linarith
  obtain ⟨h1, h2⟩ := vertex_multiplicities hA.hrel hA.hirr p q r 1 1 h'
  omega

/-- **`lem:cornerstep`, engine.**  A base corner tile lays `a` on the side `[A, V_v]` (the first tile edge on that side has length `a`).
Then, with `P` the far end of that edge and `Q` the other end of the corner tile's `b`-chord: ... (see the module docstring). -/
theorem corner_step (D : CongruentDissection N) {e f : ℕ} {s α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ)
    (hshape : BaseBetaShape D.target α β) (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β)
    {v : Fin 3} (hv : v ≠ k) (wl : GLI.Wall D.toDissection) (hwa : wl.a = D.target.pts k)
    (hwb : wl.b = D.target.pts v) (E : ℕ → Fin N × Fin 3) (n : ℕ) (hE : GLI.IsChain wl E n)
    (hlay : EdgeWordConversion.len D (E 0) = sideOpp D.model 0) :
    ∃ (iA i3 : Fin N) (P Q : Plane),
      -- the base has a second tile edge `E 1`; the tile that lays the `a`-edge `E 0` is the corner tile `T_A`
      2 ≤ n ∧ (E 0).1 = iA ∧ CornerChord D α β γ k iA P Q ∧ (D.tile iA).localAngle (D.target.pts k) = β ∧
      -- `T_A` presents `γ` at the far end `P` of the `a`-edge, where the junction is straight
      Placement.edgeEast D.toDissection wl.dir (E 0) = P ∧
      Placement.edgeWest D.toDissection wl.dir (E 1) = P ∧
      P ∈ openSegment ℝ wl.a wl.b ∧ (D.tile iA).localAngle P = γ ∧
      -- the remainder is `α + β` with the unique fill `{α, β}`
      (Real.pi - γ = α + β ∧
        ∀ p q r : ℕ, (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = α + β → p = 1 ∧ q = 1 ∧ r = 0) ∧
      -- the `b`-edge of `T_A` is the chord `[P, Q]`: from the vertex `P` on this side to the vertex `Q` on the other side
      -- at `A`; both ends lie on the boundary
      (∃ j : Fin 3, (D.tile iA).edge j = segment ℝ P Q ∧
        dist ((D.tile iA).pts j) ((D.tile iA).pts (j + 1)) = sideOpp D.model 1) ∧
      P ∈ frontier D.target.carrier ∧ Q ∈ frontier D.target.carrier ∧
      (∃ z : Fin 3, z ≠ k ∧ z ≠ v ∧ ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        Q = (1 - r) • D.target.pts k + r • D.target.pts z) ∧
      -- the tile across it lays a whole `b`: `i3` is the unique tile other than `T_A` with an edge equal to `[P, Q]` ...
      i3 ≠ iA ∧ (∃ k3 : Fin 3, (D.tile i3).edge k3 = segment ℝ P Q) ∧
      (∀ i' : Fin N, i' ≠ iA → (∃ k' : Fin 3, (D.tile i').edge k' = segment ℝ P Q) → i' = i3) ∧
      -- ... and presents `α` at the junction
      (D.tile i3).localAngle P = α ∧
      -- the `β`-tile is the owner of the second base edge, adjacent to the base, and exactly these three tiles meet at `P`
      (E 1).1 ≠ iA ∧ (E 1).1 ≠ i3 ∧ (D.tile (E 1).1).localAngle P = β ∧
      (∀ K : Fin N, P ∈ (D.tile K).carrier → K = iA ∨ K = i3 ∨ K = (E 1).1) ∧
      -- the second base edge is an `a` or a `c`
      (EdgeWordConversion.len D (E 1) = sideOpp D.model 0 ∨
        EdgeWordConversion.len D (E 1) = sideOpp D.model 2) := by
  obtain ⟨iA, P, Q, hC⟩ := corner_chord_data D hco he hef hM hA hshape k hcorner
  obtain ⟨i3, ⟨hne, k3, h3⟩, huniq⟩ := corner_chord_partner hM hco he hef hC
  obtain ⟨w, z, hkw, hkz, hwz, ⟨p, hp0, hp1, hP⟩, ⟨r, hr0, hr1, hQ⟩, hPw, hQz⟩ :=
    corner_first_two_edges_sides hM hA hshape hco he hef hC hne h3
  -- the side along which the first edge has length `a` is the side through `P`
  have hvw : v = w := by
    by_contra hvw
    have hvz : v = z := fin3_third k v w z hv hkw hkz hwz hvw
    obtain ⟨-, -, hlen0, -⟩ := hQz wl hwa (hvz ▸ hwb) E n hE
    exact hM.scalene hco he hef 0 2 (by decide) (hlay.symm.trans hlen0)
  subst hvw
  obtain ⟨hn, hE0, -, hE1A, hE13, hwest, hang, hlen1, hall, -⟩ := hPw wl hwa hwb E n hE
  obtain ⟨hαP, -, -, -⟩ := corner_chord_parallelogram hM hA hshape hco he hef hC hne h3
  have hjunc : Placement.edgeEast D.toDissection wl.dir (E 0) = P :=
    (hE.junc 0 (by omega)).trans hwest
  refine ⟨iA, i3, P, Q, hn, hE0, hC, hC.angA, hjunc, hwest, ?_, hC.angP, fill_alpha_beta_unique hA,
    corner_chord_b_edge hC, hC.P_frontier, hC.Q_frontier, ⟨z, hkz, hwz.symm, r, hr0, hr1, hQ⟩, hne,
    ⟨k3, h3⟩, fun i' hne' ⟨k', hk'⟩ => huniq i' ⟨hne', k', hk'⟩, hαP, hE1A, hE13, hang, hall, hlen1⟩
  rw [hwa, hwb]
  exact ⟨1 - p, p, by linarith, hp0, by ring, hP.symm⟩

/-- **`lem:cornerstep` in the paper's setting.**  The target is isosceles with base angles `β` at `a + 1`, `a + 2` and apex `a` (angle `3α`);
`k` is a base corner and the base is `[A, V_v]` for the OTHER base corner `V_v` (`v ≠ k`, `v ≠ a`).  If the corner tile lays `a` on the
base, then the conclusions of `corner_step` hold, with the side vertex `Q` on the leg `[A, V_a]` towards the apex. -/
theorem corner_step_base (D : CongruentDissection N) {e f : ℕ} {s α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : BaseBetaModel D e f s α β γ) (hA : MarchSlots.AngleData α β γ) (a : Fin 3)
    (h₁ : cornerAngle (D.target.pts (a + 1 + 1)) (D.target.pts (a + 1)) (D.target.pts (a + 1 + 2)) = β)
    (h₂ : cornerAngle (D.target.pts (a + 2 + 1)) (D.target.pts (a + 2)) (D.target.pts (a + 2 + 2)) = β)
    (k : Fin 3) (hk : k = a + 1 ∨ k = a + 2) {v : Fin 3} (hvk : v ≠ k) (hva : v ≠ a)
    (wl : GLI.Wall D.toDissection) (hwa : wl.a = D.target.pts k) (hwb : wl.b = D.target.pts v)
    (E : ℕ → Fin N × Fin 3) (n : ℕ) (hE : GLI.IsChain wl E n)
    (hlay : EdgeWordConversion.len D (E 0) = sideOpp D.model 0) :
    cornerAngle (D.target.pts (a + 1)) (D.target.pts a) (D.target.pts (a + 2)) = 3 * α ∧
    ∃ (iA i3 : Fin N) (P Q : Plane),
      2 ≤ n ∧ (E 0).1 = iA ∧ CornerChord D α β γ k iA P Q ∧ (D.tile iA).localAngle (D.target.pts k) = β ∧
      Placement.edgeEast D.toDissection wl.dir (E 0) = P ∧
      Placement.edgeWest D.toDissection wl.dir (E 1) = P ∧
      P ∈ openSegment ℝ wl.a wl.b ∧ (D.tile iA).localAngle P = γ ∧
      (Real.pi - γ = α + β ∧
        ∀ p q r : ℕ, (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = α + β → p = 1 ∧ q = 1 ∧ r = 0) ∧
      (∃ j : Fin 3, (D.tile iA).edge j = segment ℝ P Q ∧
        dist ((D.tile iA).pts j) ((D.tile iA).pts (j + 1)) = sideOpp D.model 1) ∧
      P ∈ frontier D.target.carrier ∧ Q ∈ frontier D.target.carrier ∧
      (∃ r : ℝ, 0 < r ∧ r < 1 ∧ Q = (1 - r) • D.target.pts k + r • D.target.pts a) ∧
      i3 ≠ iA ∧ (∃ k3 : Fin 3, (D.tile i3).edge k3 = segment ℝ P Q) ∧
      (∀ i' : Fin N, i' ≠ iA → (∃ k' : Fin 3, (D.tile i').edge k' = segment ℝ P Q) → i' = i3) ∧
      (D.tile i3).localAngle P = α ∧
      (E 1).1 ≠ iA ∧ (E 1).1 ≠ i3 ∧ (D.tile (E 1).1).localAngle P = β ∧
      (∀ K : Fin N, P ∈ (D.tile K).carrier → K = iA ∨ K = i3 ∨ K = (E 1).1) ∧
      (EdgeWordConversion.len D (E 1) = sideOpp D.model 0 ∨
        EdgeWordConversion.len D (E 1) = sideOpp D.model 2) := by
  have hshape : BaseBetaShape D.target α β := htarget_of_isosceles D.target hA.hrel a h₁ h₂
  refine ⟨target_apex_angle D.target hA.hrel a h₁ h₂, ?_⟩
  have hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β := by
    rcases hk with rfl | rfl
    · exact h₁
    · exact h₂
  obtain ⟨iA, i3, P, Q, hn, h0, hC, hAng, hjE, hjW, hP, hγ, hfill, hb, hPf, hQf, ⟨z, hzk, hzv, hQz⟩, hrest⟩ :=
    corner_step D hco he hef hM hA hshape k hcorner hvk wl hwa hwb E n hE hlay
  have hza : z = a := fin3_apex a k v z hk hvk hva hzk hzv
  subst hza
  exact ⟨iA, i3, P, Q, hn, h0, hC, hAng, hjE, hjW, hP, hγ, hfill, hb, hPf, hQf, hQz, hrest⟩

end Erdos634.CornerPara

#print axioms Erdos634.CornerPara.fill_alpha_beta_unique
#print axioms Erdos634.CornerPara.corner_step
#print axioms Erdos634.CornerPara.corner_step_base
