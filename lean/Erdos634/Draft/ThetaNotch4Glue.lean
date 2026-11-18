-- Draft/ThetaNotch4Glue.lean -- TASK B (geometry): the hub gluing  alpha_g = (g b) tau  u  theta_{g f}.  INTERNAL BUILD ONLY, UNAUDITED (reading audit of lines 40-201, 2026-11-14, SOUND WITH GAPS, internal audit).
-- No sorry, no native_decide.
/-
**Hub (iv) of internal notes:  `alpha_g(e,f) = (g b) tau  u  theta_{g f}(e,f)`.**
Tile `tau = (e f, b, f^2)`, `b = f^2 - e^2`, `Q = 2 f^2 - e^2 = b + f^2`.  `theta_{g f}` is the isosceles triangle with legs `g f b f = K f^2`
and base `g f b e = K e f`, `K = g b`.  Put its apex `O` and base vertices `Pp, Bb`.  Extend the leg `O Bb` beyond `Bb` to `X` with
`|Bb X| = K b` (so `X = Bb + mu (Bb - O)`, `mu = b / f^2`).  Then `|O X| = K Q`, and (law of cosines / Stewart) `|X Pp| = K f^2`, so
the triangle `(Pp, Bb, X)` has sides `(K e f, K b, K f^2) = K (e f, b, f^2)`: it is `K tau`, cut into `K^2` tiles by the ladder
(`tileKgen`, the general-tile form of `CVCCevianCut.tileK`).  The union `O Pp X` is isosceles with base `O X = K Q` and legs `K f^2`: the
target of `alpha_g` (`g b = K`).  Placement is by explicit vectors; the general union lemma is the corpus's `unionCongruentDissection`, the fan cut
is `CVCCevianCut.fan_cover` / `fan_disjoint` (as in `ThetaComposeGlue.glue_cevian`, whose shape this follows).
Main results: `glue_notch` (reals, any `K : N`), `AlphaTiled` (target data identical to `ThetaCompose.alpha_exists`),
`alphaTiled_of_thetaTiled : ThetaTiled e f b (g f) -> AlphaTiled e f b g`; count `(g b)^2 + b (g f)^2 = b (b + f^2) g^2`.
PRIOR ART (credit order: by date): the gluing of a theta tiling and a scaled tile onto an isosceles triangle with base angles alpha is
M. Beeson, arXiv:1206.2229 v5, Corollary 8 and Fig. 25 (isosceles ABC with base angles alpha cut into the blue triangle DBC, base angles alpha+beta,
and ABD similar to the tile; count `L^2 + c^2 N1`; for the tile (2,3,4) see also Fig. 23, N = 84); his Cor. 5 and Fig. 22 are the same idea for the
triangle (2 alpha, alpha, 2 beta).  It is also D. Paliy's alpha-isosceles construction (count `b Q K^2`, `docs/universal-rational-scales.md`, 29 Sep 2026).
Here the integral case `f | t` is used, which avoids the blow-up factor of Beeson's Cor. 8.  Only the values resting on the seeds of
`ThetaNotch4Rho` (2576, 4025, 5796, 7008) are new.
CREDIT: the formal statement and proof here: this project (internal notes); the gluing: M. Beeson (Cor. 8, Fig. 25), D. Paliy; theta family and `alpha`: D. Paliy, M. Beeson and I. Rosu; Herdt-style cevian cut; Laczkovich.
INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.CVCCevianCut
import Erdos634.Draft.ThetaUnitStep
import Erdos634.Draft.ThetaComposeGlue

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.CVCCevianCut
open Erdos634.Draft.FDBBaseBetaE1 (HasSides congruent_of_hasSides)
open Erdos634.Draft.ThetaComposeGlue (congruent_of_hasSides_both)
open Erdos634.Draft.FDCCevianAtom (hasSides_scaleN)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled)

/-- `CVCCevianCut.tileK` for an arbitrary model tile `t` with sides `(a,b,c)`. -/
theorem tileKgen (t T : Erdos634.Geometry.Tri) (K : ℕ) (hK : 0 < K) (a b c : ℝ) (ht : HasSides t a b c)
    (hT : HasSides T ((K : ℝ) * a) ((K : ℝ) * b) ((K : ℝ) * c)) :
    ∃ E : CongruentDissection (K * K * 1), E.target.carrier = T.carrier ∧ E.model = t := by
  obtain ⟨D, hDt, hDm⟩ := Erdos634.Realizable.cut_scale (T := t) (t := t) (N := 1)
    ⟨selfDissection t, rfl, rfl⟩ K hK
  have hS := hasSides_scaleN ht K hK
  obtain ⟨τ, h1, h2, h3⟩ := hT
  have hc : (Erdos634.Realizable.scaleN K hK t).Congruent T :=
    Tri.Congruent.trans (congruent_of_hasSides hS (U := T.relabel τ) h1 h2 h3)
      (Tri.congruent_relabel T τ).symm
  obtain ⟨E, hEc, hEm⟩ := transport D T (by rw [hDt]; exact hc)
  exact ⟨E, hEc, hEm.trans hDm⟩

theorem hsc {T : Erdos634.Geometry.Tri} {a b c a' b' c' : ℝ} (h : HasSides T a b c) (ha : a = a') (hb : b = b')
    (hc : c = c') : HasSides T a' b' c' := by
  subst ha; subst hb; subst hc; exact h

/-- **THE HUB GLUING, in reals** (prior art: Beeson, arXiv:1206.2229 v5, Cor. 8 / Fig. 25; Paliy).  `theta_{gf}` (legs `K f^2`, base `K e f`, `K = g b`) glued to the scaled tile `K tau` along its base
is the isosceles triangle with base `K (2 f^2 - e^2)` and legs `K f^2`; `K^2 + N2` tiles. -/
theorem glue_notch (e f : ℝ) (K : ℕ) (hK : 0 < K) (he : 0 < e) (hef : e < f)
    {N2 : ℕ} (D2 : CongruentDissection N2)
    (h2t : HasSides D2.target ((K : ℝ) * f ^ 2) ((K : ℝ) * f ^ 2) ((K : ℝ) * (e * f)))
    (h2m : HasSides D2.model (e * f) (f ^ 2 - e ^ 2) (f ^ 2)) :
    ∃ D : CongruentDissection (K * K + N2),
      HasSides D.target ((K : ℝ) * (2 * f ^ 2 - e ^ 2)) ((K : ℝ) * f ^ 2) ((K : ℝ) * f ^ 2) ∧
      D.model = D2.model := by
  have hf : 0 < f := by linarith
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hQ : 0 < 2 * f ^ 2 - e ^ 2 := by nlinarith
  have hQne : 2 * f ^ 2 - e ^ 2 ≠ 0 := hQ.ne'
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨τ, h12, h20, h01⟩ := h2t
  have hnd : cr (D2.target.pts (τ 0)) (D2.target.pts (τ 1)) (D2.target.pts (τ 2)) ≠ 0 :=
    cr_pts_ne_zero (D2.target.relabel τ)
  obtain ⟨Pp, hPp⟩ : ∃ Pp, Pp = D2.target.pts (τ 0) := ⟨_, rfl⟩
  obtain ⟨Bb, hBb⟩ : ∃ Bb, Bb = D2.target.pts (τ 1) := ⟨_, rfl⟩
  obtain ⟨O, hO⟩ : ∃ O, O = D2.target.pts (τ 2) := ⟨_, rfl⟩
  rw [← hPp, ← hBb, ← hO] at hnd
  rw [← hBb, ← hO] at h12
  rw [← hO, ← hPp] at h20
  rw [← hPp, ← hBb] at h01
  have sBO := sqd_of_dist _ _ _ h12
  have sOP := sqd_of_dist _ _ _ h20
  have sPB := sqd_of_dist _ _ _ h01
  -- the parameters
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = (f ^ 2 - e ^ 2) / f ^ 2 := ⟨_, rfl⟩
  have hf2 : f ^ 2 ≠ 0 := by positivity
  have hμf : μ * f ^ 2 = f ^ 2 - e ^ 2 := by rw [hμ]; exact div_mul_cancel₀ _ hf2
  have hμpos : 0 < μ := by rw [hμ]; positivity
  have hq : (1 + μ) * f ^ 2 = 2 * f ^ 2 - e ^ 2 := by linarith
  have h1μ : 0 < 1 + μ := by linarith
  obtain ⟨s, hs0⟩ : ∃ s : ℝ, s = f ^ 2 / (2 * f ^ 2 - e ^ 2) := ⟨_, rfl⟩
  have hs : s * (1 + μ) = 1 := by
    have h1 : 1 + μ = (2 * f ^ 2 - e ^ 2) / f ^ 2 := by
      rw [hμ]; field_simp <;> ring
    rw [hs0, h1, div_mul_div_comm, mul_comm (2 * f ^ 2 - e ^ 2) (f ^ 2)]
    exact div_self (mul_ne_zero hf2 hQne)
  have hspos : 0 < s := by rw [hs0]; positivity
  have hs1 : s < 1 := by rw [hs0, div_lt_one hQ]; nlinarith
  obtain ⟨X, hX⟩ : ∃ X : Plane, X = Bb + μ • (Bb - O) := ⟨_, rfl⟩
  have hX0 : X 0 = Bb 0 + μ * (Bb 0 - O 0) := by rw [hX]; simp
  have hX1 : X 1 = Bb 1 + μ * (Bb 1 - O 1) := by rw [hX]; simp
  -- nondegeneracy
  have hcrΔ : cr Pp O X ≠ 0 := by
    have : cr Pp O X = -(1 + μ) * cr Pp Bb O := by unfold cr; rw [hX0, hX1]; ring
    rw [this]; exact mul_ne_zero (neg_ne_zero.mpr h1μ.ne') hnd
  have hcrT : cr X Pp Bb ≠ 0 := by
    have : cr X Pp Bb = -μ * cr Pp Bb O := by unfold cr; rw [hX0, hX1]; ring
    rw [this]; exact mul_ne_zero (neg_ne_zero.mpr hμpos.ne') hnd
  -- distances
  have dOX : dist O X = (K : ℝ) * (2 * f ^ 2 - e ^ 2) := by
    refine dist_of_sqd _ _ _ (mul_pos hKR hQ).le ?_
    have key : (O 0 - X 0) ^ 2 + (O 1 - X 1) ^ 2 = (1 + μ) ^ 2 * ((Bb 0 - O 0) ^ 2 + (Bb 1 - O 1) ^ 2) := by
      rw [hX0, hX1]; ring
    rw [key, sBO]
    calc (1 + μ) ^ 2 * ((K : ℝ) * f ^ 2) ^ 2 = (K : ℝ) ^ 2 * ((1 + μ) * f ^ 2) ^ 2 := by ring
      _ = _ := by rw [hq]; ring
  have dXP : dist X Pp = (K : ℝ) * f ^ 2 := by
    refine dist_of_sqd _ _ _ (mul_pos hKR (by positivity)).le ?_
    have key : (X 0 - Pp 0) ^ 2 + (X 1 - Pp 1) ^ 2 =
        (1 + μ) * ((Pp 0 - Bb 0) ^ 2 + (Pp 1 - Bb 1) ^ 2) + (μ ^ 2 + μ) * ((Bb 0 - O 0) ^ 2 + (Bb 1 - O 1) ^ 2)
          - μ * ((O 0 - Pp 0) ^ 2 + (O 1 - Pp 1) ^ 2) := by
      rw [hX0, hX1]; ring
    rw [key, sPB, sBO, sOP]
    calc (1 + μ) * ((K : ℝ) * (e * f)) ^ 2 + (μ ^ 2 + μ) * ((K : ℝ) * f ^ 2) ^ 2 - μ * ((K : ℝ) * f ^ 2) ^ 2
        = (K : ℝ) ^ 2 * (e ^ 2 * ((1 + μ) * f ^ 2) + (μ * f ^ 2) ^ 2) := by ring
      _ = _ := by rw [hq, hμf]; ring
  have dBX : dist Bb X = (K : ℝ) * (f ^ 2 - e ^ 2) := by
    refine dist_of_sqd _ _ _ (mul_pos hKR hb).le ?_
    have key : (Bb 0 - X 0) ^ 2 + (Bb 1 - X 1) ^ 2 = μ ^ 2 * ((Bb 0 - O 0) ^ 2 + (Bb 1 - O 1) ^ 2) := by
      rw [hX0, hX1]; ring
    rw [key, sBO]
    calc μ ^ 2 * ((K : ℝ) * f ^ 2) ^ 2 = (K : ℝ) ^ 2 * (μ * f ^ 2) ^ 2 := by ring
      _ = _ := by rw [hμf]; ring
  have dPO : dist Pp O = (K : ℝ) * f ^ 2 := by rw [dist_comm]; exact h20
  -- the triangles
  let Δ : Erdos634.Geometry.Tri := triOf Pp O X hcrΔ
  let T1 : Erdos634.Geometry.Tri := triOf X Pp Bb hcrT
  have hT1 : HasSides T1 ((K : ℝ) * (e * f)) ((K : ℝ) * (f ^ 2 - e ^ 2)) ((K : ℝ) * f ^ 2) :=
    ⟨Equiv.refl _, h01, dBX, dXP⟩
  obtain ⟨E1, hE1c, hE1m⟩ := tileKgen D2.model T1 K hK _ _ _ h2m hT1
  -- the fan
  have hB : Bb = O + s • (X - O) := by
    have h : X - O = (1 + μ) • (Bb - O) := by rw [hX]; module
    rw [h, smul_smul, hs, one_smul]; abel
  have cov := fan_cover Pp O X Bb s hspos hs1 hB
  have dis := fan_disjoint Pp O X Bb s hspos hs1 hB hcrΔ
  have hΔc : Δ.carrier = convexHull ℝ {Pp, O, X} := carrier_triOf _ _ _ hcrΔ
  have hT1c : T1.carrier = convexHull ℝ {X, Pp, Bb} := carrier_triOf _ _ _ hcrT
  have hset : ({Pp, Bb, O} : Set Plane) = {Pp, O, Bb} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hset2 : ({X, Pp, Bb} : Set Plane) = {Pp, Bb, X} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hD2c : D2.target.carrier = convexHull ℝ {Pp, O, Bb} := by
    unfold Tri.carrier
    rw [range_perm D2.target τ, ← hPp, ← hBb, ← hO, hset]
  have hcov : E1.target.carrier ∪ D2.target.carrier = Δ.carrier := by
    rw [hE1c, hT1c, hD2c, hΔc, cov, hset2, Set.union_comm]
  have hdisj : Disjoint (interior E1.target.carrier) (interior D2.target.carrier) := by
    rw [hE1c, hT1c, hset2, hD2c]; exact dis.symm
  obtain ⟨F, hFt, hFm⟩ := exists_reindex (show K * K * 1 + N2 = K * K + N2 by ring)
    (_root_.unionCongruentDissection Δ E1 D2 hE1m hcov hdisj)
  refine ⟨F, ?_, ?_⟩
  · rw [hFt]
    show HasSides Δ _ _ _
    exact ⟨Equiv.refl _, dOX, dXP, dPO⟩
  · rw [hFm]; exact hE1m

/-- the `alpha_g` target statement, identical in its data to `ThetaCompose.alpha_exists` (base `g b Q`, legs `g b f^2`, count `b (b + f f) g g`). -/
def AlphaTiled (e f b g : ℕ) : Prop :=
  ∃ D : CongruentDissection (b * (b + f * f) * g * g),
    HasSides D.target ((g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      ((g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (f : ℝ) ^ 2) ((g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (f : ℝ) ^ 2) ∧
    HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)

/-- **HUB (iv).**  `ThetaTiled e f b (g f)  ->  AlphaTiled e f b g`  (`f f = e e + b`, `1 <= e < f`, `g >= 1`):
`alpha_g = (g b) tau  u  theta_{g f}`; count `(g b)^2 + b (g f)^2 = b (b + f^2) g^2`. -/
theorem alphaTiled_of_thetaTiled (e f b g : ℕ) (he : 1 ≤ e) (hef : e < f) (hb : f * f = e * e + b) (hg : 1 ≤ g)
    (h : ThetaTiled e f b (g * f)) : AlphaTiled e f b g := by
  obtain ⟨D2, h2t, h2m⟩ := h
  have hbR : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : ((f * f : ℕ) : ℝ) = ((e * e + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; nlinarith
  have hbpos : 0 < b := by
    have : e * e < f * f := Nat.mul_self_lt_mul_self hef
    omega
  have hK : 0 < g * b := Nat.mul_pos (by omega) hbpos
  have heR : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have h2t' : HasSides D2.target (((g * b : ℕ) : ℝ) * (f : ℝ) ^ 2) (((g * b : ℕ) : ℝ) * (f : ℝ) ^ 2)
      (((g * b : ℕ) : ℝ) * ((e : ℝ) * f)) := by
    refine hsc h2t ?_ ?_ ?_ <;> (rw [← hbR]; push_cast; ring)
  obtain ⟨D, hDt, hDm⟩ := glue_notch (e : ℝ) f (g * b) hK heR hefR D2 h2t' h2m
  obtain ⟨E, hEt, hEm⟩ := exists_reindex
    (show g * b * (g * b) + b * (g * f) * (g * f) = b * (b + f * f) * g * g by ring) D
  refine ⟨E, ?_, by rw [hEm, hDm]; exact h2m⟩
  rw [hEt]
  refine hsc hDt ?_ ?_ ?_ <;> (rw [← hbR]; push_cast; ring)

end
end Erdos634.Draft.ThetaNotch
