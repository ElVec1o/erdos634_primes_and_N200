import Erdos634.Draft.CompositeE5Gen
import Erdos634.Draft.GapE120Dis

/-! `GapE120 N` with ONE exceptional (square-`D`) pair `{x, y}`.

`CompositeE5Gen.gapE120_of_pairs` kills every admissible pair `(s,t)` (`s t = 3N`) whose `D = (t-s)² + 16N` is not a
square.  A square-`D` pair gives a tile with RATIONAL side ratios; it cannot be killed by the irrational-part argument
and is carried here as the named leaf `E120Pair N s t`.  `close_of_cert` discharges such a leaf from a search
certificate (`not_dissection` of a `Refl.CheckM` instance): the pair equations pin the tile to `l·(x,y,z)` and the target
side to `L·l`; scale by `1/l`; SSS.  (Generalises `GapE120Dis.gapE120_15`, which is the case `N = 15`.) -/

open scoped Classical
open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeE5Gen

namespace Erdos634.Draft.GapE120Exc

/-- no equilateral-target dissection by a `2π/3` tile whose invariant pair is exactly `(s, t)` -/
def E120Pair (N : ℕ) (s t : ℤ) : Prop :=
  ∀ (D : CongruentDissection N) (α a b c : ℝ), IrrPi α → D.model.TwoPiThreeData α a b c → Equilateral D →
    (s : ℝ) * (c + a - b) = 3 * D.target.oppLen 0 → (t : ℝ) * (c + b - a) = 3 * D.target.oppLen 0 →
    D.target.oppLen 0 ^ 2 = (N : ℝ) * a * b → False

/-- `GapE120 N` from the pair table with the exceptional pair `{x, y}` carried as two `E120Pair` leaves. -/
theorem gapE120_of_pairs_exc (N : ℕ) (hN : 0 < N) (x y : ℤ) (g1 : E120Pair N x y) (g2 : E120Pair N y x)
    (hpairs : ∀ s t : ℤ, 1 ≤ s → s ≤ N → 1 ≤ t → t ≤ N → s * t = 3 * (N : ℤ) →
      (s = x ∧ t = y) ∨ (s = y ∧ t = x) ∨
      (¬ IsSquare ((t - s) ^ 2 + 16 * (N : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * (N : ℤ) ≠ r * (s + t))) : GapE120 N := by
  intro D α a b c hα h hE
  obtain ⟨s, t, -, -, hs1, hsN, ht1, htN, hS1, hS2, harea, hprod, -⟩ := Row5.theoremE_twoPiThree D hα h hE
  rcases hpairs s t hs1 hsN ht1 htN hprod with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨hD, hno⟩
  · subst e1; subst e2
    exact g1 D α a b c hα h hE hS1 hS2 harea
  · subst e1; subst e2
    exact g2 D α a b c hα h hE hS1 hS2 harea
  · obtain ⟨p, q, r, hpqr⟩ := Row5TwoPiThreeFull.side_decomposition D h
    obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0
      (fun k => D.model.data_angles_mem hα h 0 k) hE
    have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
      rw [← e2]; unfold Tri.oppLen; rfl
    rw [hd] at hpqr
    exact twoPiThree_side_kill (N := N) (a := a) (b := b) (c := c) (S := D.target.oppLen 0) s t hN hS1 hS2 harea hprod
      (D.target.oppLen_pos 0) (p : ℤ) (q : ℤ) (r : ℤ) (by positivity) (by positivity)
      (by rw [hpqr]; push_cast; ring) hD (hno (r : ℤ) (by positivity))

/-- a relabelled, scaled model with sides `(x,y,z)` is congruent to a model with those sides -/
theorem cong_of_sides' (M MODEL : Erdos634.Geometry.Tri) (x y z : ℝ)
    (hMod : dist (MODEL.pts 0) (MODEL.pts 1) = x ∧ dist (MODEL.pts 1) (MODEL.pts 2) = y ∧
      dist (MODEL.pts 0) (MODEL.pts 2) = z)
    (r : ℝ) (hr : 0 < r) (τ : Equiv.Perm (Fin 3))
    (hx : r * dist (M.pts (τ 0)) (M.pts (τ 1)) = x) (hy : r * dist (M.pts (τ 1)) (M.pts (τ 2)) = y)
    (hz : r * dist (M.pts (τ 0)) (M.pts (τ 2)) = z) :
    (Erdos634.DissectionMap.mapTri (Erdos634.Realizable.homothetyEquiv 0 r hr.ne') M).Congruent MODEL := by
  set T := Erdos634.DissectionMap.mapTri (Erdos634.Realizable.homothetyEquiv 0 r hr.ne') M with hT
  have hdist : ∀ i j, dist ((T.relabel τ).pts i) ((T.relabel τ).pts j) = r * dist (M.pts (τ i)) (M.pts (τ j)) := by
    intro i j
    simp only [Tri.relabel_pts, hT, Erdos634.DissectionMap.mapTri, Function.comp]
    rw [Erdos634.Realizable.homothetyEquiv_dist 0 r hr.ne', abs_of_pos hr]
  obtain ⟨m1, m2, m3⟩ := hMod
  have := Tri.congruent_of_dist (T.relabel τ) MODEL
    (by rw [hdist, hx, m1]) (by rw [hdist, hy, m2]) (by rw [hdist, hz, m3])
  exact (T.congruent_relabel τ).trans this

open Erdos634.Geometry.GapE120Dis in
/-- **Closing an exceptional pair by a certificate.**  If the pair equations force the tile to be `l·(·,·,z)` with
`{a, b} = {x l, y l}` and the target side to be `L l`, and no dissection of `TGT` (equilateral, side `L`) by `MODEL`
(sides `x, y, z` in vertex order `01, 12, 02`) exists, then no such dissection `D` exists. -/
theorem close_of_cert {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (h : D.model.TwoPiThreeData α a b c) (hE : Equilateral D)
    (TGT MODEL : Erdos634.Geometry.Tri) (L x y z l : ℝ) (hl : 0 < l)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = L ∧ dist (TGT.pts 1) (TGT.pts 2) = L ∧ dist (TGT.pts 0) (TGT.pts 2) = L)
    (hM : dist (MODEL.pts 0) (MODEL.pts 1) = x ∧ dist (MODEL.pts 1) (MODEL.pts 2) = y ∧
      dist (MODEL.pts 0) (MODEL.pts 2) = z)
    (hS : D.target.oppLen 0 = L * l) (hc : c = z * l)
    (hab : (b = x * l ∧ a = y * l) ∨ (a = x * l ∧ b = y * l))
    (hno : ∀ D' : CongruentDissection N, D'.target.Congruent TGT → D'.model.Congruent MODEL → False) : False := by
  have hα' : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi := hα
  have hr : 0 < l⁻¹ := inv_pos.mpr hl
  have hrl : ∀ x : ℝ, l⁻¹ * (x * l) = x := fun x => by field_simp
  set D' := Erdos634.Realizable.scaleDissection 0 l⁻¹ hr.ne' D with hD'
  obtain ⟨e1, e2, -⟩ := Row5.equilateral_boundary D hα' 0 (fun k => D.model.data_angles_mem hα' h 0 k) hE
  have d01 : dist (D.target.pts 0) (D.target.pts 1) = L * l := by
    rw [← hS, ← e2]; unfold Tri.oppLen; rfl
  have d12 : dist (D.target.pts 1) (D.target.pts 2) = L * l := by
    rw [← hS]; unfold Tri.oppLen; rfl
  have d02 : dist (D.target.pts 0) (D.target.pts 2) = L * l := by
    rw [← hS, ← e1, dist_comm]; unfold Tri.oppLen; rfl
  have tdist : ∀ i j, dist (D'.target.pts i) (D'.target.pts j) = l⁻¹ * dist (D.target.pts i) (D.target.pts j) := by
    intro i j
    rw [hD', Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.homothetyEquiv_dist, abs_of_pos hr]
  obtain ⟨g1, g2, g3⟩ := hT
  have hTc : D'.target.Congruent TGT :=
    Tri.congruent_of_dist _ _ (by rw [tdist, d01, g1]; exact hrl L) (by rw [tdist, d12, g2]; exact hrl L)
      (by rw [tdist, d02, g3]; exact hrl L)
  obtain ⟨σ, -, oa, -, ob, -, oc⟩ := h
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  rw [oa] at s1; rw [ob] at s2; rw [oc] at s3
  have hMc : D'.model.Congruent MODEL := by
    rcases hab with ⟨hb, ha⟩ | ⟨ha, hb⟩
    · refine cong_of_sides' D.model MODEL x y z hM l⁻¹ hr ((Equiv.swap (1 : Fin 3) 2).trans σ) ?_ ?_ ?_
      · have : ((Equiv.swap (1 : Fin 3) 2).trans σ) 0 = σ 0 := by simp [sw0]
        have h2 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 1 = σ 2 := by simp [sw1]
        rw [this, h2, s2, hb]; exact hrl x
      · have h1 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 1 = σ 2 := by simp [sw1]
        have h2 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 2 = σ 1 := by simp [sw2]
        rw [h1, h2, dist_comm, s1, ha]; exact hrl y
      · have h0 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 0 = σ 0 := by simp [sw0]
        have h2 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 2 = σ 1 := by simp [sw2]
        rw [h0, h2, s3, hc]; exact hrl z
    · refine cong_of_sides' D.model MODEL x y z hM l⁻¹ hr ((finRotate 3).trans σ) ?_ ?_ ?_
      · have h0 : ((finRotate 3).trans σ) 0 = σ 1 := by simp [fr0]
        have h1 : ((finRotate 3).trans σ) 1 = σ 2 := by simp [fr1]
        rw [h0, h1, s1, ha]; exact hrl x
      · have h1 : ((finRotate 3).trans σ) 1 = σ 2 := by simp [fr1]
        have h2 : ((finRotate 3).trans σ) 2 = σ 0 := by simp [fr2]
        rw [h1, h2, dist_comm, s2, hb]; exact hrl y
      · have h0 : ((finRotate 3).trans σ) 0 = σ 1 := by simp [fr0]
        have h2 : ((finRotate 3).trans σ) 2 = σ 0 := by simp [fr2]
        rw [h0, h2, dist_comm, s3, hc]; exact hrl z
  exact hno D' hTc hMc

/-- the pair equations determine the tile: `s(c+a-b) = 3S`, `t(c+b-a) = 3S`, `S² = N a b` with
`c = z·l`, `a - b = δ·l`, `(a+b)² = σ²·l²` for `S = L·l` (all the numbers supplied by the caller) -/
theorem shape_of_pair (S a b c s t Nn L z δ σ : ℝ) (hS : 0 < S) (ha : 0 < a) (hb : 0 < b) (hL : 0 < L) (hσ : 0 ≤ σ)
    (e1 : s * (c + a - b) = 3 * S) (e2 : t * (c + b - a) = 3 * S) (harea : S ^ 2 = Nn * a * b)
    (hs : s ≠ 0) (ht : t ≠ 0)
    (hz : 2 * s * t * z = 3 * L * (s + t)) (hδ : 2 * s * t * δ = 3 * L * (t - s))
    (hσ2 : Nn * (σ ^ 2 - δ ^ 2) = 4 * L ^ 2) (hNn : 0 < Nn) :
    c = z * (S / L) ∧ a = (σ + δ) / 2 * (S / L) ∧ b = (σ - δ) / 2 * (S / L) := by
  have hLne : L ≠ 0 := hL.ne'
  have hc : c = z * (S / L) := by
    have h1 : 2 * s * t * c = 3 * S * (s + t) := by linear_combination t * e1 + s * e2
    have h2 : 2 * s * t * (c - z * (S / L)) = 0 := by
      have : 2 * s * t * (z * (S / L)) = 3 * S * (s + t) := by
        have : 2 * s * t * (z * (S / L)) = (2 * s * t * z) * (S / L) := by ring
        rw [this, hz]; field_simp
      linarith
    have h3 : 2 * s * t ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hs) ht
    have := (mul_eq_zero.mp h2).resolve_left h3
    linarith
  have hd : a - b = δ * (S / L) := by
    have h1 : 2 * s * t * (a - b) = 3 * S * (t - s) := by linear_combination t * e1 - s * e2
    have h2 : 2 * s * t * ((a - b) - δ * (S / L)) = 0 := by
      have : 2 * s * t * (δ * (S / L)) = 3 * S * (t - s) := by
        have : 2 * s * t * (δ * (S / L)) = (2 * s * t * δ) * (S / L) := by ring
        rw [this, hδ]; field_simp
      linarith
    have h3 : 2 * s * t ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hs) ht
    have := (mul_eq_zero.mp h2).resolve_left h3
    linarith
  have hsq : (a + b) ^ 2 = (σ * (S / L)) ^ 2 := by
    have hab : a * b = S ^ 2 / Nn := by field_simp; linarith
    have hx : 4 * L ^ 2 / Nn = σ ^ 2 - δ ^ 2 := by rw [← hσ2]; field_simp
    calc (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
      _ = (δ * (S / L)) ^ 2 + 4 * (S ^ 2 / Nn) := by rw [hd, hab]
      _ = (δ ^ 2 + 4 * L ^ 2 / Nn) * (S / L) ^ 2 := by first | (field_simp; ring) | field_simp
      _ = (σ * (S / L)) ^ 2 := by rw [hx]; ring
  have hab : a + b = σ * (S / L) := by
    have h0 : 0 ≤ σ * (S / L) := by positivity
    exact (pow_left_inj₀ (by positivity) h0 (by norm_num)).mp hsq
  refine ⟨hc, ?_, ?_⟩
  · linear_combination (hab + hd) / 2
  · linear_combination (hab - hd) / 2

end Erdos634.Draft.GapE120Exc
