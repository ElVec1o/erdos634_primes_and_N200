-- Draft/ChainW.lean -- CHAIN LEMMA, stage 2: Theorem W placement from the chain lemma.  The six pieces of the Theorem W template in
-- Fable's integer skew frame, each quadrilateral split along a diagonal into two triangles (ten triangles in all).  The boundary-chain
-- identity holds for ALL real parameters (five line equations, by `ring`); the ten strict turns are `positive monomial * factor`.
-- UNAUDITED.  No sorry.
-- Credit: Beeson-Rosu (W/T targets, isosceles-apex frame idea), Paliy (W/beta framework), template from engine `bto`, integer frame and
-- the "only C3..C7 and t >= 1 carry content" observation: the AI assistant (project working notes);
-- chain lemma: Ramanujan-rows session (project working notes), audited SOUND-WITH-FIX (project working notes).
import Erdos634.Draft.ChainCover

open scoped Classical
namespace Erdos634.Draft.Chain.W

/-- the 11 distinct vertices (`b = f^2-e^2`), integer skew frame -/
noncomputable def O (e f M : ℝ) : ℝ × ℝ := (f * (f ^ 2 - e ^ 2) * M, 0)
noncomputable def B (e f M : ℝ) : ℝ × ℝ := (0, e * (f ^ 2 - e ^ 2) * M)
noncomputable def A (e f M : ℝ) : ℝ × ℝ := (0, -(e * f ^ 2 * M))
noncomputable def P2 (e f t : ℝ) : ℝ × ℝ := ((f ^ 2 - e ^ 2) * e * t, 0)
noncomputable def P3 (e f t : ℝ) : ℝ × ℝ := (0, -(e ^ 2 * f * t))
noncomputable def Q (e f t : ℝ) : ℝ × ℝ := (0, f * (f ^ 2 - e ^ 2) * t)
noncomputable def C' (e f r : ℝ) : ℝ × ℝ := ((f ^ 2 - e ^ 2) * e * r, 0)
noncomputable def B' (e f M r : ℝ) : ℝ × ℝ := (e * f * (f * r - e * M), e * f * (f * M - e * r))
noncomputable def V2 (e f t r : ℝ) : ℝ × ℝ := (e * f ^ 2 * (r - t), f * (f ^ 2 * t - e ^ 2 * r))
noncomputable def U1 (e f t q : ℝ) : ℝ × ℝ := (e * f * (f * t - e * q), e * f * (f * q - e * t))
noncomputable def U2 (e f r q : ℝ) : ℝ × ℝ := (e * f * (f * r - e * q), e * f * (f * q - e * r))

/-- the target triangle `A, O, B` -/
noncomputable def tgt (e f M : ℝ) : Tri3 := ⟨A e f M, O e f M, B e f M⟩

/-- the ten triangles: fans of the quadrilaterals `p0 = A,O,P2,P3`, `p3 = B,Q,V2,B'`, `p4 = Q,U1,U2,V2`, `p5 = U1,P2,C',U2`,
and the triangles `p1 = O,B',C'`, `p2 = P3,P2,Q`. -/
noncomputable def tris (e f M t r q : ℝ) : Fin 10 → Tri3 :=
  ![⟨A e f M, O e f M, P2 e f t⟩, ⟨A e f M, P2 e f t, P3 e f t⟩, ⟨O e f M, B' e f M r, C' e f r⟩, ⟨P3 e f t, P2 e f t, Q e f t⟩,
    ⟨B e f M, Q e f t, V2 e f t r⟩, ⟨B e f M, V2 e f t r, B' e f M r⟩, ⟨Q e f t, U1 e f t q, U2 e f r q⟩, ⟨Q e f t, U2 e f r q, V2 e f t r⟩,
    ⟨U1 e f t q, P2 e f t, C' e f r⟩, ⟨U1 e f t q, C' e f r, U2 e f r q⟩]

/-- **The chain identity**, for all real parameters and every point `z`: the crossing sums of the ten triangles add up to that of the
target.  Uses only antisymmetry and collinear additivity of `kap` and the five line equations. -/
theorem chain_identity (e f M t r q : ℝ) (z : ℝ × ℝ) :
    ∑ i, (tris e f M t r q i).k z = (tgt e f M).k z := by
  have hy0 : crs (O e f M) (P2 e f t) (C' e f r) = 0 := by simp only [crs, O, P2, C']; ring
  have hOB : crs (O e f M) (B' e f M r) (B e f M) = 0 := by simp only [crs, O, B', B]; ring
  have hlr1 : crs (B' e f M r) (C' e f r) (U2 e f r q) = 0 := by simp only [crs, B', C', U2]; ring
  have hlr2 : crs (B' e f M r) (U2 e f r q) (V2 e f t r) = 0 := by simp only [crs, B', U2, V2]; ring
  have hlt : crs (P2 e f t) (Q e f t) (U1 e f t q) = 0 := by simp only [crs, P2, Q, U1]; ring
  have hAB1 : crs (B e f M) (Q e f t) (P3 e f t) = 0 := by simp only [crs, B, Q, P3]; ring
  have hAB2 : crs (B e f M) (P3 e f t) (A e f M) = 0 := by simp only [crs, B, P3, A]; ring
  have a1 := kap_add _ _ _ z hy0
  have a2 := kap_add _ _ _ z hOB
  have a3 := kap_add _ _ _ z hlr1
  have a4 := kap_add _ _ _ z hlr2
  have a5 := kap_add _ _ _ z hlt
  have a6 := kap_add _ _ _ z hAB1
  have a7 := kap_add _ _ _ z hAB2
  have s1 := kap_swap (A e f M) (P2 e f t) z
  have s2 := kap_swap (P2 e f t) (P3 e f t) z
  have s3 := kap_swap (B e f M) (V2 e f t r) z
  have s4 := kap_swap (Q e f t) (U2 e f r q) z
  have s5 := kap_swap (U1 e f t q) (U2 e f r q) z
  have s6 := kap_swap (Q e f t) (V2 e f t r) z
  have s7 := kap_swap (U1 e f t q) (C' e f r) z
  have s8 := kap_swap (O e f M) (C' e f r) z
  have s9 := kap_swap (B' e f M r) (V2 e f t r) z
  have s10 := kap_swap (P2 e f t) (U1 e f t q) z
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, tris, Tri3.k, kapTri, tgt, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, add_zero]
  omega

/-- the five independent conditions (audit VERDICT: `t, C3, C4, C6, C7`) with the basic sign facts. -/
structure WC (e f M t r q : ℝ) : Prop where
  he : 0 < e
  hef : e < f
  ht : 0 < t
  htr : t < r
  c3 : 0 < e * M - f * t
  c4 : 0 < f * r - e * M
  c6 : 0 < f * q - e * r
  c7 : 0 < f * t - e * q

namespace WC
variable {e f M t r q : ℝ}
theorem hf (h : WC e f M t r q) : 0 < f := h.he.trans h.hef
theorem hb (h : WC e f M t r q) : 0 < f ^ 2 - e ^ 2 := by nlinarith [h.he, h.hef]
theorem hM (h : WC e f M t r q) : 0 < M := by
  have := h.c3; have := mul_pos h.hf h.ht
  by_contra hh; rw [not_lt] at hh; nlinarith [h.he, mul_nonneg h.he.le (neg_nonneg.2 hh)]
theorem x1 (h : WC e f M t r q) : 0 < f * M - e * t := by
  have := h.hM; have := h.c3; nlinarith [mul_pos (sub_pos.2 h.hef) h.hM, mul_pos (sub_pos.2 h.hef) h.ht]
/-- `C5 = f M - e r` is implied: `e * C5 = f * C3 + f * C7 + e * C6`. -/
theorem c5 (h : WC e f M t r q) : 0 < f * M - e * r := by
  have := h.c3; have := h.c7; have := h.c6
  have key : e * (f * M - e * r) = f * (e * M - f * t) + f * (f * t - e * q) + e * (f * q - e * r) := by ring
  have : 0 < e * (f * M - e * r) := by rw [key]; nlinarith [h.hf, h.he]
  exact (mul_pos_iff_of_pos_left h.he).mp this
theorem x2 (h : WC e f M t r q) : 0 < f * q - e * t := by nlinarith [h.c6, mul_pos h.he (sub_pos.2 h.htr)]
end WC

section pos
variable {e f M t r q : ℝ}

theorem pos0 (h : WC e f M t r q) : (tris e f M t r q 0).pos := by
  have k : crs (A e f M) (O e f M) (P2 e f t) = M * e * f ^ 2 * (f ^ 2 - e ^ 2) * (f * M - e * t) := by simp only [crs, A, O, P2]; ring
  have := h.he; have := h.hf; have := h.hb; have := h.hM; have := h.x1
  show 0 < crs (A e f M) (O e f M) (P2 e f t); rw [k]; positivity

theorem pos1 (h : WC e f M t r q) : (tris e f M t r q 1).pos := by
  have k : crs (A e f M) (P2 e f t) (P3 e f t) = e ^ 2 * f * t * (f ^ 2 - e ^ 2) * (f * M - e * t) := by simp only [crs, A, P2, P3]; ring
  have := h.he; have := h.hf; have := h.hb; have := h.ht; have := h.x1
  show 0 < crs (A e f M) (P2 e f t) (P3 e f t); rw [k]; positivity

theorem pos2 (h : WC e f M t r q) : (tris e f M t r q 2).pos := by
  have k : crs (O e f M) (B' e f M r) (C' e f r) = e * f * (f ^ 2 - e ^ 2) * (f * M - e * r) ^ 2 := by simp only [crs, O, B', C']; ring
  have := h.he; have := h.hf; have := h.hb; have := h.c5
  show 0 < crs (O e f M) (B' e f M r) (C' e f r); rw [k]; positivity

theorem pos3 (h : WC e f M t r q) : (tris e f M t r q 3).pos := by
  have k : crs (P3 e f t) (P2 e f t) (Q e f t) = e * f ^ 3 * t ^ 2 * (f ^ 2 - e ^ 2) := by simp only [crs, P3, P2, Q]; ring
  have := h.he; have := h.hf; have := h.hb; have := h.ht
  show 0 < crs (P3 e f t) (P2 e f t) (Q e f t); rw [k]; positivity

theorem pos4 (h : WC e f M t r q) : (tris e f M t r q 4).pos := by
  have k : crs (B e f M) (Q e f t) (V2 e f t r) = e * f ^ 2 * (f ^ 2 - e ^ 2) * (r - t) * (e * M - f * t) := by simp only [crs, B, Q, V2]; ring
  have := h.he; have := h.hf; have := h.hb; have := sub_pos.2 h.htr; have := h.c3
  show 0 < crs (B e f M) (Q e f t) (V2 e f t r); rw [k]; positivity

theorem pos5 (h : WC e f M t r q) : (tris e f M t r q 5).pos := by
  have k : crs (B e f M) (V2 e f t r) (B' e f M r) = e * f * (f ^ 2 - e ^ 2) * (f * r - e * M) * (e * M - f * t) := by simp only [crs, B, V2, B']; ring
  have := h.he; have := h.hf; have := h.hb; have := h.c4; have := h.c3
  show 0 < crs (B e f M) (V2 e f t r) (B' e f M r); rw [k]; positivity

theorem pos6 (h : WC e f M t r q) : (tris e f M t r q 6).pos := by
  have k : crs (Q e f t) (U1 e f t q) (U2 e f r q) = e * f ^ 2 * (f ^ 2 - e ^ 2) * (r - t) * (f * t - e * q) := by simp only [crs, Q, U1, U2]; ring
  have := h.he; have := h.hf; have := h.hb; have := sub_pos.2 h.htr; have := h.c7
  show 0 < crs (Q e f t) (U1 e f t q) (U2 e f r q); rw [k]; positivity

theorem pos7 (h : WC e f M t r q) : (tris e f M t r q 7).pos := by
  have k : crs (Q e f t) (U2 e f r q) (V2 e f t r) = e * f ^ 2 * (f ^ 2 - e ^ 2) * (r - t) * (f * t - e * q) := by simp only [crs, Q, U2, V2]; ring
  have := h.he; have := h.hf; have := h.hb; have := sub_pos.2 h.htr; have := h.c7
  show 0 < crs (Q e f t) (U2 e f r q) (V2 e f t r); rw [k]; positivity

theorem pos8 (h : WC e f M t r q) : (tris e f M t r q 8).pos := by
  have k : crs (U1 e f t q) (P2 e f t) (C' e f r) = e ^ 2 * f * (f ^ 2 - e ^ 2) * (r - t) * (f * q - e * t) := by simp only [crs, U1, P2, C']; ring
  have := h.he; have := h.hf; have := h.hb; have := sub_pos.2 h.htr; have := h.x2
  show 0 < crs (U1 e f t q) (P2 e f t) (C' e f r); rw [k]; positivity

theorem pos9 (h : WC e f M t r q) : (tris e f M t r q 9).pos := by
  have k : crs (U1 e f t q) (C' e f r) (U2 e f r q) = e ^ 2 * f * (f ^ 2 - e ^ 2) * (r - t) * (f * q - e * r) := by simp only [crs, U1, C', U2]; ring
  have := h.he; have := h.hf; have := h.hb; have := sub_pos.2 h.htr; have := h.c6
  show 0 < crs (U1 e f t q) (C' e f r) (U2 e f r q); rw [k]; positivity

theorem pos_tgt (h : WC e f M t r q) : (tgt e f M).pos := by
  have k : crs (A e f M) (O e f M) (B e f M) = M ^ 2 * e * f * (f ^ 2 - e ^ 2) * (2 * f ^ 2 - e ^ 2) := by simp only [crs, A, O, B]; ring
  have := h.he; have := h.hf; have := h.hb; have := h.hM
  have h2 : 0 < 2 * f ^ 2 - e ^ 2 := by nlinarith
  show 0 < crs (A e f M) (O e f M) (B e f M); rw [k]; positivity

theorem pos_all (h : WC e f M t r q) : ∀ i, (tris e f M t r q i).pos := by
  intro i; fin_cases i
  exacts [pos0 h, pos1 h, pos2 h, pos3 h, pos4 h, pos5 h, pos6 h, pos7 h, pos8 h, pos9 h]
end pos

/-- **Placement of Theorem W from the chain lemma.**  Under the five conditions `t, C3, C4, C6, C7` the ten triangles have pairwise
disjoint interiors, lie in the target triangle `A, O, B`, and cover its interior. -/
theorem w_placement {e f M t r q : ℝ} (h : WC e f M t r q) :
    (∀ i j, i ≠ j → Disjoint (tris e f M t r q i).op (tris e f M t r q j).op) ∧
    (∀ i, (tris e f M t r q i).cl ⊆ (tgt e f M).cl) ∧ (∀ z ∈ (tgt e f M).op, ∃ i, z ∈ (tris e f M t r q i).cl) :=
  chain_tri _ _ (pos_tgt h) (pos_all h) (chain_identity e f M t r q)

end Erdos634.Draft.Chain.W

#print axioms Erdos634.Draft.Chain.W.w_placement
