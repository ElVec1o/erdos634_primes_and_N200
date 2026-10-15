/-
Draft/PI3FT.lean -- Theorem T, stage (d): the assembly.

`theoremT : PI3F_TheoremT`:  an equilateral target dissected by `N` copies of a `π/3`-tile with invariant pair `(m₁, m₂)`,
`D = (m₁+m₂)² − 16N` non-square, and `2 N gcd(m₁+m₂, m₁−m₂) < m₁² − m₂²`, cannot exist.

Proof (all steps are Lean theorems of this development; no hypothesis is left open):
 1. each tile `i` has a type `(tᵢ, oᵢ, xᵢ)`: edge `k` has length `![a,b,c] (tᵢ (k+2))` and direction class `pk oᵢ tᵢ xᵢ k`
    (`PI3FCert.tile_edge_pos`);
 2. total count identity: `Σ_{all edges} ρ_bc(type) · gV(class) = 0`  (`PI3FCert.tile_count_zero`, a finite check over the 216
    tile types), where `ρ_bc` is the indicator of the sides `b, c`;
 3. the interior contributes `0`  (`PI3FBal.interior_type_balance`, the chain-balance lemma L1, fed by the length-kernel floor
    `PI3FKernel.kernel_floor`, the diameter bound `S` of the equilateral target, and the oddness of `gV`);
 4. the boundary: only side `0` carries weight `1` (`PI3FCert.target_side_weight`), so the `b/c`-edges on side `0` number `0`;
 5. then side `0` (length `S`) consists of `P` edges of type `a` only: `P a = S`; the irrational split (`PI3FKernel.split_gen`,
    `D` non-square) forces `P = 0` and `0 = 4N`: contradiction.
No sorry, no native_decide.
-/
import Erdos634.Draft.PI3FStatement
import Erdos634.Draft.PI3FKernel
import Erdos634.Draft.PI3FCert
import Erdos634.Draft.PI3FBal

open scoped Classical

namespace Erdos634.Draft.PI3F

open Erdos634.Geometry Erdos634.Geometry.Row5Hr0 Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.E60Mod9 Erdos634.Draft.CompositeE5Gen Erdos634.Draft.E60V

/-- A triangle whose vertices are pairwise `≤ S` apart has diameter `≤ S`. -/
theorem tri_dist_le (T : Tri) {S : ℝ} (h : ∀ i j, dist (T.pts i) (T.pts j) ≤ S) :
    ∀ x ∈ T.carrier, ∀ y ∈ T.carrier, dist x y ≤ S := by
  have h1 : ∀ j, ∀ x ∈ T.carrier, dist x (T.pts j) ≤ S := by
    intro j x hx
    have : T.carrier ⊆ Metric.closedBall (T.pts j) S :=
      convexHull_min (by rintro _ ⟨i, rfl⟩; simpa [Metric.mem_closedBall, dist_comm] using h i j)
        (convex_closedBall _ _)
    simpa [Metric.mem_closedBall] using this hx
  intro x hx y hy
  have : T.carrier ⊆ Metric.closedBall x S :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; simpa [Metric.mem_closedBall, dist_comm] using h1 i x hx)
      (convex_closedBall _ _)
  simpa [Metric.mem_closedBall, dist_comm] using this hy

/-- **Theorem T.** -/
theorem theoremT : PI3F_TheoremT := by
  intro N m₁ m₂ hN hprod hD hfl D α a b c hα h hE hS1 hS2
  have hP : ∀ k, D.target.angleAt k = Real.pi / 3 := hE
  set anc := (D.target.leftUnit 0).angle with hanc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, harea, -⟩ := Row5.theoremE_sixty D hα h hP
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  set S := D.target.oppLen 0 with hSdef
  have hpos3 : 0 < a ∧ 0 < b ∧ 0 < c := by
    obtain ⟨τ, h0, o0, h1, o1, h2, o2⟩ := h
    exact ⟨by rw [← o0]; exact D.model.oppLen_pos _, by rw [← o1]; exact D.model.oppLen_pos _,
      by rw [← o2]; exact D.model.oppLen_pos _⟩
  obtain ⟨ha, hb, hc⟩ := hpos3
  have hmem : ∀ i k, (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ (Gc α hα anc).L :=
    fun i => Row5Hr0.tile_angles_mem D hα h i
  -- (1) per-tile data
  have hdata : ∀ i, ∃ t : Fin 3 → Fin 3, Function.Injective t ∧ (∀ k, (D.tile i).oppLen k = ![a, b, c] (t k)) ∧
      ∃ (o : Bool) (x : GZ), ∀ k : Fin 3, pos α hα anc ((D.tile i).leftUnit k).angle = pk o t x k := by
    intro i
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
    have hS : (D.tile i).SixtyData α a b c := by
      obtain ⟨τ, h0, o0, h1, o1, h2, o2⟩ := h
      refine ⟨σ.symm * τ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Equiv.Perm.mul_apply, (hσ _).1, (hσ _).2, Equiv.apply_symm_apply] <;> assumption
    exact tile_edge_pos α hα anc (D.tile i) hS (hmem i)
  choose t ht hlen o x hpos using hdata
  -- edge types
  set τ : Fin N × Fin 3 → Fin 3 := fun e => t e.1 (e.2 + 2) with hτ
  have heLen : ∀ e : Fin N × Fin 3, D.toDissection.eLen e = ![a, b, c] (τ e) := by
    intro e
    rw [hτ]
    show D.toDissection.eLen e = ![a, b, c] (t e.1 (e.2 + 2))
    rw [← hlen e.1 (e.2 + 2)]
    unfold Dissection.eLen Tri.oppLen
    have h1 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
    have h2 : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
    rw [h1, h2]
  -- equilateral: all sides S, so the target has diameter ≤ S
  obtain ⟨e1, e2, -⟩ := Row5.equilateral_boundary D hα 0
    (fun k => D.model.sixty_angles_mem hα h 0 _ k) hP
  have hdiam : ∀ x ∈ D.target.carrier, ∀ y ∈ D.target.carrier, dist x y ≤ S := by
    apply tri_dist_le
    intro i j
    have d0 : dist (D.target.pts 1) (D.target.pts 2) = S := rfl
    have d1 : dist (D.target.pts 2) (D.target.pts 0) = S := e1
    have d2 : dist (D.target.pts 0) (D.target.pts 1) = S := e2
    have d0' : dist (D.target.pts 2) (D.target.pts 1) = S := by rw [dist_comm]; exact d0
    have d1' : dist (D.target.pts 0) (D.target.pts 2) = S := by rw [dist_comm]; exact d1
    have d2' : dist (D.target.pts 1) (D.target.pts 0) = S := by rw [dist_comm]; exact d2
    fin_cases i <;> fin_cases j <;> simp [d0, d0', d1, d1', d2, d2', hS0.le]
  -- the floor hypothesis
  have hfloor : ∀ n : Fin 3 → ℤ, (∃ i, n i ≠ 0) → ∑ i, (n i : ℝ) * ![a, b, c] i = 0 →
      S < ∑ i, ((max (n i) 0 : ℤ) : ℝ) * ![a, b, c] i := by
    intro n hex hrel
    obtain ⟨i, hi⟩ := hex
    simp only [Fin.sum_univ_three] at hrel ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hrel ⊢
    refine kernel_floor (N := N) (a := a) (b := b) (c := c) (S := S) m₁ m₂ hN ha hb hc hS1 hS2
      (by exact_mod_cast harea) hprod hS0 hD hfl (n 0) (n 1) (n 2) ?_ hrel
    rintro ⟨h0, h1, h2⟩
    apply hi
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  -- (3) the interior balance
  have hω : ∀ d : Dir, gV (pos α hα anc (Dir.neg d).angle) = - gV (pos α hα anc d.angle) :=
    fun d => omega_odd α hα anc d
  have hint := interior_type_balance D.toDissection τ ![a, b, c] heLen
    (by intro i; fin_cases i <;> simp [ha.le, hb.le, hc.le]) hdiam hfloor rhoBC
    (fun d => gV (pos α hα anc d.angle)) hω
  -- (2) the total
  have htot : ∑ e : Fin N × Fin 3, rhoBC (τ e) * gV (pos α hα anc (D.toDissection.eDir e).angle) = 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ∀ k : Fin 3, rhoBC (τ (i, k)) * gV (pos α hα anc (D.toDissection.eDir (i, k)).angle)
        = rhoBC (t i (k + 2)) * gV (pk (o i) (t i) (x i) k) := by
      intro k
      show rhoBC (t i (k + 2)) * gV (pos α hα anc ((D.tile i).leftUnit k).angle) = _
      rw [hpos i k]
    rw [Finset.sum_congr rfl fun k _ => this k]
    exact tile_count_zero (t i) (ht i) (o i) (x i)
  -- (4) the boundary
  have hsplit := D.toDissection.sum_split
    (fun e => rhoBC (τ e) * gV (pos α hα anc (D.toDissection.eDir e).angle))
  rw [htot, hint, zero_add] at hsplit
  have hside : ∀ j : Fin 3, ∑ e ∈ D.toDissection.sideEdges j,
      rhoBC (τ e) * gV (pos α hα anc (D.toDissection.eDir e).angle)
      = ∑ e ∈ D.toDissection.sideEdges j, rhoBC (τ e) * (if j = 0 then 1 else 0) := by
    intro j
    refine Finset.sum_congr rfl fun e he => ?_
    have hes : D.toDissection.eSet e ⊆ D.target.edge j := (Finset.mem_filter.mp he).2
    rw [D.toDissection.eDir_of_side hes]
    rw [target_side_weight D hα h hP j]
  simp only [hside, Fin.sum_univ_three] at hsplit
  simp only [Fin.isValue, one_ne_zero, if_false, ne_eq, OfNat.ofNat_ne_zero, mul_zero,
    Finset.sum_const_zero, add_zero, if_true, mul_one] at hsplit
  have hzero : ∀ e ∈ D.toDissection.sideEdges 0, rhoBC (τ e) = 0 := by
    have hnn : ∀ e ∈ D.toDissection.sideEdges 0, 0 ≤ rhoBC (τ e) := by
      intro e _; unfold rhoBC; split <;> norm_num
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (by simpa using hsplit.symm)
  have htyp : ∀ e ∈ D.toDissection.sideEdges 0, τ e = 0 := by
    intro e he
    have := hzero e he
    unfold rhoBC at this
    by_contra hne
    simp [hne] at this
  -- (5) side 0 is `P` edges of type `a`
  have hlen0 := D.toDissection.side_len_sum 0
  have hd : dist (D.target.pts 0) (D.target.pts (0 + 1)) = S := e2
  rw [hd] at hlen0
  have hsum : ∑ e ∈ D.toDissection.sideEdges 0, D.toDissection.eLen e
      = ((D.toDissection.sideEdges 0).card : ℝ) * a := by
    rw [Finset.sum_congr rfl fun e he => by rw [heLen e, htyp e he]]
    simp
  obtain ⟨hPQ, hz⟩ := split_gen (N := N) (a := a) (b := b) (c := c) (S := S) m₁ m₂ hN hS1 hS2
    (by exact_mod_cast harea) hprod hS0 hD ((D.toDissection.sideEdges 0).card : ℤ) 0 0 1
    (by push_cast; rw [← hsum, hlen0]; ring)
  have hP0 : ((D.toDissection.sideEdges 0).card : ℤ) = 0 := hPQ
  rw [hP0] at hz
  have : (4 : ℤ) * N = 0 := by linarith
  omega

/-- Stage (b) as a proved Prop. -/
theorem cert : PI3F_Cert := ⟨tile_count_zero, boundary_value⟩

/-- Stage (c0) as a proved Prop. -/
theorem kernel : PI3F_Kernel := by
  intro N a b c S m₁ m₂ hN ha hb hc h1 h2 harea hprod hS0 hD hfl n₀ n₁ n₂ hn hrel
  exact kernel_floor m₁ m₂ hN ha hb hc h1 h2 harea hprod hS0 hD hfl n₀ n₁ n₂ hn hrel

/-- Stage (c) as a proved Prop. -/
theorem chainBalance : PI3F_ChainBalance :=
  fun N D τ ℓ hlen hℓ B hB hfloor ρ ω hω => interior_type_balance D τ ℓ hlen hℓ hB hfloor ρ ω hω

/-! ### Controls: the arithmetic hypotheses are satisfiable, and the known realized case fails them -/

/-- `D = 38² − 16·87 = 52` is not a square. -/
theorem D87_nonsq : ¬ IsSquare ((29 + 9 : ℤ) ^ 2 - 16 * ((87 : ℕ) : ℤ)) := by
  rintro ⟨r, hr⟩
  have h52 : r * r = 52 := by push_cast at hr; linarith
  have h1 : r ≤ 8 := by nlinarith
  have h2 : -8 ≤ r := by nlinarith
  interval_cases r <;> omega

/-- **Positive control (arithmetic).**  At `N = 87`, `(m₁, m₂) = (29, 9)` every arithmetic hypothesis of Theorem T holds,
so `theoremT` produces `E60Pair 87 29 9` — by a route independent of the mod-9 obstruction (`E60Mod9C.e60Pair_87`). -/
theorem e60Pair_87_via_T : E60Pair 87 29 9 :=
  theoremT 87 29 9 (by norm_num) (by norm_num) D87_nonsq (by decide)

/-- **Kernel-floor witness (all hypotheses of `kernel_floor` hold, and the floor is attained).**  `N = 87`,
`(m₁,m₂) = (29,9)`, `S = 174`, `a = 19 + √13`, `b = 19 − √13`, `c = 20`: the relation `10 a + 10 b − 19 c = 0` has one-sided
length `380 = ℓκ · (S / 2N) > S`. -/
theorem kernel_floor_witness :
    ∃ a b c S : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (29 : ℝ) * (a + b - c) = 3 * S ∧ (9 : ℝ) * (a + b + c) = 3 * S ∧
      S ^ 2 = (87 : ℕ) * a * b ∧ 0 < S ∧ ((10 : ℤ) : ℝ) * a + ((10 : ℤ) : ℝ) * b + ((-19 : ℤ) : ℝ) * c = 0 ∧
      S < ((max (10 : ℤ) 0 : ℤ) : ℝ) * a + ((max (10 : ℤ) 0 : ℤ) : ℝ) * b + ((max (-19 : ℤ) 0 : ℤ) : ℝ) * c := by
  have h13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 13 < 4 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt 13 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨19 + Real.sqrt 13, 19 - Real.sqrt 13, 20, 174, by linarith, by linarith, by norm_num, by ring, by ring,
    ?_, by norm_num, by push_cast; ring, ?_⟩
  · push_cast; nlinarith [h13]
  · push_cast; norm_num; linarith

/-- **Kernel-floor applied at the witness**: the conclusion of `kernel_floor` holds there (non-vacuity of the whole
implication, including `hD` and the gcd inequality). -/
theorem kernel_floor_at_87 : True := by
  obtain ⟨a, b, c, S, ha, hb, hc, h1, h2, harea, hS0, hrel, hconc⟩ := kernel_floor_witness
  have := kernel_floor (N := 87) (a := a) (b := b) (c := c) (S := S) 29 9 (by norm_num) ha hb hc (by exact_mod_cast h1)
    (by exact_mod_cast h2) (by exact_mod_cast harea) (by norm_num) hS0 D87_nonsq (by decide) 10 10 (-19)
    (by decide) (by exact_mod_cast hrel)
  trivial

/-- **The realized case.**  The certified 1440-tiling of the equilateral triangle by the `π/3` tile
`(5,8,7)` (`G3CSixtyControl`) has `(m₁, m₂) = (120, 36)`; there `D = 156² − 16·1440 = 36²`
is a SQUARE and `ℓκ = 1092 < 2N = 2880`: both hypotheses of Theorem T fail, as they must. -/
theorem control_1440 :
    (120 : ℤ) * 36 = 3 * (1440 : ℕ) ∧ IsSquare ((120 + 36 : ℤ) ^ 2 - 16 * ((1440 : ℕ) : ℤ)) ∧
      ¬ (2 * ((1440 : ℕ) : ℤ) * (Int.gcd (120 + 36) (120 - 36) : ℤ) < (120 + 36) * (120 - 36)) := by
  refine ⟨by norm_num, ⟨36, by norm_num⟩, by decide⟩

end Erdos634.Draft.PI3F

#print axioms Erdos634.Draft.PI3F.tri_dist_le
#print axioms Erdos634.Draft.PI3F.theoremT
#print axioms Erdos634.Draft.PI3F.cert
#print axioms Erdos634.Draft.PI3F.kernel
#print axioms Erdos634.Draft.PI3F.chainBalance
#print axioms Erdos634.Draft.PI3F.e60Pair_87_via_T
#print axioms Erdos634.Draft.PI3F.kernel_floor_witness
#print axioms Erdos634.Draft.PI3F.kernel_floor_at_87
#print axioms Erdos634.Draft.PI3F.control_1440
