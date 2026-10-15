/-
Draft/ReframeD.lean  In `AllThreshold`.

Paper: Proposition `prop:reframe` (d): in a dissection of `T_M(1,f)`, suppose that on a wall from the apex along a
cevian, up to the first point that is a vertex of tiles on both sides, the tiles of one side lay only edges `b = f² − 1`
on it and those of the other side only edges `c = f²`.  Then that point is at distance `b c` from the apex, and `M ≥ f`.

LAYER 1 (pure arithmetic, complete):
    first_common_bc      : `0 < i`, `i (f²−1) = j f²`  ⟹  `f² ∣ i ∧ (f²−1) ∣ j`
    coprime_pred_self    : `Nat.Coprime (f²−1) (f²)`
    lcm_pred_self, common_multiple_ge, least_common_multiple : the least positive common multiple of `f²−1` and `f²` is
                           `(f²−1) f²`
    scale_ge             : `(f²−1) f² ≤ M f (f²−1)  ⟹  f ≤ M`

LAYER 2 (geometry, over `TraceCovering`):
    card_mul_of_filter, not_straddled_multiple, junction_eq_prod
                         : on a line `{φ = c}` through `X`, direction `u` (`‖u‖ = 1`), let `x₀ > 0` be a first common
                           junction (nothing passes through `X`, `X + x₀u`; every point strictly between is passed through
                           by an edge of one side; both sides sum to `x₀`).  If the edges of the near side in `[X, X+x₀u]`
                           all have length `p`, those of the far side all `q`, `Nat.Coprime p q`, then `x₀ = p q`.
    reframe_d            : the statement of the paper, with `TraceCovering.trace_covering` supplying the first common
                           junction, ending in `x₀ = (f²−1) f²` and `f ≤ M`.

HYPOTHESES OF `reframe_d` (nothing is hidden; there is no `sorry`):
  hφ, hX, hu, hu1   the line: `φ ≠ 0`, `φ X = c`, `φ u = 0`, `‖u‖ = 1` (`X` the apex, `u` the unit direction of a cevian).
  hℓ, hℓL           `0 < ℓ ≤ L`, `L = M f (f²−1)` the length of the cevian.
  hint              the open stretch `(X, X + L u)` is interior to the target (the cevian is interior except at its ends).
  hout0, houtL      the line leaves the target at `X` and at `X + L u` (the apex and the foot of the cevian on the base);
                    they give "no edge on the line passes through the ends" through `not_straddled_of_outside_before/after`.
  hseed             the ray from `X` starts with a tile edge `[X, X + ℓu]` of either side (the paper's "the tiles at the apex
                    lay an edge on the cevian"): NOT derived here.
  hbc               the hypothesis of the paper's (d): at the first common junction, one side lays only edges `b`, the other
                    only edges `c` (either assignment).  It is stated for every `x₀` with the properties of the first common
                    junction, which determine it uniquely.
Not part of the statement: that `D` is a dissection of `T_M(1,f)` into copies of the tile (the tile enters only through
`hbc`), that `X` is the apex, that the line is a cevian.  These are the geometric data that the consumer supplies; `L` is
the length of the cevian only through `hint`, `houtL`.
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.TraceCovering

open scoped Classical
set_option linter.unusedVariables false
open Erdos634.Geometry Erdos634.Draft.TraceCovering Set

namespace Erdos634.Draft.ReframeD

/-! ## Layer 1: arithmetic -/

theorem coprime_pred_self (f : ℕ) (hf : 1 ≤ f) : Nat.Coprime (f ^ 2 - 1) (f ^ 2) := by
  have h1 : 1 ≤ f ^ 2 := by nlinarith
  obtain ⟨n, hn⟩ : ∃ n, f ^ 2 = n + 1 := ⟨f ^ 2 - 1, (Nat.sub_add_cancel h1).symm⟩
  rw [hn, Nat.add_sub_cancel]
  exact Nat.isCoprime_iff_coprime.mp ⟨-1, 1, by push_cast; ring⟩

/-- **`i b = j c` with `b = f² − 1`, `c = f²`**: then `c ∣ i` and `b ∣ j`. -/
theorem first_common_bc (f : ℕ) (hf : 2 ≤ f) (i j : ℕ) (hi : 0 < i)
    (h : i * (f ^ 2 - 1) = j * f ^ 2) : f ^ 2 ∣ i ∧ (f ^ 2 - 1) ∣ j := by
  have hcop := coprime_pred_self f (by omega)
  constructor
  · have h2 : f ^ 2 ∣ i * (f ^ 2 - 1) := ⟨j, by rw [h]; exact Nat.mul_comm _ _⟩
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop.symm h2
  · have h2 : (f ^ 2 - 1) ∣ j * f ^ 2 := ⟨i, by rw [← h]; exact Nat.mul_comm _ _⟩
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop h2

theorem lcm_pred_self (f : ℕ) (hf : 2 ≤ f) : Nat.lcm (f ^ 2 - 1) (f ^ 2) = (f ^ 2 - 1) * f ^ 2 :=
  (coprime_pred_self f (by omega)).lcm_eq_mul

/-- a positive common multiple of `f² − 1` and `f²` is at least `(f² − 1) f²` -/
theorem common_multiple_ge (f : ℕ) (hf : 2 ≤ f) (x : ℕ) (hx : 0 < x) (hb : (f ^ 2 - 1) ∣ x)
    (hc : f ^ 2 ∣ x) : (f ^ 2 - 1) * f ^ 2 ≤ x :=
  Nat.le_of_dvd hx ((coprime_pred_self f (by omega)).mul_dvd_of_dvd_of_dvd hb hc)

/-- **The least positive common multiple of `f² − 1` and `f²` is `(f² − 1) f²`.** -/
theorem least_common_multiple (f : ℕ) (hf : 2 ≤ f) :
    IsLeast {x : ℕ | 0 < x ∧ (f ^ 2 - 1) ∣ x ∧ f ^ 2 ∣ x} ((f ^ 2 - 1) * f ^ 2) := by
  have h4 : 4 ≤ f ^ 2 := by nlinarith
  have hb : 0 < f ^ 2 - 1 := Nat.sub_pos_of_lt (by nlinarith)
  have hc : 0 < f ^ 2 := by nlinarith
  refine ⟨⟨Nat.mul_pos hb hc, dvd_mul_right _ _, dvd_mul_left _ _⟩, ?_⟩
  rintro x ⟨hx, hb, hc⟩
  exact common_multiple_ge f hf x hx hb hc

/-- **`M ≥ f`** from `b c ≤ M f b`. -/
theorem scale_ge (f M : ℕ) (hf : 2 ≤ f) (h : (f ^ 2 - 1) * f ^ 2 ≤ M * f * (f ^ 2 - 1)) : f ≤ M := by
  have h4 : 4 ≤ f ^ 2 := by nlinarith
  have hb : 0 < f ^ 2 - 1 := Nat.sub_pos_of_lt (by nlinarith)
  have h1 : (f ^ 2 - 1) * f ^ 2 ≤ (f ^ 2 - 1) * (M * f) := by
    calc (f ^ 2 - 1) * f ^ 2 ≤ M * f * (f ^ 2 - 1) := h
      _ = (f ^ 2 - 1) * (M * f) := Nat.mul_comm _ _
  have h2 : f ^ 2 ≤ M * f := Nat.le_of_mul_le_mul_left h1 hb
  have h3 : f * f ≤ M * f := by
    rw [← pow_two]
    exact h2
  exact Nat.le_of_mul_le_mul_right h3 (by omega)

/-! ## Layer 2: the geometry over `TraceCovering` -/

/-- all edges of the chain `lineChain ψ d` lying in the stretch `[X, X + x₀ u]` have length `b` -/
def AllLen {N : ℕ} (D : Dissection N) (ψ : Plane →ₗ[ℝ] ℝ) (d : ℝ) (X u : Plane) (x₀ b : ℝ) : Prop :=
  ∀ e ∈ D.lineChain ψ d, (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u) →
    dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b

/-- a sum over a filtered finset of terms all equal to `b` -/
theorem card_mul_of_filter {ι : Type*} (s : Finset ι) (P : ι → Prop) [DecidablePred P] (F : ι → ℝ)
    (b x : ℝ) (hsum : ∑ e ∈ s.filter P, F e = x) (h : ∀ e ∈ s, P e → F e = b) :
    ((s.filter P).card : ℝ) * b = x := by
  have h2 : ∑ e ∈ s.filter P, F e = ∑ e ∈ s.filter P, b :=
    Finset.sum_congr rfl (fun e he => h e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2)
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  exact h2.symm.trans hsum

section Geo

variable {N : ℕ} {D : Dissection N} {X u : Plane} {φ ψ : Plane →ₗ[ℝ] ℝ} {c d : ℝ}

/-- **On one side, a multiple of the edge length is not passed through.**  Let `[X, X + x₀u]` be a wall stretch of the line
`{φ = c}` (the open stretch is interior to the target and meets no tile interior) whose ends are not passed through by an
edge of the side `lineChain ψ d`, and let every edge of that side lying in the stretch have length `b`.  Then no edge of
that side passes through a point at a positive multiple `k b < x₀` of `b` from `X`: the junctions of the side are the
multiples of `b`. -/
theorem not_straddled_multiple (hψ : ψ ≠ 0) (hgd : ∀ y, ψ y = d ↔ φ y = c) (hφ : φ ≠ 0) (hX : φ X = c)
    (hu : φ u = 0) (hu1 : ‖u‖ = 1) {x₀ : ℝ} (hx0 : 0 ≤ x₀)
    (hint : ∀ x ∈ Ioo 0 x₀, X + x • u ∈ interior D.target.carrier)
    (hwall : ∀ x ∈ Ioo 0 x₀, ∀ i, X + x • u ∉ interior (D.tile i).carrier)
    (h0 : ¬ Straddled D ψ d X) (h1 : ¬ Straddled D ψ d (X + x₀ • u))
    {b : ℝ} (hb : 0 < b) (hlen : AllLen D ψ d X u x₀ b)
    (k : ℕ) (hk : 0 < (k : ℝ) * b) (hk' : (k : ℝ) * b < x₀) :
    ¬ Straddled D ψ d (X + ((k : ℝ) * b) • u) := by
  have hu0 := ne_zero_of_norm hu1
  intro hstr
  rw [str_iff hgd hφ hX hu hu0] at hstr
  obtain ⟨e, he, hlo, hhi⟩ := hstr
  obtain ⟨h0e, h1e⟩ := onLine hgd he
  obtain ⟨hlt, hedge, -, hdist⟩ := edge_data hφ hX hu hu0 h0e h1e
  have hlo0 : 0 ≤ lo D X u e := by
    by_contra hc
    have hc' : lo D X u e < 0 := not_le.mp hc
    apply h0
    have := (str_iff hgd hφ hX hu hu0 0).mpr ⟨e, he, hc', by linarith⟩
    simpa using this
  have hhix : hi D X u e ≤ x₀ := by
    by_contra hc
    have hc' : x₀ < hi D X u e := not_le.mp hc
    apply h1
    exact (str_iff hgd hφ hX hu hu0 x₀).mpr ⟨e, he, by linarith, hc'⟩
  have hin : (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u) := by
    have := (inside_iff hgd hφ hX hu hu0 he hx0).mpr ⟨hlo0, hhix⟩
    rw [zero_smul, add_zero] at this
    exact this
  have hlenE : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b := hlen e he hin
  have hhl : hi D X u e - lo D X u e = b := (hdist hu1).symm.trans hlenE
  have key : ∀ p, (p = (D.tile e.1).pts e.2 ∨ p = (D.tile e.1).pts (e.2 + 1)) →
      ∃ n : ℕ, par X u p = (n : ℝ) * b := by
    intro p hp
    have hpline : φ p = c := by rcases hp with rfl | rfl <;> assumption
    have hpe := par_spec (exists_param hφ hX hu hu0 hpline)
    have hbd : lo D X u e ≤ par X u p ∧ par X u p ≤ hi D X u e := by
      rcases hp with rfl | rfl
      · simp only [lo, hi]
        exact ⟨min_le_left _ _, le_max_left _ _⟩
      · simp only [lo, hi]
        exact ⟨min_le_right _ _, le_max_right _ _⟩
    set a := par X u p with ha
    have ha0 : 0 ≤ a := le_trans hlo0 hbd.1
    have hax : a ≤ x₀ := le_trans hbd.2 hhix
    have hseg0 : segment ℝ X (X + x₀ • u) = (fun x : ℝ => X + x • u) '' Icc 0 x₀ := by
      have h := segment_param (X := X) (u := u) 0 x₀
      rw [zero_smul, add_zero, min_eq_left hx0, max_eq_right hx0] at h
      exact h
    have hpmem : p ∈ segment ℝ X (X + x₀ • u) := by
      rw [hseg0]
      exact ⟨a, ⟨ha0, hax⟩, hpe.symm⟩
    have hdXp : dist X p = a := by
      have h := dist_param (X := X) (u := u) hu1 0 a
      rw [zero_smul, add_zero, ← hpe] at h
      rw [h, max_eq_right ha0, min_eq_left ha0, sub_zero]
    have hps := junction_partial_sum hψ hgd hφ hX hu hu1 hx0 hint hwall h0 he hin hp
    have hall : ∀ e' ∈ (D.lineChain ψ d).filter
        (fun e' => (D.tile e'.1).edge e'.2 ⊆ segment ℝ X p),
        dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = b := by
      intro e' he'
      obtain ⟨he'1, he'2⟩ := Finset.mem_filter.mp he'
      refine hlen e' he'1 (he'2.trans ?_)
      exact (convex_segment X (X + x₀ • u)).segment_subset (left_mem_segment ℝ _ _) hpmem
    rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, hdXp] at hps
    exact ⟨_, hps.symm⟩
  obtain ⟨n0, hn0⟩ := key _ (Or.inl rfl)
  obtain ⟨n1, hn1⟩ := key _ (Or.inr rfl)
  have hlo_mult : ∃ n : ℕ, lo D X u e = (n : ℝ) * b := by
    rcases min_choice (par X u ((D.tile e.1).pts e.2)) (par X u ((D.tile e.1).pts (e.2 + 1))) with h | h
    · exact ⟨n0, by simp only [lo]; rw [h]; exact hn0⟩
    · exact ⟨n1, by simp only [lo]; rw [h]; exact hn1⟩
  obtain ⟨n, hn⟩ := hlo_mult
  have hhi' : hi D X u e = (n : ℝ) * b + b := by linarith
  rw [hn] at hlo
  rw [hhi'] at hhi
  have h1' : (n : ℝ) < k := lt_of_mul_lt_mul_right hlo hb.le
  have h2' : (k : ℝ) < n + 1 :=
    lt_of_mul_lt_mul_right (by linarith : (k : ℝ) * b < ((n : ℝ) + 1) * b) hb.le
  have h1'' : n < k := by exact_mod_cast h1'
  have h2'' : k < n + 1 := by exact_mod_cast h2'
  omega

/-- **The first common junction of a `p`-side and a `q`-side is at `p q`.**  On the line `{φ = c}` through `X` with unit
direction `u`, let `x₀ > 0` have the properties of the first common junction (what `trace_covering` delivers): no edge of
either side passes through `X` or `X + x₀u`, every point strictly between is passed through by an edge of one side, and the
edges of each side lying in `[X, X + x₀u]` have total length `x₀`.  If those of the near side all have length `p`, those
of the far side all have length `q`, and `Nat.Coprime p q`, then `x₀ = p q`. -/
theorem junction_eq_prod (hφ : φ ≠ 0) (hX : φ X = c) (hu : φ u = 0) (hu1 : ‖u‖ = 1) {x₀ : ℝ}
    (hx0 : 0 < x₀)
    (hint : ∀ x ∈ Ioo 0 x₀, X + x • u ∈ interior D.target.carrier)
    (hstart : ¬ Straddled D φ c X ∧ ¬ Straddled D (-φ) (-c) X)
    (hjn : ¬ Straddled D φ c (X + x₀ • u) ∧ ¬ Straddled D (-φ) (-c) (X + x₀ • u))
    (hfirst : ∀ y ∈ Ioo 0 x₀, Straddled D φ c (X + y • u) ∨ Straddled D (-φ) (-c) (X + y • u))
    (hsum₁ : ∑ e ∈ (D.lineChain φ c).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u)),
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = x₀)
    (hsum₂ : ∑ e ∈ (D.lineChain (-φ) (-c)).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u)),
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = x₀)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hcop : Nat.Coprime p q)
    (hnear : AllLen D φ c X u x₀ (p : ℝ)) (hfar : AllLen D (-φ) (-c) X u x₀ (q : ℝ)) :
    x₀ = (p : ℝ) * q := by
  have hu0 := ne_zero_of_norm hu1
  have hφ' : (-φ) ≠ 0 := neg_ne_zero.mpr hφ
  have hgd2 : ∀ y, (-φ) y = -c ↔ φ y = c := fun y => neg_iff y
  have hwall : ∀ x ∈ Ioo 0 x₀, ∀ i, X + x • u ∉ interior (D.tile i).carrier := by
    intro x hx i hi
    rcases hfirst x hx with ⟨e, he, hm⟩ | ⟨e, he, hm⟩
    · exact D.edge_point_not_interior (j := e.1) (k := e.2) (openSegment_subset_segment ℝ _ _ hm) i hi
    · exact D.edge_point_not_interior (j := e.1) (k := e.2) (openSegment_subset_segment ℝ _ _ hm) i hi
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, (n : ℝ) * p = x₀ :=
    ⟨_, card_mul_of_filter _ _ _ (p : ℝ) x₀ hsum₁ hnear⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n : ℕ, (n : ℝ) * q = x₀ :=
    ⟨_, card_mul_of_filter _ _ _ (q : ℝ) x₀ hsum₂ hfar⟩
  have hnn : n₁ * p = n₂ * q := by
    have h : ((n₁ * p : ℕ) : ℝ) = ((n₂ * q : ℕ) : ℝ) := by
      push_cast
      rw [hn₁, hn₂]
    exact_mod_cast h
  have hqdvd : q ∣ n₁ * p := ⟨n₂, by rw [hnn, Nat.mul_comm]⟩
  obtain ⟨a, ha⟩ : q ∣ n₁ := Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hqdvd
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hn1R : (n₁ : ℝ) = (q : ℝ) * (a : ℝ) := by exact_mod_cast ha
  have ha1 : 1 ≤ a := by
    by_contra hc
    have ha0 : a = 0 := by omega
    have hx00 : x₀ = 0 := by
      rw [← hn₁, hn1R, ha0]
      simp
    linarith
  have ha2 : a < 2 := by
    by_contra hc
    have hc' : 2 ≤ a := not_lt.mp hc
    have haR : (2 : ℝ) ≤ a := by exact_mod_cast hc'
    have hk : 0 < (q : ℝ) * p := mul_pos hqR hpR
    have hk' : (q : ℝ) * p < x₀ := by
      rw [← hn₁, hn1R]
      nlinarith [mul_nonneg hk.le (sub_nonneg.2 haR)]
    have hN := not_straddled_multiple hφ (fun _ => Iff.rfl) hφ hX hu hu1 hx0.le hint hwall
      hstart.1 hjn.1 hpR hnear q hk hk'
    have hk2 : 0 < (p : ℝ) * q := mul_pos hpR hqR
    have hk2' : (p : ℝ) * q < x₀ := by
      rw [mul_comm]
      exact hk'
    have hF := not_straddled_multiple hφ' hgd2 hφ hX hu hu1 hx0.le hint hwall
      hstart.2 hjn.2 hqR hfar p hk2 hk2'
    rw [mul_comm (p : ℝ) (q : ℝ)] at hF
    rcases hfirst ((q : ℝ) * p) ⟨hk, hk'⟩ with h | h
    · exact hN h
    · exact hF h
  have ha1' : a = 1 := by omega
  rw [ha1', Nat.cast_one, mul_one] at hn1R
  rw [← hn₁, hn1R]
  ring

end Geo

/-! ## The statement of (d) -/

theorem reframe_d {N : ℕ} {D : Dissection N} {X u : Plane} {φ : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (f M : ℕ) (hf : 2 ≤ f) (hφ : φ ≠ 0) (hX : φ X = c) (hu : φ u = 0) (hu1 : ‖u‖ = 1)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓL : ℓ ≤ (M : ℝ) * f * ((f : ℝ) ^ 2 - 1))
    (hint : ∀ x ∈ Ioo 0 ((M : ℝ) * f * ((f : ℝ) ^ 2 - 1)), X + x • u ∈ interior D.target.carrier)
    (hout0 : ∀ t : ℝ, t < 0 → X + t • u ∉ D.target.carrier)
    (houtL : ∀ t : ℝ, (M : ℝ) * f * ((f : ℝ) ^ 2 - 1) < t → X + t • u ∉ D.target.carrier)
    (hseed : ∃ e ∈ D.lineChain φ c ∪ D.lineChain (-φ) (-c),
      (D.tile e.1).edge e.2 = segment ℝ X (X + ℓ • u))
    (hbc : ∀ x₀ : ℝ, ℓ ≤ x₀ → x₀ ≤ (M : ℝ) * f * ((f : ℝ) ^ 2 - 1) →
      ¬ Straddled D φ c (X + x₀ • u) → ¬ Straddled D (-φ) (-c) (X + x₀ • u) →
      (∀ y ∈ Ioo 0 x₀, Straddled D φ c (X + y • u) ∨ Straddled D (-φ) (-c) (X + y • u)) →
      (AllLen D φ c X u x₀ ((f : ℝ) ^ 2 - 1) ∧ AllLen D (-φ) (-c) X u x₀ ((f : ℝ) ^ 2)) ∨
      (AllLen D φ c X u x₀ ((f : ℝ) ^ 2) ∧ AllLen D (-φ) (-c) X u x₀ ((f : ℝ) ^ 2 - 1))) :
    ∃ x₀ : ℝ, x₀ = ((f : ℝ) ^ 2 - 1) * (f : ℝ) ^ 2 ∧ ℓ ≤ x₀ ∧
      x₀ ≤ (M : ℝ) * f * ((f : ℝ) ^ 2 - 1) ∧ f ≤ M := by
  have hu0 := ne_zero_of_norm hu1
  have hφ' : (-φ) ≠ 0 := neg_ne_zero.mpr hφ
  have hgd2 : ∀ y, (-φ) y = -c ↔ φ y = c := fun y => neg_iff y
  have hstart : ¬ Straddled D φ c X ∧ ¬ Straddled D (-φ) (-c) X := by
    constructor
    · have h := not_straddled_of_outside_before (D := D) (g := φ) (d := c) (fun _ => Iff.rfl) hφ hX
        hu hu0 (x₀ := 0) hout0
      simpa using h
    · have h := not_straddled_of_outside_before (D := D) (g := -φ) (d := -c) hgd2 hφ hX
        hu hu0 (x₀ := 0) hout0
      simpa using h
  have hend : ¬ Straddled D φ c (X + ((M : ℝ) * f * ((f : ℝ) ^ 2 - 1)) • u) ∧
      ¬ Straddled D (-φ) (-c) (X + ((M : ℝ) * f * ((f : ℝ) ^ 2 - 1)) • u) :=
    ⟨not_straddled_of_outside_after (D := D) (g := φ) (d := c) (fun _ => Iff.rfl) hφ hX hu hu0
      (x₀ := (M : ℝ) * f * ((f : ℝ) ^ 2 - 1)) houtL,
     not_straddled_of_outside_after (D := D) (g := -φ) (d := -c) hgd2 hφ hX hu hu0
      (x₀ := (M : ℝ) * f * ((f : ℝ) ^ 2 - 1)) houtL⟩
  obtain ⟨x₀, hℓx, hxL, hn1, hn2, hfirst, hs1, hs2⟩ :=
    trace_covering hφ hX hu hu1 hℓ hℓL hint hstart hend hseed
  have hx0 : 0 < x₀ := lt_of_lt_of_le hℓ hℓx
  have hint' : ∀ x ∈ Ioo 0 x₀, X + x • u ∈ interior D.target.carrier :=
    fun x hx => hint x ⟨hx.1, lt_of_lt_of_le hx.2 hxL⟩
  have h1 : 1 ≤ f ^ 2 := by nlinarith
  have hpR : ((f ^ 2 - 1 : ℕ) : ℝ) = (f : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hqR : ((f ^ 2 : ℕ) : ℝ) = (f : ℝ) ^ 2 := by push_cast; ring
  have hcop := coprime_pred_self f (by omega)
  have hpos : 0 < f ^ 2 - 1 := Nat.sub_pos_of_lt (by nlinarith)
  have hqpos : 0 < f ^ 2 := by nlinarith
  have hxbc : x₀ = ((f : ℝ) ^ 2 - 1) * (f : ℝ) ^ 2 := by
    rcases hbc x₀ hℓx hxL hn1 hn2 hfirst with ⟨hnear, hfar⟩ | ⟨hnear, hfar⟩
    · rw [← hpR] at hnear
      rw [← hqR] at hfar
      have h := junction_eq_prod hφ hX hu hu1 hx0 hint' hstart ⟨hn1, hn2⟩ hfirst hs1 hs2
        (p := f ^ 2 - 1) (q := f ^ 2) hpos hqpos hcop hnear hfar
      rw [h, hpR, hqR]
    · rw [← hqR] at hnear
      rw [← hpR] at hfar
      have h := junction_eq_prod hφ hX hu hu1 hx0 hint' hstart ⟨hn1, hn2⟩ hfirst hs1 hs2
        (p := f ^ 2) (q := f ^ 2 - 1) hqpos hpos hcop.symm hnear hfar
      rw [h, hpR, hqR]
      ring
  refine ⟨x₀, hxbc, hℓx, hxL, ?_⟩
  apply scale_ge f M hf
  have hcast : (((f ^ 2 - 1) * f ^ 2 : ℕ) : ℝ) ≤ ((M * f * (f ^ 2 - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, hpR, hqR]
    linarith [hxbc, hxL]
  exact Nat.cast_le.mp hcast

end Erdos634.Draft.ReframeD

#print axioms Erdos634.Draft.ReframeD.first_common_bc
#print axioms Erdos634.Draft.ReframeD.lcm_pred_self
#print axioms Erdos634.Draft.ReframeD.common_multiple_ge
#print axioms Erdos634.Draft.ReframeD.least_common_multiple
#print axioms Erdos634.Draft.ReframeD.scale_ge
#print axioms Erdos634.Draft.ReframeD.not_straddled_multiple
#print axioms Erdos634.Draft.ReframeD.junction_eq_prod
#print axioms Erdos634.Draft.ReframeD.reframe_d
