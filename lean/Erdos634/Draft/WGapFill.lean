/-
Draft/WGapFill.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (Lemma 3.2, wedge uses W1-W13).
Not imported by any aggregate.  Module W3d: WEDGE API parts C (edge table) and D (the filler is not a known tile).

* `same_third`        : a point is determined by its distances to two points and the side of the line through them (two circles + side).
* `tri_cross_ne`      : three distinct vertices of a tile are not collinear.
* `sides_of_alpha`    : a tile with the angle `α` at a vertex has the opposite side `a = e f` and the two adjacent sides `{b, c}` (either order).
* `off_ray_of_cross_ne`, `off_ray_of_dot_neg`, `known_off_ray`: PART D.  The sign facts for a KNOWN tile `k` (vertices `X, P_k, Q_k`): neither `P_k`
  nor `Q_k` lies on the open ray `X + ℝ₊ (Y - X)`.  Each is one cross-product sign (or one dot-product sign) of a known tile's other vertices.
* `filler_alpha`      : the one-lemma instantiation of Lemma 3.2 for a wedge of size `α` beside the ray `X → Y` (the known tile `t₀` is on the left,
  the free wedge on the right): there is a tile `τ ∉ K` with vertices `X`, `P` on the ray, `W` strictly right of the line, angle `α` at `X`, and
  `{|XP|, |XW|} = {b, c}`, `|PW| = a`.   Every use W2, W3 (and, with `wedge_beta`/`wedge_gamma`... variants, W1, W9) is this lemma plus sign facts.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapRay
import Erdos634.SixPlacements

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

variable {N : ℕ} {D : CongruentDissection N}

/-- a point is determined by its distances to two distinct points and the (strict) side of the line through them -/
theorem same_third {X P Z W : Plane} (hXP : X ≠ P) (h1 : dist Z X = dist W X) (h2 : dist Z P = dist W P)
    (hz : cross (P - X) (Z - X) < 0) (hw : cross (P - X) (W - X) < 0) : Z = W := by
  have e1 := dist_sq_pts Z X
  have e1' := dist_sq_pts W X
  have e2 := dist_sq_pts Z P
  have e2' := dist_sq_pts W P
  rw [h1] at e1
  rw [h2] at e2
  have hu : (P 0 - X 0) ^ 2 + (P 1 - X 1) ^ 2 ≠ 0 := by
    intro h
    apply hXP
    have h0 : P 0 - X 0 = 0 := by nlinarith [sq_nonneg (P 0 - X 0), sq_nonneg (P 1 - X 1)]
    have h1' : P 1 - X 1 = 0 := by nlinarith [sq_nonneg (P 0 - X 0), sq_nonneg (P 1 - X 1)]
    ext i; fin_cases i
    · simp; linarith
    · simp; linarith
  have hupos : 0 < (P 0 - X 0) ^ 2 + (P 1 - X 1) ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hu)
  simp only [cross, PiLp.sub_apply] at hz hw
  -- dot products agree
  have hdot : (P 0 - X 0) * (Z 0 - X 0) + (P 1 - X 1) * (Z 1 - X 1) =
      (P 0 - X 0) * (W 0 - X 0) + (P 1 - X 1) * (W 1 - X 1) := by nlinarith
  -- squared crosses agree (Lagrange identity)
  have hc2 : ((P 0 - X 0) * (Z 1 - X 1) - (P 1 - X 1) * (Z 0 - X 0)) ^ 2 =
      ((P 0 - X 0) * (W 1 - X 1) - (P 1 - X 1) * (W 0 - X 0)) ^ 2 := by
    have l1 : ((P 0 - X 0) * (Z 1 - X 1) - (P 1 - X 1) * (Z 0 - X 0)) ^ 2 =
        ((P 0 - X 0) ^ 2 + (P 1 - X 1) ^ 2) * ((Z 0 - X 0) ^ 2 + (Z 1 - X 1) ^ 2) -
        ((P 0 - X 0) * (Z 0 - X 0) + (P 1 - X 1) * (Z 1 - X 1)) ^ 2 := by ring
    have l2 : ((P 0 - X 0) * (W 1 - X 1) - (P 1 - X 1) * (W 0 - X 0)) ^ 2 =
        ((P 0 - X 0) ^ 2 + (P 1 - X 1) ^ 2) * ((W 0 - X 0) ^ 2 + (W 1 - X 1) ^ 2) -
        ((P 0 - X 0) * (W 0 - X 0) + (P 1 - X 1) * (W 1 - X 1)) ^ 2 := by ring
    rw [l1, l2, hdot]
    have : (Z 0 - X 0) ^ 2 + (Z 1 - X 1) ^ 2 = (W 0 - X 0) ^ 2 + (W 1 - X 1) ^ 2 := by
      rw [← e1, ← e1']
    rw [this]
  have hcr : (P 0 - X 0) * (Z 1 - X 1) - (P 1 - X 1) * (Z 0 - X 0) =
      (P 0 - X 0) * (W 1 - X 1) - (P 1 - X 1) * (W 0 - X 0) := by
    have := (sq_eq_sq_iff_abs_eq_abs _ _).mp hc2
    rw [abs_of_neg hz, abs_of_neg hw] at this
    linarith
  have d0 : Z 0 = W 0 := by
    have : ((P 0 - X 0) ^ 2 + (P 1 - X 1) ^ 2) * (Z 0 - W 0) = 0 := by
      linear_combination (P 0 - X 0) * hdot - (P 1 - X 1) * hcr
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hu
    · linarith
  have d1 : Z 1 = W 1 := by
    have : ((P 0 - X 0) ^ 2 + (P 1 - X 1) ^ 2) * (Z 1 - W 1) = 0 := by
      linear_combination (P 1 - X 1) * hdot + (P 0 - X 0) * hcr
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hu
    · linarith
  ext i; fin_cases i
  · simpa using d0
  · simpa using d1

/-- three distinct vertices of a tile are not collinear -/
theorem tri_cross_ne (T : Tri) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n) (hmn : m ≠ n) :
    cross (T.pts m - T.pts k) (T.pts n - T.pts k) ≠ 0 := by
  have hperm : ∀ k m n : Fin 3, k ≠ m → k ≠ n → m ≠ n →
      (k = 0 ∧ m = 1 ∧ n = 2) ∨ (k = 0 ∧ m = 2 ∧ n = 1) ∨ (k = 1 ∧ m = 0 ∧ n = 2) ∨
      (k = 1 ∧ m = 2 ∧ n = 0) ∨ (k = 2 ∧ m = 0 ∧ n = 1) ∨ (k = 2 ∧ m = 1 ∧ n = 0) := by decide
  intro h
  apply T.det_ne_zero
  unfold Tri.det
  simp only [cross, PiLp.sub_apply] at h
  rcases hperm k m n hkm hkn hmn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp only [PiLp.sub_apply] <;>
    first | linear_combination h | linear_combination -h

section edges

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **PART C (edge table, angle `α`).**  Distinct vertices `X = pts k`, `P = pts m`, `W = pts j` of a tile with the angle `α` at `X`: the opposite
side is `a = e f` and the adjacent sides are `b, c` in either order. -/
theorem sides_of_alpha (S : SetupG D e f α β γ L ax ay) (i : Fin N) {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j)
    (hα : (D.tile i).localAngle ((D.tile i).pts k) = α) :
    dist ((D.tile i).pts m) ((D.tile i).pts j) = (e : ℝ) * f ∧
    ((dist ((D.tile i).pts k) ((D.tile i).pts m) = (f : ℝ) ^ 2 ∧
        dist ((D.tile i).pts k) ((D.tile i).pts j) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
      (dist ((D.tile i).pts k) ((D.tile i).pts m) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
        dist ((D.tile i).pts k) ((D.tile i).pts j) = (f : ℝ) ^ 2)) := by
  have hA := S.hA
  obtain ⟨hα0, hβ0, hαγ, hβγ, -, -, hγπ, -⟩ := Erdos634.Draft.WGapAngles.angle_ineqs hA
  have hang := angle_at_vertexG D S.tile S.hM i hkm hkj hmj
  have hopp : dist ((D.tile i).pts m) ((D.tile i).pts j) = (e : ℝ) * f := by
    rcases vertex_dist_casesG D S.hM i hmj with d | d | d
    · exact d
    · have := hang.2.1 d; rw [hα] at this; exact absurd this hA.hαβ
    · have := hang.2.2 d; rw [hα] at this; exact absurd this hαγ.ne
  refine ⟨hopp, ?_⟩
  have hsp := SixPlacements.sides_perm_of_congruent (D.tiles_congruent i) (M := D.model)
    (a := (f : ℝ) ^ 2) (b := (e : ℝ) * f) (c := (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (model_distsG D S.hM).1 (model_distsG D S.hM).2.1 (by rw [dist_comm]; exact (model_distsG D S.hM).2.2)
    k m j hkm hkj hmj
  have hef : (e : ℝ) < f := by exact_mod_cast S.hef
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hf0 : (0 : ℝ) < f := by linarith
  have h1 : (f : ℝ) ^ 2 ≠ (e : ℝ) * f := by nlinarith
  have h2 : (f : ℝ) ^ 2 ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have h3 : (e : ℝ) * f ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    intro h
    -- a = b is excluded by the angle data (alpha != beta)
    have hk := angle_at_vertexG D S.tile S.hM i hkm hkj hmj
    have : (D.tile i).localAngle ((D.tile i).pts k) = β := by
      apply hk.2.1; rw [hopp, h]
    rw [hα] at this; exact hA.hαβ this
  rcases hsp with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
  · exact Or.inl ⟨a1, a2⟩
  · exact Or.inr ⟨a1, a2⟩
  · exact absurd (hopp.symm.trans a3) h3
  · exact absurd (hopp.symm.trans a3) h3
  · exact absurd (hopp.symm.trans a3) (fun h => h1 h.symm)
  · exact absurd (hopp.symm.trans a3) (fun h => h1 h.symm)

end edges

/-! ## PART D: sign facts that put a known tile off the open ray -/

theorem off_ray_of_cross_ne {X Y P : Plane} (h : cross (Y - X) (P - X) ≠ 0) :
    ∀ s : ℝ, 0 < s → P ≠ AffineMap.lineMap X Y s := by
  intro s hs hP
  apply h
  rw [hP, AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right]
  rw [cross_smul_right]
  simp

theorem off_ray_of_dot_neg {X Y P : Plane} (h : (Y 0 - X 0) * (P 0 - X 0) + (Y 1 - X 1) * (P 1 - X 1) < 0) :
    ∀ s : ℝ, 0 < s → P ≠ AffineMap.lineMap X Y s := by
  intro s hs hP
  rw [hP, AffineMap.lineMap_apply] at h
  simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, add_sub_cancel_right] at h
  nlinarith [mul_nonneg hs.le (add_nonneg (sq_nonneg (Y 0 - X 0)) (sq_nonneg (Y 1 - X 1)))]

/-- a known tile `k` with the vertex `X` and the other vertices `P, Q` off the open ray has NO vertex on the open ray (`X` itself is not on it) -/
theorem known_off_ray {X Y P Q : Plane} (hXY : X ≠ Y) {k : Fin N} (hV : HasV D k X P Q)
    (hP : ∀ s : ℝ, 0 < s → P ≠ AffineMap.lineMap X Y s) (hQ : ∀ s : ℝ, 0 < s → Q ≠ AffineMap.lineMap X Y s) :
    ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap X Y s := by
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ := hV
  intro j s hs
  rcases fin3_cover a b c hab hac hbc j with rfl | rfl | rfl
  · rw [ha]
    intro h
    have h2 : s • (Y - X) = 0 := by
      have h' := h
      rw [AffineMap.lineMap_apply] at h'
      simp only [vsub_eq_sub, vadd_eq_add] at h'
      have h3 := congrArg (fun z => z - X) h'
      simpa using h3.symm
    rcases smul_eq_zero.mp h2 with h4 | h4
    · exact hs.ne' h4
    · exact hXY (sub_eq_zero.mp h4).symm
  · rw [hb]; exact hP s hs
  · rw [hc]; exact hQ s hs

theorem cross_smul_left' (t : ℝ) (u v : Plane) : cross (t • u) v = t * cross u v := by
  simp [cross]; ring

/-- the angle of a tile at a vertex is `α`, `β` or `γ` -/
theorem vertex_angle_cases {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay) (i : Fin N) {k m j : Fin 3}
    (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) :
    (D.tile i).localAngle ((D.tile i).pts k) = α ∨ (D.tile i).localAngle ((D.tile i).pts k) = β ∨
      (D.tile i).localAngle ((D.tile i).pts k) = γ := by
  have hang := angle_at_vertexG D S.tile S.hM i hkm hkj hmj
  rcases vertex_dist_casesG D S.hM i hmj with d | d | d
  · exact Or.inl (hang.1 d)
  · exact Or.inr (Or.inl (hang.2.1 d))
  · exact Or.inr (Or.inr (hang.2.2 d))

section filler

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **FILLER, wedge `α`** (W2, W3).  Setting as `ray_filler`: the known tile `t₀` (counted in `K`) lies on the LEFT of the ray `X → Y`; the other
tiles of `K` have no vertex on the open ray (PART D, from sign facts); the free wedge is `α`.  Then the tile adjacent to the ray is an `α`-tile
`τ ∉ K`, with vertices `X`, `P` (on the ray), `W` (right of the line), `|PW| = a`, `{|XP|, |XW|} = {b, c}`. -/
theorem filler_alpha (S : SetupG D e f α β γ L ax ay) {X Y Z P' : Plane} {t₀ : Fin N} (hXY : X ≠ Y)
    (hV : HasV D t₀ X Y Z) (hZ : 0 < cross (Y - X) (Z - X))
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    (hint : openSegment ℝ X Y ⊆ interior D.target.carrier)
    (hclamp : ∀ ed ∈ D.lineChain (crossL (Y - X)) (cross (Y - X) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y)
    {Ω : ℝ} (hΩ : ∑ i, (D.tile i).localAngle X = Ω) (K : Finset (Fin N))
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - α)
    (hKray : ∀ k ∈ K, k ≠ t₀ → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap X Y s) :
    ∃ τ : Fin N, τ ∉ K ∧ ∃ P W : Plane, HasV D τ X P W ∧ (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap X Y s) ∧
      cross (Y - X) (W - X) < 0 ∧ (D.tile τ).localAngle X = α ∧ dist P W = (e : ℝ) * f ∧
      ((dist X P = (f : ℝ) ^ 2 ∧ dist X W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
        (dist X P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist X W = (f : ℝ) ^ 2)) := by
  obtain ⟨τ, k, m, t, hτ, hkm, hk, ht, hm, hle⟩ := ray_filler D hXY hV hZ hP' hXP hint hclamp
  obtain ⟨n, hnk, hnm⟩ := fin3_third k m hkm
  have hkn : k ≠ n := hnk.symm
  have hmn : m ≠ n := hnm.symm
  have hτK : τ ∉ K := fun h => hKray τ h hτ m t ht hm
  have hne := tri_cross_ne (D.tile τ) hkm hkn hmn
  have hmX : (D.tile τ).pts m - (D.tile τ).pts k = t • (Y - X) := by
    rw [hm, hk, AffineMap.lineMap_apply]; simp
  have hneg : cross (Y - X) ((D.tile τ).pts n - X) < 0 := by
    rcases lt_or_eq_of_le (hle n) with h | h
    · exact h
    · exfalso; apply hne
      rw [hmX, cross_smul_left', hk, h]; ring
  have hvc := vertex_angle_cases S τ hkm hkn hmn
  have hcnt := wedge_alpha S hΩ hK (angles_lt_pi S).1
  have hmemτ : τ ∈ Finset.univ \ K := by simp [hτK]
  have hangα : (D.tile τ).localAngle ((D.tile τ).pts k) = α := by
    rcases hvc with h | h | h
    · exact h
    · exfalso
      have h0 := hcnt.2.1
      unfold cnt at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      exact h0 hmemτ (by rw [← hk]; exact h)
    · exfalso
      have h0 := hcnt.2.2
      unfold cnt at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      exact h0 hmemτ (by rw [← hk]; exact h)
  obtain ⟨hopp, hsd⟩ := sides_of_alpha S τ hkm hkn hmn hangα
  rw [hk] at hangα hsd
  refine ⟨τ, hτK, (D.tile τ).pts m, (D.tile τ).pts n, ⟨k, m, n, hkm, hkn, hmn, hk, rfl, rfl⟩,
    ⟨t, ht, hm⟩, hneg, hangα, hopp, ?_⟩
  rcases hsd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

end filler

end Erdos634.Draft.WGapStmt
