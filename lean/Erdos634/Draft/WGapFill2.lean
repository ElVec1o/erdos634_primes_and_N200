/-
Draft/WGapFill2.lean -- written 15 November 2026 (session 3).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (Lemma 3.2, uses W1, W4, W7, W9).
Not imported by any aggregate.  Module W5a: the wedge API for the angles `β` and `γ` (the `α` case is `WGapFill`).

* `fill_2beta`, `wedge_2beta` : a wedge of size `2β` is `{β, β}` (finding F7: the free angle at `p(0,j)` is `2β`).
* `sides_of_beta`  : a tile with angle `β` at a vertex has opposite side `b = f² - e²` and adjacent sides `{a, c}` (either order).
* `sides_of_gamma` : a tile with angle `γ` at a vertex has opposite side `c = f²` and adjacent sides `{a, b}`.
* `filler_core`    : the tile beside the ray `X → Y` (the hypotheses of `ray_filler`, no angle count): a tile `τ ∉ K` with vertex `X`, a vertex `P` on the open ray,
  third vertex strictly right, and its angle at `X` is `α`, `β` or `γ`.
* `filler_beta`    : if no tile outside `K` shows `α` or `γ` at `X`, the filler is a `β`-tile with `|PW| = b`, `{|XP|, |XW|} = {a, c}`.
* `filler_gamma`   : same for `γ`-only (`|PW| = c`, `{|XP|,|XW|} = {a, b}`); the `α`-case is `WGapFill.filler_alpha`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapFill

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

section arith

variable {α β γ : ℝ}

/-- a wedge of size `2β` is `{β, β}` -/
theorem fill_2beta (hA : AngleData α β γ) {x y z : ℕ}
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = 2 * β) : x = 0 ∧ y = 2 ∧ z = 0 := by
  have h2 := (Erdos634.Draft.WGapAngles.ledger2 hA x y z 0 2 0 0).mp (by
    have : ((x : ℤ) : ℝ) * α + ((y : ℤ) : ℝ) * β + ((z : ℤ) : ℝ) * γ =
        ((0 : ℤ) : ℝ) * α + ((2 : ℤ) : ℝ) * β + ((0 : ℤ) : ℝ) * γ + ((0 : ℤ) : ℝ) * Real.pi := by
      push_cast; linarith
    exact this)
  omega

end arith

section cor

variable {e f : ℕ} {α β γ L ax ay : ℝ} {X : Plane} {Ω : ℝ} {K : Finset (Fin N)}

theorem two_beta_lt_pi (S : SetupG D e f α β γ L ax ay) : 2 * β < Real.pi := by
  have hr := S.hA.hrel
  have := S.hA.hα
  linarith

theorem wedge_2beta (S : SetupG D e f α β γ L ax ay) (hΩ : ∑ i, (D.tile i).localAngle X = Ω)
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - 2 * β) :
    cnt D K X α = 0 ∧ cnt D K X β = 2 ∧ cnt D K X γ = 0 := by
  obtain ⟨x, y, z, h, hx, hy, hz, -⟩ := wedge_count S hΩ K hK (two_beta_lt_pi S)
  have := fill_2beta S.hA h
  unfold cnt; omega

/-- **PART C, angle `β`**: opposite side `b`, adjacent sides `{a, c}` -/
theorem sides_of_beta (S : SetupG D e f α β γ L ax ay) (i : Fin N) {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j)
    (hβ : (D.tile i).localAngle ((D.tile i).pts k) = β) :
    dist ((D.tile i).pts m) ((D.tile i).pts j) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
    ((dist ((D.tile i).pts k) ((D.tile i).pts m) = (e : ℝ) * f ∧
        dist ((D.tile i).pts k) ((D.tile i).pts j) = (f : ℝ) ^ 2) ∨
      (dist ((D.tile i).pts k) ((D.tile i).pts m) = (f : ℝ) ^ 2 ∧
        dist ((D.tile i).pts k) ((D.tile i).pts j) = (e : ℝ) * f)) := by
  have hA := S.hA
  obtain ⟨hα0, hβ0, hαγ, hβγ, -, -, hγπ, -⟩ := Erdos634.Draft.WGapAngles.angle_ineqs hA
  have hang := angle_at_vertexG D S.tile S.hM i hkm hkj hmj
  have hopp : dist ((D.tile i).pts m) ((D.tile i).pts j) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rcases vertex_dist_casesG D S.hM i hmj with d | d | d
    · have := hang.1 d; rw [hβ] at this; exact absurd this.symm hA.hαβ
    · exact d
    · have := hang.2.2 d; rw [hβ] at this; exact absurd this hβγ.ne
  refine ⟨hopp, ?_⟩
  have hsp := SixPlacements.sides_perm_of_congruent (D.tiles_congruent i) (M := D.model)
    (a := (f : ℝ) ^ 2) (b := (e : ℝ) * f) (c := (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (model_distsG D S.hM).1 (model_distsG D S.hM).2.1 (by rw [dist_comm]; exact (model_distsG D S.hM).2.2)
    k m j hkm hkj hmj
  have hef : (e : ℝ) < f := by exact_mod_cast S.hef
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hf0 : (0 : ℝ) < f := by linarith
  have h2 : (f : ℝ) ^ 2 ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have h3 : (e : ℝ) * f ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    intro h
    have : (D.tile i).localAngle ((D.tile i).pts k) = α := by
      apply hang.1; rw [hopp, ← h]
    rw [hβ] at this; exact hA.hαβ this.symm
  rcases hsp with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;>
    first
    | exact Or.inl ⟨a1, a2⟩
    | exact Or.inr ⟨a1, a2⟩
    | exact absurd (hopp.symm.trans a3) (fun h => h2 h.symm)
    | exact absurd (hopp.symm.trans a3) (fun h => h3 h.symm)

/-- **PART C, angle `γ`**: opposite side `c`, adjacent sides `{a, b}` -/
theorem sides_of_gamma (S : SetupG D e f α β γ L ax ay) (i : Fin N) {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j)
    (hγ : (D.tile i).localAngle ((D.tile i).pts k) = γ) :
    dist ((D.tile i).pts m) ((D.tile i).pts j) = (f : ℝ) ^ 2 ∧
    ((dist ((D.tile i).pts k) ((D.tile i).pts m) = (e : ℝ) * f ∧
        dist ((D.tile i).pts k) ((D.tile i).pts j) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
      (dist ((D.tile i).pts k) ((D.tile i).pts m) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
        dist ((D.tile i).pts k) ((D.tile i).pts j) = (e : ℝ) * f)) := by
  have hA := S.hA
  obtain ⟨hα0, hβ0, hαγ, hβγ, -, -, hγπ, -⟩ := Erdos634.Draft.WGapAngles.angle_ineqs hA
  have hang := angle_at_vertexG D S.tile S.hM i hkm hkj hmj
  have hopp : dist ((D.tile i).pts m) ((D.tile i).pts j) = (f : ℝ) ^ 2 := by
    rcases vertex_dist_casesG D S.hM i hmj with d | d | d
    · have := hang.1 d; rw [hγ] at this; exact absurd this.symm hαγ.ne
    · have := hang.2.1 d; rw [hγ] at this; exact absurd this.symm hβγ.ne
    · exact d
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
  rcases hsp with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;>
    first
    | exact Or.inl ⟨a1, a2⟩
    | exact Or.inr ⟨a1, a2⟩
    | exact absurd (hopp.symm.trans a3) h1.symm
    | exact absurd (hopp.symm.trans a3) h2.symm
    | exact absurd (hopp.symm.trans a3) h1
    | exact absurd (hopp.symm.trans a3) h2

/-- **FILLER CORE**: the tile beside the ray `X → Y`, no angle count.  A tile `τ ∉ K` with vertex `X`, a vertex on the open ray, the third vertex strictly
right, and the angle at `X` equal to `α`, `β` or `γ`. -/
theorem filler_core (S : SetupG D e f α β γ L ax ay) {X Y Z P' : Plane} {t₀ : Fin N} (hXY : X ≠ Y)
    (hV : HasV D t₀ X Y Z) (hZ : 0 < cross (Y - X) (Z - X))
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    (hint : openSegment ℝ X Y ⊆ interior D.target.carrier)
    (hclamp : ∀ ed ∈ D.lineChain (crossL (Y - X)) (cross (Y - X) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y)
    (K : Finset (Fin N))
    (hKray : ∀ k ∈ K, k ≠ t₀ → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap X Y s) :
    ∃ τ : Fin N, τ ∉ K ∧ ∃ (k m n : Fin 3) (t : ℝ), k ≠ m ∧ k ≠ n ∧ m ≠ n ∧ (D.tile τ).pts k = X ∧ 0 < t ∧
      (D.tile τ).pts m = AffineMap.lineMap X Y t ∧ cross (Y - X) ((D.tile τ).pts n - X) < 0 ∧
      ((D.tile τ).localAngle X = α ∨ (D.tile τ).localAngle X = β ∨ (D.tile τ).localAngle X = γ) := by
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
  rw [hk] at hvc
  exact ⟨τ, hτK, k, m, n, t, hkm, hkn, hmn, hk, ht, hm, hneg, hvc⟩

/-- **FILLER, wedge made of `β`** (W1, W9): if no tile outside `K` shows `α` or `γ` at `X`, the filler beside the ray is a `β`-tile:
vertices `X`, `P` on the ray, `W` strictly right, `|PW| = b`, `{|XP|, |XW|} = {a, c}`. -/
theorem filler_beta (S : SetupG D e f α β γ L ax ay) {X Y Z P' : Plane} {t₀ : Fin N} (hXY : X ≠ Y)
    (hV : HasV D t₀ X Y Z) (hZ : 0 < cross (Y - X) (Z - X))
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    (hint : openSegment ℝ X Y ⊆ interior D.target.carrier)
    (hclamp : ∀ ed ∈ D.lineChain (crossL (Y - X)) (cross (Y - X) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y)
    (K : Finset (Fin N)) (hα0 : cnt D K X α = 0) (hγ0 : cnt D K X γ = 0)
    (hKray : ∀ k ∈ K, k ≠ t₀ → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap X Y s) :
    ∃ τ : Fin N, τ ∉ K ∧ ∃ P W : Plane, HasV D τ X P W ∧ (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap X Y s) ∧
      cross (Y - X) (W - X) < 0 ∧ (D.tile τ).localAngle X = β ∧ dist P W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      ((dist X P = (e : ℝ) * f ∧ dist X W = (f : ℝ) ^ 2) ∨
        (dist X P = (f : ℝ) ^ 2 ∧ dist X W = (e : ℝ) * f)) := by
  obtain ⟨τ, hτK, k, m, n, t, hkm, hkn, hmn, hk, ht, hm, hneg, hvc⟩ :=
    filler_core S hXY hV hZ hP' hXP hint hclamp K hKray
  have hmemτ : τ ∈ Finset.univ \ K := by simp [hτK]
  have hangβ : (D.tile τ).localAngle ((D.tile τ).pts k) = β := by
    rw [hk]
    rcases hvc with h | h | h
    · exfalso
      unfold cnt at hα0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hα0
      exact hα0 hmemτ h
    · exact h
    · exfalso
      unfold cnt at hγ0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hγ0
      exact hγ0 hmemτ h
  obtain ⟨hopp, hsd⟩ := sides_of_beta S τ hkm hkn hmn hangβ
  rw [hk] at hangβ hsd
  refine ⟨τ, hτK, (D.tile τ).pts m, (D.tile τ).pts n, ⟨k, m, n, hkm, hkn, hmn, hk, rfl, rfl⟩,
    ⟨t, ht, hm⟩, hneg, hangβ, hopp, ?_⟩
  exact hsd

/-- **FILLER, wedge made of `γ` only** (W4, W7 in the `γ`-case): if no tile outside `K` shows `α` or `β` at `X`, the filler is a `γ`-tile -/
theorem filler_gamma (S : SetupG D e f α β γ L ax ay) {X Y Z P' : Plane} {t₀ : Fin N} (hXY : X ≠ Y)
    (hV : HasV D t₀ X Y Z) (hZ : 0 < cross (Y - X) (Z - X))
    (hP' : cross (Y - X) (P' - X) = 0) (hXP : X ∈ openSegment ℝ P' Y)
    (hint : openSegment ℝ X Y ⊆ interior D.target.carrier)
    (hclamp : ∀ ed ∈ D.lineChain (crossL (Y - X)) (cross (Y - X) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) P' X Y)
    (K : Finset (Fin N)) (hα0 : cnt D K X α = 0) (hβ0 : cnt D K X β = 0)
    (hKray : ∀ k ∈ K, k ≠ t₀ → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap X Y s) :
    ∃ τ : Fin N, τ ∉ K ∧ ∃ P W : Plane, HasV D τ X P W ∧ (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap X Y s) ∧
      cross (Y - X) (W - X) < 0 ∧ (D.tile τ).localAngle X = γ ∧ dist P W = (f : ℝ) ^ 2 ∧
      ((dist X P = (e : ℝ) * f ∧ dist X W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
        (dist X P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist X W = (e : ℝ) * f)) := by
  obtain ⟨τ, hτK, k, m, n, t, hkm, hkn, hmn, hk, ht, hm, hneg, hvc⟩ :=
    filler_core S hXY hV hZ hP' hXP hint hclamp K hKray
  have hmemτ : τ ∈ Finset.univ \ K := by simp [hτK]
  have hangγ : (D.tile τ).localAngle ((D.tile τ).pts k) = γ := by
    rw [hk]
    rcases hvc with h | h | h
    · exfalso
      unfold cnt at hα0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hα0
      exact hα0 hmemτ h
    · exfalso
      unfold cnt at hβ0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hβ0
      exact hβ0 hmemτ h
    · exact h
  obtain ⟨hopp, hsd⟩ := sides_of_gamma S τ hkm hkn hmn hangγ
  rw [hk] at hangγ hsd
  refine ⟨τ, hτK, (D.tile τ).pts m, (D.tile τ).pts n, ⟨k, m, n, hkm, hkn, hmn, hk, rfl, rfl⟩,
    ⟨t, ht, hm⟩, hneg, hangγ, hopp, ?_⟩
  exact hsd

end cor

/-- negative control: a wedge of size `2β` is never filled by one `γ` (the ledger fixes `{β, β}`) -/
theorem wedge_2beta_not_gamma {e f : ℕ} {α β γ L ax ay : ℝ} {X : Plane} {Ω : ℝ} {K : Finset (Fin N)}
    (S : SetupG D e f α β γ L ax ay) (hΩ : ∑ i, (D.tile i).localAngle X = Ω)
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - 2 * β) : ¬ 0 < cnt D K X γ := by
  have := (wedge_2beta S hΩ hK).2.2
  omega

#print axioms fill_2beta
#print axioms sides_of_beta
#print axioms sides_of_gamma
#print axioms filler_beta
#print axioms filler_gamma

end Erdos634.Draft.WGapStmt
