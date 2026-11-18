/-
Draft/WGapChord3.lean -- written 15 November 2026 (session 3).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 chord facts (C): "the far-side tiles have exactly the c_j lattice a-edges").
Not imported by any aggregate.  Module W5e: the CHORD LEMMA on a generic line.

`chord_all`: the line `{F = c}` through `X` with step vector `s` (`‖s‖ = a = e f`, `F s = 0`), the run `[X, E]`, `E = X + n s`, `1 ≤ n ≤ f - 1`, interior to the target and wall,
clamped at both ends in the form of `run_partition` (`¬ Straddles` at `X` towards `E` with extension `X - s`, and at `E` towards `X` with extension `E + s`).
CONCLUSION: for every `i < n` the far side (`F ≤ c`) carries a tile with the vertices `X + i s`, `X + (i+1) s` (an `a`-edge) and a third vertex with `F < c`.
This is the statement "(U3-c)/(C): the tiles beside the chord have exactly the lattice `a`-edges" for ANY line of a-lattice steps (mirror lines `m'_j` with `s = p'(1,j-1) - p'(0,j)`).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapChord2

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

/-- parameters on a line: `t₁ < t₂ < t₃` gives `X + t₂ s ∈ openSegment (X + t₁ s) (X + t₃ s)` -/
theorem par_mem_open (X s : Plane) {t₁ t₂ t₃ : ℝ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) :
    X + t₂ • s ∈ openSegment ℝ (X + t₁ • s) (X + t₃ • s) := by
  have hd : 0 < t₃ - t₁ := by linarith
  refine ⟨(t₃ - t₂) / (t₃ - t₁), (t₂ - t₁) / (t₃ - t₁), div_pos (by linarith) hd,
    div_pos (by linarith) hd, by field_simp; ring, ?_⟩
  ext j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- sub-segments of a parameter segment -/
theorem par_open_sub (X s : Plane) {t₀ t₁ t₂ t₃ : ℝ} (h0 : t₀ ≤ t₁) (h12 : t₁ < t₂) (h3 : t₂ ≤ t₃) :
    openSegment ℝ (X + t₁ • s) (X + t₂ • s) ⊆ openSegment ℝ (X + t₀ • s) (X + t₃ • s) := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  have hz : a • (X + t₁ • s) + b • (X + t₂ • s) = X + (a * t₁ + b * t₂) • s := by
    have : b = 1 - a := by linarith
    subst this
    module
  rw [hz]
  have e1 : a * t₁ + b * t₂ = t₁ + b * (t₂ - t₁) := by
    have : a = 1 - b := by linarith
    subst this; ring
  have e2 : a * t₁ + b * t₂ = t₂ - a * (t₂ - t₁) := by
    have : b = 1 - a := by linarith
    subst this; ring
  have p1 := mul_pos hb (sub_pos.mpr h12)
  have p2 := mul_pos ha (sub_pos.mpr h12)
  apply par_mem_open
  · linarith
  · linarith

section chord

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem lvl (F : Plane →ₗ[ℝ] ℝ) {c : ℝ} {X s : Plane} (hFX : F X = c) (hFs : F s = 0) (t : ℝ) :
    F (X + t • s) = c := by
  rw [map_add, map_smul, hFs, hFX]; simp

/-- **THE CHORD LEMMA** (generic line, step `s` of length `a`); see the module header. -/
theorem chord_all (S : SetupG D e f α β γ L ax ay) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {X s : Plane} (hs0 : s ≠ 0) (hnorm : ‖s‖ = (e : ℝ) * f) (hFX : F X = c) (hFs : F s = 0)
    {n : ℕ} (hn1 : 1 ≤ n) (hnf : n ≤ f - 1)
    (hint : openSegment ℝ X (X + (n : ℝ) • s) ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ X (X + (n : ℝ) • s), ∀ i, y ∉ interior (D.tile i).carrier)
    (hX : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) (X + (-1 : ℝ) • s) X (X + (n : ℝ) • s))
    (hE : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) (X + ((n : ℝ) + 1) • s) (X + (n : ℝ) • s) X) :
    ∀ i : ℕ, i < n → ∃ (τ : Fin N) (W : Plane), HasV D τ (X + (i : ℝ) • s) (X + ((i : ℝ) + 1) • s) W ∧ F W < c := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hef : (0 : ℝ) < (e : ℝ) * f := by
    have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
    have hef' : (e : ℝ) < f := by exact_mod_cast S.hef
    exact mul_pos he0 (he0.trans hef')
  have hdist : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ → dist (X + t₁ • s) (X + t₂ • s) = (t₂ - t₁) * ((e : ℝ) * f) := by
    intro t₁ t₂ h
    rw [dist_eq_norm, show X + t₁ • s - (X + t₂ • s) = (t₁ - t₂) • s by module, norm_smul, hnorm,
      Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hne : ∀ t₁ t₂ : ℝ, t₁ < t₂ → X + t₁ • s ≠ X + t₂ • s := by
    intro t₁ t₂ h hh
    have := hdist t₁ t₂ h.le
    rw [hh, dist_self] at this
    have hp : 0 < (t₂ - t₁) * ((e : ℝ) * f) := mul_pos (by linarith) hef
    linarith
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hi' : (i : ℝ) < n := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hjeq : ((n - i : ℕ) : ℝ) = (n : ℝ) - i := Nat.cast_sub hi.le
    -- the clamp at the start of the run [Q_i, E]
    have hPcl : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2)
        (X + ((i : ℝ) - 1) • s) (X + (i : ℝ) • s) (X + (n : ℝ) • s) := by
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        intro ed hed
        have := hX ed hed
        have e1 : (((0 : ℕ) : ℝ) - 1) = -1 := by norm_num
        rw [e1]
        simpa using this
      · obtain ⟨τ', W', hV', hW'⟩ := ih (i - 1) (by omega) (by omega)
        have hc1 : (((i - 1 : ℕ) : ℝ)) = (i : ℝ) - 1 := by
          rw [Nat.cast_sub hpos]; simp
        have hV'' : HasV D τ' (X + ((i : ℝ) - 1) • s) (X + (i : ℝ) • s) W' := by
          rw [hc1] at hV'
          have : (i : ℝ) - 1 + 1 = i := by ring
          rw [this] at hV'
          exact hV'
        exact straddle_excl S F hF c hV'' (lvl F hFX hFs _) (lvl F hFX hFs _) hW'
          (hne _ _ hi') (lvl F hFX hFs _) (par_mem_open X s (by linarith) hi')
    -- the clamp at the end of the run
    have hQcl : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2)
        (X + ((n : ℝ) + 1) • s) (X + (n : ℝ) • s) (X + (i : ℝ) • s) := by
      intro ed hed hs
      apply hE ed hed
      obtain ⟨h1, ⟨y, hy, hyseg⟩⟩ := hs
      refine ⟨h1, ⟨y, hy, ?_⟩⟩
      have hsub := par_open_sub X s (t₀ := 0) (t₁ := (i : ℝ)) (t₂ := (n : ℝ)) (t₃ := (n : ℝ))
        hi0 hi' le_rfl
      have hsym1 : openSegment ℝ (X + (n : ℝ) • s) (X + (i : ℝ) • s) =
          openSegment ℝ (X + (i : ℝ) • s) (X + (n : ℝ) • s) := openSegment_symm ℝ _ _
      have hsym2 : openSegment ℝ (X + (n : ℝ) • s) X = openSegment ℝ X (X + (n : ℝ) • s) :=
        openSegment_symm ℝ _ _
      rw [hsym1] at hyseg
      rw [hsym2]
      have := hsub hyseg
      simpa using this
    have hjpos : 1 ≤ n - i := by omega
    have hjf : n - i ≤ f - 1 := by omega
    have hint' : openSegment ℝ (X + (i : ℝ) • s) (X + (n : ℝ) • s) ⊆ interior D.target.carrier := by
      refine subset_trans ?_ hint
      have := par_open_sub X s (t₀ := 0) (t₁ := (i : ℝ)) (t₂ := (n : ℝ)) (t₃ := (n : ℝ)) hi0 hi' le_rfl
      simpa using this
    have hwall' : ∀ y ∈ openSegment ℝ (X + (i : ℝ) • s) (X + (n : ℝ) • s), ∀ k, y ∉ interior (D.tile k).carrier := by
      intro y hy
      apply hwall y
      have := par_open_sub X s (t₀ := 0) (t₁ := (i : ℝ)) (t₂ := (n : ℝ)) (t₃ := (n : ℝ)) hi0 hi' le_rfl
      have h2 := this hy
      simpa using h2
    obtain ⟨τ, k, m, n3, hkm, hkn, hmn, hk, hm, hF3, hle⟩ :=
      chord_first_a S (j := n - i) hjpos hjf F hF c (P := X + (i : ℝ) • s) (Q := X + (n : ℝ) • s)
        (P' := X + ((i : ℝ) - 1) • s) (Q' := X + ((n : ℝ) + 1) • s)
        (hne _ _ hi') (lvl F hFX hFs _) (lvl F hFX hFs _) (lvl F hFX hFs _) (lvl F hFX hFs _)
        (par_mem_open X s (by linarith) hi') (par_mem_open X s hi' (by linarith)) hint' hwall' hPcl hQcl
        (by rw [hdist _ _ hi'.le, hjeq])
    have hm' : (D.tile τ).pts m = X + ((i : ℝ) + 1) • s := by
      rw [hm, AffineMap.lineMap_apply]
      have hne0 : (n : ℝ) - i ≠ 0 := by linarith
      have : (1 / ((n - i : ℕ) : ℝ)) • ((X + (n : ℝ) • s) - (X + (i : ℝ) • s)) = s := by
        rw [hjeq, show (X + (n : ℝ) • s) - (X + (i : ℝ) • s) = ((n : ℝ) - i) • s by module,
          smul_smul, one_div_mul_cancel hne0, one_smul]
      simp only [vsub_eq_sub, vadd_eq_add]
      rw [this]
      module
    exact ⟨τ, (D.tile τ).pts n3, ⟨k, m, n3, hkm, hkn, hmn, hk, hm', rfl⟩, hF3⟩

end chord

#print axioms par_open_sub
#print axioms chord_all

end Erdos634.Draft.WGapStmt
