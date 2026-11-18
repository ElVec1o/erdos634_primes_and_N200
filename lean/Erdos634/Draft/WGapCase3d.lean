/-
Draft/WGapCase3d.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 Case 3).
Not imported by any aggregate.  Module P-D5: the CASE 3 SUPPLIER of `inv_step` (hypothesis `case3`, concrete `Bst`): `c < j`, no flipped tile at the inner points.  By `claim_S` (with `run_hint_wall`) some far-side chain edge
straddles `Y = p'(c, j+1-c)` on `l'_c`; by `straddle_data` its tile contains a short push from `Y` in every direction `v` with `crossL ub v < 0`, in particular `v = s_{j+1}` (the direction of `m'_{j+1}`),
so `BotClamp (j+1) c` follows from `not_straddles_short`.  The structure (b) is carried over (`js` unchanged) with the new near tile `D'(c-1, j-c)` of the level step.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapCase3c

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

section case3d

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 2000000 in
theorem case3_supplier (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ f - 1)
    (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) :
    ∀ j c : ℕ, Inv D e f (Bst D e f) j c → j < J → c < j → (∀ i : ℕ, 1 ≤ i → i < c → Unfl D e f j i) →
        BotClamp D e f (j + 1) c ∧ Bst D e f (j + 1) c := by
  intro j c I hjJ hcj _
  have hj1 : 1 ≤ j := by omega
  obtain ⟨js, hjs, hflip, hCl, hD⟩ := I.hb hcj
  have hnear : ∀ i' : ℕ, js ≤ i' → c + i' + 1 ≤ j + 1 → DTM D (e : ℝ) f 1 0 ((c - 1 : ℕ) : ℝ) (i' : ℝ) := by
    intro i' h1 h2
    by_cases h3 : c + i' + 1 ≤ j
    · exact hD i' h1 h3
    · have hi' : i' = j - c := by omega
      subst hi'
      have h := (level_data S hJf hU hT hj1 hjJ I).1 (c - 1) (by have := I.c1; omega)
      have e1 : j - 1 - (c - 1) = j - c := by have := I.c1; omega
      rw [e1] at h
      exact h
  refine ⟨?_, fun _ => ⟨js, by omega, hflip, hCl, hnear⟩⟩
  -- the clamp
  set m : ℕ := j + 1 - c - js with hm
  have hm1 : 1 ≤ m := by omega
  have hmf : m ≤ f - 1 := by omega
  obtain ⟨hint, hwall⟩ := run_hint_wall S I.c1 hm1 hflip (fun i' h1 h2 => hnear i' h1 (by omega))
  obtain ⟨ed₀, hed₀, hstr⟩ := claim_S S hm1 hmf hflip hCl hint hwall
  intro ed _
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨O, E1, E2, hmp⟩ := mpG_affine he0 hef
  set X₀ := mpG (e : ℝ) f 1 0 (c : ℝ) (js : ℝ) with hX₀
  set u := ub e f c js with hu
  have hu0 : u ≠ 0 := ub_ne S c js
  set Y := X₀ - (m : ℝ) • u with hY
  -- the chord end equals Y
  have hjm : (js : ℝ) + m = (j : ℝ) + 1 - c := by
    have : js + m + c = j + 1 := by omega
    have h' : ((js + m + c : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) := by rw [this]
    push_cast at h'; linarith
  have hYeq : mpG (e : ℝ) f 1 0 0 ((j + 1 : ℕ) : ℝ) + (c : ℝ) • sj e f (j + 1) = Y := by
    rw [hY, hX₀, hu]; unfold sj ub; simp only [hmp]
    have := hjm
    ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    push_cast
    have hmr : (m : ℝ) = (j : ℝ) + 1 - c - js := by linarith
    rw [hmr]; ring
  -- straddle data
  have hFu : crossL u u = 0 := by rw [crossL_apply]; simp [cross]; ring
  have hFl : ∀ s : ℝ, crossL u (X₀ + s • u) = cross u X₀ := by
    intro s; rw [map_add, map_smul, hFu, crossL_apply]; simp
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hfP : crossL u Y = cross u X₀ := by
    have := hFl (-(m : ℝ)); rw [hY]; simpa [sub_eq_add_neg] using this
  have hfP' : crossL u (Y - u) = cross u X₀ := by
    have := hFl (-((m : ℝ) + 1)); rw [hY]
    convert this using 2; ext x; simp [sub_eq_add_neg]; ring
  have hPQ : Y ≠ X₀ := by
    intro h
    have : (m : ℝ) • u = 0 := by
      have := congrArg (fun z => X₀ - z) h
      simpa [hY] using this
    rcases smul_eq_zero.mp this with h0 | h0
    · exact hmpos.ne' h0
    · exact hu0 h0
  have hP' : Y ∈ openSegment ℝ (Y - u) X₀ := by
    refine ⟨(m : ℝ) / (m + 1), 1 / (m + 1), by positivity, by positivity, by field_simp, ?_⟩
    rw [hY]
    ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp; ring
  obtain ⟨-, -, hpush⟩ := straddle_data D.toDissection (crossL u) (crossL_ne_zero hu0) (cross u X₀) hPQ hfP
    (crossL_apply _ _) hfP' hP' hed₀ hstr
  -- F s' < 0
  have hFs : crossL u (sj e f (j + 1)) < 0 := by
    rw [crossL_apply, hu]; unfold ub sj
    rw [cross_mpG he0 hef]
    have := kapG_pos he0 hef
    have e1 : ((c : ℝ) - (c : ℝ)) * ((((j + 1 : ℕ) : ℝ) - 1) - ((j + 1 : ℕ) : ℝ)) -
        ((js : ℝ) - ((js : ℝ) + 1)) * ((1 : ℝ) - 0) = 1 := by ring
    rw [e1]; nlinarith
  obtain ⟨ε₀, hε₀, hpush'⟩ := hpush (sj e f (j + 1)) hFs
  refine not_straddles_short D.toDissection (j := ed₀.1) (δ := ε₀) (ρ := (c : ℝ)) hε₀
    (by exact_mod_cast I.c1) ?_ ?_ ed.1 ed.2
  · ext x; simp; ring
  · intro ε h0 h1
    have := hpush' ε h0 h1
    convert this using 1
    rw [← hYeq]
    ext x
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
end case3d


end Erdos634.Draft.WGapStmt
