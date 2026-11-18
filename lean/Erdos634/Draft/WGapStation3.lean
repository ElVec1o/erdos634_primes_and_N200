/-
Draft/WGapStation3.lean -- written 16 November 2026 (session 17).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4).
Not imported by any aggregate.  No sorry, no native_decide.
The climb of session 16 / the station lemma of WGapStation2 with the exit hypothesis `B` WEAKENED to `BUpToP` (the apex-level pairs `(j, i)` with `j + i >= 1`, i.e. the corner `i = j = 0` is excluded).
This is exactly what the hand proof uses: (3a) calls Proposition B only at the level `j + lam >= 1`.  So `prop_B_of_station_P` is UNCONDITIONAL (no hypothesis beyond `Sigma[i]`, `BUpToP (i-1)`) for every `(i, j)` with `j + i >= 1`.
Contents: `BUpToP`, `station_Pi4_false_P`, `station_stmt_P`, `climb_gen_aux_P`, `prop_B_of_station_P`.
-/
import Erdos634.Draft.WGapStation2

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

/-- `B` up to the index `n` (exclusive), for the pairs `(j, i)` with `j + i >= 1` only (the corner `(0,0)` is not included) -/
def BUpToP (D : CongruentDissection N) (e f n : ℕ) : Prop :=
  ∀ c₀ J : ℕ, IsApex D e f c₀ J → ∀ j i : ℕ, J ≤ j → i < n → i + j + 1 ≤ f - 1 → 1 ≤ j + i → ¬ PiBCfg D e f c₀ J j i

theorem BUpToP.mono' {e f n n' : ℕ} (h : BUpToP D e f n) (hn : n' ≤ n) : BUpToP D e f n' :=
  fun c J hA j i hJ hi hij hj1 => h c J hA j i hJ (by omega) hij hj1

theorem BUpTo.toP {e f n : ℕ} (h : BUpTo D e f n) : BUpToP D e f n :=
  fun c J hA j i hJ hi hij _ => h c J hA j i hJ hi hij

section station3

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem station_Pi4_false_P {c₀ J j i lam x : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j + lam) (hij : i + j + 1 ≤ f - 1)
    (hlam1 : 1 ≤ lam) (hlt : lam < i) (hSt : ClimbSt D e f c₀ J j i lam) (hB : BUpToP D e f (i - 1)) (hx2 : x + 2 + lam ≤ i)
    (hbefore : ∀ x' : ℕ, x' < x → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x' : ℝ) ((j + lam : ℕ) : ℝ))
    (hN : NTile D e f c₀ x (j + lam)) (hPi4 : Pi4 D e f c₀ x (j + lam)) : False := by
  obtain ⟨hC1, hS1, hUa, hDa⟩ := hSt
  exact hB c₀ J hA (j + lam) x hJ (by omega) (by omega) (by omega)
    ⟨hS1, fun a b hb hab => hUa a b hb (by omega), fun a b hb hab => hDa a b hb (by omega), hbefore, hN, hPi4⟩

/-- `StationStmt` with the exit hypothesis `B` restricted to the pairs `(j,i)` with `j + i >= 1` -/
def StationStmtP : Prop :=
  ∀ {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay)
    (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) {c₀ J j i lam : ℕ}, IsApex D e f c₀ J → J ≤ j + lam →
    i + j + 1 ≤ f - 1 → 1 ≤ lam → lam < i → ClimbSt D e f c₀ J j i lam → SigmaAll D e f i → BUpToP D e f (i - 1) →
    Pi4 D e f c₀ i j → ∀ x : ℕ, x + 2 + lam ≤ i →
    (∀ x' : ℕ, x' < x → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x' : ℝ) ((j + lam : ℕ) : ℝ)) → NTile D e f c₀ x (j + lam) →
    IsApex D e f (c₀ + (x + 1)) (j + lam) ∧ StripTiles D e f (c₀ + (x + 1)) (j + lam) (j + lam)
set_option maxHeartbeats 16000000 in

theorem station_stmt_P : StationStmtP := by
  intro N D e f α β γ L ax ay S h2 hH4 c₀ J j i lam hA hJ hij hlam1 hlt hCl hSig hB hP4 x hx2 hbefore hN
  obtain ⟨y1, hy1⟩ : ∃ y1, j + lam = y1 + 1 := ⟨j + lam - 1, by omega⟩
  have hcy : (((j + lam : ℕ)) : ℝ) = (y1 : ℝ) + 1 := by rw [hy1]; push_cast; ring
  have hCl' := hCl
  obtain ⟨hC1, hS1, hUa, hDa⟩ := hCl
  have hDL := hDa x y1 (by omega) (by omega)
  have hUl := hUa (x + 1) y1 (by omega) (by omega)
  have hDl := hDa (x + 1) y1 (by omega) (by omega)
  have hUr := hUa (x + 1) (y1 + 1) (by omega) (by omega)
  have hUi := hUa x (y1 + 1) (by omega) (by omega)
  have hN' := hN
  simp only [Nat.cast_add, Nat.cast_one] at hDL hUl hDl hUr hUi
  obtain ⟨tDL, hDL⟩ := hDL
  obtain ⟨tUl, hUl⟩ := hUl
  obtain ⟨tDl, hDl⟩ := hDl
  obtain ⟨tUr, hUr⟩ := hUr
  obtain ⟨tUi, hUi⟩ := hUi
  obtain ⟨tN, hNv⟩ := hN'
  rw [hy1] at hNv
  simp only [Nat.cast_add, Nat.cast_one] at hNv
  have hE := station_E_lat S (xo f c₀) (x : ℝ) (y1 : ℝ) (x + 1) (by push_cast; ring) hDL hUl hDl hUr hUi hNv
  -- the strip tile of the station at level `j + lam`
  have hEt : UTM D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + x + 1)) 0 (((j + lam : ℕ)) : ℝ) := by
    rcases hE with ⟨iT, k, m, t, hkm, hk, hm, ht, hlen, hle⟩ | hmir
    · exfalso
      -- `E` lays `c`: `K1J` at the origin `p(c₀+x+1, 0)`
      have hK1 : K1J D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + (x + 1))) (j + lam) := by
        refine ⟨iT, k, m, t, hkm, ?_, ?_, ht, hlen, ?_⟩
        · rw [hk, lpG_xo_add _ _ f c₀ (x + 1) rfl, hcy]
          exact lpG_congr (by push_cast; ring) rfl
        · rw [hm, lpG_xo_add _ _ f c₀ (x + 1) rfl, hcy]
          exact lpG_congr (by push_cast; ring) (by ring)
        · intro i'
          have h0 : lvG (e : ℝ) (f : ℝ) 1 (xo f (c₀ + (x + 1))) 0 = lvG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((x : ℝ) + 1) := by
            rw [xo_add, lvG_shk]
            congr 1
            push_cast; ring
          rw [h0]
          exact hle i'
      have hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + (x + 1))) 0 0 := by
        have := UTG_rebase (c₀ := c₀) (m := x + 1) (a := 0) (b := ((0 : ℕ) : ℝ))
          (hUa (0 + (x + 1)) 0 (by omega) (by omega))
        rw [Nat.cast_zero] at this
        exact this
      have hNn : NTile D e f (c₀ + (x + 1)) (i - lam - (x + 1)) (j + lam) := by
        have h1 := hC1 (i - lam) le_rfl (by omega)
        have e1 : j + i - (i - lam) = j + lam := by omega
        rw [e1] at h1
        have e2 : i - lam = (i - lam - (x + 1)) + (x + 1) := by omega
        rw [e2] at h1
        exact NTile_rebase h1
      refine N_at_origin S (c₀ + (x + 1)) (j + lam) (fun h => absurd h (by omega)) hU0 hK1
        (i - lam - (x + 1)) (j + lam) le_rfl (by omega) ?_ ?_ ?_ hNn
      · intro i' j' hj' hij'
        exact UTG_rebase (c₀ := c₀) (m := x + 1) (a := i') (b := (j' : ℝ))
          (hUa (i' + (x + 1)) j' (by omega) (by omega))
      · intro i' j' hj' hij'
        exact DTG_rebase (c₀ := c₀) (m := x + 1) (a := i') (b := (j' : ℝ))
          (hDa (i' + (x + 1)) j' (by omega) (by omega))
      · intro m' hm1 hm2
        exact K_at_origin S (c₀ + (x + 1)) (j + lam) (fun h => absurd h (by omega)) hU0 hK1 m' hm1
    · have hxe : shiftX (f : ℝ) 1 (xo f c₀) (x + 1) = xo f (c₀ + x + 1) := by
        unfold shiftX xo; push_cast; ring
      have := (mirrorAt_iff_UTM_gen S _ _).1 hmir
      rw [hxe, ← hcy] at this
      exact this
  have hK2 : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) (j + lam + x + 2) (j + lam) :=
    ⟨fun a b hb hab => hUa a b hb (by omega), fun a b hb hab => hDa a b hb (by omega)⟩
  have hdich := st_dichotomy_core S (c₀ := c₀) (s := j + lam + x + 2) (y₀ := j + lam) (i := x)
    (by omega) (by omega) (by omega) hK2 hN hEt
  rcases hdich with hSt2 | hPi4
  · refine ⟨Or.inr ⟨by omega, hSt2⟩, ?_⟩
    intro y h1 h2
    have : y = j + lam := by omega
    subst this
    exact hEt
  · exact absurd hPi4 (fun h => station_Pi4_false_P hA hJ hij hlam1 hlt hCl' hB hx2 hbefore hN h)



set_option maxHeartbeats 32000000 in
theorem climb_gen_aux_P (hst : StationStmtP) (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) :
    ∀ n : ℕ, ∀ {c₀ J j i lam : ℕ}, i - lam = n → lam ≤ i → IsApex D e f c₀ J → J ≤ j + lam → i + j + 1 ≤ f - 1 →
    1 ≤ j + i → (lam = 0 → ∀ x : ℕ, x < i → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x : ℝ) (j : ℝ)) →
    ClimbSt D e f c₀ J j i lam → SigmaAll D e f i → BUpToP D e f (i - 1) → Pi4 D e f c₀ i j → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c₀ J j i lam hn hli hA hJ hij hj1 hrow0 hCl hSig hB hP4
    by_cases hlam : lam = i
    · subst hlam
      exact climb_end0 S (by omega) hij hj1 hCl hP4
    · have hlt : lam < i := by omega
      by_cases hall : ∀ x : ℕ, x < i - lam → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x : ℝ) ((j + lam : ℕ) : ℝ)
      · have hCl' := climb_step0 S h2 hH4 hA hJ hij hlt hCl hall hP4 hSig
        exact ih (i - (lam + 1)) (by omega) rfl (by omega) hA (by omega) hij hj1
          (fun h => by omega) hCl' hSig hB hP4
      · have hex : ∃ x : ℕ, x < i - lam ∧ ¬ DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x : ℝ) ((j + lam : ℕ) : ℝ) := by
          by_contra hne
          push_neg at hne
          exact hall (fun x hx => hne x hx)
        have hlam1 : 1 ≤ lam := by
          by_contra h0
          obtain ⟨x0, hx0, hnd⟩ := hex
          have : lam = 0 := by omega
          subst this
          exact hnd (by simpa using hrow0 rfl x0 (by omega))
        obtain ⟨hxlt, hxnd⟩ := Nat.find_spec hex
        set x := Nat.find hex with hxdef
        have hbefore : ∀ x' : ℕ, x' < x → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x' : ℝ) ((j + lam : ℕ) : ℝ) := by
          intro x' hx'
          by_contra hnd
          exact Nat.find_min hex hx' ⟨by omega, hnd⟩
        have hN : NTile D e f c₀ x (j + lam) := by
          rcases row_cases S hA hJ hij hlam1 hlt hCl hSig hxlt with hD' | hN'
          · exact absurd hD' hxnd
          · exact hN'
        have hx2 : x + 2 + lam ≤ i := by
          by_contra hx2
          have hxe : x = i - lam - 1 := by omega
          rw [hxe] at hN
          exact rowN_false S hij hlam1 hlt hCl hP4 hN
        obtain ⟨hAp, hStrip⟩ := hst S h2 hH4 hA hJ hij hlam1 hlt hCl hSig hB hP4 x hx2 hbefore hN
        have hCl'' := climbSt_rebase (J' := j + lam) (m := x + 1) (by omega) hCl hStrip
        exact ih ((i - (x + 1)) - lam) (by omega) rfl (by omega) hAp le_rfl (by omega) (by omega)
          (fun h => by omega) hCl'' (hSig.mono' (by omega)) (hB.mono' (by omega)) (Pi4_rebase (by omega) hP4)

/-- **Proposition B at every `(i, j)` with `j + i >= 1`, UNCONDITIONAL** (hypotheses: `Sigma[i]`, `BUpToP (i-1)`, the geometry of the setup) -/
theorem prop_B_of_station_P (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J j i : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j) (hij : i + j + 1 ≤ f - 1) (hj1 : 1 ≤ j + i)
    (hSig : SigmaAll D e f i) (hB : BUpToP D e f (i - 1)) : ¬ PiBCfg D e f c₀ J j i := by
  rintro ⟨hS1, hUall, hDall, hD0, hN, hP4⟩
  refine climb_gen_aux_P station_stmt_P S h2 hH4 (i - 0) rfl (Nat.zero_le _) hA (by omega) hij hj1
    (fun _ x hx => hD0 x hx) ?_ hSig hB hP4
  refine ⟨?_, hS1, hUall, hDall⟩
  intro t h1 h2'
  have : t = i := by omega
  subst this
  have e1 : j + t - t = j := by omega
  rw [e1]
  exact hN

end station3

#print axioms station_stmt_P
#print axioms climb_gen_aux_P
#print axioms prop_B_of_station_P

end Erdos634.Draft.WGapStmt
