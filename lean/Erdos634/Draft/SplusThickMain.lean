/-
Credit: D. Paliy (2026-10-03 to 10-08, W/beta caps, exact boundary-adjacency and thick-member observations; public repository github.com/DenisUkranian/erdos-634-tilings), M. Beeson and G. Rosu.
Draft/SplusThickMain.lean -- written 19 October 2026.  UNAUDITED.  Not in `All`; in `AllSplusThick`.

**S+ for the thick members: `thm_corner_run_ep1_thick` and `wTilable_not_of_small_M`.**

HAND RESULT (formalized here).  `project working notes`, audit `project working notes` (SOUND-WITH-FIX; fixes G1 `M < f`, G2 `C_AQ` for `M (f − e) < f`
(`SplusThickArith.C_AQ'`) carried out).  Credit: Beeson-Rosu (framework, `thm:cornerrun`, `cor:thickw`), the E2R6 room (statements `K`, `M`, the partition property (P)), Chisel (`C1`),
the S+ audit.

WHAT IS NEW.  `Draft/SideRunGMo` (`M°(e+1)`) uses `a < b` in exactly one place, `a_geom` in the case `a^f` of the row `Λ`.  `SplusThickGeom.aF_false_thick` replaces it for `b < a` (the
first tile `Y` above `Λ` has its `b`-edge along the `a`-edge `S` of the mirror tile `T`; (P) `run_partition` on `S` with Lemma `Aa` (`j = 1`)).  Here:
* `MO_main_thick`, `MO_corner_thick`, `corner_run_short_o_thick` (`b < a`), `corner_run_short_o_any` (every member, `2α` at `A'`: `a < b` by the old `corner_run_short_o`, `b < a` by the new one;
  `a ≠ b` by `ab_ne`, from `f ∣ e²` and coprimality);
* `cornerrun_core_thick`, `thm_corner_run_ep1_thick`: the addendum of `thm:cornerrun` WITHOUT `a < b`: in alternative (ii) at a corner `2α`, `k ≥ e + 2` for every member;
* `cornerrun_counts_thick`, `thickw_count_tiling_thick`: the counts on `AQ` (`z ≥ e + 1`, `z ≥ e + 2` when `e + 2 ≤ f`), every member;
* **`wTilable_not_of_small_M`**: coprime `2 ≤ e < f`, `M < f`, `f ≤ M e`, `M (f − e) ≤ e + 1`: `¬ WTilable e f M`.
Instances at the foot: `(5,8,2)`, `(5,7,3)`, `(7,11,2)`, `(8,11,3)` and the control `(3,5,2)` (the same statement; the existing `thickw_c_pred` proves it separately).  No sorry, no native_decide.
-/
import Erdos634.Draft.SplusThickGeom
import Erdos634.Draft.SplusThickArith
import Erdos634.Draft.SideRunGThick
import Erdos634.Draft.SideRunGCornerMainB

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SplusThick

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.SideRunGA Set

variable {N : ℕ} {D : CongruentDissection N}

/-- `a ≠ b` for every coprime member: `e f = f² − e²` would give `f ∣ e²` -/
theorem ab_ne {e f : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    (e : ℝ) * f ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  intro h
  have hle : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  have h1 : e * f + e ^ 2 = f ^ 2 := by
    have : ((e * f + e ^ 2 : ℕ) : ℝ) = ((f ^ 2 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h2 : f ∣ e ^ 2 := ⟨f - e, by
    have : f * (f - e) = f ^ 2 - e * f := by rw [Nat.mul_sub]; ring_nf
    rw [this]; omega⟩
  have h3 : Nat.Coprime f (e ^ 2) := (Nat.Coprime.pow_right 2 hco.symm)
  have h4 : f = 1 := Nat.Coprime.eq_one_of_dvd h3 h2
  omega

section runthick

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- **`M°(e+1)` for `b < a`** (the proof of `SideRunGMo.MO_main`, with `aF_false_thick` in the case `a^f`) -/
theorem MO_main_thick (S : SetupG D e f α β γ L ax ay) (hba : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (e : ℝ) * f)
    (hA2 : ∃ t : ℝ, 0 < t ∧ ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) ∧
      ay = t * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)))
    (hef2 : e + 1 < f) (hch : ChordsAt D (e : ℝ) (f : ℝ) 1 0)
    (hM : MirrorAt D (e : ℝ) (f : ℝ) 1 0 ((0 : ℕ) : ℝ))
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 0 (e + 1) 0)
    (hK3 : K3G D (e : ℝ) (f : ℝ) 1 0 ((e + 1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) : False := by
  have IH : ∀ m, 1 ≤ m → m < e + 1 - 0 → MGh D e f 1 m := fun m h1 _ => MG_all S m h1
  have hA := stepAO S hch hM hK2 hK3 hef2 (by omega) IH
  have he1 := S.he
  have W : StepCtxO D e f α β γ L ax ay 0 (e + 1) 0 :=
    ⟨S, hch, hM, hK2, hK3, hef2, by omega, by omega, IH, hA⟩
  have hq : e + 0 + 1 = e + 1 := rfl
  rcases lambda_dich W (q := e) hq rfl with hc | ha
  · exact cE_false W (q := e) hq he1 hc
  · exact aF_false_thick S W hba hA2 ha

theorem MO_corner_thick (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (hba : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (e : ℝ) * f) (hef2 : e + 1 < f)
    (h2 : D.target.localAngle (mkPt 0 0) = 2 * α) (hch : ChordsAt D (e : ℝ) (f : ℝ) 1 0)
    (hM : MirrorAt D (e : ℝ) (f : ℝ) 1 0 ((0 : ℕ) : ℝ))
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 0 (e + 1) 0)
    (hK3 : K3G D (e : ℝ) (f : ℝ) 1 0 ((e + 1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) : False :=
  MO_main_thick S hba (cornersA_two_of_angle S Co h2) hef2 hch hM hK2 hK3

/-- **a run of `C1` from a corner `2α` of length `k ≤ e + 1` is impossible for EVERY member** (`a < b`: `corner_run_short_o`; `b < a`: `MO_corner_thick`; `a = b` never happens) -/
theorem corner_run_short_o_any (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (hef2 : e + 1 < f) (h2 : D.target.localAngle (mkPt 0 0) = 2 * α)
    (Ch : ChainG D e f L m X tile τ) {k : ℕ} (hk1 : 1 ≤ k) (hke : k ≤ e + 1)
    (hrun : ∀ j, j < k → τ j = Ty.C1)
    (hsucc : k = m ∨ (k < m ∧ τ k ≠ Ty.B1 ∧ τ k ≠ Ty.C1)) : False := by
  rcases lt_trichotomy ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) with hab | hab | hba
  · exact corner_run_short_o S Co hab hef2 h2 Ch hk1 hke hrun hsucc
  · exact ab_ne S.he S.hef S.hco hab
  · rcases Nat.lt_or_ge e k with h | h
    · obtain rfl : k = e + 1 := by omega
      obtain ⟨hch, hM, hK2, hK3⟩ := corner_run_data S Co Ch hk1 hef2 hrun hsucc
      exact MO_corner_thick S Co hba hef2 h2 hch hM hK2 hK3
    · exact corner_run_short S Co Ch hk1 h hrun hsucc

end runthick

section corethick

variable {N : ℕ}

/-- the theorem `cornerrun_core` with the addendum for every member -/
theorem cornerrun_core_thick (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hA : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        3 * modelAlpha (e : ℝ) (f : ℝ))
    (hQ : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    (∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C2 (x₀ + j * (f : ℝ) ^ 2)))) ∨
    (∃ (k : ℕ) (t : ℕ → Fin N), e + 1 ≤ k ∧ k ≤ f - 1 ∧
      (∀ j, j < k → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 ((j : ℝ) * (f : ℝ) ^ 2)) ∧
      ((k : ℝ) * (f : ℝ) ^ 2 = dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.A2
          ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.B2
          ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.C2
          ((k : ℝ) * (f : ℝ) ^ 2))) ∧
      (∃ T, MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (t 0) T) ∧
      (cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
          2 * modelAlpha (e : ℝ) (f : ℝ) → e + 2 ≤ k)) := by
  obtain ⟨D, g, L, ax, ay, hL, hLd, hD, hP, hB, S, Co, h2⟩ :=
    setup_of_corners e f he hef hco D₀ hMod τ hA hQ
  obtain ⟨m, X, tile, τc, Ch⟩ := S.exists_chainG
  rcases corner_side_theorem S Co Ch with ⟨i, him, hrun⟩ | ⟨k, hk1, hkf, hkm, hrun, hsucc⟩
  · -- alternative (i)
    left
    have hf2 := S.hf2
    have hx0 := Ch.nonneg S (k := i) (by omega)
    have hend : X (i + f) ≤ L := by
      have h1 := (S.baseTile_range (Ch.htile (i + f - 1) (by omega))).2
      have h2 := Ch.hstep (i + f - 1) (by omega)
      rw [show i + f - 1 + 1 = i + f by omega] at h2
      linarith
    rcases hrun with hrun | hrun
    · have hpos := Ch.run_pos (T := Ty.C1) (c := (f : ℝ) ^ 2) rfl him hrun
      have hXf : X (i + f) = X i + f * (f : ℝ) ^ 2 := hpos f le_rfl
      refine ⟨X i, fun j => tile (i + j), hx0, by rw [hLd]; linarith, Or.inl (fun j hj => ?_)⟩
      have h := Ch.htile (i + j) (by omega)
      rw [hrun j hj, hpos j hj.le] at h
      exact laysOn_of_baseTile hL hD hP hB h
    · have hpos := Ch.run_pos (T := Ty.C2) (c := (f : ℝ) ^ 2) rfl him hrun
      have hXf : X (i + f) = X i + f * (f : ℝ) ^ 2 := hpos f le_rfl
      refine ⟨X i, fun j => tile (i + j), hx0, by rw [hLd]; linarith, Or.inr (fun j hj => ?_)⟩
      have h := Ch.htile (i + j) (by omega)
      rw [hrun j hj, hpos j hj.le] at h
      exact laysOn_of_baseTile hL hD hP hB h
  · -- alternative (ii)
    right
    have hsucc' : k = m ∨ (k < m ∧ τc k ≠ Ty.B1 ∧ τc k ≠ Ty.C1) := by
      rcases hsucc with h | ⟨h, h'⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
    have hpos := run_positions S Ch hkm hrun
    have hek : e + 1 ≤ k := by
      by_contra hlt
      exact corner_run_short S Co Ch hk1 (by omega) hrun hsucc'
    refine ⟨k, tile, hek, by omega, fun j hj => ?_, ?_, ?_, ?_⟩
    · have h := Ch.htile j (by omega)
      rw [hrun j hj, hpos j hj.le] at h
      exact laysOn_of_baseTile hL hD hP hB h
    · rcases hsucc with h | ⟨h, h'⟩
      · left
        calc (k : ℝ) * (f : ℝ) ^ 2 = X k := (hpos k le_rfl).symm
          _ = X m := by rw [h]
          _ = L := Ch.hXm
          _ = dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := hLd.symm
      · right
        have hb := Ch.htile k h
        rw [hpos k le_rfl] at hb
        rcases h' with h' | h' | h'
        · rw [h'] at hb
          exact Or.inl ⟨tile k, laysOn_of_baseTile hL hD hP hB hb⟩
        · rw [h'] at hb
          exact Or.inr (Or.inl ⟨tile k, laysOn_of_baseTile hL hD hP hB hb⟩)
        · rw [h'] at hb
          exact Or.inr (Or.inr ⟨tile k, laysOn_of_baseTile hL hD hP hB hb⟩)
    · have hM := corner_run_mirror S Co Ch hk1 hkf hrun hsucc'
      have hU := Ch.htile 0 (by omega)
      rw [hrun 0 (by omega), Ch.hX0] at hU
      exact mirrorBeside_of_mirrorAt hD hP S hU hM
    · intro h2'
      by_contra hlt
      have hef2 : e + 1 < f := by omega
      exact corner_run_short_o_any S Co hef2 (h2 h2') Ch hk1 (by omega) hrun hsucc'


/-- **`thm_corner_run_ep1_thick`: THE CASE `k = e + 1` OF ALTERNATIVE (ii) OF `thm:cornerrun` IS IMPOSSIBLE FOR EVERY MEMBER** (S+; the addendum of `thm:cornerrun` without `a < b`): at a corner `A'` of angle `2α`,
alternative (ii) has `e + 2 ≤ k ≤ f − 1`.  (For `a < b` this is `thm_cornerrun_addendum`; the new content is `b < a`.) -/
theorem thm_corner_run_ep1_thick (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hA : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ))
    (hQ : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    (∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C2 (x₀ + j * (f : ℝ) ^ 2)))) ∨
    (∃ (k : ℕ) (t : ℕ → Fin N), e + 2 ≤ k ∧ k ≤ f - 1 ∧
      (∀ j, j < k → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 ((j : ℝ) * (f : ℝ) ^ 2)) ∧
      ((k : ℝ) * (f : ℝ) ^ 2 = dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.A2
          ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.B2
          ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.C2
          ((k : ℝ) * (f : ℝ) ^ 2))) ∧
      (∃ T, MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (t 0) T)) := by
  rcases cornerrun_core_thick e f he hef hco D₀ hMod τ (Or.inl hA) hQ with
    h | ⟨k, t, h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, t, h6 hA, h2, h3, h4, h5⟩

end corethick

#print axioms Erdos634.Draft.SplusThick.MO_main_thick
#print axioms Erdos634.Draft.SplusThick.corner_run_short_o_any
#print axioms Erdos634.Draft.SplusThick.thm_corner_run_ep1_thick

end Erdos634.Draft.SplusThick
