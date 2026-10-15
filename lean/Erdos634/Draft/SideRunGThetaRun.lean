/-
Draft/SideRunGThetaRun.lean  Part of `AllThreshold`.  Geometry, first file.

**The run lemmas for a side with the corners `α + β` at both ends.**  The existing lemmas do not apply: `kill_C2A_end` needs `1 ≤ i` and a γ-tile before the run;
`CornersG` fixes the right corner at β; `CornersA` the left corner at `2α` or `3α`; a single C2 (or C1) run spanning the whole side from `α+β` to `α+β` is covered by none of them.

The lemmas `K3G_run_end_gen`, `kill_C1A`, `kill_C2A_end` (`SideRunGCornerRules`, `SideRunGCornerSide`) read the right corner from a `CornersA` (they use only the field `hQ`), and `kill_C1G`, `kill_C2G` (`SideRunGSourcesB`)
read the right corner from `CornersG`; none can be applied to a triangle whose left corner is `α + β` and whose right corner is `α + β`.  Here the corners are hypotheses on the apex `(ax, ay)`:
`hQL : ∃ t > 0, ax = t e ∧ ay = t rt` (left corner `α + β`), `hBR : ∃ t > 0, ax = L − t e ∧ ay = t rt` (right corner `α + β`).

* `K3G_run_end_T`: (K3) at the right end of a run of `C1` that starts at any tile: the right corner is `α + β` (`bad_corner_right`) or the next tile is not `B1`, `C1` (`bad_nb`) -- the proof of `K3G_run_end_gen` with the field `hQ` replaced by `hBR`.
* `kill_C1T`: `L_k` for `C1`: a run of `k < f` tiles `C1` with (K1) and the chords at its first end that ends at the right corner or before a tile other than `B1`, `C1` does not exist (`kill_C1A` with `hBR`).
* `kill_C2T_start`: `L'_k` for `C2` that starts at the left corner `α + β` (condition (ii') at a corner `α + β`: the second tile there shows `α`): a run of `k < f` tiles `C2` from `Q`, with (K1) and the chords at its right end, does not exist
  (the branch "the run starts at `Q`" of `kill_C2G`, corner `α + β`, with the right end `X (i + k) ≤ L` an arbitrary point of the side).
* `kill_C2T`: `L'_k` for `C2`, both starts: the run starts at `Q` (`kill_C2T_start`) or follows a tile showing `γ` (`kill_C2A_core`).
* `kill_C2T_end`: `L'_k` for `C2` that ends the side (condition (i') at the right corner `α + β`: `K1_of_cornerR`, `hch_cornerR`): a run of `k < f` tiles `C2` that starts at `Q` or follows a tile showing `γ` does not end at `B`.  (Rule (d); for `i ≥ 1` this is `kill_C2A_end`
  with `hBR`; for `i = 0` it is the case of a C2 run that spans the whole side.)

Hypotheses.  As in `SideRunGCornerRules`: the statements conclude `False` (or (K3)) under the conditions of the run lemma; `hQL`, `hBR` are satisfied by the apex of the seed tiling of the isosceles triangle with base angles `α + β`
(the witnesses of `Draft/SideRunGThetaMain.lean`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGCornerSide
import Erdos634.Draft.SideRunGThetaWords

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGT

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

variable {N : ℕ} {D : CongruentDissection N}

/-! ## 1. (K3) at the right end of a run of `C1`, and `L_k` -/

section runc1

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- **(K3) at the right end `R` of a run of `k` tiles `C1` that starts at the tile `i` of the chain**, the right corner of the side being `α + β` (`hBR`): the run ends at the corner (`bad_corner_right`) or the next tile is not `B1`, `C1` (`bad_nb`).
(`K3G_run_end_gen` with the field `Co.hQ` replaced by `hBR`.) -/
theorem K3G_run_end_T (S : SetupG D e f α β γ L ax ay)
    (hBR : ∃ t : ℝ, 0 < t ∧ ax = L - t * (e : ℝ) ∧ ay = t * rtG (e : ℝ) (f : ℝ))
    (Ch : ChainG D e f L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hik : i + k ≤ m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C1)
    (hsucc : i + k = m ∨ (i + k < m ∧ τ (i + k) ≠ Ty.B1 ∧ τ (i + k) ≠ Ty.C1)) :
    K3G D (e : ℝ) (f : ℝ) 1 (X i) (k : ℝ) 0 := by
  have C : CtxBase D e f α β γ L ax ay 1 (X i) := ⟨S, Or.inl rfl⟩
  have he0 := S.e0
  have hef := S.hef'
  have hhp := hhG_pos he0 hef
  have hc := S.c_pos
  have hpos := Ch.run_pos (T := Ty.C1) (c := (f : ℝ) ^ 2) rfl hik hrun
  have hxR : X (i + k) = X i + (k : ℝ) * (f : ℝ) ^ 2 := hpos k le_rfl
  have hk0 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
  have hlast := Ch.htile (i + (k - 1)) (by omega)
  rw [hrun (k - 1) (by omega)] at hlast
  have hposl := hpos (k - 1) (by omega)
  rw [hk0] at hposl
  have hU := S.c1_lpG (x := X i) (ξ := (k : ℝ) - 1) hlast hposl
  have hG1 : 0 < (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) (0 + 1)) 1 := by
    rw [lpG_snd]; linarith
  have hA₀ : (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) 0) 1 = 0 := by rw [lpG_snd]; ring
  have eV : lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1 + 1) 0 = mkPt (X (i + k)) 0 := by
    unfold lpG; exact mkPt_congr (by rw [hxR]; ring) (by ring)
  have eA : lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) 0 = mkPt (X (i + k) - (f : ℝ) ^ 2) 0 := by
    unfold lpG; exact mkPt_congr (by rw [hxR]; ring) (by ring)
  have eG : lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) (0 + 1)
      = mkPt (X (i + k) - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) := by
    unfold lpG; exact mkPt_congr (by rw [hxR]; ring) (by ring)
  have hβ0 : (D.tile (tile (i + (k - 1)))).localAngle (mkPt (X (i + k)) 0) = β := by
    have e' : X (i + (k - 1)) + Ty.lenG (e : ℝ) (f : ℝ) Ty.C1 = X (i + k) := by
      show X (i + (k - 1)) + (f : ℝ) ^ 2 = _
      rw [hposl, hxR]; ring
    have h := (S.angles hlast).2
    rw [e'] at h
    exact h
  have hU' := hU
  rw [eV] at hU'
  rcases hsucc with hend | ⟨hlt, hZ1, hZ2⟩
  · -- the run ends at the corner `B` of angle `α + β`
    have hXL : X (i + k) = L := by rw [hend]; exact Ch.hXm
    obtain ⟨t, ht, hax, hay⟩ := hBR
    have hQ := corner_right_ab S ht hax hay
    have hRmem : mkPt L 0 ∈ D.target.carrier := by
      rw [← hXL, ← eV]; exact hU.mem₂
    have hGmem : mkPt (L - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) ∈ D.target.carrier := by
      rw [← hXL, ← eG]; exact hU.mem₃
    have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1 + 1) 0)
        (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
      rw [eV, eG, hXL]
      exact hint_right_ab S ht hax hay hRmem hGmem
    refine C.K3G_of_next hU hint (fun W Z hW hθ hZ => ?_)
    rw [eV, hXL] at hW hθ
    rw [hXL] at hU' hβ0
    exact bad_corner_right S hQ hG1 hU' hA₀ hβ0 hW hθ hZ
  · -- the run ends before a tile other than `B1`, `C1`
    have hx0 : 0 < X (i + k) := Ch.pos S (by omega) (by omega)
    have hxL : X (i + k) < L := Ch.lt_L S hlt
    have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1 + 1) 0)
        (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
      rw [eV]
      refine S.interior_seg (Ch.mem hlt) hU.mem₃ (Or.inr hG1) (Or.inl ?_) (Or.inl ?_)
      · rw [gA_mk]; nlinarith [mul_pos S.hay hx0]
      · rw [gB_mk]; nlinarith [mul_pos S.hay (sub_pos.mpr hxL)]
    have hj := Ch.htile (i + k) hlt
    have hjang := (S.angles hj).1
    have hlenpos := Ty.lenG_pos he0 hef (τ (i + k))
    obtain ⟨T, hT⟩ : ∃ T, τ (i + k) = T := ⟨_, rfl⟩
    rw [hT] at hZ1 hZ2 hjang
    have hθj : (D.tile (tile (i + k))).localAngle (mkPt (X (i + k)) 0) = γ ∨
        (D.tile (tile (i + k))).localAngle (mkPt (X (i + k)) 0) = β := by
      rw [hjang]
      cases T
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact absurd rfl hZ1
      · exact Or.inl rfl
      · exact absurd rfl hZ2
      · exact Or.inr rfl
    obtain ⟨kj, mj, jj, -, -, -, -, hmj, -, -⟩ := hj
    refine C.K3G_of_next hU hint (fun W Z hW hθ hZ => ?_)
    rw [eV] at hW hθ
    refine S.bad_nb hx0 hxL hG1 hU' hA₀ hβ0 hmj (mkPt_one _ _)
      (mkPt_ne_of_fst (by linarith)) ?_ hθj hW hθ hZ
    rw [eA]; exact mkPt_ne_of_fst (by linarith)

/-- **`L_k` for a run of `C1`, the right corner `α + β`**: a run of `k < f` tiles `C1` with (K1) and the chords at its first end that ends at the right corner or before a tile other than `B1`, `C1` does not exist. -/
theorem kill_C1T (S : SetupG D e f α β γ L ax ay)
    (hBR : ∃ t : ℝ, 0 < t ∧ ax = L - t * (e : ℝ) ∧ ay = t * rtG (e : ℝ) (f : ℝ))
    (Ch : ChainG D e f L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hkf : k < f) (hik : i + k ≤ m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C1) {x : ℝ} (hxi : X i = x)
    (hK1 : ∀ (t' : Fin N) (k' m' : Fin 3), k' ≠ m' → (D.tile t').pts k' = lpG (e : ℝ) (f : ℝ) 1 x 0 0 →
      (D.tile t').pts m' = lpG (e : ℝ) (f : ℝ) 1 x 0 1 →
      (∀ i', FXG (e : ℝ) (f : ℝ) 1 ((D.tile t').pts i') ≤ lvG (e : ℝ) (f : ℝ) 1 x 0) → False)
    (hch : ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) 1 x 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 0) (lpG (e : ℝ) (f : ℝ) 1 x 0 j) ⊆ interior D.target.carrier)
    (hsucc : i + k = m ∨ (i + k < m ∧ τ (i + k) ≠ Ty.B1 ∧ τ (i + k) ≠ Ty.C1)) : False := by
  subst hxi
  have C : CtxG D e f α β γ L ax ay 1 (X i) := ⟨⟨S, Or.inl rfl⟩, hK1, hch⟩
  have hpos := Ch.run_pos (T := Ty.C1) (c := (f : ℝ) ^ 2) rfl hik hrun
  have hUT : ∀ j : ℕ, j < k → UTG D (e : ℝ) (f : ℝ) 1 (X i) j 0 := by
    intro j hj
    have h := Ch.htile (i + j) (by omega)
    rw [hrun j hj] at h
    exact ⟨tile (i + j), S.c1_lpG h (hpos j hj.le)⟩
  exact C.run_diesG hk1 hkf hUT (K3G_run_end_T S hBR Ch hk1 hik hrun hsucc)

end runc1

/-! ## 2. The mirror run lemma `L'_k` for a run of `C2` that starts at the left corner `α + β` -/

section runc2

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- **`L'_k` for `C2` that starts at the left corner `Q`, of angle `α + β`** (`hQL`): a run of `k < f` tiles `C2` from `Q`, ending at `(X (i + k), 0)` with (K1) and the chords there (`C : CtxG` for `ε = -1`), does not exist
(condition (ii') at a corner `α + β`: the second tile at `Q` shows `α`; `bad_corner`).  The point `X (i + k)` may be the right end of the side. -/
theorem kill_C2T_start (S : SetupG D e f α β γ L ax ay)
    (hQL : ∃ t : ℝ, 0 < t ∧ ax = t * (e : ℝ) ∧ ay = t * rtG (e : ℝ) (f : ℝ))
    (Ch : ChainG D e f L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hkf : k < f) (hik : i + k ≤ m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C2) (hi0 : i = 0)
    (C : CtxG D e f α β γ L ax ay (-1) (X (i + k))) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have hhp := hhG_pos he0 hef
  have hc := S.c_pos
  have hpos := Ch.run_pos (T := Ty.C2) (c := (f : ℝ) ^ 2) rfl hik hrun
  have hx : X (i + k) = X i + (k : ℝ) * (f : ℝ) ^ 2 := hpos k le_rfl
  have hUT : ∀ j : ℕ, j < k → UTG D (e : ℝ) (f : ℝ) (-1) (X (i + k)) j 0 := by
    intro j hj
    have h := Ch.htile (i + (k - 1 - j)) (by omega)
    rw [hrun (k - 1 - j) (by omega)] at h
    have hcj : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
      rw [Nat.cast_sub (show j ≤ k - 1 by omega), Nat.cast_sub hk1, Nat.cast_one]
    refine ⟨tile (i + (k - 1 - j)), S.c2_lpG h ?_⟩
    rw [hpos (k - 1 - j) (by omega), hcj, hx]; ring
  refine C.run_diesG hk1 hkf hUT ?_
  have hτi : τ i = Ty.C2 := by
    have h := hrun 0 (by omega)
    rwa [Nat.add_zero] at h
  have hC2 := Ch.htile i (by omega)
  rw [hτi] at hC2
  have hU := S.c2_lpG (x := X (i + k)) (ξ := (k : ℝ) - 1) hC2 (by rw [hx]; ring)
  have hG1 : 0 < (lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1) (0 + 1)) 1 := by
    rw [lpG_snd]; linarith
  have hA1 : (lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1) 0) 1 = 0 := by rw [lpG_snd]; ring
  have eV : lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1 + 1) 0 = mkPt (X i) 0 := by
    unfold lpG; exact mkPt_congr (by rw [hx]; ring) (by ring)
  have hβ0 : (D.tile (tile i)).localAngle (mkPt (X i) 0) = β := (S.angles hC2).1
  have hU' := hU
  rw [eV] at hU'
  have hXi : X i = 0 := by rw [hi0]; exact Ch.hX0
  obtain ⟨t, ht, hax, hay⟩ := hQL
  have hQ := S.corner_left_ab ht hax hay
  rw [hXi] at eV hβ0 hU'
  have eG : lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1) (0 + 1)
      = mkPt (uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) := by
    unfold lpG; exact mkPt_congr (by rw [hx, hXi]; ring) (by ring)
  have hGmem : mkPt (uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) ∈ D.target.carrier := by
    rw [← eG]; exact hU.mem₃
  have hQmem : mkPt 0 0 ∈ D.target.carrier := by
    have := Ch.mem (k := i) (by omega)
    rwa [hXi] at this
  have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1 + 1) 0)
      (lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
    rw [eV, eG]
    have hu := uuG_spec he0 hef
    have hh' := hhG_spec he0 hef
    have hrt := rtG_pos he0 hef
    have key : 2 * (f : ℝ) ^ 2 * (rtG (e : ℝ) (f : ℝ) * uuG (e : ℝ) (f : ℝ) - (e : ℝ) * hhG (e : ℝ) (f : ℝ))
        = 2 * (f : ℝ) ^ 2 * (rtG (e : ℝ) (f : ℝ) * (e : ℝ) ^ 2) := by
      linear_combination (rtG (e : ℝ) (f : ℝ)) * hu - (e : ℝ) * hh'
    have hX : rtG (e : ℝ) (f : ℝ) * uuG (e : ℝ) (f : ℝ) - (e : ℝ) * hhG (e : ℝ) (f : ℝ)
        = rtG (e : ℝ) (f : ℝ) * (e : ℝ) ^ 2 :=
      mul_left_cancel₀ (two_f2_pos he0 hef).ne' key
    refine S.interior_seg hQmem hGmem (Or.inr (by rw [mkPt_one]; exact hhp)) (Or.inr ?_)
      (Or.inl ?_)
    · rw [gA_mk, hax, hay]
      have e' : t * rtG (e : ℝ) (f : ℝ) * uuG (e : ℝ) (f : ℝ) - t * (e : ℝ) * hhG (e : ℝ) (f : ℝ)
          = t * (rtG (e : ℝ) (f : ℝ) * (e : ℝ) ^ 2) := by
        linear_combination t * hX
      rw [e']; positivity
    · rw [gB_mk]; nlinarith [mul_pos S.hay S.hL]
  refine C.K3G_of_next hU hint (fun W Z hW hθ hZ => ?_)
  rw [eV] at hW hθ
  exact S.bad_corner hQ hG1 hU' hA1 hβ0 hW hθ hZ

/-- **`L'_k` for `C2`, both starts**: a run of `k < f` tiles `C2` ending at `(X (i+k), 0)` with (K1) and the chords there that starts at the left corner `Q` of angle `α + β` or follows a tile showing `γ` at its right end does not exist. -/
theorem kill_C2T (S : SetupG D e f α β γ L ax ay)
    (hQL : ∃ t : ℝ, 0 < t ∧ ax = t * (e : ℝ) ∧ ay = t * rtG (e : ℝ) (f : ℝ))
    (Ch : ChainG D e f L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hkf : k < f) (hik : i + k ≤ m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C2) (hpred : i = 0 ∨ (τ (i - 1)).gR)
    (C : CtxG D e f α β γ L ax ay (-1) (X (i + k))) : False := by
  rcases Nat.eq_zero_or_pos i with hi0 | hi1
  · exact kill_C2T_start S hQL Ch hk1 hkf hik hrun hi0 C
  · have hg : (τ (i - 1)).gR := by
      rcases hpred with h | h
      · omega
      · exact h
    exact kill_C2A_core S Ch hk1 hkf hik hrun hi1 hg C

/-- **`L'_k` for `C2` that ends the side** (rule (d); condition (i') at the right corner `α + β`, `hBR`): a run of `k < f` tiles `C2` that starts at the left corner `α + β` or follows a tile showing `γ` does not end at the right corner `B`.
(For `i ≥ 1` this is `kill_C2A_end`; for `i = 0` the run spans the whole side.) -/
theorem kill_C2T_end (S : SetupG D e f α β γ L ax ay)
    (hQL : ∃ t : ℝ, 0 < t ∧ ax = t * (e : ℝ) ∧ ay = t * rtG (e : ℝ) (f : ℝ))
    (hBR : ∃ t : ℝ, 0 < t ∧ ax = L - t * (e : ℝ) ∧ ay = t * rtG (e : ℝ) (f : ℝ))
    (Ch : ChainG D e f L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hkf : k < f) (hik : i + k = m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C2) (hpred : i = 0 ∨ (τ (i - 1)).gR) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have hXL : X (i + k) = L := by rw [hik]; exact Ch.hXm
  have hpos := Ch.run_pos (T := Ty.C2) (c := (f : ℝ) ^ 2) rfl (by omega : i + k ≤ m) hrun
  have hxk : X (i + k) = X i + (k : ℝ) * (f : ℝ) ^ 2 := hpos k le_rfl
  have hk0 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
  have hposl := hpos (k - 1) (by omega)
  rw [hk0] at hposl
  have hlast := Ch.htile (i + (k - 1)) (by omega)
  rw [hrun (k - 1) (by omega)] at hlast
  have e' : X (i + (k - 1)) + Ty.lenG (e : ℝ) (f : ℝ) Ty.C2 = L := by
    show X (i + (k - 1)) + (f : ℝ) ^ 2 = _
    rw [← hXL, hxk, hposl]; ring
  have hmem : mkPt L 0 ∈ D.target.carrier := by
    obtain ⟨k', m', j', -, -, -, -, hm', -, -⟩ := hlast
    rw [e'] at hm'
    rw [← hm']; exact pts_mem_target D.toDissection (tile (i + (k - 1))) m'
  obtain ⟨t, ht, hax, hay⟩ := hBR
  have hQ := corner_right_ab S ht hax hay
  have hxL' : X (i + (k - 1)) = L - (0 + 1) * (f : ℝ) ^ 2 := by
    rw [← hXL, hxk, hposl]; ring
  have h0 := S.c2_lpG (x := L) (ξ := 0) hlast hxL'
  have hK1 := K1_of_cornerR S hQ h0
  have hch := hch_cornerR S ht hax hay hmem
  rw [← hXL] at hK1 hch
  exact kill_C2T S hQL Ch hk1 hkf (by omega) hrun hpred ⟨⟨S, Or.inr rfl⟩, hK1, hch⟩

end runc2

end Erdos634.Draft.SideRunGT

#print axioms Erdos634.Draft.SideRunGT.K3G_run_end_T
#print axioms Erdos634.Draft.SideRunGT.kill_C1T
#print axioms Erdos634.Draft.SideRunGT.kill_C2T_start
#print axioms Erdos634.Draft.SideRunGT.kill_C2T
#print axioms Erdos634.Draft.SideRunGT.kill_C2T_end
