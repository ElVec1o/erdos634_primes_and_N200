/-
Draft/SideRunGThetaRules.lean  Part of `AllThreshold`.  Geometry, second file.

**The rules of a side with the corners `α + β`, `α + β`, and the side theorem for it**: if a side `s` of a triangle cut into copies of the tile has the angle `α + β` at both corners, then `s`
carries `f` consecutive tiles of type `C1` or `f` of type `C2`; in particular `|s| ≥ f³`.  Word part: `Draft/SideRunGThetaWords.lean` (`SideRulesT`, `side_word_T`); the run lemmas: `Draft/SideRunGThetaRun.lean`.

CONTENTS.
* `CornersT e f L ax ay`: the corners of the side `QB`: `α + β` at `Q` (`ax = t e`, `ay = t rt`) and `α + β` at `B` (`ax = L − t e`, `ay = t rt`).  (These force `t` equal at both corners: `L = 2 t e`, the apex over the midpoint.)
* `rQ_T` (the first tile is not of type `L`: the corner `α + β` is smaller than `γ`), `rB_T` (the last tile is not of type `R`: the same at `B`), `rGG_T` (= `SideRunGA.rGG_A`), `ra_T`, `rb_T`, `rc_T` (rules (a), (b), (c), with rule (d) in (b): a maximal
  run of `C2` that is first or follows a tile of type `R` does not end the side), `side_rulesT : SideRulesT f m τ`.
* `side_theoremT`, `side_theoremT_chain`: the side theorem in the chain form; `side_theorem_paperT`: the paper form: there are `x₀ ≥ 0` and tiles `t 0, …, t (f−1)` with `BaseTileG … C1 (x₀ + j f²)` for all `j < f`, or the same with `C2`, and `x₀ + f·f² ≤ L`; in particular `f³ ≤ L`.
* `theta_counts`: the counts on the side: a `SetupG` with `CornersT` has naturals `x, y, z` with `x (e f) + y (f² − e²) + z f² = L` and `f ≤ z`.

The proofs are those of `side_rulesG` (`SideRunGRules`) and `ra_A`, `rb_A`, `rc_A` (`SideRunGCornerSide`) with `kill_C1T`, `kill_C2T`, `kill_C2T_end` for `kill_C1G`/`kill_C1A`, `kill_C2G`/`kill_C2A`, `kill_C2A_end`, and the runs allowed to start at `Q` (the corner `α + β`: `K1_of_corner`, `hch_corner`).

Hypotheses.  `SideRulesT` is satisfiable (`exRulesT`); `SetupG` and `CornersT` are satisfied by the seed tilings of the isosceles triangle with base angles `α + β` (`Draft/SideRunGThetaMain.lean`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGThetaRun
import Erdos634.Draft.SideRunGRules

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

/-- **The corners of the side `QB`: `α + β` at `Q` and `α + β` at `B`.** -/
structure CornersT (e f : ℕ) (L ax ay : ℝ) : Prop where
  hQ : ∃ t : ℝ, 0 < t ∧ ax = t * (e : ℝ) ∧ ay = t * rtG (e : ℝ) (f : ℝ)
  hB : ∃ t : ℝ, 0 < t ∧ ax = L - t * (e : ℝ) ∧ ay = t * rtG (e : ℝ) (f : ℝ)

section rules

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- the first tile of the side does not show `γ` at its left end: the left corner is `α + β` and `γ > α + β` -/
theorem rQ_T (S : SetupG D e f α β γ L ax ay) (Co : CornersT e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) : τ 0 ≠ Ty.A2 ∧ τ 0 ≠ Ty.B2 := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hm0 := Ch.hm0
  have h := Ch.htile 0 hm0
  rw [Ch.hX0] at h
  have ha := (S.angles h).1
  have hle := one_angle_le D.toDissection (mkPt 0 0) (tile 0)
  obtain ⟨t, ht, hax, hay⟩ := Co.hQ
  have hQ := (S.corner_left_ab ht hax hay).le
  have hγdef := S.hA.hγdef
  constructor
  · intro hT
    rw [hT] at ha
    have ha' : (D.tile (tile 0)).localAngle (mkPt 0 0) = γ := ha
    rw [ha'] at hle
    linarith
  · intro hT
    rw [hT] at ha
    have ha' : (D.tile (tile 0)).localAngle (mkPt 0 0) = γ := ha
    rw [ha'] at hle
    linarith

/-- the last tile of the side does not show `γ` at its right end: the right corner is `α + β` and `γ > α + β` -/
theorem rB_T (S : SetupG D e f α β γ L ax ay) (Co : CornersT e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) : ¬ (τ (m - 1)).gR := by
  intro hg
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hm0 := Ch.hm0
  have h := Ch.htile (m - 1) (by omega)
  have hx := Ch.prev hm0 le_rfl
  rw [Ch.hXm] at hx
  have ha := (S.angles h).2
  rw [hx, Ty.aR_of_gR α β γ hg] at ha
  have hle := one_angle_le D.toDissection (mkPt L 0) (tile (m - 1))
  rw [ha] at hle
  obtain ⟨t, ht, hax, hay⟩ := Co.hB
  have hcorner : D.target.localAngle (mkPt L 0) ≤ α + β := (corner_right_ab S ht hax hay).le
  linarith

/-- **rule (a)**: a maximal run of `C1`, shorter than `f`, that is first or follows a tile of type `R` is followed by `B1` (or `C1`) -/
theorem ra_T (S : SetupG D e f α β γ L ax ay) (Co : CornersT e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) :
    ∀ i k, 1 ≤ k → k < f → i + k ≤ m → (∀ j, j < k → τ (i + j) = Ty.C1) →
      (i = 0 ∨ (τ (i - 1)).gR) → i + k < m ∧ (τ (i + k) = Ty.B1 ∨ τ (i + k) = Ty.C1) := by
  have he0 := S.e0
  have hef := S.hef'
  intro i k hk1 hkn hik hrun hp
  by_contra hcon
  have hsucc : i + k = m ∨ (i + k < m ∧ τ (i + k) ≠ Ty.B1 ∧ τ (i + k) ≠ Ty.C1) := by
    rcases Nat.lt_or_ge (i + k) m with h | h
    · exact Or.inr ⟨h, fun hB => hcon ⟨h, Or.inl hB⟩, fun hC => hcon ⟨h, Or.inr hC⟩⟩
    · exact Or.inl (by omega)
  have hτi : τ i = Ty.C1 := by
    have h := hrun 0 (by omega)
    rwa [Nat.add_zero] at h
  have h00 := Ch.htile i (by omega)
  rw [hτi] at h00
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- the run starts at the left corner `Q`, of angle `α + β`
    have hXi : X i = 0 := by rw [hi0]; exact Ch.hX0
    have hQmem : mkPt 0 0 ∈ D.target.carrier := by
      have := Ch.mem (k := i) (by omega)
      rwa [hXi] at this
    obtain ⟨t, ht, hax, hay⟩ := Co.hQ
    have hQ := S.corner_left_ab ht hax hay
    have hU0 := S.c1_lpG (x := (0 : ℝ)) (ξ := 0) h00 (by rw [hXi]; ring)
    exact kill_C1T S Co.hB Ch hk1 hkn hik hrun hXi (S.K1_of_corner (by norm_num) hQ hU0)
      (S.hch_corner ht hax hay hQmem) hsucc
  · have hg : (τ (i - 1)).gR := by
      rcases hp with h | h
      · omega
      · exact h
    have hx0 : 0 < X i := Ch.pos S hipos (by omega)
    have hxL : X i < L := Ch.lt_L S (by omega)
    have hU0 := S.c1_lpG (x := X i) (ξ := 0) h00 (by ring)
    have hpj := Ch.htile (i - 1) (by omega)
    have e' := Ch.prev hipos (by omega : i ≤ m)
    have hγj : (D.tile (tile (i - 1))).localAngle (mkPt (X i) 0) = γ := by
      have h := (S.angles hpj).2
      rw [e', Ty.aR_of_gR α β γ hg] at h
      exact h
    have hlam : (τ (i - 1)).lenG (e : ℝ) (f : ℝ) = (e : ℝ) * (f : ℝ) ∨
        (τ (i - 1)).lenG (e : ℝ) (f : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rcases hg with h | h
      · rw [h]; exact Or.inl rfl
      · rw [h]; exact Or.inr rfl
    obtain ⟨kj, mj, jj, hkmj, -, -, hkj, hmj, -, -⟩ := hpj
    rw [e'] at hmj
    have hkj' : (D.tile (tile (i - 1))).pts kj
        = mkPt (X i - 1 * (τ (i - 1)).lenG (e : ℝ) (f : ℝ)) 0 := by
      rw [hkj]; exact mkPt_congr (by rw [← e']; ring) rfl
    exact kill_C1T S Co.hB Ch hk1 hkn hik hrun rfl
      (S.K1_of_gamma (by norm_num) hx0 hxL hU0 (Ne.symm hkmj) hmj hkj' hlam hγj)
      (S.hch_pos hx0 hxL (Ch.mem (by omega))) hsucc

/-- **rule (b) with rule (d)**: a maximal run of `C2`, shorter than `f`, that is first or follows a tile of type `R` is followed by a tile (it does not end the side) that is not of type `L` -/
theorem rb_T (S : SetupG D e f α β γ L ax ay) (Co : CornersT e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) :
    ∀ i k, 1 ≤ k → k < f → i + k ≤ m → (∀ j, j < k → τ (i + j) = Ty.C2) →
      (i = 0 ∨ (τ (i - 1)).gR) → i + k < m ∧ ¬ (τ (i + k)).gL := by
  have he0 := S.e0
  have hef := S.hef'
  intro i k hk1 hkn hik hrun hp
  rcases Nat.lt_or_ge (i + k) m with hlt | hge
  · refine ⟨hlt, fun hgL => ?_⟩
    have hx0 : 0 < X (i + k) := Ch.pos S (by omega) (by omega)
    have hxL : X (i + k) < L := Ch.lt_L S hlt
    have hlast := Ch.htile (i + (k - 1)) (by omega)
    rw [hrun (k - 1) (by omega)] at hlast
    have hstep := Ch.hstep (i + (k - 1)) (by omega)
    rw [hrun (k - 1) (by omega), show i + (k - 1) + 1 = i + k by omega] at hstep
    have hU0 := S.c2_lpG (x := X (i + k)) (ξ := 0) hlast (by
      have h' : X (i + k) = X (i + (k - 1)) + (f : ℝ) ^ 2 := hstep
      rw [h']; ring)
    have hj := Ch.htile (i + k) hlt
    have hγj : (D.tile (tile (i + k))).localAngle (mkPt (X (i + k)) 0) = γ := by
      have h := (S.angles hj).1
      rw [Ty.aL_of_gL α β γ hgL] at h
      exact h
    have hlam : (τ (i + k)).lenG (e : ℝ) (f : ℝ) = (e : ℝ) * (f : ℝ) ∨
        (τ (i + k)).lenG (e : ℝ) (f : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rcases hgL with h | h
      · rw [h]; exact Or.inl rfl
      · rw [h]; exact Or.inr rfl
    obtain ⟨kj, mj, jj, hkmj, -, -, hkj, hmj, -, -⟩ := hj
    have hmj' : (D.tile (tile (i + k))).pts mj
        = mkPt (X (i + k) - (-1) * (τ (i + k)).lenG (e : ℝ) (f : ℝ)) 0 := by
      rw [hmj]; exact mkPt_congr (by ring) rfl
    exact kill_C2T S Co.hQ Ch hk1 hkn hlt.le hrun hp
      ⟨⟨S, Or.inr rfl⟩,
        S.K1_of_gamma (by norm_num) hx0 hxL hU0 hkmj hkj hmj' hlam hγj,
        S.hch_pos hx0 hxL (Ch.mem hlt)⟩
  · exact (kill_C2T_end S Co.hQ Co.hB Ch hk1 hkn (by omega) hrun hp).elim

/-- **rule (c)**: runs `C2^s C1^r`, shorter than `f`, that are first or follow a tile of type `R`, are followed by `B1` (or `C1`) -/
theorem rc_T (S : SetupG D e f α β γ L ax ay) (Co : CornersT e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) :
    ∀ i s r, 1 ≤ s → s < f → 1 ≤ r → r < f → i + s + r ≤ m →
      (∀ j, j < s → τ (i + j) = Ty.C2) → (∀ j, j < r → τ (i + s + j) = Ty.C1) →
      (i = 0 ∨ (τ (i - 1)).gR) →
      i + s + r < m ∧ (τ (i + s + r) = Ty.B1 ∨ τ (i + s + r) = Ty.C1) := by
  have he0 := S.e0
  have hef := S.hef'
  intro i s r hs1 hsn hr1 hrn hisr hrun2 hrun1 hp
  have hJ0 : 0 < X (i + s) := Ch.pos S (by omega) (by omega)
  have hJL : X (i + s) < L := Ch.lt_L S (by omega)
  have hτ1 : τ (i + s) = Ty.C1 := by
    have h := hrun1 0 (by omega)
    rwa [Nat.add_zero] at h
  have h1 := Ch.htile (i + s) (by omega)
  rw [hτ1] at h1
  have hU1 := S.c1_lpG (x := X (i + s)) (ξ := 0) h1 (by ring)
  have hlast := Ch.htile (i + (s - 1)) (by omega)
  rw [hrun2 (s - 1) (by omega)] at hlast
  have hstep := Ch.hstep (i + (s - 1)) (by omega)
  rw [hrun2 (s - 1) (by omega), show i + (s - 1) + 1 = i + s by omega] at hstep
  have hU2 := S.c2_lpG (x := X (i + s)) (ξ := 0) hlast (by
    have h' : X (i + s) = X (i + (s - 1)) + (f : ℝ) ^ 2 := hstep
    rw [h']; ring)
  rcases S.junction hJ0 hJL hU1 hU2 with hK | hK
  · by_contra hcon
    have hsucc : i + s + r = m ∨
        (i + s + r < m ∧ τ (i + s + r) ≠ Ty.B1 ∧ τ (i + s + r) ≠ Ty.C1) := by
      rcases Nat.lt_or_ge (i + s + r) m with h | h
      · exact Or.inr ⟨h, fun hB => hcon ⟨h, Or.inl hB⟩, fun hC => hcon ⟨h, Or.inr hC⟩⟩
      · exact Or.inl (by omega)
    exact kill_C1T S Co.hB Ch hr1 hrn hisr hrun1 rfl hK
      (S.hch_pos hJ0 hJL (Ch.mem (by omega))) hsucc
  · exact (kill_C2T S Co.hQ Ch hs1 hsn (by omega) hrun2 hp
      ⟨⟨S, Or.inr rfl⟩, hK, S.hch_pos hJ0 hJL (Ch.mem (by omega))⟩).elim

/-- **THE TYPED WORD OF A SIDE WITH THE CORNERS `α + β`, `α + β` SATISFIES THE RULES `SideRulesT`** -/
theorem side_rulesT (S : SetupG D e f α β γ L ax ay) (Co : CornersT e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) : SideRulesT f m τ :=
  ⟨rQ_T S Co Ch, rB_T S Co Ch, rGG_A S Ch, ra_T S Co Ch, rb_T S Co Ch, rc_T S Co Ch⟩

/-- **S7, chain form**: the side carries `f` consecutive tiles of type `C1` or `f` consecutive tiles of type `C2`. -/
theorem side_theoremT (S : SetupG D e f α β γ L ax ay) (Co : CornersT e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) :
    ∃ i, i + f ≤ m ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2)) :=
  side_word_T f m τ Ch.hm0 (side_rulesT S Co Ch)

/-- S7 with the chain of the dissection -/
theorem side_theoremT_chain (S : SetupG D e f α β γ L ax ay) (Co : CornersT e f L ax ay) :
    ∃ (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty), ChainG D e f L m X tile τ ∧
      ∃ i, i + f ≤ m ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2)) := by
  obtain ⟨m, X, tile, τ, Ch⟩ := S.exists_chainG
  exact ⟨m, X, tile, τ, Ch, side_theoremT S Co Ch⟩

/-- **S7, paper form** (normal position): there are `x₀ ≥ 0` and `f` tiles `t 0, …, t (f−1)` that lay their side `c` on the side `s = [Q, B]` at `x₀, x₀ + c, …` and show `α` at the same end of it (all at the left end: type `C1`; all at the right end: type `C2`),
with `x₀ + f·f² ≤ L`; in particular `f³ ≤ L`. -/
theorem side_theorem_paperT (S : SetupG D e f α β γ L ax ay) (Co : CornersT e f L ax ay) :
    ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧ x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ L ∧
      ((∀ j, j < f → BaseTileG D (e : ℝ) (f : ℝ) (t j) Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → BaseTileG D (e : ℝ) (f : ℝ) (t j) Ty.C2 (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ L := by
  obtain ⟨m, X, tile, τ, Ch, i, him, hrun⟩ := side_theoremT_chain S Co
  have hf2 := S.hf2
  have hx0 := Ch.nonneg S (k := i) (by omega)
  have hend : X (i + f) ≤ L := by
    have h1 := (S.baseTile_range (Ch.htile (i + f - 1) (by omega))).2
    have h2 := Ch.hstep (i + f - 1) (by omega)
    rw [show i + f - 1 + 1 = i + f by omega] at h2
    linarith
  have hfc : (f : ℝ) * (f : ℝ) ^ 2 = (f : ℝ) ^ 3 := by ring
  rcases hrun with hrun | hrun
  · have hpos := Ch.run_pos (T := Ty.C1) (c := (f : ℝ) ^ 2) rfl him hrun
    have hXf : X (i + f) = X i + f * (f : ℝ) ^ 2 := hpos f le_rfl
    refine ⟨X i, fun j => tile (i + j), hx0, by linarith, Or.inl (fun j hj => ?_), by linarith⟩
    have h := Ch.htile (i + j) (by omega)
    rw [hrun j hj, hpos j hj.le] at h
    exact h
  · have hpos := Ch.run_pos (T := Ty.C2) (c := (f : ℝ) ^ 2) rfl him hrun
    have hXf : X (i + f) = X i + f * (f : ℝ) ^ 2 := hpos f le_rfl
    refine ⟨X i, fun j => tile (i + j), hx0, by linarith, Or.inr (fun j hj => ?_), by linarith⟩
    have h := Ch.htile (i + j) (by omega)
    rw [hrun j hj, hpos j hj.le] at h
    exact h

/-- **The counts on the side** (S7 consumed by S8): a `SetupG` with `CornersT` has naturals `x, y, z` with `x (e f) + y (f² − e²) + z f² = L` and `f ≤ z` (the side carries a run of `f` tiles `C1` or `C2`, each laying a `c`-edge). -/
theorem theta_counts (S : SetupG D e f α β γ L ax ay) (Co : CornersT e f L ax ay) :
    ∃ x y z : ℕ, (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2 = L ∧ f ≤ z := by
  obtain ⟨m, X, tile, τ, Ch, hrun⟩ := side_theoremT_chain S Co
  obtain ⟨x, y, z, hxyz, hz⟩ := S.sideG_counts Ch
  exact ⟨x, y, z, hxyz, hz hrun⟩

end rules

end Erdos634.Draft.SideRunGT

#print axioms Erdos634.Draft.SideRunGT.rQ_T
#print axioms Erdos634.Draft.SideRunGT.rB_T
#print axioms Erdos634.Draft.SideRunGT.ra_T
#print axioms Erdos634.Draft.SideRunGT.rb_T
#print axioms Erdos634.Draft.SideRunGT.rc_T
#print axioms Erdos634.Draft.SideRunGT.side_rulesT
#print axioms Erdos634.Draft.SideRunGT.side_theoremT
#print axioms Erdos634.Draft.SideRunGT.side_theorem_paperT
#print axioms Erdos634.Draft.SideRunGT.theta_counts
