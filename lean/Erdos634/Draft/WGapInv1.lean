/-
Draft/WGapInv1.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5, invariant I_j).
Not imported by any aggregate.  Module P-E1: the INVARIANT `Inv` of Lemma U3 (S2'), with the bottom clamp `BotClamp` and the structure (b) `Bst` as parameters
(the three bottom clamps are produced by the Case lemmas), and the level step: from `Inv j c` and `j < J` get the D'-tiles of level `j` (chord_D_all)
and the alpha-wedge dichotomy at every inner chord point (level_fill).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapSide

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

/-- the chord step at level `j`: `s_j = p'(1,j-1) - p'(0,j)` -/
noncomputable def sj (e f : ℕ) (j : ℕ) : Plane :=
  mpG (e : ℝ) f 1 0 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (j : ℝ)

/-- the bottom clamp of the chord `[p'(0,j), p'(0,j) + n s_j]` (the form `hEc` of `w1_chord`) -/
def BotClamp (D : CongruentDissection N) (e f j n : ℕ) : Prop :=
  ∀ ed ∈ D.lineChain (crossL (sj e f j)) (cross (sj e f j) (mpG (e : ℝ) f 1 0 0 (j : ℝ))),
    ¬ Straddles ((D.tile ed.1).edge ed.2)
      (mpG (e : ℝ) f 1 0 0 (j : ℝ) + ((n : ℝ) + 1) • sj e f j)
      (mpG (e : ℝ) f 1 0 0 (j : ℝ) + (n : ℝ) • sj e f j) (mpG (e : ℝ) f 1 0 0 (j : ℝ))

theorem side1_botclamp {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (n : ℕ) :
    BotClamp D e f n n := side1_clamp S h2 n

/-- **The invariant `I_j`** of Lemma U3 (PROOF P5), with the structure (b) as the parameter `Bst j c` and the F5 carrier `D'` of level `j-1`. -/
structure Inv (D : CongruentDissection N) (e f : ℕ) (Bst : ℕ → ℕ → Prop) (j c : ℕ) : Prop where
  c1 : 1 ≤ c
  cj : c ≤ j
  ha : ∀ i i' : ℕ, i < c → i + i' + 1 ≤ j → UTM D (e : ℝ) f 1 0 (i : ℝ) (i' : ℝ)
  hDp : ∀ i : ℕ, i + 2 ≤ c → DTM D (e : ℝ) f 1 0 (i : ℝ) (((j - 2 - i : ℕ)) : ℝ)
  clamp : BotClamp D e f j c
  hb : Bst j c

section level

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem utm_cast {t : Fin N} {x1 y1 x2 y2 x3 y3 x1' y1' x2' y2' x3' y3' : ℝ}
    (h : HasV D t (mpG (e : ℝ) f 1 0 x1 y1) (mpG (e : ℝ) f 1 0 x2 y2) (mpG (e : ℝ) f 1 0 x3 y3))
    (a1 : x1 = x1') (b1 : y1 = y1') (a2 : x2 = x2') (b2 : y2 = y2') (a3 : x3 = x3') (b3 : y3 = y3') :
    HasV D t (mpG (e : ℝ) f 1 0 x1' y1') (mpG (e : ℝ) f 1 0 x2' y2') (mpG (e : ℝ) f 1 0 x3' y3') := by
  subst a1 b1 a2 b2 a3 b3; exact h

/-- the three near tiles at the inner chord point `p'(i, j-i)`, `1 ≤ i < c`, from the invariant -/
theorem nearOK_inv {Bst : ℕ → ℕ → Prop} {j c : ℕ} (I : Inv D e f Bst j c) {i : ℕ} (hi1 : 1 ≤ i) (hic : i < c) :
    NearOK D (e : ℝ) f 0 (i : ℝ) ((j : ℝ) - (i : ℝ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hcj := I.cj
  have c1 : ((j - (k + 1) : ℕ) : ℝ) = (j : ℝ) - ((k : ℝ) + 1) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have c2 : ((j - 2 - k : ℕ) : ℝ) = (j : ℝ) - (k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have c3 : ((j - (k + 1) - 1 : ℕ) : ℝ) = (j : ℝ) - ((k : ℝ) + 1) - 1 := by
    rw [Nat.cast_sub (by omega), c1]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := I.ha k (j - (k + 1)) (by omega) (by omega)
    simp only [c1] at ht
    exact ⟨t, utm_cast ht.rot (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩
  · obtain ⟨t, ht⟩ := I.ha (k + 1) (j - (k + 1) - 1) hic (by omega)
    simp only [c3] at ht
    exact ⟨t, utm_cast ht.rot.rot (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩
  · obtain ⟨t, ht⟩ := I.hDp k (by omega)
    simp only [c2] at ht
    exact ⟨t, utm_cast ht.rot.rot (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩

/-- the four known tiles at `p(0,j)` in the `X`-first form needed by `chord_D_all` / `level_fill` -/
theorem level_known {J : ℕ} (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) {j : ℕ} (hj1 : 1 ≤ j) (hjJ : j < J) :
    (∃ t, HasV D t (mpG (e : ℝ) f 1 0 0 (j : ℝ)) (lpG (e : ℝ) f 1 0 1 (j : ℝ)) (lpG (e : ℝ) f 1 0 0 ((j : ℝ) + 1))) ∧
    (∃ t, HasV D t (mpG (e : ℝ) f 1 0 0 (j : ℝ)) (mpG (e : ℝ) f 1 0 1 (j : ℝ)) (mpG (e : ℝ) f 1 0 0 ((j : ℝ) + 1))) ∧
    (∃ t, HasV D t (mpG (e : ℝ) f 1 0 0 (j : ℝ)) (mpG (e : ℝ) f 1 0 1 ((j : ℝ) - 1)) (mpG (e : ℝ) f 1 0 0 ((j : ℝ) - 1))) ∧
    (∃ t, HasV D t (mpG (e : ℝ) f 1 0 0 (j : ℝ)) (lpG (e : ℝ) f 1 0 0 ((j : ℝ) - 1)) (lpG (e : ℝ) f 1 0 1 ((j : ℝ) - 1))) := by
  have hcast : (((j - 1 : ℕ)) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj1]; simp
  have hu0 := hU j hjJ
  have ht0 := hT j hjJ
  have hu1 := hU (j - 1) (by omega)
  have ht1 := hT (j - 1) (by omega)
  rw [hcast] at hu1 ht1
  obtain ⟨t0, h0⟩ := hu0
  obtain ⟨t1, h1⟩ := ht0
  obtain ⟨t2, h2⟩ := ht1
  obtain ⟨t3, h3⟩ := hu1
  have hz : ∀ η : ℝ, mpG (e : ℝ) f 1 0 0 η = lpG (e : ℝ) f 1 0 0 η := fun η => mp_zero_eta _ _ _ _ _
  refine ⟨⟨t0, ?_⟩, ⟨t1, ?_⟩, ⟨t2, ?_⟩, ⟨t3, ?_⟩⟩
  · rw [hz]; simpa using h0
  · simpa using h1
  · have := h2.swap.rot.rot
    refine hasV_congr this ?_ ?_ ?_
    · exact mpG_congr' rfl (by ring)
    · simp
    · simp
  · have := h3.rot.rot
    rw [hz]
    refine hasV_congr this ?_ ?_ ?_
    · exact lpG_congr (by ring) (by ring)
    · simp
    · simp

/-- the chord hypotheses `hint`, `hwall` of level `j` from the invariant -/
theorem inv_hint_wall (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) {Bst : ℕ → ℕ → Prop} {j c : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J)
    (I : Inv D e f Bst j c) :
    openSegment ℝ (mpG (e : ℝ) f 1 0 0 (j : ℝ))
        (mpG (e : ℝ) f 1 0 0 (j : ℝ) + (c : ℝ) • (mpG (e : ℝ) f 1 0 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (j : ℝ))) ⊆
        interior D.target.carrier ∧
    ∀ y ∈ openSegment ℝ (mpG (e : ℝ) f 1 0 0 (j : ℝ))
        (mpG (e : ℝ) f 1 0 0 (j : ℝ) + (c : ℝ) • (mpG (e : ℝ) f 1 0 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (j : ℝ))),
        ∀ i, y ∉ interior (D.tile i).carrier := by
  have hcast : (((j - 1 : ℕ)) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj1]; simp
  have hX0 : mpG (e : ℝ) f 1 0 0 (j : ℝ) ∈ interior D.target.carrier := by
    have h5 := lemma_5_0 S (hU (j - 1) (by omega)) (hT (j - 1) (by omega))
    rw [hcast] at h5
    rw [mp_zero_eta]
    simpa using h5
  refine chord_hint_wall S 0 (j : ℝ) I.c1 hX0 ?_
  intro i hi
  have hcj := I.cj
  obtain ⟨t, ht⟩ := I.ha i (j - 1 - i) hi (by omega)
  have c1 : ((j - 1 - i : ℕ) : ℝ) = (j : ℝ) - 1 - (i : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  simp only [c1] at ht
  exact ⟨t, utm_cast ht (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)⟩

/-- **Level step (I)**: from `Inv j c` and `j < J`: `D'(i, j-1-i)` is a tile for `i < c`, and at every inner chord point the alpha-wedge
is `U'(i, j-i)` or the flipped tile. -/
theorem level_data (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ f - 1)
    (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) {Bst : ℕ → ℕ → Prop} {j c : ℕ} (hj1 : 1 ≤ j) (hjJ : j < J)
    (I : Inv D e f Bst j c) :
    (∀ i : ℕ, i < c → DTM D (e : ℝ) f 1 0 (i : ℝ) (((j - 1 - i : ℕ)) : ℝ)) ∧
    (∀ i : ℕ, 1 ≤ i → i < c →
      (∃ τ, HasV D τ (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - (i : ℝ))) (mpG (e : ℝ) f 1 0 ((i : ℝ) + 1) ((j : ℝ) - (i : ℝ)))
        (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - (i : ℝ) + 1))) ∨
      (∃ τ, HasV D τ (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - (i : ℝ)))
        (mpG (e : ℝ) f 1 0 ((i : ℝ) + nuG (e : ℝ) f) ((j : ℝ) - (i : ℝ)))
        (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - (i : ℝ) + 1 / nuG (e : ℝ) f)))) := by
  obtain ⟨hu0, ht0, ht1, hu1⟩ := level_known hU hT hj1 hjJ
  obtain ⟨hint, hwall⟩ := inv_hint_wall S hU hT hj1 hjJ.le I
  have hn : c ≤ f - 1 := by have := I.cj; omega
  have hEc := I.clamp
  have hnear : ∀ i : ℕ, 1 ≤ i → i < c → NearOK D (e : ℝ) f 0 (i : ℝ) ((j : ℝ) - (i : ℝ)) :=
    fun i h1 h2 => nearOK_inv I h1 h2
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨τ, hτ⟩ := chord_D_all S 0 (j : ℝ) hu0 ht0 ht1 hu1 I.c1 hn hint hwall hEc hnear i hi
    have hcj := I.cj
    have c1 : ((j - 1 - i : ℕ) : ℝ) = (j : ℝ) - 1 - (i : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    refine ⟨τ, ?_⟩
    rw [c1]
    exact utm_cast hτ.swap (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
  · exact level_fill S 0 (j : ℝ) hu0 ht0 ht1 hu1 I.c1 hn hint hwall hEc hnear

end level

end Erdos634.Draft.WGapStmt
