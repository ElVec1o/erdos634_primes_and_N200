/-
Draft/WGapStInv1.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.3, U3-ST).
Not imported by any aggregate.  STATION port of `WGapInv1` (corner: x = 0, floor 0): the lattice has an arbitrary real origin `x` (= c0 f^2) and ABSOLUTE levels:
the station is `O = p(c0, J0)`, the levels `j` below are the absolute heights `J0 + (relative level)`, the floor is `J0` (the wall `L_O` is the row `eta = J0`
of the mirror lattice).  Differences with the corner invariant: `cj : c + J0 <= j`, `ha` only for `J0 <= i'`.
Namespace `Erdos634.Draft.WGapSt` (so no renaming of declarations).  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapSide

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapSt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set Erdos634.Draft.WGapStmt

variable {N : ℕ} {D : CongruentDissection N}

/-- the chord step at the absolute level `j`: `s_j = p'(1,j-1) - p'(0,j)` -/
noncomputable def sj (e f : ℕ) (x : ℝ) (j : ℕ) : Plane :=
  mpG (e : ℝ) f 1 x 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 x 0 (j : ℝ)

/-- the bottom clamp of the chord `[p'(0,j), p'(0,j) + n s_j]` (the form `hEc` of `w1_chord`) -/
def BotClamp (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (j n : ℕ) : Prop :=
  ∀ ed ∈ D.lineChain (crossL (sj e f x j)) (cross (sj e f x j) (mpG (e : ℝ) f 1 x 0 (j : ℝ))),
    ¬ Straddles ((D.tile ed.1).edge ed.2)
      (mpG (e : ℝ) f 1 x 0 (j : ℝ) + ((n : ℝ) + 1) • sj e f x j)
      (mpG (e : ℝ) f 1 x 0 (j : ℝ) + (n : ℝ) • sj e f x j) (mpG (e : ℝ) f 1 x 0 (j : ℝ))

/-- **The station invariant `I_j`** (absolute level `j`, floor `J0`), with the structure (b) as the parameter `Bst j c` -/
structure Inv (D : CongruentDissection N) (e f : ℕ) (x : ℝ) (J0 : ℕ) (Bst : ℕ → ℕ → Prop) (j c : ℕ) : Prop where
  c1 : 1 ≤ c
  cj : c + J0 ≤ j
  ha : ∀ i i' : ℕ, i < c → J0 ≤ i' → i + i' + 1 ≤ j → UTM D (e : ℝ) f 1 x (i : ℝ) (i' : ℝ)
  hDp : ∀ i : ℕ, i + 2 ≤ c → DTM D (e : ℝ) f 1 x (i : ℝ) (((j - 2 - i : ℕ)) : ℝ)
  clamp : BotClamp D e f x j c
  hb : Bst j c

section level

variable {e f : ℕ} {α β γ L ax ay : ℝ} {x : ℝ} {J0 : ℕ}

theorem utm_cast {t : Fin N} {x1 y1 x2 y2 x3 y3 x1' y1' x2' y2' x3' y3' : ℝ}
    (h : HasV D t (mpG (e : ℝ) f 1 x x1 y1) (mpG (e : ℝ) f 1 x x2 y2) (mpG (e : ℝ) f 1 x x3 y3))
    (a1 : x1 = x1') (b1 : y1 = y1') (a2 : x2 = x2') (b2 : y2 = y2') (a3 : x3 = x3') (b3 : y3 = y3') :
    HasV D t (mpG (e : ℝ) f 1 x x1' y1') (mpG (e : ℝ) f 1 x x2' y2') (mpG (e : ℝ) f 1 x x3' y3') := by
  subst a1 b1 a2 b2 a3 b3; exact h

/-- the three near tiles at the inner chord point `p'(i, j-i)`, `1 ≤ i < c`, from the invariant -/
theorem nearOK_inv {Bst : ℕ → ℕ → Prop} {j c : ℕ} (I : Inv D e f x J0 Bst j c) {i : ℕ} (hi1 : 1 ≤ i) (hic : i < c) :
    NearOK D (e : ℝ) f x (i : ℝ) ((j : ℝ) - (i : ℝ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hcj := I.cj
  have c1 : ((j - (k + 1) : ℕ) : ℝ) = (j : ℝ) - ((k : ℝ) + 1) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have c2 : ((j - 2 - k : ℕ) : ℝ) = (j : ℝ) - (k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have c3 : ((j - (k + 1) - 1 : ℕ) : ℝ) = (j : ℝ) - ((k : ℝ) + 1) - 1 := by
    rw [Nat.cast_sub (by omega), c1]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := I.ha k (j - (k + 1)) (by omega) (by omega) (by omega)
    simp only [c1] at ht
    exact ⟨t, utm_cast ht.rot (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩
  · obtain ⟨t, ht⟩ := I.ha (k + 1) (j - (k + 1) - 1) hic (by omega) (by omega)
    simp only [c3] at ht
    exact ⟨t, utm_cast ht.rot.rot (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩
  · obtain ⟨t, ht⟩ := I.hDp k (by omega)
    simp only [c2] at ht
    exact ⟨t, utm_cast ht.rot.rot (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩

/-- the four known tiles at `p(0,j)` in the `X`-first form needed by `chord_D_all` / `level_fill` -/
theorem level_known {J : ℕ} (hU : ∀ j : ℕ, J0 ≤ j → j < J → UTG D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ))
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) {j : ℕ} (hj1 : J0 + 1 ≤ j) (hjJ : j < J) :
    (∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 (j : ℝ)) (lpG (e : ℝ) f 1 x 1 (j : ℝ)) (lpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1))) ∧
    (∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 (j : ℝ)) (mpG (e : ℝ) f 1 x 1 (j : ℝ)) (mpG (e : ℝ) f 1 x 0 ((j : ℝ) + 1))) ∧
    (∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 (j : ℝ)) (mpG (e : ℝ) f 1 x 1 ((j : ℝ) - 1)) (mpG (e : ℝ) f 1 x 0 ((j : ℝ) - 1))) ∧
    (∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 (j : ℝ)) (lpG (e : ℝ) f 1 x 0 ((j : ℝ) - 1)) (lpG (e : ℝ) f 1 x 1 ((j : ℝ) - 1))) := by
  have hcast : (((j - 1 : ℕ)) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hu0 := hU j (by omega) hjJ
  have ht0 := hT j (by omega) hjJ
  have hu1 := hU (j - 1) (by omega) (by omega)
  have ht1 := hT (j - 1) (by omega) (by omega)
  rw [hcast] at hu1 ht1
  obtain ⟨t0, h0⟩ := hu0
  obtain ⟨t1, h1⟩ := ht0
  obtain ⟨t2, h2⟩ := ht1
  obtain ⟨t3, h3⟩ := hu1
  have hz : ∀ η : ℝ, mpG (e : ℝ) f 1 x 0 η = lpG (e : ℝ) f 1 x 0 η := fun η => mp_zero_eta _ _ _ _ _
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
theorem inv_hint_wall (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hU : ∀ j : ℕ, J0 ≤ j → j < J → UTG D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ))
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) {Bst : ℕ → ℕ → Prop} {j c : ℕ} (hj1 : J0 + 1 ≤ j) (hjJ : j ≤ J)
    (I : Inv D e f x J0 Bst j c) :
    openSegment ℝ (mpG (e : ℝ) f 1 x 0 (j : ℝ))
        (mpG (e : ℝ) f 1 x 0 (j : ℝ) + (c : ℝ) • (mpG (e : ℝ) f 1 x 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 x 0 (j : ℝ))) ⊆
        interior D.target.carrier ∧
    ∀ y ∈ openSegment ℝ (mpG (e : ℝ) f 1 x 0 (j : ℝ))
        (mpG (e : ℝ) f 1 x 0 (j : ℝ) + (c : ℝ) • (mpG (e : ℝ) f 1 x 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 x 0 (j : ℝ))),
        ∀ i, y ∉ interior (D.tile i).carrier := by
  have hcast : (((j - 1 : ℕ)) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hX0 : mpG (e : ℝ) f 1 x 0 (j : ℝ) ∈ interior D.target.carrier := by
    have h5 := lemma_5_0 S (hU (j - 1) (by omega) (by omega)) (hT (j - 1) (by omega) (by omega))
    rw [hcast] at h5
    rw [mp_zero_eta]
    simpa using h5
  refine chord_hint_wall S x (j : ℝ) I.c1 hX0 ?_
  intro i hi
  have hcj := I.cj
  obtain ⟨t, ht⟩ := I.ha i (j - 1 - i) hi (by omega) (by omega)
  have c1 : ((j - 1 - i : ℕ) : ℝ) = (j : ℝ) - 1 - (i : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  simp only [c1] at ht
  exact ⟨t, utm_cast ht (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)⟩

/-- **Level step (I)**: from `Inv j c` and `j < J`: `D'(i, j-1-i)` is a tile for `i < c`, and at every inner chord point the alpha-wedge
is `U'(i, j-i)` or the flipped tile. -/
theorem level_data (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ J0 + (f - 1))
    (hU : ∀ j : ℕ, J0 ≤ j → j < J → UTG D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ))
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) {Bst : ℕ → ℕ → Prop} {j c : ℕ} (hj1 : J0 + 1 ≤ j) (hjJ : j < J)
    (I : Inv D e f x J0 Bst j c) :
    (∀ i : ℕ, i < c → DTM D (e : ℝ) f 1 x (i : ℝ) (((j - 1 - i : ℕ)) : ℝ)) ∧
    (∀ i : ℕ, 1 ≤ i → i < c →
      (∃ τ, HasV D τ (mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - (i : ℝ))) (mpG (e : ℝ) f 1 x ((i : ℝ) + 1) ((j : ℝ) - (i : ℝ)))
        (mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - (i : ℝ) + 1))) ∨
      (∃ τ, HasV D τ (mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - (i : ℝ)))
        (mpG (e : ℝ) f 1 x ((i : ℝ) + nuG (e : ℝ) f) ((j : ℝ) - (i : ℝ)))
        (mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - (i : ℝ) + 1 / nuG (e : ℝ) f)))) := by
  obtain ⟨hu0, ht0, ht1, hu1⟩ := level_known hU hT hj1 hjJ
  obtain ⟨hint, hwall⟩ := inv_hint_wall S hU hT hj1 hjJ.le I
  have hn : c ≤ f - 1 := by have := I.cj; omega
  have hEc := I.clamp
  have hnear : ∀ i : ℕ, 1 ≤ i → i < c → NearOK D (e : ℝ) f x (i : ℝ) ((j : ℝ) - (i : ℝ)) :=
    fun i h1 h2 => nearOK_inv I h1 h2
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨τ, hτ⟩ := chord_D_all S x (j : ℝ) hu0 ht0 ht1 hu1 I.c1 hn hint hwall hEc hnear i hi
    have hcj := I.cj
    have c1 : ((j - 1 - i : ℕ) : ℝ) = (j : ℝ) - 1 - (i : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    refine ⟨τ, ?_⟩
    rw [c1]
    exact utm_cast hτ.swap (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
  · exact level_fill S x (j : ℝ) hu0 ht0 ht1 hu1 I.c1 hn hint hwall hEc hnear

end level

end Erdos634.Draft.WGapSt
