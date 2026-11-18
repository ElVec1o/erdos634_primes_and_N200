/-
Draft/WGapChordHyps.lean -- written 15 November 2026 (session 4).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 "chord facts (C)": the open chord is interior and contains no tile interior point).
Not imported by any aggregate.  Module W8a: `chord_hint_wall`: for the chord `[X0, X0 + n s]`, `X0 = p'(0,η)`, `s = p'(1,η-1) - p'(0,η)`, with the near tiles `U'(i,η-1-i)` (`i < n`) and `X0` interior:
the open chord lies in `int Δ` (`hint`) and meets no tile interior (`hwall`) -- exactly the hypotheses of `w1_chord` / `chord_all`.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapDall

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

/-- the segment between two vertices of a tile is contained in an edge of the tile -/
theorem hasV_seg_edge {t : Fin N} {A B C : Plane} (h : HasV D t A B C) :
    ∃ k : Fin 3, segment ℝ A B ⊆ (D.tile t).edge k := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  rcases fin3_adj k m hkm with h' | h'
  · refine ⟨k, ?_⟩
    simp only [Tri.edge]; rw [← h', hk, hm]
  · refine ⟨m, ?_⟩
    simp only [Tri.edge]; rw [← h', hk, hm, segment_symm]

/-- a point of the open chord lies on one of its `a`-steps -/
theorem chord_point_step (X s : Plane) {n : ℕ} (hn : 1 ≤ n) {y : Plane} (hy : y ∈ openSegment ℝ X (X + (n : ℝ) • s)) :
    ∃ i : ℕ, i < n ∧ y ∈ segment ℝ (X + (i : ℝ) • s) (X + ((i : ℝ) + 1) • s) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set u : ℝ := b * n with hu
  have hu0 : 0 ≤ u := by positivity
  have hun : u < n := by
    have : b < 1 := by linarith
    nlinarith
  set i := ⌊u⌋₊ with hi
  have hin : i < n := by
    rw [hi, Nat.floor_lt hu0]; exact hun
  have hi1 : (i : ℝ) ≤ u := Nat.floor_le hu0
  have hi2 : u < (i : ℝ) + 1 := Nat.lt_floor_add_one u
  refine ⟨i, hin, 1 - (u - i), u - i, by linarith, by linarith, by ring, ?_⟩
  have ha' : a = 1 - b := by linarith
  subst ha'
  ext j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hu]
  ring

section hyps

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **interior and wall hypotheses of the chord** from the near tiles -/
theorem chord_hint_wall (S : SetupG D e f α β γ L ax ay) (x η : ℝ) {n : ℕ} (hn1 : 1 ≤ n)
    (hX0 : mpG (e : ℝ) f 1 x 0 η ∈ interior D.target.carrier)
    (hnear : ∀ i : ℕ, i < n → ∃ t, HasV D t (mpG (e : ℝ) f 1 x (i : ℝ) (η - 1 - (i : ℝ)))
      (mpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η - 1 - (i : ℝ))) (mpG (e : ℝ) f 1 x (i : ℝ) (η - (i : ℝ)))) :
    openSegment ℝ (mpG (e : ℝ) f 1 x 0 η)
        (mpG (e : ℝ) f 1 x 0 η + (n : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η)) ⊆
        interior D.target.carrier ∧
    ∀ y ∈ openSegment ℝ (mpG (e : ℝ) f 1 x 0 η)
        (mpG (e : ℝ) f 1 x 0 η + (n : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η)),
        ∀ i, y ∉ interior (D.tile i).carrier := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hef : (e : ℝ) < f := by exact_mod_cast S.hef
  have hsp := step_pt he0 hef x η
  set X0 := mpG (e : ℝ) f 1 x 0 η with hX0d
  set s := mpG (e : ℝ) f 1 x 1 (η - 1) - X0 with hs
  constructor
  · have hEt : X0 + (n : ℝ) • s ∈ D.target.carrier := by
      obtain ⟨t, ht⟩ := hnear (n - 1) (by omega)
      have hc : ((n - 1 : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_sub hn1]; simp
      have e1 : X0 + (n : ℝ) • s = mpG (e : ℝ) f 1 x (((n - 1 : ℕ) : ℝ) + 1) (η - 1 - ((n - 1 : ℕ) : ℝ)) := by
        rw [hsp]
        exact mpG_congr' hc.symm (by rw [← hc]; ring)
      rw [e1]
      exact ht.mem₂
    exact openSeg_interior D.toDissection hX0 hEt
  · intro y hy
    obtain ⟨i, hi, hyi⟩ := chord_point_step X0 s hn1 hy
    obtain ⟨t, ht⟩ := hnear i hi
    obtain ⟨k, hk⟩ := hasV_seg_edge ht.rot.swap
    have e1 : X0 + (i : ℝ) • s = mpG (e : ℝ) f 1 x (i : ℝ) (η - (i : ℝ)) := hsp _
    have e2 : X0 + ((i : ℝ) + 1) • s = mpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η - 1 - (i : ℝ)) := by
      rw [hsp]; exact mpG_congr' rfl (by ring)
    rw [e1, e2] at hyi
    exact D.toDissection.edge_point_not_interior (hk hyi)

end hyps

#print axioms chord_hint_wall

end Erdos634.Draft.WGapStmt
