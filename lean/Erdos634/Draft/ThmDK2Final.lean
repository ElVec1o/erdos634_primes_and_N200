import Mathlib.Tactic
import Erdos634.Draft.ThmDL32

/-!
# Theorem D' (R6): Lemma K (K2), unconditional in the corner context  

`lemmaK2_final` : `lemmaK2` with `L32Hyp` discharged by `lemma32`.  A run of `n` tiles `Δ_{i,0}` (`1 ≤ n < v`) on the base side of a
`SetupT`/`CtxBaseT`, with the ends `P_w = lp 0 w` (`w ≤ n`) on the side line `S'` as frontier non-vertices, the diagonals `P_w Q_w`
interior, stopped at `V = lp n 0`, does not exist.  Standing assumptions (`hnoγ`: no `γ` at a vertex of the target; `hVnv`) are
hypotheses of the context, not proved here.
-/

open scoped Classical

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem lemmaK2_final (C : CtxBaseT D u v α β γ L ax ay ε x) {n : ℕ} (hn1 : 1 ≤ n) (hnv : n < v)
    (hrun : ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) ε x (i : ℝ) 0)
    (hPf : ∀ w : ℕ, 1 ≤ w → w ≤ n → lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ∈ frontier D.target.carrier ∧
      lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ∉ Set.range D.target.pts ∧
      ((ε = 1 ∧ gA ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) = 0) ∨
        (ε = -1 ∧ gB L ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) = 0)))
    (hQf : ∀ w : ℕ, 1 ≤ w → w ≤ n → lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ frontier D.target.carrier)
    (hint : ∀ w : ℕ, 1 ≤ w → w ≤ n →
      openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
        interior D.target.carrier)
    (hVnv : (∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) →
      lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∉ Set.range D.target.pts)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∈ Set.range D.target.pts ∨
      ∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) : False :=
  lemmaK2 C hn1 hnv (lemma32 C hn1 hnv hrun hPf (hQf n hn1 le_rfl) hVnv hnoγ hstop) hrun hPf hQf hint hVnv hnoγ hstop

#print axioms lemmaK2_final

/-- **Lemma K (K2) with good ends**: the same, for ends `P_w` that need not be frontier points (interior start, `PGood`). -/
theorem lemmaK2_final_gen (C : CtxBaseT D u v α β γ L ax ay ε x) {n : ℕ} (hn1 : 1 ≤ n) (hnv : n < v)
    (hrun : ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) ε x (i : ℝ) 0)
    (hPG : ∀ w : ℕ, 1 ≤ w → w ≤ n → (∀ j : ℕ, j < w → UTT D (u : ℝ) (v : ℝ) ε x 0 (j : ℝ)) →
      PGood D (u : ℝ) (v : ℝ) ε x α (w : ℝ))
    (hQf : ∀ w : ℕ, 1 ≤ w → w ≤ n → lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ frontier D.target.carrier)
    (hint : ∀ w : ℕ, 1 ≤ w → w ≤ n → (∀ j : ℕ, j < w → UTT D (u : ℝ) (v : ℝ) ε x 0 (j : ℝ)) →
      openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
        interior D.target.carrier)
    (hVnv : (∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) →
      lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∉ Set.range D.target.pts)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∈ Set.range D.target.pts ∨
      ∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) ε x (n : ℝ) 0) = γ) : False :=
  lemmaK2_gen C hn1 hnv
    (lemma32_gen C hn1 hnv hrun (fun w h1 h2 hr => (hPG w h1 h2 hr).toRow) (hQf n hn1 le_rfl) hVnv hnoγ hstop)
    hrun hPG hQf hint hVnv hnoγ hstop

#print axioms lemmaK2_final_gen
end Erdos634.Draft.ThmDRun
