import Mathlib.Tactic
import Erdos634.Draft.ThmDIso
import Erdos634.Draft.ThmDLegPos
import Erdos634.Draft.ThmDGeoLegRun

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (3)): a positioned leg is transported by an isometry of the dissection  

If the tiles of `D` are the `g`-images (`g` an isometry of the plane) of the tiles of `D₀` (same index) and `g` carries the frontier and the
vertices of the target of `D₀` into those of `D`, then `realLeg_iso`, `legPos_iso`, `legEnd_iso` carry a real / positioned leg of `D₀` to one of
`D` (steps `mapSteps g r`); the edge list is unchanged (`legEdges_mapSteps`).
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.Draft.APrimeLegBuild Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

variable {N : ℕ}

noncomputable def mapSteps (g : Plane ≃ᵢ Plane) (r : List (LegStep N)) : List (LegStep N) :=
  r.map (fun s => { s with p := g s.p })

theorem legEdges_mapSteps (g : Plane ≃ᵢ Plane) (e : OE) (r : List (LegStep N)) :
    legEdges e (mapSteps g r) = legEdges e r := by
  simp [legEdges, mapSteps, List.map_map, Function.comp_def]

theorem realLeg_iso {D₀ D : Dissection N} (g : Plane ≃ᵢ Plane)
    (htile : ∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m))
    (hfr : ∀ p, p ∈ frontier D₀.target.carrier → g p ∈ frontier D.target.carrier)
    (hnv : ∀ p, p ∉ Set.range D₀.target.pts → g p ∉ Set.range D.target.pts) (α : ℝ) :
    ∀ (r : List (LegStep N)) (t : Fin N) (e : OE), RealLeg D₀ α t e r → RealLeg D α t e (mapSteps g r) := by
  intro r
  induction r with
  | nil => intro t e _; trivial
  | cons s r ih =>
    intro t e h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨hfr _ h1, hnv _ h2, h3, ?_, ?_, ih s.t s.e h6⟩
    · rw [localAngle_iso g (htile t)]; exact h4
    · rw [localAngle_iso g (htile s.t)]; exact h5

theorem legPos_iso {D₀ D : Dissection N} {model₀ model : Tri} (g : Plane ≃ᵢ Plane)
    (htile : ∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m))
    (hw : ∀ o, Erdos634.Draft.ThmD.wlen model o = Erdos634.Draft.ThmD.wlen model₀ o) (A B : Plane) :
    ∀ (r : List (LegStep N)) (t : Fin N) (e : OE) (s : ℝ), LegPos D₀ model₀ A B t e s r →
      LegPos D model (g A) (g B) t e s (mapSteps g r) := by
  intro r
  induction r with
  | nil =>
    intro t e s h
    obtain ⟨j, k, hjk, hj, hk, hs, hl⟩ := h
    refine ⟨j, k, hjk, ?_, ?_, hs, ?_⟩
    · rw [htile, hj, Erdos634.E1NormalForm.iso_lineMap]
    · rw [htile, hk, Erdos634.E1NormalForm.iso_lineMap]
    · rw [hw, hl, g.dist_eq]
  | cons st r ih =>
    intro t e s h
    obtain ⟨s', j, k, hjk, hj, hk, hs, hs1, hp, hl, hr⟩ := h
    refine ⟨s', j, k, hjk, ?_, ?_, hs, hs1, ?_, ?_, ih st.t st.e s' hr⟩
    · rw [htile, hj, Erdos634.E1NormalForm.iso_lineMap]
    · rw [htile, hk, Erdos634.E1NormalForm.iso_lineMap]
    · show g st.p = _
      rw [hp, Erdos634.E1NormalForm.iso_lineMap]
    · rw [hw, hl, g.dist_eq]

theorem legEnd_iso {D₀ D : Dissection N} (g : Plane ≃ᵢ Plane) (htile : ∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m))
    (α : ℝ) (B : Plane) :
    ∀ (r : List (LegStep N)) (t : Fin N) (e : OE), LegEnd D₀ α B t e r →
      LegEnd D α (g B) t e (mapSteps g r) := by
  intro r
  induction r with
  | nil =>
    intro t e h
    have h' : (D₀.tile t).localAngle B = angVal α e.r := h
    show (D.tile t).localAngle (g B) = angVal α e.r
    rw [localAngle_iso g (htile t)]; exact h'
  | cons st r ih =>
    intro t e h
    exact ih st.t st.e h

#print axioms realLeg_iso
#print axioms legPos_iso
#print axioms legEnd_iso
end Erdos634.Draft.ThmDRun
