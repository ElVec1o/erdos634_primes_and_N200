import Mathlib.Tactic
import Erdos634.Draft.ThmDLegBlocks
import Erdos634.Draft.ThmDRayAlpha

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (4)/(5)): the tile `T₀` across the ray in lattice form  

`hT0_of_ray` : a `RayTileAC` for the lattice ray `lp 0 0 → lp 0 1` (third vertex `lp 1 0`) is the hypothesis `hT0` of `lemma33_interior`
(a tile with an `a`- or `c`-edge from `U` along the ray and lying in `FXT ≤ lv 0`).
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.Draft.APrimeLegBuild
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Erdos634.MarchSlots Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem hT0_of_ray (C : CtxBaseT D u v α β γ L ax ay ε x) {t1 : Fin N}
    (h : RayTileAC D u v (lpT (u : ℝ) (v : ℝ) ε x 0 0) (lpT (u : ℝ) (v : ℝ) ε x 0 1)
      (lpT (u : ℝ) (v : ℝ) ε x 1 0) t1) :
    ∃ (e : Fin N) (k m : Fin 3) (t : ℝ), k ≠ m ∧ (D.tile e).pts k = lpT (u : ℝ) (v : ℝ) ε x 0 0 ∧ 0 < t ∧
        (D.tile e).pts m = lpT (u : ℝ) (v : ℝ) ε x 0 t ∧
        (dist ((D.tile e).pts k) ((D.tile e).pts m) = (u : ℝ) ^ 2 ∨
          dist ((D.tile e).pts k) ((D.tile e).pts m) = (u : ℝ) * v) ∧
        (∀ i, FXT (u : ℝ) (v : ℝ) ε ((D.tile e).pts i) ≤ lvT (u : ℝ) (v : ℝ) ε x 0) := by
  obtain ⟨e, k, m, t, -, hkm, hk, ht, hm, hd, hside⟩ := h
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  refine ⟨e, k, m, t, hkm, hk, ht, ?_, hd, ?_⟩
  · rw [hm, lineMap_lpT]
    exact lpT_congr (by ring) (by ring)
  · intro i
    have h1 := hside i
    have hc : ∀ y, cross (lpT (u : ℝ) (v : ℝ) ε x 0 1 - lpT (u : ℝ) (v : ℝ) ε x 0 0) y = (-ε) * FXT (u : ℝ) (v : ℝ) ε y := by
      intro y
      have := cross_rayT (u := (u : ℝ)) (v := (v : ℝ)) (x := x) hε 0 0 y
      rwa [zero_add] at this
    rw [hc, hc] at h1
    simp only [map_sub, FXT_lp hε] at h1
    have hlt : lvT (u : ℝ) (v : ℝ) ε x 0 < lvT (u : ℝ) (v : ℝ) ε x 1 := lvT_lt hu huv hv2 one_pos
    have key : (FXT (u : ℝ) (v : ℝ) ε ((D.tile e).pts i) - lvT (u : ℝ) (v : ℝ) ε x 0) *
        (lvT (u : ℝ) (v : ℝ) ε x 1 - lvT (u : ℝ) (v : ℝ) ε x 0) ≤ 0 := by
      have e2 : ε * ε = 1 := by nlinarith [hε]
      nlinarith [h1, e2]
    by_contra hgt
    push Not at hgt
    nlinarith [mul_pos (sub_pos.mpr hgt) (sub_pos.mpr hlt)]

#print axioms hT0_of_ray
end Erdos634.Draft.ThmDRun
