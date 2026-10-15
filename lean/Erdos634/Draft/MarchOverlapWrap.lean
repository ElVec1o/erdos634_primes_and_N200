import Erdos634.MarchOverlap
namespace Erdos634.Draft.MarchOverlapWrap
open Erdos634.MarchOverlap
open Erdos634.Geometry Erdos634.EdgeDisjoint

theorem wrap_mem_interior_of_vertex_push (T : Tri) (k : Fin 3) {v : Plane}
    (h1 : 0 < ((T.basis.coord (k + 1)).linear) v)
    (h2 : 0 < ((T.basis.coord (k + 2)).linear) v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → T.pts k + ε • v ∈ interior T.carrier :=
  Tri.mem_interior_of_vertex_push T k h1 h2

theorem wrap_wedge_disjoint_at_vertex {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {k₁ k₂ : Fin 3}
    (hshare : (D.tile i₁).pts k₁ = (D.tile i₂).pts k₂) (v : Plane) :
    ¬ (0 < (((D.tile i₁).basis.coord (k₁ + 1)).linear) v
       ∧ 0 < (((D.tile i₁).basis.coord (k₁ + 2)).linear) v
       ∧ 0 < (((D.tile i₂).basis.coord (k₂ + 1)).linear) v
       ∧ 0 < (((D.tile i₂).basis.coord (k₂ + 2)).linear) v) :=
  Dissection.wedge_disjoint_at_vertex D hne hshare v

theorem wrap_coord_pos_of_combo (T : Tri) (k : Fin 3) {v : Plane} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hv : v = α • (T.pts (k + 1) - T.pts k) + β • (T.pts (k + 2) - T.pts k)) :
    0 < ((T.basis.coord (k + 1)).linear) v ∧ 0 < ((T.basis.coord (k + 2)).linear) v :=
  coord_pos_of_combo T k hα hβ hv

theorem wrap_wedge_disjoint_combo {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {k₁ k₂ : Fin 3}
    (hshare : (D.tile i₁).pts k₁ = (D.tile i₂).pts k₂) {v : Plane}
    {α₁ β₁ α₂ β₂ : ℝ} (hα₁ : 0 < α₁) (hβ₁ : 0 < β₁) (hα₂ : 0 < α₂) (hβ₂ : 0 < β₂)
    (hv₁ : v = α₁ • ((D.tile i₁).pts (k₁ + 1) - (D.tile i₁).pts k₁)
             + β₁ • ((D.tile i₁).pts (k₁ + 2) - (D.tile i₁).pts k₁))
    (hv₂ : v = α₂ • ((D.tile i₂).pts (k₂ + 1) - (D.tile i₂).pts k₂)
             + β₂ • ((D.tile i₂).pts (k₂ + 2) - (D.tile i₂).pts k₂)) :
    False :=
  Dissection.wedge_disjoint_combo D hne hshare hα₁ hβ₁ hα₂ hβ₂ hv₁ hv₂

example : True := trivial
#print axioms wrap_wedge_disjoint_combo
end Erdos634.Draft.MarchOverlapWrap
