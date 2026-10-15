import Erdos634.ChordTraceReal

namespace Erdos634.Draft.ChordTraceRealWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_le_iff_forall_vertices_le (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    (∀ x ∈ T.carrier, f x ≤ c) ↔ ∀ i, f (T.pts i) ≤ c :=
  Tri.le_iff_forall_vertices_le T f c

theorem wrap_sign_trichotomy (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    (∀ x ∈ T.carrier, f x ≤ c) ∨ (∀ x ∈ T.carrier, c ≤ f x)
      ∨ ((∃ i, f (T.pts i) < c) ∧ (∃ j, c < f (T.pts j))) :=
  Tri.sign_trichotomy T f c

theorem wrap_convex_inter_hyperplane (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    Convex ℝ (T.carrier ∩ {x | f x = c}) :=
  Tri.convex_inter_hyperplane T f c

theorem wrap_ker_finrank_one (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    Module.finrank ℝ (LinearMap.ker f) = 1 :=
  ker_finrank_one f hf

theorem wrap_isSegment_of_convex_inter_hyperplane
    {S : Set Plane} (hconv : Convex ℝ S) (hcpt : IsCompact S)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) (hSf : ∀ x ∈ S, f x = c) (x0 : Plane) (hx0 : x0 ∈ S) :
    ∃ p q, p ∈ S ∧ q ∈ S ∧ S = segment ℝ p q :=
  isSegment_of_convex_inter_hyperplane hconv hcpt f hf c hSf x0 hx0

theorem wrap_straddle_no_edge_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hlo : ∃ i, f (T.pts i) < c) (hhi : ∃ j, c < f (T.pts j)) (k : Fin 3) :
    f (T.pts (k + 1)) ≠ c ∨ f (T.pts (k + 2)) ≠ c :=
  Tri.straddle_no_edge_on_line T f c hlo hhi k

theorem wrap_trace_disjoint_of_straddle {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {i j : Fin N} (hij : i ≠ j)
    (hloj : ∃ a, f ((D.tile j).pts a) < c) (hhij : ∃ b, c < f ((D.tile j).pts b)) :
    (((D.tile i).carrier ∩ {x | f x = c}) ∩ ((D.tile j).carrier ∩ {x | f x = c})).Subsingleton :=
  trace_disjoint_of_straddle D f c hij hloj hhij

example : True := trivial
#print axioms wrap_isSegment_of_convex_inter_hyperplane

end Erdos634.Draft.ChordTraceRealWrap
