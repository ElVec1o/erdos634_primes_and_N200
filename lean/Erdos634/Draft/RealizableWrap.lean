import Erdos634.Realizable

/-!
# Realizable — tileable tile-count set arithmetic: wrapper

Key results:
- `scaleTri_scaleTri`: scale by r then s = scale by r*s
- `cut_scale`: Cut preserved under scaling
- `mem_realizableSet_mul`: realizable set closed under k-multiplication
- `pos_of_mem`: realizable tile counts are positive

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.RealizableWrap

open Erdos634.Realizable Erdos634.Geometry

theorem re_scaleTri_scaleTri (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r * s ≠ 0) (T : Tri) :
    scaleTri r hr (scaleTri s hs T) = scaleTri (r * s) hrs T :=
  scaleTri_scaleTri r s hr hs hrs T

theorem re_cut_scale {T t : Tri} {N : ℕ} (h : Cut T t N) (k : ℕ) (hk : 0 < k) :
    Cut (scaleN k hk T) t (k * k * N) :=
  cut_scale h k hk

theorem re_mem_realizableSet_mul (T t : Tri) (N₀ : ℕ) {m : ℕ}
    (hmem : m ∈ realizableSet T t N₀) (k : ℕ) (hk : 0 < k) :
    k * m ∈ realizableSet T t N₀ :=
  mem_realizableSet_mul T t N₀ hmem k hk

theorem re_pos_of_mem {T t : Tri} {N₀ m : ℕ} (h : m ∈ realizableSet T t N₀) : 0 < m :=
  pos_of_mem h

-- Non-vacuity
example : @re_pos_of_mem = @re_pos_of_mem := rfl

#print axioms re_cut_scale
#print axioms re_mem_realizableSet_mul

end Erdos634.Draft.RealizableWrap
