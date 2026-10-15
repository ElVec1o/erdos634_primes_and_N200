import Erdos634.ChordInterface
namespace Erdos634.Draft.ChordInterfaceWrap
open Erdos634.ChordInterface

theorem wrap_sum_ge_min {a b c : ℕ} (hab : a ≤ b) (hac : a ≤ c)
    (L : List ℕ) (hL : ∀ l ∈ L, l = a ∨ l = b ∨ l = c) (hne : L ≠ []) :
    a ≤ L.sum :=
  sum_ge_min hab hac L hL hne

theorem wrap_no_interior_vertex {a b c L : ℕ} (hab : a ≤ b) (hac : a ≤ c) (hL : L ≤ a)
    (F : FarSide a b c) (pre : List ℕ) (hpre : pre ≠ [])
    (hsub : ∀ l ∈ pre, l ∈ F.run) (hlt : pre.sum < L) : False :=
  no_interior_vertex hab hac hL F pre hpre hsub hlt

theorem wrap_prefix_sum_is_semigroup {a b c : ℕ} (F : FarSide a b c)
    (pre : List ℕ) (hsub : ∀ l ∈ pre, l ∈ F.run) :
    ∃ x y z : ℕ, pre.sum = x * a + y * b + z * c :=
  prefix_sum_is_semigroup F pre hsub

theorem wrap_prefix_hit_or_straddle (run : List ℕ) (L : ℕ) (hL : L ≤ run.sum) :
    (∃ pre suf : List ℕ, run = pre ++ suf ∧ pre.sum = L) ∨
    (∃ (pre : List ℕ) (l : ℕ) (suf : List ℕ),
      run = pre ++ l :: suf ∧ pre.sum < L ∧ L < pre.sum + l) :=
  prefix_hit_or_straddle run L hL

example : True := trivial
#print axioms prefix_hit_or_straddle
end Erdos634.Draft.ChordInterfaceWrap
