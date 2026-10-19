/-
Draft/PHypG.lean — the parameter structure of the Paliy F3 family theorem (`PF3`, `b < a < 2 b`).  For a triple `b < a`, `c² = a² + a b + b²`
(`b = 2d + y`, `a = b + t`, `c = 3d + 2y + t`, `3 d² = y² + y t`) and `w = 2 b - a = 2d + y - t > 0` (carried in the slot `A`; `a = 2 b` is
impossible since `7` is not a square).  Same field names as `PHyp.Hyp` so that the generated modules apply to both.
-/
import Erdos634.Draft.PHyp

namespace Erdos634.Draft.PHypG

structure Hyp (d y t A B s : ℝ) : Prop where
  hd : 0 < d
  hy : 0 < y
  ht : 0 < t
  hA : 0 < A
  hB : 0 ≤ B
  hs : 0 ≤ s
  hR : 3 * d ^ 2 = y ^ 2 + y * t
  hS : A + t = 2 * d + y

def ea (d y t : ℝ) : ℝ := 2 * d + y + t
def eb (d y : ℝ) : ℝ := 2 * d + y
def ec (d y t : ℝ) : ℝ := 3 * d + 2 * y + t

theorem pa {d y t A B s : ℝ} (H : Hyp d y t A B s) : 0 < ea d y t := by obtain ⟨hd, hy, ht, -⟩ := H; unfold ea; positivity
theorem pb {d y t A B s : ℝ} (H : Hyp d y t A B s) : 0 < eb d y := by obtain ⟨hd, hy, ht, -⟩ := H; unfold eb; positivity
theorem pc {d y t A B s : ℝ} (H : Hyp d y t A B s) : 0 < ec d y t := by obtain ⟨hd, hy, ht, -⟩ := H; unfold ec; positivity
theorem hcR {d y t A B s : ℝ} (H : Hyp d y t A B s) : ec d y t ^ 2 = ea d y t ^ 2 + ea d y t * eb d y + eb d y ^ 2 := by
  obtain ⟨hd, hy, ht, hA, hB, hs, hR, hS⟩ := H; unfold ea eb ec; linear_combination (-1 : ℝ) * hR

theorem hypOf {nd ny nt nA nB ns : ℕ} (hnd : 0 < nd) (hny : 0 < ny) (hnt : 0 < nt) (hnA : 0 < nA)
    (hR : 3 * nd ^ 2 = ny ^ 2 + ny * nt) (hS : nA + nt = 2 * nd + ny) : Hyp (nd : ℝ) ny nt nA nB ns := by
  refine ⟨by exact_mod_cast hnd, by exact_mod_cast hny, by exact_mod_cast hnt, by exact_mod_cast hnA, Nat.cast_nonneg _, Nat.cast_nonneg _,
    by exact_mod_cast hR, by exact_mod_cast hS⟩

end Erdos634.Draft.PHypG
