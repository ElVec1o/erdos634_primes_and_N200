/-
Draft/PHyp.lean — the parameter structure of the Paliy nested-corner family theorems.  For a triple `a > b > 0`, `c² = a² + a b + b²`
(here `b = 2d + y`, `a = b + t = 2d + y + t`, `c = 3d + 2y + t`, `3 d² = y² + y t`, all of `d, y, t > 0`) and the semigroup witness
`A a + B b + s c = b c - a²` with `A, B, s ≥ 0` (D. Paliy's precondition `b c - a² ∈ ⟨a, b, c⟩`).
-/
import Erdos634.Draft.PCore

namespace Erdos634.Draft.PHyp

structure Hyp (d y t A B s : ℝ) : Prop where
  hd : 0 < d
  hy : 0 < y
  ht : 0 < t
  hA : 0 ≤ A
  hB : 0 ≤ B
  hs : 0 ≤ s
  hR : 3 * d ^ 2 = y ^ 2 + y * t
  hS : A * (2 * d + y + t) + B * (2 * d + y) + s * (3 * d + 2 * y + t) = (2 * d + y) * (3 * d + 2 * y + t) - (2 * d + y + t) ^ 2

def ea (d y t : ℝ) : ℝ := 2 * d + y + t
def eb (d y : ℝ) : ℝ := 2 * d + y
def ec (d y t : ℝ) : ℝ := 3 * d + 2 * y + t

theorem pa {d y t A B s : ℝ} (H : Hyp d y t A B s) : 0 < ea d y t := by obtain ⟨hd, hy, ht, -⟩ := H; unfold ea; positivity
theorem pb {d y t A B s : ℝ} (H : Hyp d y t A B s) : 0 < eb d y := by obtain ⟨hd, hy, ht, -⟩ := H; unfold eb; positivity
theorem pc {d y t A B s : ℝ} (H : Hyp d y t A B s) : 0 < ec d y t := by obtain ⟨hd, hy, ht, -⟩ := H; unfold ec; positivity
theorem hcR {d y t A B s : ℝ} (H : Hyp d y t A B s) : ec d y t ^ 2 = ea d y t ^ 2 + ea d y t * eb d y + eb d y ^ 2 := by
  obtain ⟨hd, hy, ht, hA, hB, hs, hR, hS⟩ := H; unfold ea eb ec; linear_combination (-1 : ℝ) * hR

/-- the parameters of a triple `b < a`: `a + b = c + d`, `2 c = 2 a + b + y`, `a = b + t`, `3 d² = y² + y t`. -/
theorem params (a b c : ℕ) (hb : 0 < b) (hab : b < a) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ∃ nd ny nt : ℕ, 0 < nd ∧ 0 < ny ∧ 0 < nt ∧ 3 * nd ^ 2 = ny ^ 2 + ny * nt ∧
      b = 2 * nd + ny ∧ a = 2 * nd + ny + nt ∧ c = 3 * nd + 2 * ny + nt := by
  have h1 : c < a + b := by
    by_contra h
    have h' : a + b ≤ c := not_lt.mp h
    nlinarith [Nat.mul_le_mul h' h', Nat.mul_pos hb (by omega : 0 < a)]
  have h2 : 2 * a + b < 2 * c := by
    by_contra h
    have h' : 2 * c ≤ 2 * a + b := not_lt.mp h
    nlinarith [Nat.mul_le_mul h' h', Nat.mul_pos hb hb]
  obtain ⟨nd, hnd⟩ : ∃ nd, a + b = c + nd := ⟨a + b - c, by omega⟩
  obtain ⟨ny, hny⟩ : ∃ ny, 2 * c = 2 * a + b + ny := ⟨2 * c - (2 * a + b), by omega⟩
  obtain ⟨nt, hnt⟩ : ∃ nt, a = b + nt := ⟨a - b, by omega⟩
  have eb : b = 2 * nd + ny := by omega
  have ea : a = 2 * nd + ny + nt := by omega
  have ec : c = 3 * nd + 2 * ny + nt := by omega
  subst ea eb ec
  refine ⟨nd, ny, nt, by omega, by omega, by omega, ?_, rfl, rfl, rfl⟩
  have hz : ((3 * nd + 2 * ny + nt : ℕ) : ℤ) ^ 2 = ((2 * nd + ny + nt : ℕ) : ℤ) ^ 2 + ((2 * nd + ny + nt : ℕ) : ℤ) * ((2 * nd + ny : ℕ) : ℤ)
      + ((2 * nd + ny : ℕ) : ℤ) ^ 2 := by exact_mod_cast hc
  have : 3 * (nd : ℤ) ^ 2 = (ny : ℤ) ^ 2 + ny * nt := by
    push_cast at hz
    linear_combination (-1 : ℤ) * hz
  exact_mod_cast this

theorem hypOf {nd ny nt nA nB ns : ℕ} (hnd : 0 < nd) (hny : 0 < ny) (hnt : 0 < nt) (hR : 3 * nd ^ 2 = ny ^ 2 + ny * nt)
    (hS : nA * (2 * nd + ny + nt) + nB * (2 * nd + ny) + ns * (3 * nd + 2 * ny + nt) + (2 * nd + ny + nt) ^ 2
      = (2 * nd + ny) * (3 * nd + 2 * ny + nt)) : Hyp (nd : ℝ) ny nt nA nB ns := by
  refine ⟨by exact_mod_cast hnd, by exact_mod_cast hny, by exact_mod_cast hnt, Nat.cast_nonneg _, Nat.cast_nonneg _, Nat.cast_nonneg _,
    by exact_mod_cast hR, ?_⟩
  have := congrArg (Nat.cast : ℕ → ℝ) hS
  push_cast at this
  linarith

end Erdos634.Draft.PHyp
