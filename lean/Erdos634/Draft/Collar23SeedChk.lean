-- Draft/Collar23SeedChk.lean -- the kernel checks of the 720-tile table `seedTab0` (T(12)): model sides, non-degeneracy, containment in
-- the triangle 0 <= x, 0 <= y, 2x+3y <= 2880 (scale 8), total |zcr| = 64 * 21600, and a separating edge line for EVERY pair
-- (258,840 pairs, `List.Pairwise sep`).  All by `decide +kernel` (kernel evaluation only, no native_decide).  UNAUDITED.  Credit: B. Herdt.
import Erdos634.Draft.Collar23SeedTab

namespace Erdos634.Draft.Collar23

def Pm8 (t : ZT) : Prop := zq t.a t.b = 3200 ∧ zq t.b t.c = 4608 ∧ zq t.c t.a = 2048
def In8 (p : ZP) : Prop := 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 2 * p.1 + 3 * p.2 ≤ 2880
def Good8 (t : ZT) : Prop := Pm8 t ∧ t.nd ∧ In8 t.a ∧ In8 t.b ∧ In8 t.c

instance (t : ZT) : Decidable (Pm8 t) := by unfold Pm8; infer_instance
instance (p : ZP) : Decidable (In8 p) := by unfold In8; infer_instance
instance (t : ZT) : Decidable (Good8 t) := by unfold Good8; infer_instance

theorem seed_len : seedTab0.length = 720 := by decide +kernel
theorem seed_good : ∀ t ∈ seedTab0, Good8 t := by decide +kernel
theorem seed_area : (seedTab0.map fun t => |zcr t.a t.b t.c|).sum = 1382400 := by decide +kernel

/-- row `n`: tile `n` is separated from every later tile. -/
def rowOK (n : ℕ) : Bool :=
  match seedTab0.drop n with
  | [] => true
  | t :: ts => ts.all fun s => decide (sep t s)

/-- rows `a, a+1, ..., a+k-1`. -/
def rowsOK (a k : ℕ) : Bool := (List.range' a k).all rowOK

theorem pairwise_of_rows {l : List ZT} (h : ∀ n, (match l.drop n with | [] => true | t :: ts => ts.all fun s => decide (sep t s)) = true) :
    l.Pairwise sep := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    refine List.pairwise_cons.mpr ⟨?_, ih ?_⟩
    · have := h 0
      simp only [List.drop_zero, List.all_eq_true, decide_eq_true_eq] at this
      exact this
    · intro n
      have := h (n + 1)
      simpa using this

end Erdos634.Draft.Collar23
