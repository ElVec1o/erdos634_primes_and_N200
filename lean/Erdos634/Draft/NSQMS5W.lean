/-
Draft/NSQMS5W.lean — the S5 word leaf.  For an S5 instance `(t, e, f)` (`N = t² (f² − e²)`, `t ≥ 2`, `0 < e < f`, coprime)
the base of a dissection of `θ_t(e, f)` carries a word `x (e f) + y (f² − e²) + z f² = t e (f² − e²)` with `z ≥ f`
(`ThetaKill.theta_word`, from `SideRunGThetaMain.theta_word_hasSides`).
  `WordN t e f`  : decidable bounded form of that word (naturals).
  `S5wChk N`     : decidable; every S5 decomposition `N = t² a b` (`a = f − e`, `b = f + e`) has NO word.
  `S5wFree N`    : the integer form (`¬ S5WordF t e f` for every S5 instance).
  `s5wFree_of_chk`, `raStatement_of_s5w : S5wChk N → RAStatementNsq N`.
The word leaf subsumes the old bounds `t e < 2 f` and (`e = f − 1`) `t < f + 2` (they are consequences of the word:
`ThetaKill.s5wordF_ge`, `s5wordF_thick`).      No sorry, no native_decide.
-/
import Erdos634.Draft.ThetaKill
import Erdos634.Draft.RAInst

open Erdos634.Geometry Erdos634.Draft.ThetaKill

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM

/-- decidable bounded word: `T = t e (f² − e²)`; `z ≥ f` edges `c`, `y` edges `b`, the rest a multiple of `e f` -/
def WordN (t e f : ℕ) : Prop :=
  ∃ z < t * e * (f * f - e * e) / (f * f) + 1, f ≤ z ∧
    ∃ y < t * e * (f * f - e * e) / (f * f - e * e) + 1,
      z * (f * f) + y * (f * f - e * e) ≤ t * e * (f * f - e * e) ∧
      e * f ∣ t * e * (f * f - e * e) - z * (f * f) - y * (f * f - e * e)

instance (t e f : ℕ) : Decidable (WordN t e f) := by unfold WordN; infer_instance

def S5wChk (N : ℕ) : Prop :=
  ∀ t ≤ N, 2 ≤ t → t * t ∣ N → ∀ a ≤ N, a ∣ N / (t * t) → 0 < a → a < N / (t * t) / a →
    a % 2 = (N / (t * t) / a) % 2 →
    Nat.Coprime ((N / (t * t) / a - a) / 2) ((a + N / (t * t) / a) / 2) →
    ¬ WordN t ((N / (t * t) / a - a) / 2) ((a + N / (t * t) / a) / 2)

instance (N : ℕ) : Decidable (S5wChk N) := by unfold S5wChk; infer_instance

def S5wFree (N : ℕ) : Prop :=
  ∀ t e f : ℤ, 2 ≤ t → 0 < e → e < f → IsCoprime e f → (N : ℤ) = t ^ 2 * (f ^ 2 - e ^ 2) → ¬ S5WordF t e f

theorem wordN_of_wordF {t e f : ℕ} (he : 0 < e) (hef : e < f)
    (h : S5WordF (t : ℤ) (e : ℤ) (f : ℤ)) : WordN t e f := by
  obtain ⟨P, Q, R, hR, hw⟩ := h
  have hee : e * e ≤ f * f := Nat.mul_le_mul hef.le hef.le
  have hb : 0 < f * f - e * e := by
    have : e * e < f * f := Nat.mul_lt_mul'' hef hef
    omega
  have hf0 : 0 < f * f := Nat.mul_pos (by omega) (by omega)
  have hT : t * e * (f * f - e * e) = P * (e * f) + Q * (f * f - e * e) + R * (f * f) := by
    have : ((t * e * (f * f - e * e) : ℕ) : ℤ) = ((P * (e * f) + Q * (f * f - e * e) + R * (f * f) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hee]
      linear_combination hw
    exact_mod_cast this
  have hRf : f ≤ R := by exact_mod_cast hR
  refine ⟨R, ?_, hRf, Q, ?_, ?_, ?_⟩
  · apply Nat.lt_succ_of_le; rw [Nat.le_div_iff_mul_le hf0]; rw [hT]
    nlinarith [Nat.zero_le (P * (e * f)), Nat.zero_le (Q * (f * f - e * e))]
  · apply Nat.lt_succ_of_le; rw [Nat.le_div_iff_mul_le hb]; rw [hT]
    nlinarith [Nat.zero_le (P * (e * f)), Nat.zero_le (R * (f * f))]
  · rw [hT]; omega
  · have : t * e * (f * f - e * e) - R * (f * f) - Q * (f * f - e * e) = P * (e * f) := by
      rw [hT]
      generalize P * (e * f) = A
      generalize Q * (f * f - e * e) = B
      generalize R * (f * f) = C
      omega
    rw [this]; exact ⟨P, by ring⟩

theorem s5wFree_of_chk {N : ℕ} (h : S5wChk N) : S5wFree N := by
  intro t e f ht he hef hcop hN hW
  lift t to ℕ using (by omega)
  lift e to ℕ using he.le
  obtain ⟨a, ha⟩ : ∃ a : ℕ, f = (e : ℤ) + a := ⟨(f - e).toNat, by omega⟩
  have hapos : 0 < a := by omega
  have ht2 : 2 ≤ t := by exact_mod_cast ht
  have he0 : 0 < e := by exact_mod_cast he
  have hNn : N = t * t * (a * (2 * e + a)) := by
    have : (N : ℤ) = ((t * t * (a * (2 * e + a)) : ℕ) : ℤ) := by
      rw [hN, ha]; push_cast; ring
    exact_mod_cast this
  have hdiv : N / (t * t) = a * (2 * e + a) := by
    rw [hNn]; exact Nat.mul_div_cancel_left _ (by positivity)
  have hdiv2 : a * (2 * e + a) / a = 2 * e + a := Nat.mul_div_cancel_left _ hapos
  have hn0 : 0 < a * (2 * e + a) := by positivity
  have htN : t ≤ N := by
    have : t ≤ t * t := Nat.le_mul_self t
    have : t * t ≤ N := by rw [hNn]; exact Nat.le_mul_of_pos_right _ hn0
    omega
  have haN : a ≤ N := by
    have : a ≤ a * (2 * e + a) := Nat.le_mul_of_pos_right _ (by omega)
    have : a * (2 * e + a) ≤ N := by rw [hNn]; exact Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have htt : t * t ∣ N := ⟨_, hNn⟩
  have e1 : (2 * e + a - a) / 2 = e := by omega
  have e2 : (a + (2 * e + a)) / 2 = e + a := by omega
  have hcop' : Nat.Coprime e (e + a) := by
    have : IsCoprime (e : ℤ) ((e : ℤ) + a) := by rw [← ha]; exact hcop
    have h2 : IsCoprime (e : ℤ) ((e + a : ℕ) : ℤ) := by push_cast; exact this
    exact Nat.isCoprime_iff_coprime.mp h2
  have key := h t htN ht2 htt a haN (by rw [hdiv]; exact Dvd.intro _ rfl) hapos
    (by rw [hdiv, hdiv2]; omega) (by rw [hdiv, hdiv2]; omega)
    (by rw [hdiv, hdiv2, e1, e2]; exact hcop')
  rw [hdiv, hdiv2, e1, e2] at key
  apply key
  have hfe : (f : ℤ) = ((e + a : ℕ) : ℤ) := by push_cast; exact ha
  rw [hfe] at hW
  exact wordN_of_wordF he0 (by omega) hW

theorem s5inst_of_no_wordF {t e f : ℤ} (ht : 0 < t) (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f)
    (hno : ¬ S5WordF t e f) : S5Inst t e f := by
  intro N D h0 h1 h2 hm
  obtain ⟨hT, hM⟩ := Erdos634.Draft.ThetaKill.s5_hyps_to_hasSides D h0 h1 h2 hm
  exact hno (theta_word D ht he hef hcop hT hM)

/-- **The S5 word leaf**: `S5wChk N` gives `RAStatementNsq N`. -/
theorem raStatement_of_s5w (N : ℕ) (h : S5wChk N) : Erdos634.Draft.NSQRA.RAStatementNsq N :=
  raStatement_of_inst N (fun t e f ht he hef hcop hN =>
    s5inst_of_no_wordF (by omega) he hef hcop (s5wFree_of_chk h t e f ht he hef hcop hN))

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.raStatement_of_s5w
