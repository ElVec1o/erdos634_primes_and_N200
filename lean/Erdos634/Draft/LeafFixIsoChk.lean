/-
Draft/LeafFixIsoChk.lean -- the strengthened Iso leaf (ISO-INT): decidable checks and their closure lemma.

`IsoBadX N a b := IsoBad N a b ∧ b ∣ k` where `k = Nat.sqrt (b * (N / (a + 2 * b)))`  (`IsoBad` = `AllNExclusionArith.IsoBad`).
`IsoH9cChk N`   : no `IsoBadX` pair `(a, b) = (e - 2b, b)` with `e ∣ N`, `3 ≤ e < N`, `2b < e`, `gcd(b,e) = 1`.
`IsoH9cChkW N`  : the windowed form (as `NSQWin3.IsoH9bChkW`): divisors `d ≤ √N`, `k ≤ √(N/2)`.
`isoH9c_of_check` / `isoH9c_of_chk` : `IsoH9cChk N → IsoH9c N`  (`IsoH9c`: `LeafFixIsoThm`).
`isoH9cChk_of_W` : `IsoH9cChkW N → IsoH9cChk N`.

THE ARGUMENT (ISO-INT, `Paper.cor_int`): `IsoH9c` has the data `k (c-a-b) = nA b`, `k (c+a+b) = nB b`, `nA ≡ nB ≡ N (mod 2)`.  Then
`2 k (a+b) = (nB - nA) b = 2 (s - t) b`, so `b ∣ k (a+b)`, and `gcd(b, a+b) = gcd(b, a+2b) = 1` gives `b ∣ k`.
Hence a pair satisfying `IsoBad` with the extra `b ∣ k` is the only one that has to be excluded.
COPIES (with the extra conjunct) of `CompositeIsoB.isoH9b_of_check`, `NSQWin3.IsoQ/IsoH9bChkW/isoQ_apply/isoH9bChk_of_W`.
Credit: Beeson-Rosu (`cor:int`), Laczkovich, Paliy.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.LeafFixIsoThm
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM

open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.NSQMain Erdos634.Draft.E60Irr
open Erdos634.Draft.LeafFixIso

/-- `IsoBad` with the extra ISO-INT conjunct `b ∣ k` -/
def IsoBadX (N a b : ℕ) : Prop :=
  IsoBad N a b ∧ ((Nat.sqrt (b * (N / (a + 2 * b))) : ℤ) % b = 0)

instance (N a b : ℕ) : Decidable (IsoBadX N a b) := by unfold IsoBadX; infer_instance

def IsoH9cChk (N : ℕ) : Prop :=
  ∀ e < N, 3 ≤ e → e ∣ N → ∀ b < e, 0 < b → 2 * b < e → Nat.gcd b e = 1 → ¬ IsoBadX N (e - 2 * b) b

instance (N : ℕ) : Decidable (IsoH9cChk N) := by unfold IsoH9cChk; infer_instance

theorem isoH9c_of_check (N : ℕ) (hN : 0 < N)
    (hchk : ∀ a : ℕ, a < N → ∀ b : ℕ, b < N → 0 < a → 0 < b → a + 2 * b < N → 3 ≤ a + 2 * b →
      a + 2 * b ∣ N → Nat.gcd b (a + 2 * b) = 1 →
      Nat.sqrt (a ^ 2 + a * b + b ^ 2) * Nat.sqrt (a ^ 2 + a * b + b ^ 2) = a ^ 2 + a * b + b ^ 2 →
      Nat.sqrt (b * (N / (a + 2 * b))) * Nat.sqrt (b * (N / (a + 2 * b))) = b * (N / (a + 2 * b)) →
      ((Nat.sqrt (b * (N / (a + 2 * b))) : ℤ) * ((Nat.sqrt (a ^ 2 + a * b + b ^ 2) : ℤ) - a - b)) % b = 0 →
      ((((Nat.sqrt (b * (N / (a + 2 * b))) : ℤ) * ((Nat.sqrt (a ^ 2 + a * b + b ^ 2) : ℤ) - a - b)) / b - N) % 2
        = 0) → ((Nat.sqrt (b * (N / (a + 2 * b))) : ℤ) % b = 0) → False) :
    IsoH9c N := by
  intro a b c k nA nB ha hb hc hk hcc h3 hcop hdvd hne harea hkc hkc2 hpar hparB
  have hle : a + 2 * b ≤ (N : ℤ) := Int.le_of_dvd (by exact_mod_cast hN) hdvd
  have hlt : a + 2 * b < (N : ℤ) := lt_of_le_of_ne hle hne
  -- ISO-INT: b ∣ k, from both parities (before the lifts)
  have hcop2 : IsCoprime b (a + b) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨u + v, v, by linear_combination huv⟩
  have hdiv2 : b ∣ k * (a + b) := by
    obtain ⟨t, ht⟩ := hpar
    obtain ⟨s, hs⟩ := hparB
    refine ⟨s - t, ?_⟩
    have h2 : 2 * (k * (a + b)) = 2 * (b * (s - t)) := by
      linear_combination hkc2 - hkc + b * (hs - ht)
    linarith
  have hbk : b ∣ k := hcop2.dvd_of_dvd_mul_right hdiv2
  lift a to ℕ using ha.le
  lift b to ℕ using hb.le
  lift c to ℕ using hc.le
  lift k to ℕ using hk.le
  have hdvd' : a + 2 * b ∣ N := by exact_mod_cast hdvd
  have hcc' : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by exact_mod_cast hcc
  have hcop' : Nat.gcd b (a + 2 * b) = 1 := by
    have : IsCoprime ((b : ℕ) : ℤ) (((a + 2 * b : ℕ)) : ℤ) := by exact_mod_cast hcop
    exact Nat.isCoprime_iff_coprime.mp this
  obtain ⟨n', hn'⟩ := hdvd'
  have hepos : 0 < a + 2 * b := by omega
  have hdiv : N / (a + 2 * b) = n' := by rw [hn']; exact Nat.mul_div_cancel_left _ hepos
  have hkq : k ^ 2 = b * n' := by
    have h1 : (b : ℤ) * (N : ℤ) = (k : ℤ) ^ 2 * (a + 2 * b) := by exact_mod_cast harea
    have h2 : b * N = k ^ 2 * (a + 2 * b) := by exact_mod_cast h1
    rw [hn'] at h2
    have h3' : (a + 2 * b) * (b * n') = (a + 2 * b) * k ^ 2 := by linarith [h2]
    exact (Nat.eq_of_mul_eq_mul_left hepos h3').symm
  have hsc : Nat.sqrt (a ^ 2 + a * b + b ^ 2) = c := by rw [← hcc']; exact Nat.sqrt_eq' c
  have hsk : Nat.sqrt (b * (N / (a + 2 * b))) = k := by rw [hdiv, ← hkq]; exact Nat.sqrt_eq' k
  have hnA : ((k : ℤ) * ((c : ℤ) - a - b)) / b = nA := by
    have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [hkc]; exact Int.mul_ediv_cancel nA hb0
  have hmod : ((k : ℤ) * ((c : ℤ) - a - b)) % b = 0 := Int.emod_eq_zero_of_dvd ⟨nA, by rw [hkc]; ring⟩
  have hpar' : ((nA - (N : ℤ)) % 2 = 0) := Int.emod_eq_zero_of_dvd hpar
  have hmodk : (k : ℤ) % b = 0 := Int.emod_eq_zero_of_dvd hbk
  refine hchk a (by omega) b (by omega) (by exact_mod_cast ha) (by exact_mod_cast hb) (by omega) (by omega)
    ⟨n', hn'⟩ hcop' ?_ ?_ ?_ ?_ ?_
  · rw [hsc]; nlinarith [hcc']
  · rw [hsk, hdiv, ← hkq]; ring
  · rw [hsk, hsc]; exact hmod
  · rw [hsk, hsc, hnA]; exact hpar'
  · rw [hsk]; exact hmodk

theorem isoH9c_of_chk {N : ℕ} (hN : 0 < N) (h : IsoH9cChk N) : IsoH9c N := by
  apply isoH9c_of_check N hN
  intro a ha b hb ha0 hb0 hlt h3 hdvd hg h1 h2 h3' h4 h5
  have := h (a + 2 * b) hlt h3 hdvd b (by omega) hb0 (by omega) hg
  apply this
  simp only [Nat.add_sub_cancel]
  exact ⟨⟨h1, h2, h3', h4⟩, h5⟩

/-! ## windowed form -/

def IsoQX (N e : ℕ) : Prop :=
  e < N → 3 ≤ e → ∀ k ≤ Nat.sqrt (N / 2), N / e ∣ k * k → 0 < k * k / (N / e) → 2 * (k * k / (N / e)) < e →
    Nat.gcd (k * k / (N / e)) e = 1 → ¬ IsoBadX N (e - 2 * (k * k / (N / e))) (k * k / (N / e))

instance (N e : ℕ) : Decidable (IsoQX N e) := by unfold IsoQX; infer_instance

def IsoH9cChkW (N : ℕ) : Prop :=
  ∀ d ≤ Nat.sqrt N, 0 < d → d ∣ N → IsoQX N d ∧ IsoQX N (N / d)

instance (N : ℕ) : Decidable (IsoH9cChkW N) := by unfold IsoH9cChkW; infer_instance

theorem isoQX_apply {N e : ℕ} (hQ : IsoQX N e) (he : e < N) (h3 : 3 ≤ e) (hd : e ∣ N) {b : ℕ} (hb0 : 0 < b)
    (h2b : 2 * b < e) (hg : Nat.gcd b e = 1) (hbad : IsoBadX N (e - 2 * b) b) : False := by
  have hN : 0 < N := by omega
  have hE : e - 2 * b + 2 * b = e := by omega
  have hm0 : 0 < N / e := Nat.div_pos (by omega) (by omega)
  have hem : e * (N / e) = N := Nat.mul_div_cancel' hd
  have hbad' := hbad.1
  unfold IsoBad at hbad'
  rw [hE] at hbad'
  have h2 := hbad'.2.1
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.sqrt (b * (N / e)) := ⟨_, rfl⟩
  rw [← hk] at h2
  have hbk : k * k / (N / e) = b := by rw [h2]; exact Nat.mul_div_cancel _ hm0
  have hks : k ≤ Nat.sqrt (N / 2) := by
    apply Nat.le_sqrt.mpr
    apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
    have : (2 * b + 1) * (N / e) ≤ e * (N / e) := Nat.mul_le_mul_right _ h2b
    nlinarith
  have hdv : N / e ∣ k * k := ⟨b, by rw [h2]; ring⟩
  have := hQ he h3 k hks hdv (by rw [hbk]; exact hb0) (by rw [hbk]; exact h2b) (by rw [hbk]; exact hg)
  rw [hbk] at this
  exact this hbad

theorem isoH9cChk_of_W {N : ℕ} (h : IsoH9cChkW N) : IsoH9cChk N := by
  intro e he h3 hd b hb hb0 h2b hg hbad
  have hN : 0 < N := by omega
  have hQ : IsoQX N e := by
    by_cases hc : e * e ≤ N
    · exact (h e (Nat.le_sqrt.mpr hc) (by omega) hd).1
    · have hd0 : 0 < N / e := Nat.div_pos (by omega) (by omega)
      have hem : e * (N / e) = N := Nat.mul_div_cancel' hd
      have hdd : N / (N / e) = e := Nat.div_div_self hd (by omega)
      have hle : N / e * (N / e) ≤ N := by
        by_contra hcon
        have : N < N / e * (N / e) := by omega
        have h1 : N / e < e := by
          by_contra h1; push Not at h1
          have : e * e ≤ N := by nlinarith
          exact hc this
        nlinarith
      have := (h (N / e) (Nat.le_sqrt.mpr hle) hd0 (Nat.div_dvd_of_dvd hd)).2
      rwa [hdd] at this
  exact isoQX_apply hQ he h3 hd hb0 h2b hg hbad

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.isoH9c_of_chk
#print axioms Erdos634.Draft.NSQM.isoH9cChk_of_W
