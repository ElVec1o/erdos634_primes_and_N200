/-
Draft/GAUFinal.lean -- **Case A for `N = 15 s²` and `N = 30 s²`** (`GapA (d s²)`, `d ∈ {15, 30}`, every `s ≥ 1`).

No triangle is cut into `N = 15 s²` or `N = 30 s²` congruent triangles all of whose angles are rational multiples of `π`.
(`s = 1`: `GapA 15`, `GapA 30`; `s = 2`: `GapA 60`, `GapA 120`; `s = 3`: `GapA 135`, ...; the earlier proofs of
`GapA 15, 30, 60` bound the coefficients of the identity and are specific to each `N`.)

Proof.  `GAUBridge.gapA_of_residual` leaves the ten tiles with `R ≠ R₀` at the levels `n = 30, 60`
(`exc30`, `exc60`, by the tables `excChk30`, `excChk60`).  For such a tile `a` and a target `(A, B, C)·π/n`, the area
identity of the dissection, divided by `s²`, is `IdQ d n a A B C m` with RATIONAL `m = c / s`; it has no rational
solution, by the kernel-checked certificates of the tile tables `GAUT30_*`, `GAUT60_*` (9,280 certificates in the
cyclotomic field `ℚ(ζ_{2n})`, `GAUCheck.chkCase_sound`).  The constant `d` matters: for a square constant the identity is
solvable (`GAUBridge.idQ_square_witness`).

Composite-N statement; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.GAUT30_1_5_24
import Erdos634.Draft.GAUT30_1_10_19
import Erdos634.Draft.GAUT30_5_6_19
import Erdos634.Draft.GAUT30_5_7_18
import Erdos634.Draft.GAUT30_5_12_13
import Erdos634.Draft.GAUT30_7_10_13
import Erdos634.Draft.GAUT60_1_10_49
import Erdos634.Draft.GAUT60_7_10_43
import Erdos634.Draft.GAUT60_10_13_37
import Erdos634.Draft.GAUT60_10_19_31
import Erdos634.Draft.GAUBridge

open scoped Classical

namespace Erdos634.Draft.GAU

open Erdos634.Geometry Erdos634.LemmaS Erdos634.N30K

/-- the tiles of `exc30` have no rational solution of the identity, for `d = 15, 30` -/
theorem kill_exc30 {d : ℕ} (hd : d = 15 ∨ d = 30) {t : ℕ × ℕ × ℕ} (ht : t ∈ exc30) {a : Fin 3 → ℕ}
    (σ : Equiv.Perm (Fin 3)) (h0 : a (σ 0) = t.1) (h1 : a (σ 1) = t.2.1) (h2 : a (σ 2) = t.2.2)
    {A B C : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) (hs : A + B + C = 30) (m : Fin 3 → ℚ)
    (hid : IdQ d 30 a A B C m) : False := by
  simp only [exc30, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · have e0 : a (σ 0) = T30_1_5_24.a 0 := by simpa [T30_1_5_24.a] using h0
    have e1 : a (σ 1) = T30_1_5_24.a 1 := by simpa [T30_1_5_24.a] using h1
    have e2 : a (σ 2) = T30_1_5_24.a 2 := by simpa [T30_1_5_24.a] using h2
    rcases hd with rfl | rfl
    · exact kill_perm (a₀ := T30_1_5_24.a) T30_1_5_24.kill15 σ e0 e1 e2 hA hB hC hs m hid
    · exact kill_perm (a₀ := T30_1_5_24.a) T30_1_5_24.kill30 σ e0 e1 e2 hA hB hC hs m hid
  · have e0 : a (σ 0) = T30_1_10_19.a 0 := by simpa [T30_1_10_19.a] using h0
    have e1 : a (σ 1) = T30_1_10_19.a 1 := by simpa [T30_1_10_19.a] using h1
    have e2 : a (σ 2) = T30_1_10_19.a 2 := by simpa [T30_1_10_19.a] using h2
    rcases hd with rfl | rfl
    · exact kill_perm (a₀ := T30_1_10_19.a) T30_1_10_19.kill15 σ e0 e1 e2 hA hB hC hs m hid
    · exact kill_perm (a₀ := T30_1_10_19.a) T30_1_10_19.kill30 σ e0 e1 e2 hA hB hC hs m hid
  · have e0 : a (σ 0) = T30_5_6_19.a 0 := by simpa [T30_5_6_19.a] using h0
    have e1 : a (σ 1) = T30_5_6_19.a 1 := by simpa [T30_5_6_19.a] using h1
    have e2 : a (σ 2) = T30_5_6_19.a 2 := by simpa [T30_5_6_19.a] using h2
    rcases hd with rfl | rfl
    · exact kill_perm (a₀ := T30_5_6_19.a) T30_5_6_19.kill15 σ e0 e1 e2 hA hB hC hs m hid
    · exact kill_perm (a₀ := T30_5_6_19.a) T30_5_6_19.kill30 σ e0 e1 e2 hA hB hC hs m hid
  · have e0 : a (σ 0) = T30_5_7_18.a 0 := by simpa [T30_5_7_18.a] using h0
    have e1 : a (σ 1) = T30_5_7_18.a 1 := by simpa [T30_5_7_18.a] using h1
    have e2 : a (σ 2) = T30_5_7_18.a 2 := by simpa [T30_5_7_18.a] using h2
    rcases hd with rfl | rfl
    · exact kill_perm (a₀ := T30_5_7_18.a) T30_5_7_18.kill15 σ e0 e1 e2 hA hB hC hs m hid
    · exact kill_perm (a₀ := T30_5_7_18.a) T30_5_7_18.kill30 σ e0 e1 e2 hA hB hC hs m hid
  · have e0 : a (σ 0) = T30_5_12_13.a 0 := by simpa [T30_5_12_13.a] using h0
    have e1 : a (σ 1) = T30_5_12_13.a 1 := by simpa [T30_5_12_13.a] using h1
    have e2 : a (σ 2) = T30_5_12_13.a 2 := by simpa [T30_5_12_13.a] using h2
    rcases hd with rfl | rfl
    · exact kill_perm (a₀ := T30_5_12_13.a) T30_5_12_13.kill15 σ e0 e1 e2 hA hB hC hs m hid
    · exact kill_perm (a₀ := T30_5_12_13.a) T30_5_12_13.kill30 σ e0 e1 e2 hA hB hC hs m hid
  · have e0 : a (σ 0) = T30_7_10_13.a 0 := by simpa [T30_7_10_13.a] using h0
    have e1 : a (σ 1) = T30_7_10_13.a 1 := by simpa [T30_7_10_13.a] using h1
    have e2 : a (σ 2) = T30_7_10_13.a 2 := by simpa [T30_7_10_13.a] using h2
    rcases hd with rfl | rfl
    · exact kill_perm (a₀ := T30_7_10_13.a) T30_7_10_13.kill15 σ e0 e1 e2 hA hB hC hs m hid
    · exact kill_perm (a₀ := T30_7_10_13.a) T30_7_10_13.kill30 σ e0 e1 e2 hA hB hC hs m hid

/-- the tiles of `exc60` have no rational solution of the identity, for `d = 15, 30` -/
theorem kill_exc60 {d : ℕ} (hd : d = 15 ∨ d = 30) {t : ℕ × ℕ × ℕ} (ht : t ∈ exc60) {a : Fin 3 → ℕ}
    (σ : Equiv.Perm (Fin 3)) (h0 : a (σ 0) = t.1) (h1 : a (σ 1) = t.2.1) (h2 : a (σ 2) = t.2.2)
    {A B C : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) (hs : A + B + C = 60) (m : Fin 3 → ℚ)
    (hid : IdQ d 60 a A B C m) : False := by
  simp only [exc60, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · have e0 : a (σ 0) = T60_1_10_49.a 0 := by simpa [T60_1_10_49.a] using h0
    have e1 : a (σ 1) = T60_1_10_49.a 1 := by simpa [T60_1_10_49.a] using h1
    have e2 : a (σ 2) = T60_1_10_49.a 2 := by simpa [T60_1_10_49.a] using h2
    rcases hd with rfl | rfl
    · exact kill_perm (a₀ := T60_1_10_49.a) T60_1_10_49.kill15 σ e0 e1 e2 hA hB hC hs m hid
    · exact kill_perm (a₀ := T60_1_10_49.a) T60_1_10_49.kill30 σ e0 e1 e2 hA hB hC hs m hid
  · have e0 : a (σ 0) = T60_7_10_43.a 0 := by simpa [T60_7_10_43.a] using h0
    have e1 : a (σ 1) = T60_7_10_43.a 1 := by simpa [T60_7_10_43.a] using h1
    have e2 : a (σ 2) = T60_7_10_43.a 2 := by simpa [T60_7_10_43.a] using h2
    rcases hd with rfl | rfl
    · exact kill_perm (a₀ := T60_7_10_43.a) T60_7_10_43.kill15 σ e0 e1 e2 hA hB hC hs m hid
    · exact kill_perm (a₀ := T60_7_10_43.a) T60_7_10_43.kill30 σ e0 e1 e2 hA hB hC hs m hid
  · have e0 : a (σ 0) = T60_10_13_37.a 0 := by simpa [T60_10_13_37.a] using h0
    have e1 : a (σ 1) = T60_10_13_37.a 1 := by simpa [T60_10_13_37.a] using h1
    have e2 : a (σ 2) = T60_10_13_37.a 2 := by simpa [T60_10_13_37.a] using h2
    rcases hd with rfl | rfl
    · exact kill_perm (a₀ := T60_10_13_37.a) T60_10_13_37.kill15 σ e0 e1 e2 hA hB hC hs m hid
    · exact kill_perm (a₀ := T60_10_13_37.a) T60_10_13_37.kill30 σ e0 e1 e2 hA hB hC hs m hid
  · have e0 : a (σ 0) = T60_10_19_31.a 0 := by simpa [T60_10_19_31.a] using h0
    have e1 : a (σ 1) = T60_10_19_31.a 1 := by simpa [T60_10_19_31.a] using h1
    have e2 : a (σ 2) = T60_10_19_31.a 2 := by simpa [T60_10_19_31.a] using h2
    rcases hd with rfl | rfl
    · exact kill_perm (a₀ := T60_10_19_31.a) T60_10_19_31.kill15 σ e0 e1 e2 hA hB hC hs m hid
    · exact kill_perm (a₀ := T60_10_19_31.a) T60_10_19_31.kill30 σ e0 e1 e2 hA hB hC hs m hid

/-- **The residual of `GapA (d s²)`**, `d ∈ {15, 30}`. -/
theorem residual_sq {d s : ℕ} (hd : d = 15 ∨ d = 30) (hs : 0 < s) : GapAResidual (d * s ^ 2) := by
  intro D n a hn hgcd ha hex hne
  obtain ⟨ha1, hsum, b, c, hb1, hbs, hid⟩ := identityN D hn a ha
  have hq := idQ_of_idFin hs hid
  rw [Fin.sum_univ_three] at hbs
  rcases hex with rfl | rfl
  · obtain ⟨t, ht, σ, h0, h1, h2⟩ := exc_of_excChk excChk30 a ha1 hsum hgcd hne
    exact kill_exc30 hd ht σ h0 h1 h2 (hb1 0) (hb1 1) (hb1 2) hbs _ hq
  · obtain ⟨t, ht, σ, h0, h1, h2⟩ := exc_of_excChk excChk60 a ha1 hsum hgcd hne
    exact kill_exc60 hd ht σ h0 h1 h2 (hb1 0) (hb1 1) (hb1 2) hbs _ hq

/-- **Case A for `N = 15 s²` and `N = 30 s²`**: no dissection into `d s²` congruent triangles with all angles in
`ℚπ`, for `d ∈ {15, 30}` and every `s ≥ 1`. -/
theorem gapA_sq {d s : ℕ} (hd : d = 15 ∨ d = 30) (hs : 0 < s) : Erdos634.Draft.Chain15.GapA (d * s ^ 2) := by
  have h3 : ¬ Even (padicValNat 3 (d * s ^ 2)) := by
    rcases hd with rfl | rfl
    · exact val_odd Nat.prime_three val3_15 hs
    · exact val_odd Nat.prime_three val3_30 hs
  have h5 : ¬ Even (padicValNat 5 (d * s ^ 2)) := by
    rcases hd with rfl | rfl
    · exact val_odd Nat.prime_five val5_15 hs
    · exact val_odd Nat.prime_five val5_30 hs
  exact gapA_of_residual (nq_of_sq hd hs) h3 h5 (residual_sq hd hs)

/-- **`GapA 120`** (`120 = 30 · 2²`). -/
theorem gapA_120 : Erdos634.Draft.Chain15.GapA 120 := by
  have h := gapA_sq (d := 30) (s := 2) (Or.inr rfl) (by norm_num)
  norm_num at h
  exact h

/-- **`GapA 135`** (`135 = 15 · 3²`). -/
theorem gapA_135 : Erdos634.Draft.Chain15.GapA 135 := by
  have h := gapA_sq (d := 15) (s := 3) (Or.inl rfl) (by norm_num)
  norm_num at h
  exact h

end Erdos634.Draft.GAU

#print axioms Erdos634.Draft.GAU.gapA_sq
#print axioms Erdos634.Draft.GAU.gapA_120
#print axioms Erdos634.Draft.GAU.gapA_135
