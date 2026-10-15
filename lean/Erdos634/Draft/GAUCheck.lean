/-
The certificate checker of the uniform commensurable-angle kill and its soundness.

For a tile `a` (angles `a_k π/n`), a target `(A, B, C)` and the constant `d`, a certificate proves that the identity
`IdQ d n a A B C m` has no rational solution `m`:
* `Cert.I ℓ`: the row `ℓ` vanishes on all nine columns and not on the right side (the linear system for the products
  `m_i m_j` is inconsistent);
* `Cert.D p ℓ`: the row isolates `m_p²`: `m_p² · D = d · r`, and `d r D` is negative or not a perfect square;
* `Cert.Z ℓ0 ℓ1 ℓ2`: three rows give `m_0 = m_1 = m_2 = 0`, and then the identity reads `0 = d sin A Π sin a_k ≠ 0`;
* `Cert.R …`: the tiles whose six products are linearly dependent (one free parameter `t = m_2²`): five rows express
  the other products through `t`, and an integer combination of the `2 × 2` minors of `(m_i m_j)` with linear
  multipliers is `c₀ + c₁ t`; either `c₁ = 0 ≠ c₀`, or `t = −c₀/c₁` and one `m_p²` is negative or not a square.

`chkTile_sound`: if `chkTile d n red a certs` evaluates to `true`, no target and no rational `m` satisfy the identity.

No sorry, no native_decide.
-/
import Erdos634.Draft.GAURow

open Finset

namespace Erdos634.Draft.GAU

def pairs9 : List (Fin 3 × Fin 3) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

theorem mem_pairs9 (i j : Fin 3) : (i, j) ∈ pairs9 := by
  fin_cases i <;> fin_cases j <;> simp [pairs9]

/-- the row `ℓ` (on the power basis) as a functional on lists of length `n` -/
def lamOf (red : List (List ℤ)) (ℓ : List ℤ) : List ℤ := red.map (dotL ℓ)

/-- the value of the row on the column `(i, j)` -/
def LamC (n : ℕ) (red : List (List ℤ)) (a : Fin 3 → ℕ) (B C : ℕ) (ℓ : List ℤ) (i j : Fin 3) : ℤ :=
  dotL (colV n a B C i j) (lamOf red ℓ)

/-- the value of the row on the right side -/
def LamR (n : ℕ) (red : List (List ℤ)) (a : Fin 3 → ℕ) (A : ℕ) (ℓ : List ℤ) : ℤ :=
  dotL (rV n a A) (lamOf red ℓ)

/-- the row vanishes outside the listed columns -/
def suppOK (L : Fin 3 → Fin 3 → ℤ) (S : List (Fin 3 × Fin 3)) : Bool :=
  pairs9.all fun ij => S.contains ij || L ij.1 ij.2 == 0

theorem suppOK_sound {L : Fin 3 → Fin 3 → ℤ} {S : List (Fin 3 × Fin 3)} (h : suppOK L S = true) (i j : Fin 3)
    (hij : (i, j) ∉ S) : L i j = 0 := by
  unfold suppOK at h
  rw [List.all_eq_true] at h
  have := h (i, j) (mem_pairs9 i j)
  simp only [Bool.or_eq_true, List.contains_iff_mem, beq_iff_eq] at this
  rcases this with h1 | h1
  · exact absurd h1 hij
  · exact h1

theorem sum9 (m : Fin 3 → ℚ) (L : Fin 3 → Fin 3 → ℤ) :
    ∑ i, ∑ j, m i * m j * ((L i j : ℤ) : ℚ)
      = m 0 * m 0 * L 0 0 + m 0 * m 1 * L 0 1 + m 0 * m 2 * L 0 2 + m 1 * m 0 * L 1 0 + m 1 * m 1 * L 1 1
        + m 1 * m 2 * L 1 2 + m 2 * m 0 * L 2 0 + m 2 * m 1 * L 2 1 + m 2 * m 2 * L 2 2 := by
  simp only [Fin.sum_univ_three]
  ring

/-- a row supported on the single column `(p, p)` -/
theorem sum_single {L : Fin 3 → Fin 3 → ℤ} {p : Fin 3} (h : suppOK L [(p, p)] = true) (m : Fin 3 → ℚ) :
    ∑ i, ∑ j, m i * m j * ((L i j : ℤ) : ℚ) = m p * m p * (L p p : ℚ) := by
  have hz : ∀ i j, (i, j) ≠ (p, p) → L i j = 0 := fun i j hij =>
    suppOK_sound h i j (by simpa using hij)
  rw [Finset.sum_eq_single p, Finset.sum_eq_single p]
  · intro j _ hj
    rw [hz p j (by intro e; exact hj (Prod.ext_iff.mp e).2)]; simp
  · intro hp; exact absurd (Finset.mem_univ p) hp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [hz i j (by intro e; exact hi (Prod.ext_iff.mp e).1)]; simp
  · intro hp; exact absurd (Finset.mem_univ p) hp

/-- perfect square test -/
def isSqZ (k : ℤ) : Bool := Int.sqrt k * Int.sqrt k == k

theorem isSqZ_of_sq {q : ℚ} {k : ℤ} (h : q ^ 2 = (k : ℚ)) : isSqZ k = true := by
  have h1 : IsSquare ((k : ℤ) : ℚ) := ⟨q, by rw [← h]; ring⟩
  obtain ⟨z, hz⟩ := Rat.isSquare_intCast_iff.mp h1
  unfold isSqZ
  rw [beq_iff_eq]
  exact (Int.exists_mul_self k).mp ⟨z, hz.symm⟩

/-- a square is not negative and, when an integer, a perfect square -/
theorem sq_kill {q : ℚ} {k : ℤ} (h : q ^ 2 = (k : ℚ)) (hk : (decide (k < 0) || !(isSqZ k)) = true) : False := by
  rcases Bool.or_eq_true _ _ |>.mp hk with h1 | h1
  · have h2 : k < 0 := by simpa using h1
    have h3 : ((k : ℤ) : ℚ) < 0 := by exact_mod_cast h2
    have := sq_nonneg q
    linarith
  · rw [isSqZ_of_sq h] at h1
    simp at h1

/-! ## The rank-5 certificate, as integer arithmetic

`O_ij (m_i m_j) = x_ija + x_ijb t` with `t = m_2²` (five relations); the scaled `2 × 2` minors
`N₀ = O₁₂² X₁₁ X₂₂ − O₁₁ O₂₂ X₁₂²`, `N₁ = O₁₃² X₁₁ t − O₁₁ X₁₃²`, `N₂ = O₂₃² X₂₂ t − O₂₂ X₂₃²` vanish; the combination
`P(t) = Σ (p_k + q_k t) N_k(t)` is a cubic in `t`, and the checker verifies that it is `c₀ + c₁ t` by evaluating it at
`t = 0, 1, 2, 3`. -/

structure RD where
  O11 : ℤ
  O12 : ℤ
  O13 : ℤ
  O22 : ℤ
  O23 : ℤ
  x11a : ℤ
  x11b : ℤ
  x12a : ℤ
  x12b : ℤ
  x13a : ℤ
  x13b : ℤ
  x22a : ℤ
  x22b : ℤ
  x23a : ℤ
  x23b : ℤ
  p0 : ℤ
  q0 : ℤ
  p1 : ℤ
  q1 : ℤ
  p2 : ℤ
  q2 : ℤ

def Pf (r : RD) (t : ℤ) : ℤ :=
  (r.p0 + r.q0 * t) * (r.O12 ^ 2 * (r.x11a + r.x11b * t) * (r.x22a + r.x22b * t)
      - r.O11 * r.O22 * (r.x12a + r.x12b * t) ^ 2)
    + (r.p1 + r.q1 * t) * (r.O13 ^ 2 * (r.x11a + r.x11b * t) * t - r.O11 * (r.x13a + r.x13b * t) ^ 2)
    + (r.p2 + r.q2 * t) * (r.O23 ^ 2 * (r.x22a + r.x22b * t) * t - r.O22 * (r.x23a + r.x23b * t) ^ 2)

def PfQ (r : RD) (t : ℚ) : ℚ :=
  ((r.p0 : ℚ) + r.q0 * t) * ((r.O12 : ℚ) ^ 2 * (r.x11a + r.x11b * t) * (r.x22a + r.x22b * t)
      - r.O11 * r.O22 * (r.x12a + r.x12b * t) ^ 2)
    + ((r.p1 : ℚ) + r.q1 * t) * ((r.O13 : ℚ) ^ 2 * (r.x11a + r.x11b * t) * t - r.O11 * (r.x13a + r.x13b * t) ^ 2)
    + ((r.p2 : ℚ) + r.q2 * t) * ((r.O23 : ℚ) ^ 2 * (r.x22a + r.x22b * t) * t - r.O22 * (r.x23a + r.x23b * t) ^ 2)

theorem Pf_cast (r : RD) (t : ℤ) : ((Pf r t : ℤ) : ℚ) = PfQ r (t : ℚ) := by
  unfold Pf PfQ; push_cast; ring

/-- Lagrange interpolation of the cubic `PfQ r` at `0, 1, 2, 3` -/
theorem PfQ_interp (r : RD) (t : ℚ) :
    PfQ r t = PfQ r 0 * (-(t - 1) * (t - 2) * (t - 3) / 6) + PfQ r 1 * (t * (t - 2) * (t - 3) / 2)
      + PfQ r 2 * (-(t * (t - 1) * (t - 3)) / 2) + PfQ r 3 * (t * (t - 1) * (t - 2) / 6) := by
  unfold PfQ; ring

def chkRD (r : RD) (bad : ℕ) : Bool :=
  (r.O11 != 0) && (r.O12 != 0) && (r.O13 != 0) && (r.O22 != 0) && (r.O23 != 0) &&
  (Pf r 2 == Pf r 0 + 2 * (Pf r 1 - Pf r 0)) && (Pf r 3 == Pf r 0 + 3 * (Pf r 1 - Pf r 0)) &&
  (match bad with
    | 0 => (Pf r 1 - Pf r 0 == 0) && (Pf r 0 != 0)
    | 1 => (Pf r 1 - Pf r 0 != 0) &&
        (decide (r.O11 * (Pf r 1 - Pf r 0) * (r.x11a * (Pf r 1 - Pf r 0) - r.x11b * Pf r 0) < 0) ||
          !(isSqZ (r.O11 * (Pf r 1 - Pf r 0) * (r.x11a * (Pf r 1 - Pf r 0) - r.x11b * Pf r 0))))
    | 2 => (Pf r 1 - Pf r 0 != 0) &&
        (decide (r.O22 * (Pf r 1 - Pf r 0) * (r.x22a * (Pf r 1 - Pf r 0) - r.x22b * Pf r 0) < 0) ||
          !(isSqZ (r.O22 * (Pf r 1 - Pf r 0) * (r.x22a * (Pf r 1 - Pf r 0) - r.x22b * Pf r 0))))
    | _ => (Pf r 1 - Pf r 0 != 0) &&
        (decide (-(Pf r 0 * (Pf r 1 - Pf r 0)) < 0) || !(isSqZ (-(Pf r 0 * (Pf r 1 - Pf r 0))))))

theorem chkRD_sound (r : RD) (bad : ℕ) (h : chkRD r bad = true) (m0 m1 m2 : ℚ)
    (r11 : (r.O11 : ℚ) * (m0 * m0) = r.x11a + r.x11b * (m2 * m2))
    (r12 : (r.O12 : ℚ) * (m0 * m1) = r.x12a + r.x12b * (m2 * m2))
    (r13 : (r.O13 : ℚ) * (m0 * m2) = r.x13a + r.x13b * (m2 * m2))
    (r22 : (r.O22 : ℚ) * (m1 * m1) = r.x22a + r.x22b * (m2 * m2))
    (r23 : (r.O23 : ℚ) * (m1 * m2) = r.x23a + r.x23b * (m2 * m2)) : False := by
  unfold chkRD at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨o11, o12⟩, o13⟩, o22⟩, o23⟩, e2⟩, e3⟩, hbad⟩ := h
  obtain ⟨t, ht⟩ : ∃ t : ℚ, t = m2 * m2 := ⟨_, rfl⟩
  rw [← ht] at r11 r12 r13 r22 r23
  -- the cubic vanishes at `t`
  have hP : PfQ r t = 0 := by
    unfold PfQ
    rw [← r11, ← r22, ← r12, ← r13, ← r23, ht]
    ring
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℤ, c0 = Pf r 0 := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℤ, c1 = Pf r 1 - Pf r 0 := ⟨_, rfl⟩
  rw [← hc1, ← hc0] at e2 e3 hbad
  have v0 : PfQ r 0 = (c0 : ℚ) := by
    have h1 := Pf_cast r 0
    rw [← hc0] at h1
    rw [h1]; norm_num
  have v1 : PfQ r 1 = (c0 : ℚ) + c1 := by
    have h1 := Pf_cast r 1
    have h2 : (c0 : ℚ) + c1 = ((Pf r 1 : ℤ) : ℚ) := by rw [hc0, hc1]; push_cast; ring
    rw [h2, h1]; norm_num
  have v2 : PfQ r 2 = (c0 : ℚ) + 2 * c1 := by
    have h1 := Pf_cast r 2
    rw [e2] at h1
    push_cast at h1
    exact h1.symm
  have v3 : PfQ r 3 = (c0 : ℚ) + 3 * c1 := by
    have h1 := Pf_cast r 3
    rw [e3] at h1
    push_cast at h1
    exact h1.symm
  have hlin : (c0 : ℚ) + c1 * t = 0 := by
    have := PfQ_interp r t
    rw [hP, v0, v1, v2, v3] at this
    linear_combination -this
  -- the four endings
  match bad, hbad with
  | 0, hb =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hb
    obtain ⟨hb1, hb0⟩ := hb
    rw [hb1] at hlin
    apply hb0
    have : (c0 : ℚ) = 0 := by simpa using hlin
    exact_mod_cast this
  | 1, hb =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
    obtain ⟨hb1, hb2⟩ := hb
    refine sq_kill (q := m0 * r.O11 * c1) (k := r.O11 * c1 * (r.x11a * c1 - r.x11b * c0)) ?_ hb2
    push_cast
    linear_combination ((r.O11 : ℚ) * c1 ^ 2) * r11 + ((r.O11 : ℚ) * c1 * r.x11b) * hlin
  | 2, hb =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
    obtain ⟨hb1, hb2⟩ := hb
    refine sq_kill (q := m1 * r.O22 * c1) (k := r.O22 * c1 * (r.x22a * c1 - r.x22b * c0)) ?_ hb2
    push_cast
    linear_combination ((r.O22 : ℚ) * c1 ^ 2) * r22 + ((r.O22 : ℚ) * c1 * r.x22b) * hlin
  | (k + 3), hb =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
    obtain ⟨hb1, hb2⟩ := hb
    refine sq_kill (q := m2 * c1) (k := -(c0 * c1)) ?_ hb2
    push_cast
    rw [ht] at hlin
    linear_combination (c1 : ℚ) * hlin

/-! ## Certificates -/

inductive Cert
  | I (ℓ : List ℤ)
  | D (p : Fin 3) (ℓ : List ℤ)
  | Z (ℓ0 ℓ1 ℓ2 : List ℤ)
  | R (ℓ11 ℓ12 ℓ13 ℓ22 ℓ23 : List ℤ) (p0 q0 p1 q1 p2 q2 : ℤ) (bad : ℕ)

/-- one row of a `Z` certificate: `m_p² · D = 0` with `D ≠ 0` -/
def rowZ (n : ℕ) (red : List (List ℤ)) (a : Fin 3 → ℕ) (A B C : ℕ) (p : Fin 3) (ℓ : List ℤ) : Bool :=
  suppOK (LamC n red a B C ℓ) [(p, p)] && (LamC n red a B C ℓ p p != 0) && (LamR n red a A ℓ == 0)

/-- the integer data of an `R` certificate -/
def rdOf (d n : ℕ) (red : List (List ℤ)) (a : Fin 3 → ℕ) (A B C : ℕ) (ℓ11 ℓ12 ℓ13 ℓ22 ℓ23 : List ℤ)
    (p0 q0 p1 q1 p2 q2 : ℤ) : RD where
  O11 := LamC n red a B C ℓ11 0 0
  O12 := LamC n red a B C ℓ12 0 1 + LamC n red a B C ℓ12 1 0
  O13 := LamC n red a B C ℓ13 0 2 + LamC n red a B C ℓ13 2 0
  O22 := LamC n red a B C ℓ22 1 1
  O23 := LamC n red a B C ℓ23 1 2 + LamC n red a B C ℓ23 2 1
  x11a := (d : ℤ) * LamR n red a A ℓ11
  x11b := -(LamC n red a B C ℓ11 2 2)
  x12a := (d : ℤ) * LamR n red a A ℓ12
  x12b := -(LamC n red a B C ℓ12 2 2)
  x13a := (d : ℤ) * LamR n red a A ℓ13
  x13b := -(LamC n red a B C ℓ13 2 2)
  x22a := (d : ℤ) * LamR n red a A ℓ22
  x22b := -(LamC n red a B C ℓ22 2 2)
  x23a := (d : ℤ) * LamR n red a A ℓ23
  x23b := -(LamC n red a B C ℓ23 2 2)
  p0 := p0
  q0 := q0
  p1 := p1
  q1 := q1
  p2 := p2
  q2 := q2

def chkCase (d n : ℕ) (red : List (List ℤ)) (a : Fin 3 → ℕ) (A B C : ℕ) : Cert → Bool
  | .I ℓ => suppOK (LamC n red a B C ℓ) [] && (LamR n red a A ℓ != 0)
  | .D p ℓ => suppOK (LamC n red a B C ℓ) [(p, p)] && (LamC n red a B C ℓ p p != 0) &&
      (decide ((d : ℤ) * LamR n red a A ℓ * LamC n red a B C ℓ p p < 0) ||
        !(isSqZ ((d : ℤ) * LamR n red a A ℓ * LamC n red a B C ℓ p p)))
  | .Z ℓ0 ℓ1 ℓ2 => rowZ n red a A B C 0 ℓ0 && rowZ n red a A B C 1 ℓ1 && rowZ n red a A B C 2 ℓ2
  | .R ℓ11 ℓ12 ℓ13 ℓ22 ℓ23 p0 q0 p1 q1 p2 q2 bad =>
      suppOK (LamC n red a B C ℓ11) [(0, 0), (2, 2)] && suppOK (LamC n red a B C ℓ12) [(0, 1), (1, 0), (2, 2)] &&
      suppOK (LamC n red a B C ℓ13) [(0, 2), (2, 0), (2, 2)] && suppOK (LamC n red a B C ℓ22) [(1, 1), (2, 2)] &&
      suppOK (LamC n red a B C ℓ23) [(1, 2), (2, 1), (2, 2)] &&
      chkRD (rdOf d n red a A B C ℓ11 ℓ12 ℓ13 ℓ22 ℓ23 p0 q0 p1 q1 p2 q2) bad

/-! ## Soundness -/

section sound

variable {n : ℕ} (hn : 0 < n) {red : List (List ℤ)} (hredlen : red.length = n)
  (hred : ∀ e, e < n → zx n ^ e = ev (zx n) (red.getD e []) ∧ (red.getD e []).length ≤ Nat.totient (2 * n))
  {d : ℕ} (hd : 0 < d) {a : Fin 3 → ℕ} (ha0 : ∀ k, 0 < a k) (han : ∀ k, a k < n)
  {A B C : ℕ} (hA0 : 0 < A) (hAn : A < n) (hB : B ≤ n) (hC : C ≤ n)

include hn hredlen hred han hAn hB hC in
/-- the equation of a row -/
theorem row_eq' {m : Fin 3 → ℚ} (hid : IdQ d n a A B C m) (ℓ : List ℤ) :
    ∑ i, ∑ j, m i * m j * ((LamC n red a B C ℓ i j : ℤ) : ℚ) = (d : ℚ) * ((LamR n red a A ℓ : ℤ) : ℚ) :=
  row_eq hn hredlen hred (fun k => (han k).le) hAn.le hB hC hid ℓ

theorem sin_pos' {u : ℕ} (hu0 : 0 < u) (hun : u < n) : 0 < Real.sin ((u : ℝ) * Real.pi / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le u) hun)
  have huR : (0 : ℝ) < u := by exact_mod_cast hu0
  have hlt : (u : ℝ) < n := by exact_mod_cast hun
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ hnR]
    nlinarith [Real.pi_pos]

include hn hredlen hred han hAn hB hC in
theorem rowZ_sound {m : Fin 3 → ℚ} (hid : IdQ d n a A B C m) {p : Fin 3} {ℓ : List ℤ}
    (h : rowZ n red a A B C p ℓ = true) : m p = 0 := by
  unfold rowZ at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e := row_eq' hn hredlen hred han hAn hB hC hid ℓ
  rw [sum_single h1, h3] at e
  have h4 : ((LamC n red a B C ℓ p p : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h2
  have h5 : m p * m p = 0 := by
    have : m p * m p * ((LamC n red a B C ℓ p p : ℤ) : ℚ) = 0 := by rw [e]; simp
    exact (mul_eq_zero.mp this).resolve_right h4
  exact mul_self_eq_zero.mp h5

include hn hredlen hred hd ha0 han hA0 hAn hB hC in
/-- **Soundness of one certificate.** -/
theorem chkCase_sound {cert : Cert} (h : chkCase d n red a A B C cert = true) (hB0 : 0 < B) (hC0 : 0 < C)
    (hBn : B < n) (hCn : C < n) (m : Fin 3 → ℚ) (hid : IdQ d n a A B C m) : False := by
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  cases cert with
  | I ℓ =>
    unfold chkCase at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨h1, h2⟩ := h
    have e := row_eq' hn hredlen hred han hAn hB hC hid ℓ
    have hz : ∀ i j, LamC n red a B C ℓ i j = 0 := fun i j => suppOK_sound h1 i j (by simp)
    simp only [hz, Int.cast_zero, mul_zero, Finset.sum_const_zero] at e
    apply h2
    have : ((LamR n red a A ℓ : ℤ) : ℚ) = 0 := by
      rcases mul_eq_zero.mp e.symm with h3 | h3
      · exact absurd h3 hdQ.ne'
      · exact h3
    exact_mod_cast this
  | D p ℓ =>
    unfold chkCase at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have e := row_eq' hn hredlen hred han hAn hB hC hid ℓ
    rw [sum_single h1] at e
    refine sq_kill (q := m p * (LamC n red a B C ℓ p p : ℚ))
      (k := (d : ℤ) * LamR n red a A ℓ * LamC n red a B C ℓ p p) ?_ h3
    push_cast
    linear_combination ((LamC n red a B C ℓ p p : ℚ)) * e
  | Z ℓ0 ℓ1 ℓ2 =>
    unfold chkCase at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h0, h1⟩, h2⟩ := h
    have m0 := rowZ_sound hn hredlen hred han hAn hB hC hid h0
    have m1 := rowZ_sound hn hredlen hred han hAn hB hC hid h1
    have m2 := rowZ_sound hn hredlen hred han hAn hB hC hid h2
    unfold IdQ at hid
    rw [Fin.sum_univ_three, Fin.prod_univ_three, m0, m1, m2] at hid
    have sA := sin_pos' hA0 hAn
    have s0 := sin_pos' (ha0 0) (han 0)
    have s1 := sin_pos' (ha0 1) (han 1)
    have s2 := sin_pos' (ha0 2) (han 2)
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hpos : 0 < (d : ℝ) * Real.sin (A * Real.pi / n) *
        (Real.sin (a 0 * Real.pi / n) * Real.sin (a 1 * Real.pi / n) * Real.sin (a 2 * Real.pi / n)) := by
      positivity
    rw [← hid] at hpos
    simp at hpos
  | R ℓ11 ℓ12 ℓ13 ℓ22 ℓ23 p0 q0 p1 q1 p2 q2 bad =>
    unfold chkCase at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨s11, s12⟩, s13⟩, s22⟩, s23⟩, hR⟩ := h
    have e11 := row_eq' hn hredlen hred han hAn hB hC hid ℓ11
    have e12 := row_eq' hn hredlen hred han hAn hB hC hid ℓ12
    have e13 := row_eq' hn hredlen hred han hAn hB hC hid ℓ13
    have e22 := row_eq' hn hredlen hred han hAn hB hC hid ℓ22
    have e23 := row_eq' hn hredlen hred han hAn hB hC hid ℓ23
    rw [sum9] at e11 e12 e13 e22 e23
    rw [suppOK_sound s11 0 1 (by decide), suppOK_sound s11 0 2 (by decide), suppOK_sound s11 1 0 (by decide),
      suppOK_sound s11 1 1 (by decide), suppOK_sound s11 1 2 (by decide), suppOK_sound s11 2 0 (by decide),
      suppOK_sound s11 2 1 (by decide)] at e11
    rw [suppOK_sound s12 0 0 (by decide), suppOK_sound s12 0 2 (by decide), suppOK_sound s12 1 1 (by decide),
      suppOK_sound s12 1 2 (by decide), suppOK_sound s12 2 0 (by decide), suppOK_sound s12 2 1 (by decide)] at e12
    rw [suppOK_sound s13 0 0 (by decide), suppOK_sound s13 0 1 (by decide), suppOK_sound s13 1 0 (by decide),
      suppOK_sound s13 1 1 (by decide), suppOK_sound s13 1 2 (by decide), suppOK_sound s13 2 1 (by decide)] at e13
    rw [suppOK_sound s22 0 0 (by decide), suppOK_sound s22 0 1 (by decide), suppOK_sound s22 0 2 (by decide),
      suppOK_sound s22 1 0 (by decide), suppOK_sound s22 1 2 (by decide), suppOK_sound s22 2 0 (by decide),
      suppOK_sound s22 2 1 (by decide)] at e22
    rw [suppOK_sound s23 0 0 (by decide), suppOK_sound s23 0 1 (by decide), suppOK_sound s23 0 2 (by decide),
      suppOK_sound s23 1 0 (by decide), suppOK_sound s23 1 1 (by decide), suppOK_sound s23 2 0 (by decide)] at e23
    refine chkRD_sound _ bad hR (m 0) (m 1) (m 2) ?_ ?_ ?_ ?_ ?_
    · simp only [rdOf]; push_cast; push_cast at e11; linear_combination e11
    · simp only [rdOf]; push_cast; push_cast at e12; linear_combination e12
    · simp only [rdOf]; push_cast; push_cast at e13; linear_combination e13
    · simp only [rdOf]; push_cast; push_cast at e22; linear_combination e22
    · simp only [rdOf]; push_cast; push_cast at e23; linear_combination e23

end sound

/-! ## A tile -/

/-- the certificate of the target `(A, B, n − A − B)` -/
def lookup (certs : List (List Cert)) (A B : ℕ) : Cert := (certs.getD (A - 1) []).getD (B - 1) (Cert.I [])

def chkTile (d n : ℕ) (red : List (List ℤ)) (a : Fin 3 → ℕ) (certs : List (List Cert)) : Bool :=
  (List.range n).all fun A => (List.range n).all fun B =>
    !(decide (1 ≤ A ∧ 1 ≤ B ∧ A + B < n)) || chkCase d n red a A B (n - A - B) (lookup certs A B)

/-- **Soundness of a tile table.** -/
theorem chkTile_sound {n : ℕ} (hn : 0 < n) {red : List (List ℤ)} (hredlen : red.length = n)
    (hred : ∀ e, e < n → zx n ^ e = ev (zx n) (red.getD e []) ∧ (red.getD e []).length ≤ Nat.totient (2 * n))
    {d : ℕ} (hd : 0 < d) {a : Fin 3 → ℕ} (ha0 : ∀ k, 0 < a k) (han : ∀ k, a k < n) {certs : List (List Cert)}
    (h : chkTile d n red a certs = true) {A B C : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) (hs : A + B + C = n)
    (m : Fin 3 → ℚ) (hid : IdQ d n a A B C m) : False := by
  unfold chkTile at h
  rw [List.all_eq_true] at h
  have hA' := h A (List.mem_range.mpr (by omega))
  rw [List.all_eq_true] at hA'
  have hB' := hA' B (List.mem_range.mpr (by omega))
  have hcond : decide (1 ≤ A ∧ 1 ≤ B ∧ A + B < n) = true := by simp; omega
  rw [hcond] at hB'
  simp only [Bool.not_true, Bool.false_or] at hB'
  have hC' : n - A - B = C := by omega
  rw [hC'] at hB'
  exact chkCase_sound hn hredlen hred hd ha0 han (by omega) (by omega) (by omega) (by omega) hB' (by omega)
    (by omega) (by omega) (by omega) m hid

/-! ## Row-wise tables (one kernel check per row keeps the memory of a single declaration small) -/

/-- one row: the targets `(A, B, n − A − B)`, `B = 1, 2, …`, with their certificates in this order -/
def chkRow (d n : ℕ) (red : List (List ℤ)) (a : Fin 3 → ℕ) (A : ℕ) (row : List Cert) : Bool :=
  (List.range n).all fun B =>
    !(decide (1 ≤ B ∧ A + B < n)) || chkCase d n red a A B (n - A - B) (row.getD (B - 1) (Cert.I []))

/-- **Soundness of a table given row by row.** -/
theorem chkRows_sound {n : ℕ} (hn : 0 < n) {red : List (List ℤ)} (hredlen : red.length = n)
    (hred : ∀ e, e < n → zx n ^ e = ev (zx n) (red.getD e []) ∧ (red.getD e []).length ≤ Nat.totient (2 * n))
    {d : ℕ} (hd : 0 < d) {a : Fin 3 → ℕ} (ha0 : ∀ k, 0 < a k) (han : ∀ k, a k < n)
    (h : ∀ A, 1 ≤ A → A + 2 ≤ n → ∃ row, chkRow d n red a A row = true)
    {A B C : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) (hs : A + B + C = n)
    (m : Fin 3 → ℚ) (hid : IdQ d n a A B C m) : False := by
  obtain ⟨row, hrow⟩ := h A hA (by omega)
  unfold chkRow at hrow
  rw [List.all_eq_true] at hrow
  have hB' := hrow B (List.mem_range.mpr (by omega))
  have hcond : decide (1 ≤ B ∧ A + B < n) = true := by simp; omega
  rw [hcond] at hB'
  simp only [Bool.not_true, Bool.false_or] at hB'
  have hC' : n - A - B = C := by omega
  rw [hC'] at hB'
  exact chkCase_sound hn hredlen hred hd ha0 han (by omega) (by omega) (by omega) (by omega) hB' (by omega)
    (by omega) (by omega) (by omega) m hid

end Erdos634.Draft.GAU

#print axioms Erdos634.Draft.GAU.chkRD_sound
#print axioms Erdos634.Draft.GAU.chkCase_sound
#print axioms Erdos634.Draft.GAU.chkTile_sound
#print axioms Erdos634.Draft.GAU.chkRows_sound
