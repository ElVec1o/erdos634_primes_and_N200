-- Draft/ThmW.lean — **Theorem W** (parametric): for coprime 2 <= e <= f-2 and M with M e >= f, (M-1)(f-e) >= f,
-- the triangle W_M(e,f) is tiled by M^2 (2f^2-e^2) copies of the tile (ef, f^2-e^2, f^2); plus TileCount of the W and T counts.
-- Natural-number lemmas F1-F5 of PROOF.md ((project working notes)) + canonical parameters.  UNAUDITED.  No sorry, no native_decide.
-- Credit: D. Paliy (W/beta framework, caps), M. Beeson & I. Rosu (W/T targets, S2L skew frame); the six-piece template was found by our engine `bto`.
import Erdos634.Draft.ThmWParams

open scoped Classical
open Erdos634.Draft.CollarG (WTilable)
open Erdos634.Draft.TileCountFamilies (TileCount)

namespace Erdos634.Draft.ThmW

/-- (F5) `g n >= e + 1`. -/
theorem F5 (e g M n ρ : ℕ) (hco : Nat.Coprime e (e + g)) (hg : 2 ≤ g) (he : 2 ≤ e) (hn : 1 ≤ n)
    (h2 : e + g ≤ (M - 1) * g) (hE : (e + g) * n + ρ = e * M) (hρ : ρ < e + g) : e + 1 ≤ g * n := by
  by_cases hge : e + 1 ≤ g
  · nlinarith
  · push Not at hge
    have hge' : g ≤ e := by omega
    -- f = g h + j
    obtain ⟨h, j, hj, hfj⟩ : ∃ h j : ℕ, j < g ∧ e + g = g * h + j :=
      ⟨(e + g) / g, (e + g) % g, Nat.mod_lt _ (by omega), (Nat.div_add_mod (e + g) g).symm⟩
    have hj0 : 0 < j := by
      by_contra hj0
      have hj0' : j = 0 := by omega
      subst hj0'
      have hgf : g ∣ e + g := ⟨h, by simpa using hfj⟩
      have hge2 : g ∣ e := (Nat.dvd_add_left (dvd_refl g)).mp hgf
      have : g ∣ Nat.gcd e (e + g) := Nat.dvd_gcd hge2 hgf
      rw [hco] at this
      have := Nat.le_of_dvd one_pos this
      omega
    have hh2 : 2 ≤ h := by
      by_contra hh
      push Not at hh
      have : h ≤ 1 := by omega
      nlinarith
    have hMh : h + 2 ≤ M := by
      by_contra hM
      push Not at hM
      have hM1 : M - 1 ≤ h := by omega
      have : (M - 1) * g ≤ h * g := Nat.mul_le_mul_right g hM1
      nlinarith
    have hnh : h ≤ n := by
      by_contra hnh
      push Not at hnh
      have h1 : n + 1 ≤ h := hnh
      have hlt : (e + g) * n + ρ < (e + g) * (n + 1) := by nlinarith
      have h3 : (e + g) * (n + 1) ≤ (e + g) * h := Nat.mul_le_mul_left _ h1
      have h4 : e * (h + 2) ≤ e * M := Nat.mul_le_mul_left _ hMh
      -- e = g (h-1) + j
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 2 := ⟨h - 2, by omega⟩
      have he' : e = g * (h' + 1) + j := by nlinarith
      nlinarith
    nlinarith

/-- (F4) `e g >= f + 1` for coprime `e`, `f = e + g` with `e, g >= 2`. -/
theorem F4 (e g : ℕ) (hco : Nat.Coprime e (e + g)) (hg : 2 ≤ g) (he : 2 ≤ e) : e + g + 1 ≤ e * g := by
  by_cases h : e = 2 ∧ g = 2
  · obtain ⟨rfl, rfl⟩ := h
    exact absurd hco (by decide)
  · have : 3 ≤ e ∨ 3 ≤ g := by omega
    rcases this with h3 | h3 <;> nlinarith

/-- **Theorem W (natural form).** -/
theorem thmW_wTilable (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f) (h1 : f ≤ M * e)
    (h2 : f ≤ (M - 1) * (f - e)) : WTilable e f M := by
  obtain ⟨g, rfl⟩ : ∃ g, f = e + g := ⟨f - e, by omega⟩
  have hg : 2 ≤ g := by omega
  have hfe : e + g - e = g := by omega
  rw [hfe] at h2
  have hF4 := F4 e g hco hg he
  obtain ⟨n, ρ, hE, hρ⟩ : ∃ n ρ : ℕ, (e + g) * n + ρ = e * M ∧ ρ < e + g :=
    ⟨e * M / (e + g), e * M % (e + g), Nat.div_add_mod (e * M) (e + g), Nat.mod_lt _ (by omega)⟩
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    nlinarith
  have hF5 := F5 e g M n ρ hco hg he hn1 h2 hE hρ
  have hnM : n ≤ M := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s, M = n + s := ⟨M - n, by omega⟩
  have hM2 : 2 ≤ M := by
    by_contra hM
    push Not at hM
    have hM1 : M - 1 ≤ 0 := by omega
    have : (M - 1) * g ≤ 0 := by simp [Nat.le_zero.mp hM1]
    omega
  have hgM : (e + g) * s = g * M + ρ := by
    have : (e + g) * M = (e + g) * n + (e + g) * s := by rw [hs]; ring
    nlinarith
  have hs2 : 2 ≤ s := by
    by_contra hs2
    push Not at hs2
    have hgM' : e + g + g ≤ g * M := by
      have : (M - 1) * g + g = M * g := by
        obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
        simp; ring
      nlinarith
    have : s ≤ 1 := by omega
    nlinarith
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hco' : Nat.Coprime (e + g) e := hco.symm
  by_cases hρ0 : ρ = 0
  · -- rho = 0
    have hE0 : (e + g) * n = e * M := by rw [hρ0] at hE; omega
    have hdvd : (e + g) ∣ e * M := ⟨n, hE0.symm⟩
    have hfM : (e + g) ∣ M := hco'.dvd_of_dvd_mul_left hdvd
    obtain ⟨m, hm⟩ := hfM
    have hm1 : 1 ≤ m := by
      by_contra h0
      have : m = 0 := by omega
      subst this; omega
    have hnm : n = e * m := by
      have : (e + g) * n = (e + g) * (e * m) := by rw [hE0, hm]; ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    have hem : 1 ≤ e * m := by nlinarith
    have hreal := canonB (e : ℝ) ((e + g : ℕ) : ℝ) (m : ℝ) (by exact_mod_cast he)
      (by push_cast; linarith)
      (by have : ((e + g + 1 : ℕ) : ℝ) ≤ ((e * g : ℕ) : ℝ) := by exact_mod_cast hF4
          push_cast at this ⊢; linarith) (by exact_mod_cast hm1)
    rw [hm] at *
    have := wTilable_of_WP e (e + g) ((e + g) * m) (e * m - 1) (e * m + 1) (e * m) (by omega) (by omega) (by
      have hc : ((e * m - 1 : ℕ) : ℝ) = (e : ℝ) * m - 1 := by rw [Nat.cast_sub hem]; push_cast; ring
      rw [hc]; push_cast at hreal ⊢; exact hreal)
    simpa using this
  · -- rho >= 1
    have hρ1 : 1 ≤ ρ := by omega
    have hreal := canonA (e : ℝ) ((e + g : ℕ) : ℝ) (M : ℝ) (n : ℝ) (ρ : ℝ) (s : ℝ) (by exact_mod_cast he)
      (by push_cast; linarith)
      (by have : ((e + g + 1 : ℕ) : ℝ) ≤ ((e * g : ℕ) : ℝ) := by exact_mod_cast hF4
          push_cast at this ⊢; linarith) (by exact_mod_cast hn1) (by exact_mod_cast hρ1)
      (by have : (ρ : ℝ) + 1 ≤ ((e + g : ℕ) : ℝ) := by exact_mod_cast hρ
          push_cast at this ⊢; linarith)
      (by have : ((e * M : ℕ) : ℝ) = (((e + g) * n + ρ : ℕ) : ℝ) := by rw [hE]
          push_cast at this ⊢; linarith)
      (by exact_mod_cast hs) (by exact_mod_cast hs2)
      (by have : ((e + 1 : ℕ) : ℝ) ≤ ((g * n : ℕ) : ℝ) := by exact_mod_cast hF5
          push_cast at this ⊢; linarith)
    exact wTilable_of_WP e (e + g) M n (n + 1) n (by omega) (by omega) (by push_cast at hreal ⊢; exact hreal)

end Erdos634.Draft.ThmW
