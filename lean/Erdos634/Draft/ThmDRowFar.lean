import Mathlib.Tactic
import Erdos634.Draft.ThmDRowOrient
import Erdos634.Draft.ThmDRowFarGeom
import Erdos634.Draft.ThmDRowFarLat
import Erdos634.Draft.ThmDRowIntervals
import Erdos634.Draft.ThmDRunFrame2

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' (H2): the far-side tiles across a diagonal `PQ` have the lattice `a`-edges as edges  

`hfar_of_near` discharges hypothesis (H2) `hfar` of `row_orient` (RA at tile level, edge-level placement on an interior segment):

 the diagonal `PQ` (`P = lp 0 w`, `Q = lp w 0`, `w < v`) is the union of the `a`-edges of the near towers (so a wall); its open
 segment lies in the target and `P, Q` are frontier points; the far-side edge chain `lineChain GST (-lv w)` is then an exactly-once
 cover of `PQ` by tile edges (`ThmDRowFar.far_chain`), of total length `w a`, hence (rigidity window `v`, `chord_a`) of `w` edges of
 length `a`; unit intervals tiling `[0,w]` start at every integer (`interval_tiling`), so each lattice `a`-edge is an edge of a far tile.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set
  Erdos634.Draft.ThmDRowFar Erdos634.Draft.ThmDRowIntervals

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem fin3_cases : ∀ m j : Fin 3, m ≠ j → j = m + 1 ∨ m = j + 1 := by decide
theorem fin3_ne : ∀ m : Fin 3, m ≠ m + 1 := by decide

theorem max_eq_min_add_one {a b : ℝ} (h : |a - b| = 1) : max a b = min a b + 1 := by
  rcases le_total a b with h1 | h1
  · rw [abs_of_nonpos (by linarith)] at h
    rw [max_eq_right h1, min_eq_left h1]; linarith
  · rw [abs_of_nonneg (by linarith)] at h
    rw [max_eq_left h1, min_eq_right h1]; linarith

theorem near_wall (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ) (hw0 : 0 < w)
    (hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1))) :
    ∀ y ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0),
      ∀ j, y ∉ interior (D.tile j).carrier := by
  set P := lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) with hPdef
  set Q := lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 with hQdef
  intro y hy j
  have hys : y ∈ segment ℝ P Q := openSegment_subset_segment ℝ P Q hy
  have hQe : Q = lpT (u : ℝ) (v : ℝ) ε x (0 + (w : ℝ) * 1) ((w : ℝ) + (w : ℝ) * (-1)) :=
    lpT_congr (by ring) (by ring)
  rw [hQe] at hys
  obtain ⟨i, hi, hyi⟩ := seg_split_lpT (u := (u : ℝ)) (v := (v : ℝ)) (ε := ε) (x := x) (ξ := 0)
    (η := (w : ℝ)) (dξ := 1) (dη := -1) (q := w) hw0 hys
  obtain ⟨t, k, m, j', hkm, hkj, hmj, hk, hm, hj⟩ := hnear i hi
  have eB : lpT (u : ℝ) (v : ℝ) ε x (0 + ((i : ℝ) + 1) * 1) ((w : ℝ) + ((i : ℝ) + 1) * (-1))
      = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) := lpT_congr (by ring) (by unfold ηw; ring)
  have eC : lpT (u : ℝ) (v : ℝ) ε x (0 + (i : ℝ) * 1) ((w : ℝ) + (i : ℝ) * (-1))
      = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1) := lpT_congr (by ring) (by unfold ηw; ring)
  rw [eB, eC] at hyi
  rcases fin3_cases m j' hmj with h | h
  · -- j' = m + 1 : edge m = segment B C
    have hyE : y ∈ (D.tile t).edge m := by
      show y ∈ segment ℝ ((D.tile t).pts m) ((D.tile t).pts (m + 1))
      rw [← h, hj, hm, segment_symm]
      exact hyi
    exact D.toDissection.edge_point_not_interior hyE j
  · have hyE : y ∈ (D.tile t).edge j' := by
      rw [Tri.edge, ← h, hj, hm]
      exact hyi
    exact D.toDissection.edge_point_not_interior hyE j

theorem hfar_of_near_data (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ) (hw0 : 0 < w) (hwv : w < v)
    (hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)))
    (A : Finset (Fin N × Fin 3))
    (hAch : ∀ e ∈ A, e ∈ D.toDissection.lineChain (GST (u : ℝ) (v : ℝ) ε) (-lvT (u : ℝ) (v : ℝ) ε x (w : ℝ)))
    (hsub : ∀ e ∈ A, (D.tile e.1).edge e.2 ⊆
      segment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0))
    (hsum : ∑ e ∈ A, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      dist (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0))
    (hdisj : ∀ e₁ ∈ A, ∀ e₂ ∈ A, e₁ ≠ e₂ → ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton) :
    ∀ i : ℕ, i < w → ∃ (t : Fin N) (k m : Fin 3), k ≠ m ∧
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∧
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1) ∧
      ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hh := hhT_pos hu huv hv2
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw0
  set P := lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) with hPdef
  set Q := lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 with hQdef
  set g := GST (u : ℝ) (v : ℝ) ε with hgdef
  set c : ℝ := -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) with hcdef
  have hg : g ≠ 0 := GST_ne hu huv hv2 hε
  have hPQ : P ≠ Q := by
    rw [hPdef, hQdef]; exact lpT_ne_eta hu huv hv2 hwR.ne'
  have hdiag : ∀ η : ℝ, g (lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - η) η) = c := by
    intro η
    rw [hgdef, GST_lp hε, show (w : ℝ) - η + η = w by ring]
  have hP' : P = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - w) w := lpT_congr (by ring) rfl
  have hQ' : Q = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - 0) 0 := lpT_congr (by ring) rfl
  -- parametrisation of the diagonal segment
  have hparam : ∀ y ∈ segment ℝ P Q, ∃ η : ℝ, 0 ≤ η ∧ η ≤ w ∧
      y = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - η) η := by
    intro y hy
    rw [hP', hQ'] at hy
    obtain ⟨η, h1, h2, h3⟩ := diag_seg_param hy
    refine ⟨η, ?_, ?_, h3⟩
    · simpa using h1
    · simpa using h2
    -- total length
  have hdistPQ : dist P Q = (w : ℝ) * (u : ℝ) ^ 2 := by
    refine dist_lpT hu huv hv2 hε (mul_nonneg hwR.le (sq_nonneg _)) ?_
    unfold QfT; ring
  -- all edges have length a
  have hlen : ∀ e ∈ A, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = (u : ℝ) ^ 2 :=
    all_len_a A (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) S.hco S.hu S.huv w hwv
      (fun e _ => edge_length_casesT D S.hM e.1 e.2) (by rw [hsum, hdistPQ])
  -- coordinates of the endpoints
  set ηp : Fin N × Fin 3 → ℝ := fun e => (D.tile e.1).pts e.2 1 / hhT (u : ℝ) (v : ℝ) with hηp
  set ηq : Fin N × Fin 3 → ℝ := fun e => (D.tile e.1).pts (e.2 + 1) 1 / hhT (u : ℝ) (v : ℝ) with hηq
  have hpe : ∀ e ∈ A, (D.tile e.1).pts e.2 = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - ηp e) (ηp e) := by
    intro e he
    obtain ⟨h1, -, -⟩ := Dissection.mem_lineChain.mp (hAch e he)
    exact onL_eq_lp hu huv hv2 hε (s := w) h1
  have hqe : ∀ e ∈ A, (D.tile e.1).pts (e.2 + 1) = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - ηq e) (ηq e) := by
    intro e he
    obtain ⟨-, h2, -⟩ := Dissection.mem_lineChain.mp (hAch e he)
    exact onL_eq_lp hu huv hv2 hε (s := w) h2
  have hunit : ∀ e ∈ A, |ηp e - ηq e| = 1 := by
    intro e he
    have h1 := dist_diag (x := x) hu huv hv2 hε (w : ℝ) (ηp e) (ηq e)
    rw [← hpe e he, ← hqe e he, hlen e he] at h1
    have h2 : (0 : ℝ) < (u : ℝ) ^ 2 := by positivity
    nlinarith
  have hrange : ∀ e ∈ A, 0 ≤ ηp e ∧ ηp e ≤ w ∧ 0 ≤ ηq e ∧ ηq e ≤ w := by
    intro e he
    have hpm : (D.tile e.1).pts e.2 ∈ segment ℝ P Q := hsub e he (left_mem_segment ℝ _ _)
    have hqm : (D.tile e.1).pts (e.2 + 1) ∈ segment ℝ P Q := hsub e he (right_mem_segment ℝ _ _)
    obtain ⟨η, h0, h1, hη⟩ := hparam _ hpm
    obtain ⟨η', h0', h1', hη'⟩ := hparam _ hqm
    have e1 : ηp e = η := by
      show (D.tile e.1).pts e.2 1 / hhT (u : ℝ) (v : ℝ) = η
      rw [hη, lp_snd_eq]; field_simp
    have e2 : ηq e = η' := by
      show (D.tile e.1).pts (e.2 + 1) 1 / hhT (u : ℝ) (v : ℝ) = η'
      rw [hη', lp_snd_eq]; field_simp
    exact ⟨by rw [e1]; exact h0, by rw [e1]; exact h1, by rw [e2]; exact h0', by rw [e2]; exact h1'⟩
  set lo : Fin N × Fin 3 → ℝ := fun e => min (ηp e) (ηq e) with hlo
  have hmax : ∀ e ∈ A, max (ηp e) (ηq e) = lo e + 1 := fun e he => max_eq_min_add_one (hunit e he)
  have hne : ∀ e ∈ A, ηp e ≠ ηq e := by
    intro e he h
    have := hunit e he
    rw [h, sub_self] at this
    simp at this
  have hedge_pt : ∀ e ∈ A, ∀ η : ℝ, lo e ≤ η → η ≤ lo e + 1 →
      lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - η) η ∈ (D.tile e.1).edge e.2 := by
    intro e he η h1 h2
    have := lp_diag_mem_seg (u := (u : ℝ)) (v := (v : ℝ)) (ε := ε) (x := x) (s := (w : ℝ)) (hne e he)
      (η := η) h1 (by rw [hmax e he]; exact h2)
    rw [← hpe e he, ← hqe e he] at this
    exact this
  have hedge_param : ∀ e ∈ A, ∀ y ∈ (D.tile e.1).edge e.2, ∃ η : ℝ, lo e ≤ η ∧ η ≤ lo e + 1 ∧
      y = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - η) η := by
    intro e he y hy
    have hy' : y ∈ segment ℝ (lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - ηp e) (ηp e))
        (lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - ηq e) (ηq e)) := by
      rw [← hpe e he, ← hqe e he]; exact hy
    obtain ⟨η, h1, h2, h3⟩ := diag_seg_param hy'
    exact ⟨η, h1, by rw [← hmax e he]; exact h2, h3⟩
  have hsep : ∀ e₁ e₂ : A, e₁ ≠ e₂ → 1 ≤ |lo e₁.1 - lo e₂.1| := by
    intro e₁ e₂ hne12
    by_contra hlt
    push_neg at hlt
    have hne' : e₁.1 ≠ e₂.1 := fun h => hne12 (Subtype.ext h)
    have h1 := e₁.2
    have h2 := e₂.2
    obtain ⟨hl1, hl2⟩ := abs_lt.mp hlt
    set m := max (lo e₁.1) (lo e₂.1) with hm
    set M := min (lo e₁.1 + 1) (lo e₂.1 + 1) with hM
    have hmM : m < M := by
      apply lt_min <;> apply max_lt <;> linarith
    have mem1 : ∀ η : ℝ, lo e₁.1 ≤ η → η ≤ lo e₁.1 + 1 → lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - η) η ∈
        (D.tile e₁.1.1).edge e₁.1.2 := fun η a b => hedge_pt e₁.1 h1 η a b
    have mem2 : ∀ η : ℝ, lo e₂.1 ≤ η → η ≤ lo e₂.1 + 1 → lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - η) η ∈
        (D.tile e₂.1.1).edge e₂.1.2 := fun η a b => hedge_pt e₂.1 h2 η a b
    have hsub1 := hdisj e₁.1 h1 e₂.1 h2 hne'
    have z1 : lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - m) m ∈
        (D.tile e₁.1.1).edge e₁.1.2 ∩ (D.tile e₂.1.1).edge e₂.1.2 :=
      ⟨mem1 m (le_max_left _ _) (max_le (by linarith) (by linarith)),
       mem2 m (le_max_right _ _) (max_le (by linarith) (by linarith))⟩
    have z2 : lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - M) M ∈
        (D.tile e₁.1.1).edge e₁.1.2 ∩ (D.tile e₂.1.1).edge e₂.1.2 :=
      ⟨mem1 M (le_min (by linarith) (by linarith)) (min_le_left _ _),
       mem2 M (le_min (by linarith) (by linarith)) (min_le_right _ _)⟩
    have := lpT_eta_eq hu huv hv2 (hsub1 z1 z2)
    linarith
  have hrng : ∀ e : A, 0 ≤ lo e.1 ∧ lo e.1 + 1 ≤ w := by
    intro e
    obtain ⟨a1, a2, a3, a4⟩ := hrange e.1 e.2
    constructor
    · exact le_min a1 a3
    · rw [← hmax e.1 e.2]; exact max_le a2 a4
  have hcardA : A.card = w := by
    have h1 : ∑ e ∈ A, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = (A.card : ℝ) * (u : ℝ) ^ 2 := by
      rw [Finset.sum_congr rfl (fun e he => hlen e he), Finset.sum_const, nsmul_eq_mul]
    have h2 : (A.card : ℝ) * (u : ℝ) ^ 2 = (w : ℝ) * (u : ℝ) ^ 2 := by rw [← h1, hsum, hdistPQ]
    have hu2 : (0 : ℝ) < (u : ℝ) ^ 2 := by positivity
    exact_mod_cast mul_right_cancel₀ hu2.ne' h2
  have key := interval_tiling_card (ι := A) (fun e : A => lo e.1) w (by simpa using hcardA) hsep hrng
  intro i hi
  have hmR : ((w - 1 - i : ℕ) : ℝ) = (w : ℝ) - 1 - i := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  obtain ⟨⟨e, he⟩, hloe⟩ := key (w - 1 - i) (by omega)
  simp only at hloe
  have hfs : ∀ j, g ((D.tile e.1).pts j) ≤ c := fun j => (Dissection.mem_lineChain.mp (hAch e he)).2.2 j
  rcases le_total (ηp e) (ηq e) with hle | hle
  · have hp : ηp e = lo e := by simp [hlo, min_eq_left hle]
    have hq : ηq e = lo e + 1 := by rw [← hmax e he, max_eq_right hle]
    refine ⟨e.1, e.2, e.2 + 1, fin3_ne e.2, ?_, ?_, hfs⟩
    · rw [hpe e he]
      exact lpT_congr (by rw [hp, hloe, hmR]; ring) (by rw [hp, hloe, hmR]; unfold ηw; ring)
    · rw [hqe e he]
      exact lpT_congr (by rw [hq, hloe, hmR]; ring) (by rw [hq, hloe, hmR]; unfold ηw; ring)
  · have hq : ηq e = lo e := by simp [hlo, min_eq_right hle]
    have hp : ηp e = lo e + 1 := by rw [← hmax e he, max_eq_left hle]
    refine ⟨e.1, e.2 + 1, e.2, (fin3_ne e.2).symm, ?_, ?_, hfs⟩
    · rw [hqe e he]
      exact lpT_congr (by rw [hq, hloe, hmR]; ring) (by rw [hq, hloe, hmR]; unfold ηw; ring)
    · rw [hpe e he]
      exact lpT_congr (by rw [hp, hloe, hmR]; ring) (by rw [hp, hloe, hmR]; unfold ηw; ring)

theorem hfar_of_near_blocked (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ) (hw0 : 0 < w) (hwv : w < v)
    (hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)))
    (hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
      interior D.target.carrier)
    (hblock : ∀ e ∈ D.toDissection.lineChain (GST (u : ℝ) (v : ℝ) ε) (-lvT (u : ℝ) (v : ℝ) ε x (w : ℝ)),
      (D.tile e.1).edge e.2 ⊆ segment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0)) :
    ∀ i : ℕ, i < w → ∃ (t : Fin N) (k m : Fin 3), k ≠ m ∧
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∧
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1) ∧
      ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw0
  set P := lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) with hPdef
  set Q := lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 with hQdef
  set g := GST (u : ℝ) (v : ℝ) ε with hgdef
  set c : ℝ := -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) with hcdef
  have hg : g ≠ 0 := GST_ne hu huv hv2 hε
  have hPQ : P ≠ Q := by
    rw [hPdef, hQdef]; exact lpT_ne_eta hu huv hv2 hwR.ne'
  have hdiag : ∀ η : ℝ, g (lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - η) η) = c := by
    intro η
    rw [hgdef, GST_lp hε, show (w : ℝ) - η + η = w by ring]
  have hP' : P = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - w) w := lpT_congr (by ring) rfl
  have hQ' : Q = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - 0) 0 := lpT_congr (by ring) rfl
  have hS : segment ℝ P Q ⊆ {y | g y = c} := by
    intro y hy
    rw [hP', hQ'] at hy
    obtain ⟨η, -, -, rfl⟩ := diag_seg_param hy
    exact hdiag η
  have hwall : ∀ y ∈ openSegment ℝ P Q, ∀ j, y ∉ interior (D.tile j).carrier :=
    near_wall C w hw0 hnear
  obtain ⟨hsum, -, hdisj⟩ := far_chain_blocked D.toDissection g c hg hPQ hS hint hwall hblock
  exact hfar_of_near_data C w hw0 hwv hnear _ (fun e he => he) hblock hsum hdisj

#print axioms hfar_of_near_blocked

theorem hfar_of_near (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ) (hw0 : 0 < w) (hwv : w < v)
    (hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)))
    (hP : lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) ∈ frontier D.target.carrier)
    (hQ : lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ frontier D.target.carrier)
    (hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
      interior D.target.carrier) :
    ∀ i : ℕ, i < w → ∃ (t : Fin N) (k m : Fin 3), k ≠ m ∧
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∧
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1) ∧
      ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) := by
  have hS := C.S
  have hε := C.e2
  have hu := hS.u0
  have huv := hS.uv'
  have hv2 := hS.v2
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw0
  have hPeq : lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) = lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) :=
    lpT_congr (by simp) (by unfold ηw; simp)
  rw [hPeq] at hP
  have hPQ : lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ≠ lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 :=
    lpT_ne_eta hu huv hv2 hwR.ne'
  have hseg : segment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
      {y | GST (u : ℝ) (v : ℝ) ε y = -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ)} := by
    intro y hy
    have hP' : lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - w) w := lpT_congr (by ring) rfl
    have hQ' : lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - 0) 0 := lpT_congr (by ring) rfl
    rw [hP', hQ'] at hy
    obtain ⟨η, -, -, rfl⟩ := diag_seg_param hy
    show GST (u : ℝ) (v : ℝ) ε (lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - η) η) = _
    rw [GST_lp hε, show (w : ℝ) - η + η = w by ring]
  exact hfar_of_near_blocked C w hw0 hwv hnear hint
    (chain_sub_of_frontier D.toDissection (GST (u : ℝ) (v : ℝ) ε) (-lvT (u : ℝ) (v : ℝ) ε x (w : ℝ))
      (GST_ne hu huv hv2 hε) hPQ hseg hint hP hQ)

#print axioms hfar_of_near
end Erdos634.Draft.ThmDRun
