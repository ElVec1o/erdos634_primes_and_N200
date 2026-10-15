/-
Draft/ResidueSeed.lean -- the residue seeds: the target `W` of the member `(u, v)` at the scales `v + t`, `1 ≤ t < u`,
and with them a tiling of `W` and of the base-β target at EVERY scale `M ≥ v`.

    theorem wTilable_residue : coprime `u < v`, `1 ≤ t < u`  →  WTilable u v (v + t)
    theorem wTilable_ge      : coprime `1 ≤ u < v`, `M ≥ v`  →  WTilable u v M
    theorem betaTilable_ge   : coprime `1 ≤ u < v`, `M ≥ v`  →  BetaTilable u v M
    theorem threshold_iff_small : (∀ M ≥ 1, ThresholdAt e f M) ↔ (∀ M, 2 ≤ M < f → ¬ BetaTilable e f M)

The triangle `O A C` (sides `u Q m`, `v b m`, `v³ m`, `m = v + t`) is the union of eight regions with disjoint
interiors: two pieces of each of the blocks 1 and 2 (a scaled tile and a lattice parallelogram), block 3 (a scaled
tile), the pile of the lower strips, the pile of the middle strips (with the strip of the kink), and the triangle on
top.  Geometry: `Draft.ResidueBlocks*` (generated), `Draft.ResidueStrips`, `Draft.ResidueSeedBlocks`,
`Draft.ResidueSeedTarget`; here the piles, the packing lemma with the area identity, the count `Q m²`, and the
induction with the collar of `Draft.CollarG`.

The construction is due to D. Paliy, "unrestricted all-scale positive theorem for W and beta" (2026, unrefereed; the
seed at scale `v` is credited there to M. Beeson), which states the existence for all `M ≥ v`.  The formal proof is
given here.  No sorry, no native_decide.
-/
import Erdos634.Draft.ResidueStrips
import Erdos634.Draft.ResidueBlocks
import Erdos634.Draft.ResidueSeedBlocks
import Erdos634.Draft.ResidueSeedTarget

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.Residue
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (triC triC_pts carrier_triC brickL brickU brick_rt cong_U_cell grid scaledRT baseTri
  baseTri_cong vol_triC sq_Phi' dPhi' disjoint_image' f_ne)
open Erdos634.Draft.WBrickF (interior_disj_lin)
open Erdos634.Draft.CollarE1 (mapped_grid Pg)
open Erdos634.Draft.CollarG (φβ hφβ ca cb hapos hbpos hvpos hPpos WTilable)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.UniformThreshold (BetaTilable ThresholdAt hasSides_congr)

/-! ## Generic -/

/-- a pile of `n` strips; the hypotheses are needed only for the strips `j < n` -/
theorem stackN {φ : ℝ} (hφ : 1 < 4 * φ ^ 2) {M : Erdos634.Geometry.Tri} (S : ℕ → Set (ℝ × ℝ)) (cnt : ℕ → ℕ)
    (lv : ℕ → ℝ) (hmono : ∀ j, lv j ≤ lv (j + 1)) :
    ∀ n : ℕ, (∀ j, j < n → ∀ q ∈ S j, lv j ≤ q.2 ∧ q.2 ≤ lv (j + 1)) →
      (∀ j, j < n → Nonempty (RTiling (Phi φ '' S j) M (cnt j))) →
      Nonempty (RTiling (Phi φ '' ⋃ j ∈ Finset.range n, S j) M (∑ j ∈ Finset.range n, cnt j)) := by
  have hm : Monotone lv := monotone_nat_of_le_succ hmono
  intro n
  induction n with
  | zero =>
    intro _ _
    have hE : (⋃ j ∈ Finset.range 0, S j) = (∅ : Set (ℝ × ℝ)) := by simp
    rw [hE, Set.image_empty, Finset.sum_range_zero]
    exact ⟨emptyRT⟩
  | succ n ih =>
    intro hb R
    have Rn := R n (Nat.lt_succ_self n)
    have Rp := ih (fun j hj => hb j (Nat.lt_succ_of_lt hj)) (fun j hj => R j (Nat.lt_succ_of_lt hj))
    have hU : (⋃ j ∈ Finset.range (n + 1), S j) = (⋃ j ∈ Finset.range n, S j) ∪ S n := by
      ext q
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union]
      constructor
      · rintro ⟨j, hj, hq⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact Or.inl ⟨j, h, hq⟩
        · subst h; exact Or.inr hq
      · rintro (⟨j, hj, hq⟩ | hq)
        · exact ⟨j, Nat.lt_succ_of_lt hj, hq⟩
        · exact ⟨n, Nat.lt_succ_self n, hq⟩
    rw [hU, Finset.sum_range_succ]
    refine unionF hφ Rp Rn (interior_disj_snd (lv n) ?_ (fun q hq => (hb n (Nat.lt_succ_self n) q hq).1))
    intro q hq
    simp only [Set.mem_iUnion, Finset.mem_range] at hq
    obtain ⟨j, hj, hqj⟩ := hq
    exact ((hb j (Nat.lt_succ_of_lt hj) q hqj).2).trans (hm (Nat.succ_le_of_lt hj))

theorem sum_affine (α β : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (α + β * (j : ℝ)) = (n : ℝ) * α + β * ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

def cnt8 (n0 n1 n2 n3 n4 n5 n6 n7 : ℕ) : Fin 8 → ℕ := fun i => match i with
  | ⟨0, _⟩ => n0
  | ⟨1, _⟩ => n1
  | ⟨2, _⟩ => n2
  | ⟨3, _⟩ => n3
  | ⟨4, _⟩ => n4
  | ⟨5, _⟩ => n5
  | ⟨6, _⟩ => n6
  | ⟨7, _⟩ => n7
  | ⟨k + 8, h⟩ => absurd h (by omega)

theorem sum_cnt8 (n0 n1 n2 n3 n4 n5 n6 n7 : ℕ) :
    ∑ a, cnt8 n0 n1 n2 n3 n4 n5 n6 n7 a = n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 := by
  rw [Fin.sum_univ_eight]
  rfl

/-! ## The parameters, the two piles, the count -/

def qLn (un gn j : ℕ) : ℕ := (gn - 1) * un + gn * j
def cntL (un vn gn j : ℕ) : ℕ := un * un + 2 * (vn + qLn un gn j) * un + 2 * qLn un gn j * vn + vn * vn
def qSn (un gn tn : ℕ) : ℕ := (gn - 1) * un + gn * (tn - 1)
def cntM (un vn gn tn : ℕ) : ℕ := vn * vn + 2 * (vn + qSn un gn tn) * un + 2 * qSn un gn tn * vn + vn * vn
def cntK (un vn gn tn ρn dn : ℕ) : ℕ :=
  vn * vn + 2 * (vn + qSn un gn tn) * un + 2 * qSn un gn tn * vn + (ρn * ρn + 2 * ρn * dn)
def Knat (un vn gn tn : ℕ) : ℕ := gn * (un + vn + tn)
def gU (un vn Kn i : ℕ) : ℕ := vn * vn + 2 * Kn * un + 2 * (vn * i) * vn

/-- the number of tiles of the seed, region by region -/
def total (tn rn gn ρn dn i0 nn : ℕ) : ℕ :=
  ((tn + rn) * (tn + rn + gn)) * ((tn + rn) * (tn + rn + gn))
    + 2 * ((tn + rn) * (tn + rn + gn)) * ((tn + rn) * tn)
    + ((tn + rn) * tn) * ((tn + rn) * tn)
    + 2 * (gn * tn) * ((tn + rn) * tn)
    + Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn
    + ∑ j ∈ Finset.range tn, cntL (tn + rn) (tn + rn + gn) gn j
    + ((∑ i ∈ Finset.range i0, cntM (tn + rn) (tn + rn + gn) gn tn) + cntK (tn + rn) (tn + rn + gn) gn tn ρn dn
        + ∑ i ∈ Finset.range nn, gU (tn + rn) (tn + rn + gn) (Knat (tn + rn) (tn + rn + gn) gn tn) (nn - 1 - i))
    + Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn

set_option maxHeartbeats 1600000 in
/-- **The count.**  The eight regions carry `Q m²` tiles. -/
theorem count_id (tn rn gn Jn ρn i0 nn dn : ℕ) (htn : 1 ≤ tn) (hgn : 1 ≤ gn)
    (hJ : (tn + rn) * (tn + rn + gn + tn) = (tn + rn + gn) * Jn + ρn) (hd : ρn + dn = tn + rn + gn)
    (hi0 : Jn = tn + i0) (hnn : Jn + 1 + nn = tn + rn + tn) :
    ((total tn rn gn ρn dn i0 nn : ℕ) : ℝ)
      = (((tn : ℝ) + rn) ^ 2 + 4 * ((tn : ℝ) + rn) * gn + 2 * (gn : ℝ) ^ 2) * ((tn : ℝ) + rn + gn + tn) ^ 2 := by
  have hJr : ((tn : ℝ) + rn) * ((tn : ℝ) + rn + gn + tn) = ((tn : ℝ) + rn + gn) * Jn + ρn := by exact_mod_cast hJ
  have hdr : (ρn : ℝ) + dn = (tn : ℝ) + rn + gn := by exact_mod_cast hd
  have hi0r : (Jn : ℝ) = (tn : ℝ) + i0 := by exact_mod_cast hi0
  have hnnr : (Jn : ℝ) + 1 + nn = (tn : ℝ) + rn + tn := by exact_mod_cast hnn
  have s1 : ((∑ j ∈ Finset.range tn, cntL (tn + rn) (tn + rn + gn) gn j : ℕ) : ℝ)
      = (tn : ℝ) * (((tn : ℝ) + rn) * ((tn : ℝ) + rn)
            + 2 * (((tn : ℝ) + rn + gn) + ((gn : ℝ) - 1) * ((tn : ℝ) + rn)) * ((tn : ℝ) + rn)
            + 2 * (((gn : ℝ) - 1) * ((tn : ℝ) + rn)) * ((tn : ℝ) + rn + gn)
            + ((tn : ℝ) + rn + gn) * ((tn : ℝ) + rn + gn))
        + (2 * (gn : ℝ) * ((tn : ℝ) + rn) + 2 * (gn : ℝ) * ((tn : ℝ) + rn + gn))
          * ((tn : ℝ) * ((tn : ℝ) - 1) / 2) := by
    rw [Nat.cast_sum, ← sum_affine]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [cntL, qLn]
    push_cast [Nat.cast_sub hgn]
    ring
  have s2 : ((∑ i ∈ Finset.range i0, cntM (tn + rn) (tn + rn + gn) gn tn : ℕ) : ℝ)
      = (i0 : ℝ) * (((tn : ℝ) + rn + gn) * ((tn : ℝ) + rn + gn)
          + 2 * (((tn : ℝ) + rn + gn) + (((gn : ℝ) - 1) * ((tn : ℝ) + rn) + (gn : ℝ) * ((tn : ℝ) - 1)))
              * ((tn : ℝ) + rn)
          + 2 * (((gn : ℝ) - 1) * ((tn : ℝ) + rn) + (gn : ℝ) * ((tn : ℝ) - 1)) * ((tn : ℝ) + rn + gn)
          + ((tn : ℝ) + rn + gn) * ((tn : ℝ) + rn + gn)) := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    simp only [cntM, qSn]
    push_cast [Nat.cast_sub hgn, Nat.cast_sub htn]
    ring
  have s3 : ((∑ i ∈ Finset.range nn,
        gU (tn + rn) (tn + rn + gn) (Knat (tn + rn) (tn + rn + gn) gn tn) (nn - 1 - i) : ℕ) : ℝ)
      = (nn : ℝ) * (((tn : ℝ) + rn + gn) * ((tn : ℝ) + rn + gn)
            + 2 * ((gn : ℝ) * (((tn : ℝ) + rn) + ((tn : ℝ) + rn + gn) + tn)) * ((tn : ℝ) + rn))
        + (2 * ((tn : ℝ) + rn + gn) * ((tn : ℝ) + rn + gn)) * ((nn : ℝ) * ((nn : ℝ) - 1) / 2) := by
    rw [Finset.sum_range_reflect (fun i => gU (tn + rn) (tn + rn + gn) (Knat (tn + rn) (tn + rn + gn) gn tn) i) nn,
      Nat.cast_sum, ← sum_affine]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [gU, Knat]
    push_cast
    ring
  have ei0 : (i0 : ℝ) = (Jn : ℝ) - tn := by linarith only [hi0r]
  have enn : (nn : ℝ) = (tn : ℝ) + rn + tn - 1 - Jn := by linarith only [hnnr]
  have edn : (dn : ℝ) = (tn : ℝ) + rn + gn - ρn := by linarith only [hdr]
  have eρ : (ρn : ℝ) = ((tn : ℝ) + rn) * ((tn : ℝ) + rn + gn + tn) - ((tn : ℝ) + rn + gn) * Jn := by
    linarith only [hJr]
  simp only [total, Nat.cast_add]
  rw [s1, s2, s3]
  simp only [cntK, qSn, Knat]
  push_cast [Nat.cast_sub hgn, Nat.cast_sub htn]
  rw [ei0, enn, edn, eρ]
  ring

/-- the parameters of one seed: reals and the naturals they come from -/
structure Par (t r e J ρ : ℝ) (tn rn gn Jn ρn i0 nn dn : ℕ) : Prop where
  et : t = tn
  er : r = rn
  ee : e = gn
  eJ : J = Jn
  eρ : ρ = ρn
  htn : 1 ≤ tn
  hrn : 1 ≤ rn
  hgn : 1 ≤ gn
  hJ : (tn + rn) * (tn + rn + gn + tn) = (tn + rn + gn) * Jn + ρn
  hρ1 : 1 ≤ ρn
  hd : ρn + dn = tn + rn + gn
  hd1 : 1 ≤ dn
  hi0 : Jn = tn + i0
  hnn : Jn + 1 + nn = tn + rn + tn

/-- the pile of the lower strips -/
def F1 (t r e : ℝ) (tn : ℕ) : Set (ℝ × ℝ) := ⋃ j ∈ Finset.range tn, SL t r e (j : ℝ)

/-- the pile of the middle strips: below the kink, the strip of the kink, above it -/
def HM (t r e J ρ : ℝ) (tn Jn i0 nn : ℕ) : Set (ℝ × ℝ) :=
  (⋃ i ∈ Finset.range i0, SM t r e ((tn + i : ℕ) : ℝ)) ∪ SK t r e J ρ
    ∪ (⋃ i ∈ Finset.range nn, SU t r e ((Jn + 1 + i : ℕ) : ℝ))

namespace Par
variable {t r e J ρ : ℝ} {tn rn gn Jn ρn i0 nn dn : ℕ} (P : Par t r e J ρ tn rn gn Jn ρn i0 nn dn)
include P

theorem ht : (1 : ℝ) ≤ t := by rw [P.et]; exact_mod_cast P.htn
theorem hr : (1 : ℝ) ≤ r := by rw [P.er]; exact_mod_cast P.hrn
theorem he : (1 : ℝ) ≤ e := by rw [P.ee]; exact_mod_cast P.hgn
theorem ht0 : (0 : ℝ) < t := by have := P.ht; linarith
theorem hr0 : (0 : ℝ) < r := by have := P.hr; linarith
theorem he0 : (0 : ℝ) < e := by have := P.he; linarith
theorem hu : (0 : ℝ) < t + r := add_pos P.ht0 P.hr0
theorem hV : (0 : ℝ) < t + r + e := add_pos P.hu P.he0
theorem hJr : (t + r) * (t + r + e + t) = (t + r + e) * J + ρ := by
  rw [P.et, P.er, P.ee, P.eJ, P.eρ]; exact_mod_cast P.hJ
theorem hρ0 : (0 : ℝ) ≤ ρ := by rw [P.eρ]; exact Nat.cast_nonneg _
theorem hρv : ρ ≤ t + r + e := by
  have h := P.hd
  rw [P.et, P.er, P.ee, P.eρ]; exact_mod_cast (by omega : ρn ≤ tn + rn + gn)
theorem htJ : t ≤ J := by
  have h := P.hi0
  rw [P.et, P.eJ]; exact_mod_cast (by omega : tn ≤ Jn)
theorem hJ0 : (0 : ℝ) ≤ J := by rw [P.eJ]; exact Nat.cast_nonneg _
theorem hqS : 0 ≤ qS t r e := by
  have h1 := P.ht; have h2 := P.hr; have h3 := P.he
  simp only [qS]
  exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
theorem eu : t + r = ((tn + rn : ℕ) : ℝ) := by rw [P.et, P.er, Nat.cast_add]
theorem ev : t + r + e = ((tn + rn + gn : ℕ) : ℝ) := by rw [P.et, P.er, P.ee, Nat.cast_add, Nat.cast_add]
theorem hJw : J + 1 + (nn : ℝ) = t + r + t := by rw [P.et, P.er, P.eJ]; exact_mod_cast P.hnn
theorem eqS : qS t r e = ((qSn (tn + rn) gn tn : ℕ) : ℝ) := by
  simp only [qS, qSn]; rw [P.et, P.er, P.ee]
  push_cast [Nat.cast_sub P.hgn, Nat.cast_sub P.htn] <;> ring
theorem eK : cK t r e = ((Knat (tn + rn) (tn + rn + gn) gn tn : ℕ) : ℝ) := by
  simp only [cK, Knat]; rw [P.et, P.er, P.ee]
  push_cast <;> ring
theorem hun : 0 < tn + rn := by have := P.htn; omega
theorem hvn : 0 < tn + rn + gn := by have := P.htn; omega
theorem hKn : 0 < Knat (tn + rn) (tn + rn + gn) gn tn := by
  simp only [Knat]; exact Nat.mul_pos P.hgn (by have := P.htn; omega)

theorem hqL (j : ℕ) : 0 ≤ qL t r e (j : ℝ) := by
  have h1 := P.ht; have h2 := P.hr; have h3 := P.he
  simp only [qL]
  exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (Nat.cast_nonneg j))

/-- the inequalities on the pile of the lower strips -/
theorem F1_all {q : ℝ × ℝ} (hq : q ∈ F1 t r e tn) :
    0 ≤ q.2 ∧ q.2 ≤ (t + r + e) ^ 2 * (t + r) * t ∧ 0 ≤ (t + r + e) * q.2 - (t + r) * q.1 ∧
      -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2))
        ≤ (t + r + e) * q.1 - (t + r) * q.2 ∧
      q.1 ≤ (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by
  obtain ⟨j, hj, hqj⟩ := mem_stack (S := fun j : ℕ => SL t r e (j : ℝ)) hq
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hjt : (j : ℝ) + 1 ≤ t := by rw [P.et]; exact_mod_cast Nat.succ_le_of_lt hj
  obtain ⟨b1, b2, b3, b4, b5⟩ := SL_bounds P.ht P.hr P.he hj0 hjt (P.hqL j) hqj
  have h0 : lvl t r e 0 ≤ lvl t r e (j : ℝ) := lvl_mono P.ht P.hr P.he hj0
  have h00 : lvl t r e 0 = 0 := by simp only [lvl]; ring
  have h1 : lvl t r e ((j : ℝ) + 1) ≤ lvl t r e t := lvl_mono P.ht P.hr P.he hjt
  have h11 : lvl t r e t = (t + r + e) ^ 2 * (t + r) * t := rfl
  exact ⟨by linarith only [b1, h0, h00], by linarith only [b2, h1, h11], b3, b4, b5⟩

theorem rt_F1 : Nonempty (RTiling (Phi (φβ (t + r) e) '' F1 t r e tn) (ModC P.hu P.he0)
    (∑ j ∈ Finset.range tn, cntL (tn + rn) (tn + rn + gn) gn j)) := by
  refine stackN (hφβ P.hu P.he0) (fun j : ℕ => SL t r e (j : ℝ))
    (fun j => cntL (tn + rn) (tn + rn + gn) gn j) (fun j : ℕ => lvl t r e (j : ℝ))
    (fun j => lvl_mono P.ht P.hr P.he (by exact_mod_cast Nat.le_succ j)) tn ?_ ?_
  · intro j hj q hq
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hjt : (j : ℝ) + 1 ≤ t := by rw [P.et]; exact_mod_cast Nat.succ_le_of_lt hj
    obtain ⟨b1, b2, -⟩ := SL_bounds P.ht P.hr P.he hj0 hjt (P.hqL j) hq
    have b2' : q.2 ≤ lvl t r e (((j + 1 : ℕ)) : ℝ) := by rw [Nat.cast_add_one]; exact b2
    exact ⟨b1, b2'⟩
  · intro j hj
    exact rt_SL P.hu P.he0 (j : ℝ) (tn + rn) (tn + rn + gn) (qLn (tn + rn) gn j) P.hun P.hvn P.eu P.ev (by
      simp only [qL, qLn]; rw [P.et, P.er, P.ee]
      push_cast [Nat.cast_sub P.hgn] <;> ring)

/-- the inequalities on the pile of the middle strips -/
theorem HM_all {q : ℝ × ℝ} (hq : q ∈ HM t r e J ρ tn Jn i0 nn) :
    (t + r + e) ^ 2 * (t + r) * t ≤ q.2 ∧ q.2 ≤ lvl t r e (t + r + t) ∧
      0 ≤ (t + r + e) * q.2 - (t + r) * q.1 ∧
      -(((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t))
        ≤ (t + r) * q.1 - (t + r + e) * q.2 ∧
      q.1 ≤ (t + r + e) ^ 2 * (t + r) * (t + r + e + t) := by
  have h11 : lvl t r e t = (t + r + e) ^ 2 * (t + r) * t := rfl
  have hw := P.hJw
  have hnn0 : (0 : ℝ) ≤ (nn : ℝ) := Nat.cast_nonneg nn
  rcases hq with (hq | hq) | hq
  · obtain ⟨i, hi, hqi⟩ := mem_stack (S := fun i : ℕ => SM t r e ((tn + i : ℕ) : ℝ)) hq
    have hj0 : (0 : ℝ) ≤ ((tn + i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hj1 : ((tn + i : ℕ) : ℝ) + 1 ≤ J := by
      have h := P.hi0
      rw [P.eJ]; exact_mod_cast (by omega : tn + i + 1 ≤ Jn)
    have hjm : (t + r + e) * (((tn + i : ℕ) : ℝ) + 1) ≤ (t + r) * (t + r + e + t) := by
      linarith only [mul_le_mul_of_nonneg_left hj1 P.hV.le, P.hJr, P.hρ0]
    obtain ⟨b1, b2, b3, b4, b5⟩ := SM_bounds P.ht P.hr P.he hj0 P.hqS hjm hqi
    have htj : t ≤ ((tn + i : ℕ) : ℝ) := by rw [P.et]; exact_mod_cast Nat.le_add_right tn i
    have h1 := lvl_mono P.ht P.hr P.he htj
    have h2 : lvl t r e (((tn + i : ℕ) : ℝ) + 1) ≤ lvl t r e (t + r + t) :=
      lvl_mono P.ht P.hr P.he (by linarith only [hj1, hw, hnn0])
    exact ⟨by linarith only [b1, h1, h11], by linarith only [b2, h2], b3, b4, b5⟩
  · obtain ⟨b1, b2, b3, b4, b5⟩ := SK_bounds P.ht P.hr P.he P.hJ0 P.hqS P.hJr P.hρ0 P.hρv hq
    have h1 := lvl_mono P.ht P.hr P.he P.htJ
    have h2 : lvl t r e (J + 1) ≤ lvl t r e (t + r + t) :=
      lvl_mono P.ht P.hr P.he (by linarith only [hw, hnn0])
    exact ⟨by linarith only [b1, h1, h11], by linarith only [b2, h2], b3, b4, b5⟩
  · obtain ⟨i, hi, hqi⟩ := mem_stack (S := fun i : ℕ => SU t r e ((Jn + 1 + i : ℕ) : ℝ)) hq
    have hJj : J + 1 ≤ ((Jn + 1 + i : ℕ) : ℝ) := by
      rw [P.eJ]; exact_mod_cast (by omega : Jn + 1 ≤ Jn + 1 + i)
    have hjw : ((Jn + 1 + i : ℕ) : ℝ) + 1 ≤ t + r + t := by
      have h := P.hnn
      rw [P.et, P.er]; exact_mod_cast (by omega : Jn + 1 + i + 1 ≤ tn + rn + tn)
    obtain ⟨b1, b2, b3, b4, b5⟩ := SU_bounds P.ht P.hr P.he P.hJr P.hρv hJj hjw hqi
    have htj : t ≤ ((Jn + 1 + i : ℕ) : ℝ) := by linarith only [P.htJ, hJj]
    have h1 := lvl_mono P.ht P.hr P.he htj
    have h2 : lvl t r e (((Jn + 1 + i : ℕ) : ℝ) + 1) ≤ lvl t r e (t + r + t) := lvl_mono P.ht P.hr P.he hjw
    exact ⟨by linarith only [b1, h1, h11], by linarith only [b2, h2], b3, b4, b5⟩

theorem rt_HM : Nonempty (RTiling (Phi (φβ (t + r) e) '' HM t r e J ρ tn Jn i0 nn) (ModC P.hu P.he0)
    ((∑ i ∈ Finset.range i0, cntM (tn + rn) (tn + rn + gn) gn tn) + cntK (tn + rn) (tn + rn + gn) gn tn ρn dn
      + ∑ i ∈ Finset.range nn, gU (tn + rn) (tn + rn + gn) (Knat (tn + rn) (tn + rn + gn) gn tn) (nn - 1 - i))) := by
  have hw := P.hJw
  have RM := stackN (hφβ P.hu P.he0) (fun i : ℕ => SM t r e ((tn + i : ℕ) : ℝ))
    (fun _ => cntM (tn + rn) (tn + rn + gn) gn tn) (fun i : ℕ => lvl t r e ((tn + i : ℕ) : ℝ))
    (fun i => lvl_mono P.ht P.hr P.he (by exact_mod_cast (by omega : tn + i ≤ tn + (i + 1)))) i0
    (fun i hi q hq => by
      have hj0 : (0 : ℝ) ≤ ((tn + i : ℕ) : ℝ) := Nat.cast_nonneg _
      have hj1 : ((tn + i : ℕ) : ℝ) + 1 ≤ J := by
        have h := P.hi0
        rw [P.eJ]; exact_mod_cast (by omega : tn + i + 1 ≤ Jn)
      have hjm : (t + r + e) * (((tn + i : ℕ) : ℝ) + 1) ≤ (t + r) * (t + r + e + t) := by
        linarith only [mul_le_mul_of_nonneg_left hj1 P.hV.le, P.hJr, P.hρ0]
      obtain ⟨b1, b2, -⟩ := SM_bounds P.ht P.hr P.he hj0 P.hqS hjm hq
      have e1 : ((tn + (i + 1) : ℕ) : ℝ) = ((tn + i : ℕ) : ℝ) + 1 := by push_cast <;> ring
      have b2' : q.2 ≤ lvl t r e ((tn + (i + 1) : ℕ) : ℝ) := by rw [e1]; exact b2
      exact ⟨b1, b2'⟩)
    (fun i hi => rt_SM P.hu P.he0 ((tn + i : ℕ) : ℝ) (tn + rn) (tn + rn + gn) (qSn (tn + rn) gn tn)
      P.hun P.hvn P.eu P.ev P.eqS)
  have RK := rt_SK P.hu P.he0 J ρ (tn + rn) (tn + rn + gn) (qSn (tn + rn) gn tn) ρn dn P.hun P.hvn
    P.hρ1 P.hd1 P.eu P.ev P.eqS P.eρ (by
      have h := P.hd
      rw [P.et, P.er, P.ee, P.eρ]; exact_mod_cast h.symm)
  have RU := stackN (hφβ P.hu P.he0) (fun i : ℕ => SU t r e ((Jn + 1 + i : ℕ) : ℝ))
    (fun i => gU (tn + rn) (tn + rn + gn) (Knat (tn + rn) (tn + rn + gn) gn tn) (nn - 1 - i))
    (fun i : ℕ => lvl t r e ((Jn + 1 + i : ℕ) : ℝ))
    (fun i => lvl_mono P.ht P.hr P.he (by exact_mod_cast (by omega : Jn + 1 + i ≤ Jn + 1 + (i + 1)))) nn
    (fun i hi q hq => by
      have hJj : J + 1 ≤ ((Jn + 1 + i : ℕ) : ℝ) := by
        rw [P.eJ]; exact_mod_cast (by omega : Jn + 1 ≤ Jn + 1 + i)
      have hjw : ((Jn + 1 + i : ℕ) : ℝ) + 1 ≤ t + r + t := by
        have h := P.hnn
        rw [P.et, P.er]; exact_mod_cast (by omega : Jn + 1 + i + 1 ≤ tn + rn + tn)
      obtain ⟨b1, b2, -⟩ := SU_bounds P.ht P.hr P.he P.hJr P.hρv hJj hjw hq
      have e1 : ((Jn + 1 + (i + 1) : ℕ) : ℝ) = ((Jn + 1 + i : ℕ) : ℝ) + 1 := by push_cast <;> ring
      have b2' : q.2 ≤ lvl t r e ((Jn + 1 + (i + 1) : ℕ) : ℝ) := by rw [e1]; exact b2
      exact ⟨b1, b2'⟩)
    (fun i hi => by
      have h1 : (((nn - 1 - i : ℕ)) : ℝ) = (t + r + t) - 1 - ((Jn + 1 + i : ℕ) : ℝ) := by
        have h2 : (((nn - 1 - i : ℕ)) : ℝ) = (nn : ℝ) - 1 - (i : ℝ) := by
          rw [Nat.sub_sub, Nat.cast_sub (by omega : 1 + i ≤ nn)]; push_cast <;> ring
        have h3 := hw
        rw [P.eJ] at h3
        rw [h2]; push_cast; linarith only [h3]
      have hy : (((tn + rn + gn) * (nn - 1 - i) : ℕ) : ℝ)
          = (t + r + e) * ((t + r + t) - 1 - ((Jn + 1 + i : ℕ) : ℝ)) := by
        rw [Nat.cast_mul, ← P.ev, h1]
      exact rt_SU P.hu P.he0 ((Jn + 1 + i : ℕ) : ℝ) (tn + rn) (tn + rn + gn)
        (Knat (tn + rn) (tn + rn + gn) gn tn) ((tn + rn + gn) * (nn - 1 - i)) P.hun P.hvn P.hKn P.eu P.ev P.eK
        (by rw [hy]; simp only [XM, cK, ca]; ring))
  refine unionF (hφβ P.hu P.he0) (unionF (hφβ P.hu P.he0) RM RK (interior_disj_snd (lvl t r e J) ?_ ?_)) RU
    (interior_disj_snd (lvl t r e (J + 1)) ?_ ?_)
  · intro q hq
    obtain ⟨i, hi, hqi⟩ := mem_stack (S := fun i : ℕ => SM t r e ((tn + i : ℕ) : ℝ)) hq
    have hj0 : (0 : ℝ) ≤ ((tn + i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hj1 : ((tn + i : ℕ) : ℝ) + 1 ≤ J := by
      have h := P.hi0
      rw [P.eJ]; exact_mod_cast (by omega : tn + i + 1 ≤ Jn)
    have hjm : (t + r + e) * (((tn + i : ℕ) : ℝ) + 1) ≤ (t + r) * (t + r + e + t) := by
      linarith only [mul_le_mul_of_nonneg_left hj1 P.hV.le, P.hJr, P.hρ0]
    obtain ⟨b1, b2, -⟩ := SM_bounds P.ht P.hr P.he hj0 P.hqS hjm hqi
    exact b2.trans (lvl_mono P.ht P.hr P.he hj1)
  · intro q hq
    exact (SK_bounds P.ht P.hr P.he P.hJ0 P.hqS P.hJr P.hρ0 P.hρv hq).1
  · rintro q (hq | hq)
    · obtain ⟨i, hi, hqi⟩ := mem_stack (S := fun i : ℕ => SM t r e ((tn + i : ℕ) : ℝ)) hq
      have hj0 : (0 : ℝ) ≤ ((tn + i : ℕ) : ℝ) := Nat.cast_nonneg _
      have hj1 : ((tn + i : ℕ) : ℝ) + 1 ≤ J := by
        have h := P.hi0
        rw [P.eJ]; exact_mod_cast (by omega : tn + i + 1 ≤ Jn)
      have hjm : (t + r + e) * (((tn + i : ℕ) : ℝ) + 1) ≤ (t + r) * (t + r + e + t) := by
        linarith only [mul_le_mul_of_nonneg_left hj1 P.hV.le, P.hJr, P.hρ0]
      obtain ⟨b1, b2, -⟩ := SM_bounds P.ht P.hr P.he hj0 P.hqS hjm hqi
      exact b2.trans (lvl_mono P.ht P.hr P.he (by linarith only [hj1]))
    · exact (SK_bounds P.ht P.hr P.he P.hJ0 P.hqS P.hJr P.hρ0 P.hρv hq).2.1
  · intro q hq
    obtain ⟨i, hi, hqi⟩ := mem_stack (S := fun i : ℕ => SU t r e ((Jn + 1 + i : ℕ) : ℝ)) hq
    have hJj : J + 1 ≤ ((Jn + 1 + i : ℕ) : ℝ) := by
      rw [P.eJ]; exact_mod_cast (by omega : Jn + 1 ≤ Jn + 1 + i)
    have hjw : ((Jn + 1 + i : ℕ) : ℝ) + 1 ≤ t + r + t := by
      have h := P.hnn
      rw [P.et, P.er]; exact_mod_cast (by omega : Jn + 1 + i + 1 ≤ tn + rn + tn)
    obtain ⟨b1, -⟩ := SU_bounds P.ht P.hr P.he P.hJr P.hρv hJj hjw hqi
    exact (lvl_mono P.ht P.hr P.he hJj).trans b1

end Par

/-! ## Assembly -/

/-- the eight regions in the plane; the two lattice parallelograms are given as sets -/
noncomputable def reg8 (t r e J ρ : ℝ) (tn Jn i0 nn : ℕ) (S1 S3 : Set Plane) : Fin 8 → Set Plane :=
  fun i => match i with
  | ⟨0, _⟩ => Phi (φβ (t + r) e) '' B1a t r e
  | ⟨1, _⟩ => S1
  | ⟨2, _⟩ => Phi (φβ (t + r) e) '' B2a t r e
  | ⟨3, _⟩ => S3
  | ⟨4, _⟩ => Phi (φβ (t + r) e) '' B3 t r e
  | ⟨5, _⟩ => Phi (φβ (t + r) e) '' F1 t r e tn
  | ⟨6, _⟩ => Phi (φβ (t + r) e) '' HM t r e J ρ tn Jn i0 nn
  | ⟨7, _⟩ => Phi (φβ (t + r) e) '' STOP t r e
  | ⟨k + 8, h⟩ => absurd h (by omega)

/-- the eight regions in the frame -/
noncomputable def Zf8 (t r e J ρ : ℝ) (tn Jn i0 nn : ℕ) : Fin 8 → Set (ℝ × ℝ) := fun i => match i with
  | ⟨0, _⟩ => B1a t r e
  | ⟨1, _⟩ => B1b t r e
  | ⟨2, _⟩ => B2a t r e
  | ⟨3, _⟩ => B2b t r e
  | ⟨4, _⟩ => B3 t r e
  | ⟨5, _⟩ => F1 t r e tn
  | ⟨6, _⟩ => HM t r e J ρ tn Jn i0 nn
  | ⟨7, _⟩ => STOP t r e
  | ⟨k + 8, h⟩ => absurd h (by omega)

set_option maxHeartbeats 1600000 in
/-- **The residue seed, as a dissection of the triangle `O A C`.** -/
theorem seed_exists {t r e J ρ : ℝ} {tn rn gn Jn ρn i0 nn dn : ℕ} (P : Par t r e J ρ tn rn gn Jn ρn i0 nn dn) :
    ∃ D : CongruentDissection (total tn rn gn ρn dn i0 nn),
      D.model = ModC P.hu P.he0 ∧ D.target = tgtT P.ht0 P.hr0 P.he0 := by
  have ht0 := P.ht0
  have hr0 := P.hr0
  have he0 := P.he0
  have hu := P.hu
  have hV := P.hV
  have hB := hBnn hu he0
  have hw := P.hJw
  have hnn0 : (0 : ℝ) ≤ (nn : ℝ) := Nat.cast_nonneg nn
  -- the tilings
  obtain ⟨R0⟩ := rt_B1a ht0 hr0 he0 ((tn + rn) * (tn + rn + gn)) (Nat.mul_pos P.hun P.hvn)
    (by rw [Nat.cast_mul, ← P.eu, ← P.ev])
  obtain ⟨S1, ⟨R1⟩, h1⟩ := rt_B1b ht0 hr0 he0 ((tn + rn) * (tn + rn + gn)) ((tn + rn) * tn)
    (Nat.mul_pos P.hun P.hvn) (Nat.mul_pos P.hun P.htn) (by rw [Nat.cast_mul, ← P.eu, ← P.ev])
    (by rw [Nat.cast_mul, ← P.eu, ← P.et])
  obtain ⟨R2⟩ := rt_B2a ht0 hr0 he0 ((tn + rn) * tn) (Nat.mul_pos P.hun P.htn)
    (by rw [Nat.cast_mul, ← P.eu, ← P.et])
  obtain ⟨S3, ⟨R3⟩, h3⟩ := rt_B2b ht0 hr0 he0 (gn * tn) ((tn + rn) * tn) (Nat.mul_pos P.hgn P.htn)
    (Nat.mul_pos P.hun P.htn) (by rw [Nat.cast_mul, ← P.ee, ← P.et]) (by rw [Nat.cast_mul, ← P.eu, ← P.et])
  obtain ⟨R4⟩ := rt_B3 ht0 hr0 he0 (Knat (tn + rn) (tn + rn + gn) gn tn) P.hKn (by
    have := P.eK; simp only [cK] at this; exact this.symm)
  obtain ⟨R5⟩ := P.rt_F1
  obtain ⟨R6⟩ := P.rt_HM
  obtain ⟨R7⟩ := rt_STOP hu he0 (Knat (tn + rn) (tn + rn + gn) gn tn) P.hKn P.eK
  have Rall : ∀ a : Fin 8, RTiling (reg8 t r e J ρ tn Jn i0 nn S1 S3 a) (ModC hu he0)
      (cnt8 (((tn + rn) * (tn + rn + gn)) * ((tn + rn) * (tn + rn + gn)))
        (2 * ((tn + rn) * (tn + rn + gn)) * ((tn + rn) * tn)) (((tn + rn) * tn) * ((tn + rn) * tn))
        (2 * (gn * tn) * ((tn + rn) * tn))
        (Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn)
        (∑ j ∈ Finset.range tn, cntL (tn + rn) (tn + rn + gn) gn j)
        ((∑ i ∈ Finset.range i0, cntM (tn + rn) (tn + rn + gn) gn tn) + cntK (tn + rn) (tn + rn + gn) gn tn ρn dn
          + ∑ i ∈ Finset.range nn,
              gU (tn + rn) (tn + rn + gn) (Knat (tn + rn) (tn + rn + gn) gn tn) (nn - 1 - i))
        (Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn) a) := fun a => match a with
    | ⟨0, _⟩ => R0
    | ⟨1, _⟩ => R1
    | ⟨2, _⟩ => R2
    | ⟨3, _⟩ => R3
    | ⟨4, _⟩ => R4
    | ⟨5, _⟩ => R5
    | ⟨6, _⟩ => R6
    | ⟨7, _⟩ => R7
    | ⟨k + 8, h⟩ => absurd h (by omega)
  have sub_all : ∀ a : Fin 8, reg8 t r e J ρ tn Jn i0 nn S1 S3 a
      ⊆ Phi (φβ (t + r) e) '' Zf8 t r e J ρ tn Jn i0 nn a := fun a => match a with
    | ⟨0, _⟩ => subset_rfl
    | ⟨1, _⟩ => h1
    | ⟨2, _⟩ => subset_rfl
    | ⟨3, _⟩ => h3
    | ⟨4, _⟩ => subset_rfl
    | ⟨5, _⟩ => subset_rfl
    | ⟨6, _⟩ => subset_rfl
    | ⟨7, _⟩ => subset_rfl
    | ⟨k + 8, h⟩ => absurd h (by omega)
  -- the inequalities, region by region
  have hcut0 : (0 : ℝ) ≤ (t + r + e) ^ 2 * (t + r) * t := by positivity
  have hcw : (t + r + e) ^ 2 * (t + r) * t ≤ lvl t r e (t + r + t) :=
    lvl_mono P.ht P.hr P.he (by linarith only [hu])
  have yB1a : ∀ p ∈ B1a t r e, p.2 ≤ 0 := fun p hp => by
    have := B1a_Y_zero_le ht0 hr0 he0 p hp; linarith only [this]
  have yB1b : ∀ p ∈ B1b t r e, p.2 ≤ 0 := fun p hp => by
    have := B1b_Y_zero_le ht0 hr0 he0 p hp; linarith only [this]
  have yB2a : ∀ p ∈ B2a t r e, p.2 ≤ (t + r + e) ^ 2 * (t + r) * t := fun p hp => by
    have := B2a_Y_cut_le ht0 hr0 he0 p hp; linarith only [this]
  have yB2b : ∀ p ∈ B2b t r e, p.2 ≤ (t + r + e) ^ 2 * (t + r) * t := fun p hp => by
    have := B2b_Y_cut_le ht0 hr0 he0 p hp; linarith only [this]
  have yB3 : ∀ p ∈ B3 t r e, 0 ≤ p.2 := fun p hp => by
    have := B3_Y_zero_ge ht0 hr0 he0 p hp; linarith only [this]
  have yF1lo : ∀ p ∈ F1 t r e tn, 0 ≤ p.2 := fun p hp => (P.F1_all hp).1
  have yF1hi : ∀ p ∈ F1 t r e tn, p.2 ≤ (t + r + e) ^ 2 * (t + r) * t := fun p hp => (P.F1_all hp).2.1
  have yHMlo : ∀ p ∈ HM t r e J ρ tn Jn i0 nn, (t + r + e) ^ 2 * (t + r) * t ≤ p.2 :=
    fun p hp => (P.HM_all hp).1
  have yHM0 : ∀ p ∈ HM t r e J ρ tn Jn i0 nn, 0 ≤ p.2 := fun p hp => hcut0.trans (yHMlo p hp)
  have yHMhi : ∀ p ∈ HM t r e J ρ tn Jn i0 nn, p.2 ≤ lvl t r e (t + r + t) := fun p hp => (P.HM_all hp).2.1
  have yTOPlo : ∀ p ∈ STOP t r e, lvl t r e (t + r + t) ≤ p.2 :=
    fun p hp => (STOP_bounds P.ht P.hr P.he hp).1
  have yTOPcut : ∀ p ∈ STOP t r e, (t + r + e) ^ 2 * (t + r) * t ≤ p.2 := fun p hp => hcw.trans (yTOPlo p hp)
  have yTOP0 : ∀ p ∈ STOP t r e, 0 ≤ p.2 := fun p hp => hcut0.trans (yTOPcut p hp)
  have lF1 : ∀ p ∈ F1 t r e tn,
      -((t + r + e) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2))
        ≤ (t + r + e) * p.1 + (-(t + r)) * p.2 := fun p hp => by
    have := (P.F1_all hp).2.2.2.1; linarith only [this]
  have nF1 : ∀ p ∈ F1 t r e tn, (-(t + r)) * p.1 + (t + r + e) * p.2
      ≤ ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) := fun p hp => by
    have := low_N hu he0 (P.F1_all hp).2.1 (P.F1_all hp).2.2.2.1; linarith only [this]
  have nHM : ∀ p ∈ HM t r e J ρ tn Jn i0 nn, (-(t + r)) * p.1 + (t + r + e) * p.2
      ≤ ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) := fun p hp => by
    have := (P.HM_all hp).2.2.2.1; linarith only [this]
  have lTOP : ∀ p ∈ STOP t r e, 0 ≤ (t + r + e) * p.1 + (-(t + r)) * p.2 := fun p hp => by
    have := (STOP_bounds P.ht P.hr P.he hp).2.2.2.1; linarith only [this]
  have hNne : (-(t + r)) ≠ 0 := by intro h; linarith only [h, hu]
  have hLne : t + r + e ≠ 0 := hV.ne'
  have hTne : (t + r + e) ^ 3 ≠ 0 := (pow_pos hV 3).ne'
  have d01 : Disjoint (interior (B1a t r e)) (interior (B1b t r e)) :=
    (interior_disj_lin ((t + r + e) ^ 3) (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) _ hTne (B1b_T_mv3ab_le ht0 hr0 he0) (B1a_T_mv3ab_ge ht0 hr0 he0)).symm
  have d02 : Disjoint (interior (B1a t r e)) (interior (B2a t r e)) :=
    interior_disj_lin (-(t + r)) (t + r + e) _ hNne (B1a_N_uab_le ht0 hr0 he0) (B2a_N_uab_ge ht0 hr0 he0)
  have d03 : Disjoint (interior (B1a t r e)) (interior (B2b t r e)) :=
    interior_disj_lin (-(t + r)) (t + r + e) _ hNne (B1a_N_uab_le ht0 hr0 he0) (B2b_N_uab_ge ht0 hr0 he0)
  have d04 : Disjoint (interior (B1a t r e)) (interior (B3 t r e)) :=
    interior_disj_snd 0 yB1a yB3
  have d05 : Disjoint (interior (B1a t r e)) (interior (F1 t r e tn)) :=
    interior_disj_snd 0 yB1a yF1lo
  have d06 : Disjoint (interior (B1a t r e)) (interior (HM t r e J ρ tn Jn i0 nn)) :=
    interior_disj_snd 0 yB1a yHM0
  have d07 : Disjoint (interior (B1a t r e)) (interior (STOP t r e)) :=
    interior_disj_snd 0 yB1a yTOP0
  have d12 : Disjoint (interior (B1b t r e)) (interior (B2a t r e)) :=
    interior_disj_lin (-(t + r)) (t + r + e) _ hNne (B1b_N_uab_le ht0 hr0 he0) (B2a_N_uab_ge ht0 hr0 he0)
  have d13 : Disjoint (interior (B1b t r e)) (interior (B2b t r e)) :=
    interior_disj_lin (-(t + r)) (t + r + e) _ hNne (B1b_N_uab_le ht0 hr0 he0) (B2b_N_uab_ge ht0 hr0 he0)
  have d14 : Disjoint (interior (B1b t r e)) (interior (B3 t r e)) :=
    interior_disj_snd 0 yB1b yB3
  have d15 : Disjoint (interior (B1b t r e)) (interior (F1 t r e tn)) :=
    interior_disj_snd 0 yB1b yF1lo
  have d16 : Disjoint (interior (B1b t r e)) (interior (HM t r e J ρ tn Jn i0 nn)) :=
    interior_disj_snd 0 yB1b yHM0
  have d17 : Disjoint (interior (B1b t r e)) (interior (STOP t r e)) :=
    interior_disj_snd 0 yB1b yTOP0
  have d23 : Disjoint (interior (B2a t r e)) (interior (B2b t r e)) :=
    (interior_disj_lin ((t + r + e) ^ 3) (-((t + r) * (2 * (t + r + e) ^ 2 - (t + r) ^ 2))) _ hTne (B2b_T_l3s_le ht0 hr0 he0) (B2a_T_l3s_ge ht0 hr0 he0)).symm
  have d24 : Disjoint (interior (B2a t r e)) (interior (B3 t r e)) :=
    interior_disj_lin (-(t + r)) (t + r + e) _ hNne (B2a_N_abw_le ht0 hr0 he0) (B3_N_abw_ge ht0 hr0 he0)
  have d25 : Disjoint (interior (B2a t r e)) (interior (F1 t r e tn)) :=
    interior_disj_lin (t + r + e) (-(t + r)) _ hLne (B2a_L_mvab_le ht0 hr0 he0) lF1
  have d26 : Disjoint (interior (B2a t r e)) (interior (HM t r e J ρ tn Jn i0 nn)) :=
    interior_disj_snd _ yB2a yHMlo
  have d27 : Disjoint (interior (B2a t r e)) (interior (STOP t r e)) :=
    interior_disj_snd _ yB2a yTOPcut
  have d34 : Disjoint (interior (B2b t r e)) (interior (B3 t r e)) :=
    interior_disj_lin (-(t + r)) (t + r + e) _ hNne (B2b_N_abw_le ht0 hr0 he0) (B3_N_abw_ge ht0 hr0 he0)
  have d35 : Disjoint (interior (B2b t r e)) (interior (F1 t r e tn)) :=
    interior_disj_lin (t + r + e) (-(t + r)) _ hLne (B2b_L_mvab_le ht0 hr0 he0) lF1
  have d36 : Disjoint (interior (B2b t r e)) (interior (HM t r e J ρ tn Jn i0 nn)) :=
    interior_disj_snd _ yB2b yHMlo
  have d37 : Disjoint (interior (B2b t r e)) (interior (STOP t r e)) :=
    interior_disj_snd _ yB2b yTOPcut
  have d45 : Disjoint (interior (B3 t r e)) (interior (F1 t r e tn)) :=
    (interior_disj_lin (-(t + r)) (t + r + e) _ hNne nF1 (B3_N_abw_ge ht0 hr0 he0)).symm
  have d46 : Disjoint (interior (B3 t r e)) (interior (HM t r e J ρ tn Jn i0 nn)) :=
    (interior_disj_lin (-(t + r)) (t + r + e) _ hNne nHM (B3_N_abw_ge ht0 hr0 he0)).symm
  have d47 : Disjoint (interior (B3 t r e)) (interior (STOP t r e)) :=
    interior_disj_lin (t + r + e) (-(t + r)) _ hLne (B3_L_zero_le ht0 hr0 he0) lTOP
  have d56 : Disjoint (interior (F1 t r e tn)) (interior (HM t r e J ρ tn Jn i0 nn)) :=
    interior_disj_snd _ yF1hi yHMlo
  have d57 : Disjoint (interior (F1 t r e tn)) (interior (STOP t r e)) :=
    interior_disj_snd _ yF1hi yTOPcut
  have d67 : Disjoint (interior (HM t r e J ρ tn Jn i0 nn)) (interior (STOP t r e)) :=
    interior_disj_snd _ yHMhi yTOPlo
  have dZ : ∀ a b : Fin 8, a ≠ b → Disjoint (interior (Zf8 t r e J ρ tn Jn i0 nn a)) (interior (Zf8 t r e J ρ tn Jn i0 nn b)) := by
    intro a b hab
    exact match a, b with
    | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hab
    | ⟨0, _⟩, ⟨1, _⟩ => d01
    | ⟨0, _⟩, ⟨2, _⟩ => d02
    | ⟨0, _⟩, ⟨3, _⟩ => d03
    | ⟨0, _⟩, ⟨4, _⟩ => d04
    | ⟨0, _⟩, ⟨5, _⟩ => d05
    | ⟨0, _⟩, ⟨6, _⟩ => d06
    | ⟨0, _⟩, ⟨7, _⟩ => d07
    | ⟨1, _⟩, ⟨0, _⟩ => d01.symm
    | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hab
    | ⟨1, _⟩, ⟨2, _⟩ => d12
    | ⟨1, _⟩, ⟨3, _⟩ => d13
    | ⟨1, _⟩, ⟨4, _⟩ => d14
    | ⟨1, _⟩, ⟨5, _⟩ => d15
    | ⟨1, _⟩, ⟨6, _⟩ => d16
    | ⟨1, _⟩, ⟨7, _⟩ => d17
    | ⟨2, _⟩, ⟨0, _⟩ => d02.symm
    | ⟨2, _⟩, ⟨1, _⟩ => d12.symm
    | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hab
    | ⟨2, _⟩, ⟨3, _⟩ => d23
    | ⟨2, _⟩, ⟨4, _⟩ => d24
    | ⟨2, _⟩, ⟨5, _⟩ => d25
    | ⟨2, _⟩, ⟨6, _⟩ => d26
    | ⟨2, _⟩, ⟨7, _⟩ => d27
    | ⟨3, _⟩, ⟨0, _⟩ => d03.symm
    | ⟨3, _⟩, ⟨1, _⟩ => d13.symm
    | ⟨3, _⟩, ⟨2, _⟩ => d23.symm
    | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hab
    | ⟨3, _⟩, ⟨4, _⟩ => d34
    | ⟨3, _⟩, ⟨5, _⟩ => d35
    | ⟨3, _⟩, ⟨6, _⟩ => d36
    | ⟨3, _⟩, ⟨7, _⟩ => d37
    | ⟨4, _⟩, ⟨0, _⟩ => d04.symm
    | ⟨4, _⟩, ⟨1, _⟩ => d14.symm
    | ⟨4, _⟩, ⟨2, _⟩ => d24.symm
    | ⟨4, _⟩, ⟨3, _⟩ => d34.symm
    | ⟨4, _⟩, ⟨4, _⟩ => absurd rfl hab
    | ⟨4, _⟩, ⟨5, _⟩ => d45
    | ⟨4, _⟩, ⟨6, _⟩ => d46
    | ⟨4, _⟩, ⟨7, _⟩ => d47
    | ⟨5, _⟩, ⟨0, _⟩ => d05.symm
    | ⟨5, _⟩, ⟨1, _⟩ => d15.symm
    | ⟨5, _⟩, ⟨2, _⟩ => d25.symm
    | ⟨5, _⟩, ⟨3, _⟩ => d35.symm
    | ⟨5, _⟩, ⟨4, _⟩ => d45.symm
    | ⟨5, _⟩, ⟨5, _⟩ => absurd rfl hab
    | ⟨5, _⟩, ⟨6, _⟩ => d56
    | ⟨5, _⟩, ⟨7, _⟩ => d57
    | ⟨6, _⟩, ⟨0, _⟩ => d06.symm
    | ⟨6, _⟩, ⟨1, _⟩ => d16.symm
    | ⟨6, _⟩, ⟨2, _⟩ => d26.symm
    | ⟨6, _⟩, ⟨3, _⟩ => d36.symm
    | ⟨6, _⟩, ⟨4, _⟩ => d46.symm
    | ⟨6, _⟩, ⟨5, _⟩ => d56.symm
    | ⟨6, _⟩, ⟨6, _⟩ => absurd rfl hab
    | ⟨6, _⟩, ⟨7, _⟩ => d67
    | ⟨7, _⟩, ⟨0, _⟩ => d07.symm
    | ⟨7, _⟩, ⟨1, _⟩ => d17.symm
    | ⟨7, _⟩, ⟨2, _⟩ => d27.symm
    | ⟨7, _⟩, ⟨3, _⟩ => d37.symm
    | ⟨7, _⟩, ⟨4, _⟩ => d47.symm
    | ⟨7, _⟩, ⟨5, _⟩ => d57.symm
    | ⟨7, _⟩, ⟨6, _⟩ => d67.symm
    | ⟨7, _⟩, ⟨7, _⟩ => absurd rfl hab
    | ⟨k + 8, h⟩, _ => absurd h (by omega)
    | _, ⟨k + 8, h⟩ => absurd h (by omega)
  have hS_all : ∀ a b : Fin 8, a ≠ b → Disjoint (interior (reg8 t r e J ρ tn Jn i0 nn S1 S3 a))
      (interior (reg8 t r e J ρ tn Jn i0 nn S1 S3 b)) := fun a b hab =>
    (disjoint_image' (hφβ hu he0) (dZ a b hab)).mono (interior_mono (sub_all a)) (interior_mono (sub_all b))
  -- containment in the target
  have huab0 : (0 : ℝ) ≤ (t + r) * ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) :=
    mul_nonneg (mul_nonneg hu.le (mul_nonneg hu.le hV.le)) hB
  have habw0 : (0 : ℝ) ≤ ((t + r) * (t + r + e)) * ((t + r + e) ^ 2 - (t + r) ^ 2) * ((t + r) + t) :=
    mul_nonneg (mul_nonneg (mul_nonneg hu.le hV.le) hB) (by linarith only [hu, ht0])
  have hTT : ∀ a : Fin 8, Zf8 t r e J ρ tn Jn i0 nn a ⊆ TT t r e := fun a => match a with
    | ⟨0, _⟩ => fun q hq => mem_TT ht0 hr0 he0 q (B1a_X_cum_le ht0 hr0 he0 q hq) (B1a_N_zero_ge ht0 hr0 he0 q hq)
        (B1a_T_mabcm_ge ht0 hr0 he0 q hq)
    | ⟨1, _⟩ => fun q hq => mem_TT ht0 hr0 he0 q (B1b_X_cum_le ht0 hr0 he0 q hq) (B1b_N_zero_ge ht0 hr0 he0 q hq)
        (B1b_T_mabcm_ge ht0 hr0 he0 q hq)
    | ⟨2, _⟩ => fun q hq => mem_TT ht0 hr0 he0 q (B2a_X_cum_le ht0 hr0 he0 q hq)
        (huab0.trans (B2a_N_uab_ge ht0 hr0 he0 q hq)) (B2a_T_mabcm_ge ht0 hr0 he0 q hq)
    | ⟨3, _⟩ => fun q hq => mem_TT ht0 hr0 he0 q (B2b_X_cum_le ht0 hr0 he0 q hq)
        (huab0.trans (B2b_N_uab_ge ht0 hr0 he0 q hq)) (B2b_T_mabcm_ge ht0 hr0 he0 q hq)
    | ⟨4, _⟩ => fun q hq => mem_TT ht0 hr0 he0 q (B3_X_cum_le ht0 hr0 he0 q hq)
        (habw0.trans (B3_N_abw_ge ht0 hr0 he0 q hq)) (B3_T_mabcm_ge ht0 hr0 he0 q hq)
    | ⟨5, _⟩ => fun q hq => by
        obtain ⟨b1, b2, b3, b4, b5⟩ := P.F1_all hq
        exact mem_TT ht0 hr0 he0 q (by linarith only [b5]) (by linarith only [b3]) (low_T ht0 hu he0 b2 b4)
    | ⟨6, _⟩ => fun q hq => by
        obtain ⟨b1, b2, b3, b4, b5⟩ := P.HM_all hq
        exact mem_TT ht0 hr0 he0 q (by linarith only [b5]) (by linarith only [b3])
          (mid_T ht0 hu he0 b1 (by linarith only [b4]))
    | ⟨7, _⟩ => fun q hq => by
        obtain ⟨b1, b2, b3, b4, b5⟩ := STOP_bounds P.ht P.hr P.he hq
        exact mem_TT ht0 hr0 he0 q (by linarith only [b5]) (by linarith only [b3]) (top_T hu he0 b2 b4)
    | ⟨k + 8, h⟩ => absurd h (by omega)
  have hsub_all : ∀ a : Fin 8, reg8 t r e J ρ tn Jn i0 nn S1 S3 a ⊆ (tgtT ht0 hr0 he0).carrier := fun a => by
    rw [carrier_tgtT]
    exact (sub_all a).trans (Set.image_mono (hTT a))
  -- the count and the areas
  have hsumR : ((∑ a, cnt8 (((tn + rn) * (tn + rn + gn)) * ((tn + rn) * (tn + rn + gn)))
        (2 * ((tn + rn) * (tn + rn + gn)) * ((tn + rn) * tn)) (((tn + rn) * tn) * ((tn + rn) * tn))
        (2 * (gn * tn) * ((tn + rn) * tn))
        (Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn)
        (∑ j ∈ Finset.range tn, cntL (tn + rn) (tn + rn + gn) gn j)
        ((∑ i ∈ Finset.range i0, cntM (tn + rn) (tn + rn + gn) gn tn) + cntK (tn + rn) (tn + rn + gn) gn tn ρn dn
          + ∑ i ∈ Finset.range nn,
              gU (tn + rn) (tn + rn + gn) (Knat (tn + rn) (tn + rn + gn) gn tn) (nn - 1 - i))
        (Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn) a : ℕ) : ℝ)
      = ((t + r) ^ 2 + 4 * (t + r) * e + 2 * e ^ 2) * (t + r + e + t) ^ 2 := by
    rw [sum_cnt8]
    have h := count_id tn rn gn Jn ρn i0 nn dn P.htn P.hgn P.hJ P.hd P.hi0 P.hnn
    rw [P.et, P.er, P.ee]
    exact h
  have hvol : ((∑ a, cnt8 (((tn + rn) * (tn + rn + gn)) * ((tn + rn) * (tn + rn + gn)))
        (2 * ((tn + rn) * (tn + rn + gn)) * ((tn + rn) * tn)) (((tn + rn) * tn) * ((tn + rn) * tn))
        (2 * (gn * tn) * ((tn + rn) * tn))
        (Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn)
        (∑ j ∈ Finset.range tn, cntL (tn + rn) (tn + rn + gn) gn j)
        ((∑ i ∈ Finset.range i0, cntM (tn + rn) (tn + rn + gn) gn tn) + cntK (tn + rn) (tn + rn + gn) gn tn ρn dn
          + ∑ i ∈ Finset.range nn,
              gU (tn + rn) (tn + rn + gn) (Knat (tn + rn) (tn + rn + gn) gn tn) (nn - 1 - i))
        (Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn) a : ℕ) : ENNReal)
        * MeasureTheory.volume (ModC hu he0).carrier
      = MeasureTheory.volume (tgtT ht0 hr0 he0).carrier := by
    have hNR : (0 : ℝ) ≤ ((∑ a, cnt8 (((tn + rn) * (tn + rn + gn)) * ((tn + rn) * (tn + rn + gn)))
        (2 * ((tn + rn) * (tn + rn + gn)) * ((tn + rn) * tn)) (((tn + rn) * tn) * ((tn + rn) * tn))
        (2 * (gn * tn) * ((tn + rn) * tn))
        (Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn)
        (∑ j ∈ Finset.range tn, cntL (tn + rn) (tn + rn + gn) gn j)
        ((∑ i ∈ Finset.range i0, cntM (tn + rn) (tn + rn + gn) gn tn) + cntK (tn + rn) (tn + rn + gn) gn tn ρn dn
          + ∑ i ∈ Finset.range nn,
              gU (tn + rn) (tn + rn + gn) (Knat (tn + rn) (tn + rn + gn) gn tn) (nn - 1 - i))
        (Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn) a : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    rw [volModC hu he0, vol_tgtT ht0 hr0 he0, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNR,
      hsumR]
    congr 2
    simp only [ca]; ring
  obtain ⟨D, hM, hT⟩ := Erdos634.Draft.S2L.pack_exists (M := ModC hu he0) (T := tgtT ht0 hr0 he0)
    (reg8 t r e J ρ tn Jn i0 nn S1 S3) _ Rall hS_all hsub_all hvol
  have key : ∃ D : CongruentDissection (∑ a, cnt8 (((tn + rn) * (tn + rn + gn)) * ((tn + rn) * (tn + rn + gn)))
        (2 * ((tn + rn) * (tn + rn + gn)) * ((tn + rn) * tn)) (((tn + rn) * tn) * ((tn + rn) * tn))
        (2 * (gn * tn) * ((tn + rn) * tn))
        (Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn)
        (∑ j ∈ Finset.range tn, cntL (tn + rn) (tn + rn + gn) gn j)
        ((∑ i ∈ Finset.range i0, cntM (tn + rn) (tn + rn + gn) gn tn) + cntK (tn + rn) (tn + rn + gn) gn tn ρn dn
          + ∑ i ∈ Finset.range nn,
              gU (tn + rn) (tn + rn + gn) (Knat (tn + rn) (tn + rn + gn) gn tn) (nn - 1 - i))
        (Knat (tn + rn) (tn + rn + gn) gn tn * Knat (tn + rn) (tn + rn + gn) gn tn) a),
      D.model = ModC hu he0 ∧ D.target = tgtT ht0 hr0 he0 := ⟨D, hM, hT⟩
  rw [sum_cnt8] at key
  exact key

/-! ## The seeds for naturals, and every scale `M ≥ v` -/

/-- **The residue seed**: `W` of the member `(u, v) = (t + r, t + r + g)` at the scale `v + t`. -/
theorem wTilable_seed_par {t r e J ρ : ℝ} {tn rn gn Jn ρn i0 nn dn : ℕ}
    (P : Par t r e J ρ tn rn gn Jn ρn i0 nn dn) :
    WTilable (tn + rn) (tn + rn + gn) (tn + rn + gn + tn) := by
  obtain ⟨D, hM, hT⟩ := seed_exists P
  have ht0 := P.ht0
  have hr0 := P.hr0
  have he0 := P.he0
  have hu := P.hu
  have h1 : (tn + rn) ^ 2 ≤ 2 * (tn + rn + gn) ^ 2 := by nlinarith [Nat.zero_le gn, Nat.zero_le (tn + rn)]
  have hN : total tn rn gn ρn dn i0 nn = (2 * (tn + rn + gn) ^ 2 - (tn + rn) ^ 2) * (tn + rn + gn + tn) ^ 2 := by
    have h := count_id tn rn gn Jn ρn i0 nn dn P.htn P.hgn P.hJ P.hd P.hi0 P.hnn
    have : ((total tn rn gn ρn dn i0 nn : ℕ) : ℝ)
        = (((2 * (tn + rn + gn) ^ 2 - (tn + rn) ^ 2) * (tn + rn + gn + tn) ^ 2 : ℕ) : ℝ) := by
      rw [h, Nat.cast_mul, Nat.cast_sub h1]; push_cast; ring
    exact_mod_cast this
  have key : ∃ D : CongruentDissection (total tn rn gn ρn dn i0 nn),
      HasSides D.target (((tn + rn + gn + tn : ℕ) : ℝ) * (((tn + rn + gn : ℕ) : ℝ)
          * ((((tn + rn + gn : ℕ) : ℝ)) ^ 2 - (((tn + rn : ℕ) : ℝ)) ^ 2)))
        (((tn + rn + gn + tn : ℕ) : ℝ) * ((((tn + rn : ℕ) : ℝ))
          * (2 * (((tn + rn + gn : ℕ) : ℝ)) ^ 2 - (((tn + rn : ℕ) : ℝ)) ^ 2)))
        (((tn + rn + gn + tn : ℕ) : ℝ) * (((tn + rn + gn : ℕ) : ℝ)) ^ 3) ∧
      HasSides D.model ((((tn + rn : ℕ) : ℝ)) * ((tn + rn + gn : ℕ) : ℝ))
        ((((tn + rn + gn : ℕ) : ℝ)) ^ 2 - (((tn + rn : ℕ) : ℝ)) ^ 2) ((((tn + rn + gn : ℕ) : ℝ)) ^ 2) := by
    obtain ⟨t01, t12, t02⟩ := tgtT_sides ht0 hr0 he0
    obtain ⟨m01, m12, m02⟩ := ModC_sides hu he0
    have hTs : HasSides D.target ((t + r + e) * (e * (2 * t + 2 * r + e)) * (t + r + e + t))
        ((t + r + e) ^ 3 * (t + r + e + t))
        ((t + r) * ((t + r) ^ 2 + 4 * (t + r) * e + 2 * e ^ 2) * (t + r + e + t)) :=
      ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hT]; exact t12,
        by simp only [Equiv.refl_apply]; rw [hT, dist_comm]; exact t02,
        by simp only [Equiv.refl_apply]; rw [hT]; exact t01⟩
    have hMs : HasSides D.model ((t + r + e) ^ 2) (cb (t + r) e) (ca (t + r) e) :=
      ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hM]; exact m12,
        by simp only [Equiv.refl_apply]; rw [hM, dist_comm]; exact m02,
        by simp only [Equiv.refl_apply]; rw [hM]; exact m01⟩
    refine ⟨D, hasSides_congr (hasSides_rot (hasSides_swap hTs)) ?_ ?_ ?_,
      hasSides_congr (hasSides_swap (hasSides_rot hMs)) ?_ ?_ ?_⟩
    · rw [P.et, P.er, P.ee]; push_cast <;> ring
    · rw [P.et, P.er, P.ee]; push_cast <;> ring
    · rw [P.et, P.er, P.ee]; push_cast <;> ring
    · simp only [ca]; rw [P.et, P.er, P.ee]; push_cast <;> ring
    · simp only [cb]; rw [P.et, P.er, P.ee]; push_cast <;> ring
    · rw [P.et, P.er, P.ee]; push_cast <;> ring
  rw [hN] at key
  exact key

/-- **The residue seeds.**  For coprime `u < v` and `1 ≤ t < u`: `W` at the scale `v + t`. -/
theorem wTilable_residue (u v t : ℕ) (huv : u < v) (hco : Nat.Coprime u v) (ht1 : 1 ≤ t) (htu : t < u) :
    WTilable u v (v + t) := by
  obtain ⟨rn, rfl⟩ : ∃ rn, u = t + rn := ⟨u - t, by omega⟩
  obtain ⟨gn, rfl⟩ : ∃ gn, v = t + rn + gn := ⟨v - (t + rn), by omega⟩
  have hrn : 1 ≤ rn := by omega
  have hgn : 1 ≤ gn := by omega
  have hvpos : 0 < t + rn + gn := by omega
  -- the kink: u m = v J + ρ
  have hdm := Nat.div_add_mod ((t + rn) * (t + rn + gn + t)) (t + rn + gn)
  have hρlt := Nat.mod_lt ((t + rn) * (t + rn + gn + t)) hvpos
  have hρ1 : 1 ≤ (t + rn) * (t + rn + gn + t) % (t + rn + gn) := by
    by_contra h0
    have h0' : (t + rn) * (t + rn + gn + t) % (t + rn + gn) = 0 := by omega
    have hdv : (t + rn + gn) ∣ (t + rn) * (t + rn + gn + t) := Nat.dvd_of_mod_eq_zero h0'
    have hdv2 : (t + rn + gn) ∣ (t + rn + gn + t) := (Nat.Coprime.symm hco).dvd_of_dvd_mul_left hdv
    have hdv3 : (t + rn + gn) ∣ t := (Nat.dvd_add_right (dvd_refl _)).mp hdv2
    have := Nat.le_of_dvd (by omega) hdv3
    omega
  have hJlo : t ≤ (t + rn) * (t + rn + gn + t) / (t + rn + gn) := by
    rw [Nat.le_div_iff_mul_le hvpos]
    nlinarith [Nat.zero_le rn, Nat.zero_le gn, Nat.zero_le t]
  have hJhi : (t + rn) * (t + rn + gn + t) / (t + rn + gn) + 1 ≤ t + rn + t := by
    have : (t + rn) * (t + rn + gn + t) / (t + rn + gn) < t + rn + t := by
      rw [Nat.div_lt_iff_lt_mul hvpos]
      nlinarith [Nat.mul_pos hgn ht1]
    omega
  refine wTilable_seed_par (t := (t : ℝ)) (r := (rn : ℝ)) (e := (gn : ℝ))
    (J := (((t + rn) * (t + rn + gn + t) / (t + rn + gn) : ℕ) : ℝ))
    (ρ := (((t + rn) * (t + rn + gn + t) % (t + rn + gn) : ℕ) : ℝ))
    (Jn := (t + rn) * (t + rn + gn + t) / (t + rn + gn))
    (ρn := (t + rn) * (t + rn + gn + t) % (t + rn + gn))
    (i0 := (t + rn) * (t + rn + gn + t) / (t + rn + gn) - t)
    (nn := t + rn + t - 1 - (t + rn) * (t + rn + gn + t) / (t + rn + gn))
    (dn := t + rn + gn - (t + rn) * (t + rn + gn + t) % (t + rn + gn))
    { et := rfl, er := rfl, ee := rfl, eJ := rfl, eρ := rfl, htn := ht1, hrn := hrn, hgn := hgn,
      hJ := hdm.symm, hρ1 := hρ1, hd := by omega, hd1 := by omega, hi0 := by omega, hnn := by omega }

/-- collars: from one scale `T ≥ v` to `T + q u` -/
theorem wTilable_add_mul (u g T : ℕ) (hu : 0 < u) (hg : 0 < g) (hT : u + g ≤ T) (h : WTilable u (u + g) T) :
    ∀ q : ℕ, WTilable u (u + g) (T + q * u)
  | 0 => by simpa using h
  | q + 1 => by
      have ih := wTilable_add_mul u g T hu hg hT h q
      obtain ⟨s, hs⟩ : ∃ s, T + q * u = g + s := ⟨T + q * u - g, by omega⟩
      rw [hs] at ih
      have h2 := Erdos634.Draft.CollarG.collar_nat u g s hu hg (by omega) ih
      have e2 : g + s + u = T + (q + 1) * u := by rw [← hs]; ring
      rwa [e2] at h2

/-- **`W` of every member at every scale `M ≥ v`.** -/
theorem wTilable_ge (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) (hco : Nat.Coprime u v) :
    ∀ M, v ≤ M → WTilable u v M := by
  intro M hM
  obtain ⟨g, rfl⟩ : ∃ g, v = u + g := ⟨v - u, by omega⟩
  have hg : 0 < g := by omega
  have hdm := Nat.div_add_mod (M - (u + g)) u
  have hlt := Nat.mod_lt (M - (u + g)) hu
  by_cases h0 : (M - (u + g)) % u = 0
  · have hMe : M = (u + g) + ((M - (u + g)) / u) * u := by
      have : u * ((M - (u + g)) / u) = (M - (u + g)) / u * u := Nat.mul_comm _ _
      omega
    rw [hMe]
    exact wTilable_add_mul u g (u + g) hu hg le_rfl
      (Erdos634.Draft.CollarG.wTilable_seed u (u + g) hu huv) _
  · have hMe : M = (u + g + (M - (u + g)) % u) + ((M - (u + g)) / u) * u := by
      have : u * ((M - (u + g)) / u) = (M - (u + g)) / u * u := Nat.mul_comm _ _
      omega
    rw [hMe]
    exact wTilable_add_mul u g (u + g + (M - (u + g)) % u) hu hg (by omega)
      (wTilable_residue u (u + g) ((M - (u + g)) % u) huv hco (by omega) hlt) _

/-- **The base-β target of every member has a tiling at every scale `M ≥ f`**: for coprime `1 ≤ e < f` and
`M ≥ f`, the isosceles triangle with legs `M f³` and base `M e (3f² − e²)` is cut into congruent triangles with sides
`(ef, f² − e², f²)`. -/
theorem betaTilable_ge (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    ∀ M, f ≤ M → BetaTilable e f M := by
  intro M hM
  have hw := wTilable_ge e f he hef hco M hM
  obtain ⟨g, rfl⟩ : ∃ g, f = e + g := ⟨f - e, by omega⟩
  exact Erdos634.Draft.CollarG.betaTilable_of_wTilable e g M he (by omega) (by omega) hw

/-- the threshold statement at every scale `M ≥ f` -/
theorem thresholdAt_ge (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (M : ℕ) (hM : f ≤ M) :
    ThresholdAt e f M :=
  ⟨fun _ => hM, fun _ => betaTilable_ge e f he hef hco M hM⟩

open Erdos634.Draft.UniformThreshold (UniformThreshold threshold_one) in
/-- **The threshold statement of a member is equivalent to the absence of tilings at the scales `2 ≤ M < f`.** -/
theorem threshold_iff_small (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    (∀ M, 1 ≤ M → ThresholdAt e f M) ↔ (∀ M, 2 ≤ M → M < f → ¬ BetaTilable e f M) := by
  constructor
  · intro h M h2 hMf hB
    have := (h M (by omega)).mp hB
    omega
  · intro h M hM
    by_cases h1 : f ≤ M
    · exact thresholdAt_ge e f he hef hco M h1
    · by_cases h2 : M = 1
      · rw [h2]; exact threshold_one hco he hef
      · exact ⟨fun hB => absurd hB (h M (by omega) (by omega)), fun hfM => absurd hfM h1⟩

open Erdos634.Draft.UniformThreshold (UniformThreshold) in
/-- **The statement under test**, for all members: it is equivalent to the absence of tilings below the scale `f`. -/
theorem uniformThreshold_iff_small :
    UniformThreshold ↔ ∀ e f M : ℕ, 1 ≤ e → e < f → Nat.Coprime e f → 2 ≤ M → M < f → ¬ BetaTilable e f M := by
  constructor
  · intro h e f M he hef hco h2 hMf
    exact (threshold_iff_small e f he hef hco).mp (fun M hM => h e f M he hef hco hM) M h2 hMf
  · intro h e f M he hef hco hM
    exact (threshold_iff_small e f he hef hco).mpr (fun M h2 hMf => h e f M he hef hco h2 hMf) M hM

end Erdos634.Draft.Residue

#print axioms Erdos634.Draft.Residue.seed_exists
#print axioms Erdos634.Draft.Residue.wTilable_residue
#print axioms Erdos634.Draft.Residue.wTilable_ge
#print axioms Erdos634.Draft.Residue.betaTilable_ge
#print axioms Erdos634.Draft.Residue.threshold_iff_small
#print axioms Erdos634.Draft.Residue.uniformThreshold_iff_small
