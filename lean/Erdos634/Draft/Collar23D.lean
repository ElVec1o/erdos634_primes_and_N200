-- Draft/Collar23D.lean -- (2,3) collar, part D: the strip Z(g0) = T(g0+1) minus T(g0) is dissected by a C-slices, one cap and b B-slices
-- whenever 2a + 3b + 4 = 5 g0.  UNAUDITED.  No sorry, no native_decide.  NOT imported by All.
-- Credit: B. Herdt (template), Beeson-Rosu, Paliy; the strip structure is the project's AI assistant P1 (internal working notes).
import Erdos634.Draft.Collar23C
import Erdos634.RegionDissection

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling
open Erdos634.Draft.CollarParam (RTiling.cast RTiling.castN)

namespace Erdos634.Draft.Collar23

/-! ## Regions as explicit inequalities -/

theorem mem_cs (z : ℝ × ℝ) : z ∈ Rset csReg ↔
    0 ≤ z.1 ∧ z.1 ≤ 6 ∧ 0 ≤ 2 * z.1 + 3 * z.2 ∧ 2 * z.1 + 3 * z.2 ≤ 30 := by
  simp only [Rset, csReg, Set.mem_setOf_eq, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  push_cast
  constructor
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem mem_bs (z : ℝ × ℝ) : z ∈ Rset bsReg ↔
    0 ≤ z.2 ∧ z.2 ≤ 6 ∧ 0 ≤ 2 * z.1 + 3 * z.2 ∧ 2 * z.1 + 3 * z.2 ≤ 30 := by
  simp only [Rset, bsReg, Set.mem_setOf_eq, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  push_cast
  constructor
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem mem_cap (z : ℝ × ℝ) : z ∈ Rset capReg ↔
    0 ≤ z.1 ∧ -8 ≤ z.2 ∧ 0 ≤ 2 * z.1 + 3 * z.2 ∧ 2 * z.1 + 3 * z.2 ≤ 30 := by
  simp only [Rset, capReg, Set.mem_setOf_eq, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  push_cast
  constructor
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem mem_Sh (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) (z : ℝ × ℝ) : z ∈ Sh v S ↔ (z - v) ∈ S := Iff.rfl

/-- The empty region tiling. -/
def emptyRT : RTiling (∅ : Set Plane) M23 0 where
  tile := fun i => i.elim0
  covers := by simp
  disj := fun i => i.elim0
  cong := fun i => i.elim0

def Tset23 (m : ℝ) : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ 2 * z.1 + 3 * z.2 ≤ 30 * m}
def Zset (g : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ 30 * g ≤ 2 * z.1 + 3 * z.2 ∧ 2 * z.1 + 3 * z.2 ≤ 30 * g + 30}

/-! ## C-bands: a slices, `x in [0, 6a]` -/

def CBr (g : ℝ) : ℕ → Set (ℝ × ℝ)
  | 0 => ∅
  | a + 1 => CBr g a ∪ Sh (6 * (a : ℝ), 10 * g - 4 * (a : ℝ)) (Rset csReg)

theorem mem_CBr (g : ℝ) (a : ℕ) (z : ℝ × ℝ) : z ∈ CBr g a ↔
    0 < a ∧ 0 ≤ z.1 ∧ z.1 ≤ 6 * (a : ℝ) ∧ 30 * g ≤ 2 * z.1 + 3 * z.2 ∧ 2 * z.1 + 3 * z.2 ≤ 30 * g + 30 := by
  induction a with
  | zero => simp [CBr]
  | succ a ih =>
    simp only [CBr, Set.mem_union, ih, mem_Sh, mem_cs]
    simp only [Prod.fst_sub, Prod.snd_sub]
    push_cast
    constructor
    · rintro (⟨h0, h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨by omega, h1, by linarith, h3, h4⟩
      · have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
        exact ⟨by omega, by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h0, h1, h2, h3, h4⟩
      by_cases hx : z.1 ≤ 6 * (a : ℝ)
      · rcases Nat.eq_zero_or_pos a with rfl | hapos
        · right; simp at hx ⊢; refine ⟨by linarith, by linarith, by linarith, by linarith⟩
        · left; exact ⟨hapos, h1, hx, h3, h4⟩
      · right
        rw [not_le] at hx
        refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem CBr_le (g : ℝ) (a : ℕ) : ∀ p ∈ CBr g a, p.1 ≤ 6 * (a : ℝ) := fun p hp => ((mem_CBr g a p).mp hp).2.2.1

noncomputable def cBand (g : ℝ) : (a : ℕ) → RTiling (Phi '' CBr g a) M23 (4 * a)
  | 0 => RTiling.castN (by norm_num) (RTiling.cast (by simp [CBr]) emptyRT)
  | a + 1 => by
      have hs := shiftR csRT (6 * (a : ℝ), 10 * g - 4 * (a : ℝ))
      have hd : Disjoint (interior (Phi '' CBr g a))
          (interior (Phi '' Sh (6 * (a : ℝ), 10 * g - 4 * (a : ℝ)) (Rset csReg))) := by
        refine disjoint_image (interior_disj_lin (-1) 0 (-(6 * (a : ℝ))) (by norm_num) ?_ ?_)
        · intro p hp; have := CBr_le g a p hp; linarith
        · intro p hp
          rw [mem_Sh, mem_cs] at hp
          try simp only [Prod.fst_sub] at hp
          linarith [hp.1]
      have U := union (cBand g a) hs hd
      refine RTiling.castN (by ring) (RTiling.cast ?_ U)
      rw [← Set.image_union]; rfl

/-! ## B-bands: b slices, `y in [0, 6b]` -/

def BBr (g : ℝ) : ℕ → Set (ℝ × ℝ)
  | 0 => ∅
  | b + 1 => BBr g b ∪ Sh (15 * g - 9 * (b : ℝ), 6 * (b : ℝ)) (Rset bsReg)

theorem mem_BBr (g : ℝ) (b : ℕ) (z : ℝ × ℝ) : z ∈ BBr g b ↔
    0 < b ∧ 0 ≤ z.2 ∧ z.2 ≤ 6 * (b : ℝ) ∧ 30 * g ≤ 2 * z.1 + 3 * z.2 ∧ 2 * z.1 + 3 * z.2 ≤ 30 * g + 30 := by
  induction b with
  | zero => simp [BBr]
  | succ b ih =>
    simp only [BBr, Set.mem_union, ih, mem_Sh, mem_bs]
    simp only [Prod.fst_sub, Prod.snd_sub]
    push_cast
    constructor
    · rintro (⟨h0, h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨by omega, h1, by linarith, h3, h4⟩
      · have : (0 : ℝ) ≤ b := Nat.cast_nonneg b
        exact ⟨by omega, by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h0, h1, h2, h3, h4⟩
      by_cases hy : z.2 ≤ 6 * (b : ℝ)
      · rcases Nat.eq_zero_or_pos b with rfl | hbpos
        · right; simp at hy ⊢; refine ⟨by linarith, by linarith, by linarith, by linarith⟩
        · left; exact ⟨hbpos, h1, hy, h3, h4⟩
      · right
        rw [not_le] at hy
        refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem BBr_le (g : ℝ) (b : ℕ) : ∀ p ∈ BBr g b, p.2 ≤ 6 * (b : ℝ) := fun p hp => ((mem_BBr g b p).mp hp).2.2.1

noncomputable def bBand (g : ℝ) : (b : ℕ) → RTiling (Phi '' BBr g b) M23 (6 * b)
  | 0 => RTiling.castN (by norm_num) (RTiling.cast (by simp [BBr]) emptyRT)
  | b + 1 => by
      have hs := shiftR bsRT (15 * g - 9 * (b : ℝ), 6 * (b : ℝ))
      have hd : Disjoint (interior (Phi '' BBr g b))
          (interior (Phi '' Sh (15 * g - 9 * (b : ℝ), 6 * (b : ℝ)) (Rset bsReg))) := by
        refine disjoint_image (interior_disj_lin 0 (-1) (-(6 * (b : ℝ))) (by norm_num) ?_ ?_)
        · intro p hp; have := BBr_le g b p hp; linarith
        · intro p hp
          rw [mem_Sh, mem_bs] at hp
          try simp only [Prod.snd_sub] at hp
          linarith [hp.1]
      have U := union (bBand g b) hs hd
      refine RTiling.castN (by ring) (RTiling.cast ?_ U)
      rw [← Set.image_union]; rfl

/-! ## The strip -/

/-- The strip region assembled from `a` C-slices, the shifted cap, `b` B-slices. -/
def ZReg (g : ℝ) (a b : ℕ) : Set (ℝ × ℝ) :=
  (CBr g a ∪ Sh (6 * (a : ℝ), 10 * g - 4 * (a : ℝ)) (Rset capReg)) ∪ BBr g b

theorem mem_capS (g : ℝ) (a : ℕ) (z : ℝ × ℝ) :
    z ∈ Sh (6 * (a : ℝ), 10 * g - 4 * (a : ℝ)) (Rset capReg) ↔
      6 * (a : ℝ) ≤ z.1 ∧ 10 * g - 4 * (a : ℝ) - 8 ≤ z.2 ∧ 30 * g ≤ 2 * z.1 + 3 * z.2 ∧
        2 * z.1 + 3 * z.2 ≤ 30 * g + 30 := by
  rw [mem_Sh, mem_cap]
  simp only [Prod.fst_sub, Prod.snd_sub]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem ZReg_eq (g : ℝ) (a b : ℕ) (hab : 2 * (a : ℝ) + 3 * (b : ℝ) + 4 = 5 * g) :
    ZReg g a b = Zset g := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  ext z
  simp only [ZReg, Zset, Set.mem_union, mem_CBr, mem_BBr, mem_capS, Set.mem_setOf_eq]
  constructor
  · rintro ((⟨h0, h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) | ⟨h0, h1, h2, h3, h4⟩)
    · exact ⟨h1, by linarith, h3, h4⟩
    · exact ⟨by linarith, by linarith, h3, h4⟩
    · exact ⟨by linarith, h1, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases hx : z.1 ≤ 6 * (a : ℝ) ∧ 0 < a
    · left; left; exact ⟨hx.2, h1, hx.1, h3, h4⟩
    · by_cases hy : z.2 ≤ 6 * (b : ℝ) ∧ 0 < b
      · right; exact ⟨hy.2, h2, hy.1, h3, h4⟩
      · left; right
        refine ⟨?_, ?_, h3, h4⟩
        · by_contra hlt
          rw [not_le] at hlt
          have ha0 : a = 0 := by
            by_contra hne
            exact hx ⟨hlt.le, Nat.pos_of_ne_zero hne⟩
          subst ha0; push_cast at hlt hab; linarith
        · by_contra hlt
          rw [not_le] at hlt
          have hb0 : b = 0 := by
            by_contra hne
            exact hy ⟨by linarith, Nat.pos_of_ne_zero hne⟩
          subst hb0
          push_cast at hlt hab
          linarith

/-- **The strip tiling.** `Z(g) = {x,y >= 0, 30 g <= 2x+3y <= 30 g + 30}` is dissected by `4a + 13 + 6b` copies of the
tile, `a` C-slices (4 tiles each), the 13-tile cap, `b` B-slices (6 tiles each), whenever `2a + 3b + 4 = 5 g`. -/
noncomputable def ZRT (g : ℝ) (a b : ℕ) (hab : 2 * (a : ℝ) + 3 * (b : ℝ) + 4 = 5 * g) :
    RTiling (Phi '' Zset g) M23 (4 * a + 13 + 6 * b) := by
  have hcap := shiftR capRT (6 * (a : ℝ), 10 * g - 4 * (a : ℝ))
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hd1 : Disjoint (interior (Phi '' CBr g a))
      (interior (Phi '' Sh (6 * (a : ℝ), 10 * g - 4 * (a : ℝ)) (Rset capReg))) := by
    refine disjoint_image (interior_disj_lin (-1) 0 (-(6 * (a : ℝ))) (by norm_num) ?_ ?_)
    · intro p hp; have := CBr_le g a p hp; linarith
    · intro p hp
      rw [mem_capS] at hp
      linarith [hp.1]
  have U1 := union (cBand g a) hcap hd1
  have hd2 : Disjoint (interior (Phi '' CBr g a ∪ Phi '' Sh (6 * (a : ℝ), 10 * g - 4 * (a : ℝ)) (Rset capReg)))
      (interior (Phi '' BBr g b)) := by
    rw [← Set.image_union]
    refine disjoint_image (interior_disj_lin 0 1 (6 * (b : ℝ)) (by norm_num) ?_ ?_)
    · rintro p (hp | hp)
      · rw [mem_CBr] at hp
        linarith [hp.2.2.1, hp.2.2.2.1]
      · rw [mem_capS] at hp
        linarith [hp.2.1]
    · intro p hp; have := BBr_le g b p hp; linarith
  have U2 := union U1 (bBand g b) hd2
  refine RTiling.castN (by ring) (RTiling.cast ?_ U2)
  rw [← Set.image_union, ← Set.image_union]
  congr 1
  have := ZReg_eq g a b hab
  exact this

/-! ## Existence of `(a, b)` -/

theorem exists_ab (g : ℕ) (hg : 2 ≤ g) : ∃ a b : ℕ, 2 * a + 3 * b + 4 = 5 * g := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' g
  · exact ⟨5 * k - 2, 0, by omega⟩
  · exact ⟨5 * k - 1, 1, by omega⟩

/-- **(ii) The strip tiling for every `g >= 2`**, with exactly `5 (2 g + 1)` tiles. -/
theorem Z_tiling (g : ℕ) (hg : 2 ≤ g) : Nonempty (RTiling (Phi '' Zset (g : ℝ)) M23 (5 * (2 * g + 1))) := by
  obtain ⟨a, b, hab⟩ := exists_ab g hg
  have hr : 2 * (a : ℝ) + 3 * (b : ℝ) + 4 = 5 * (g : ℝ) := by exact_mod_cast hab
  exact ⟨RTiling.castN (by omega) (ZRT (g : ℝ) a b hr)⟩

/-! ## Region dissection forms of the cap and the slices -/

open Erdos634.RegionDissection in
/-- An `RTiling` as a `CongruentRegionDissection`. -/
noncomputable def toCRD23 {S : Set Plane} {N : ℕ} (R : RTiling S M23 N) : CongruentRegionDissection N where
  region := S
  tile := R.tile
  covers := R.covers
  interiors_disjoint := R.disj
  model := M23
  tiles_congruent := R.cong

open Erdos634.RegionDissection in
/-- **(i) The 13-tile cap as a `CongruentRegionDissection` of its trapezoid** (vertices (0,0),(12,-8),(27,-8),(0,10) in skew
coordinates). -/
noncomputable def capCRD : CongruentRegionDissection 13 := toCRD23 capRT

open Erdos634.RegionDissection in
noncomputable def csCRD : CongruentRegionDissection 4 := toCRD23 csRT
open Erdos634.RegionDissection in
noncomputable def bsCRD : CongruentRegionDissection 6 := toCRD23 bsRT

theorem capCRD_region : capCRD.region = Phi '' Rset capReg := rfl
theorem csCRD_region : csCRD.region = Phi '' Rset csReg := rfl
theorem bsCRD_region : bsCRD.region = Phi '' Rset bsReg := rfl

end Erdos634.Draft.Collar23

#print axioms Erdos634.Draft.Collar23.ZRT
#print axioms Erdos634.Draft.Collar23.Z_tiling
#print axioms Erdos634.Draft.Collar23.capCRD
