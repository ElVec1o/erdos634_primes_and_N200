-- Draft/Collar23B.lean -- (2,3) collar, part B: integer tile tables.  A table of triangles with integer skew coordinates is
-- checked by `decide` (congruence to the model (5,6,4), non-degeneracy, a separating edge line for every pair, vertices in the
-- region); only the covering is supplied (by a decision tree of linear case splits).  Output: an `RTiling` of `Phi '' Rset L`.
-- UNAUDITED.  No sorry, no native_decide.  NOT imported by All.  Credit: Herdt (template), Beeson-Rosu, Paliy; the project's AI assistant P1.
import Erdos634.Draft.Collar23A

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling
open Erdos634.Draft.CollarParam (RTiling.cast RTiling.castN)
open Erdos634.Draft.S2L (hull_le hull_ge mem_hull3')

namespace Erdos634.Draft.Collar23

abbrev ZP := ℤ × ℤ

structure ZT where
  a : ZP
  b : ZP
  c : ZP

def zcr (o p q : ZP) : ℤ := (p.1 - o.1) * (q.2 - o.2) - (p.2 - o.2) * (q.1 - o.1)
def zq (p q : ZP) : ℤ := 2 * (p.1 - q.1) ^ 2 + 3 * (p.1 - q.1) * (p.2 - q.2) + 2 * (p.2 - q.2) ^ 2

/-- twice the squared lengths (5,6,4)^2: the model tile `(4,5,6)` in the order (01,12,20). -/
def ZT.model (t : ZT) : Prop := zq t.a t.b = 50 ∧ zq t.b t.c = 72 ∧ zq t.c t.a = 32
def ZT.nd (t : ZT) : Prop := zcr t.a t.b t.c ≠ 0

instance (t : ZT) : Decidable t.model := by unfold ZT.model; infer_instance
instance (t : ZT) : Decidable t.nd := by unfold ZT.nd; infer_instance

/-- `o e w` are three vertices of `s`; `t` lies weakly on the other side of the line `o e` than `w`. -/
def sepE (o e w : ZP) (t : ZT) : Prop :=
  zcr o e w * zcr o e t.a ≤ 0 ∧ zcr o e w * zcr o e t.b ≤ 0 ∧ zcr o e w * zcr o e t.c ≤ 0

def sep (s t : ZT) : Prop :=
  sepE s.a s.b s.c t ∨ sepE s.b s.c s.a t ∨ sepE s.c s.a s.b t ∨
  sepE t.a t.b t.c s ∨ sepE t.b t.c t.a s ∨ sepE t.c t.a t.b s

instance (o e w : ZP) (t : ZT) : Decidable (sepE o e w t) := by unfold sepE; infer_instance
instance (s t : ZT) : Decidable (sep s t) := by unfold sep; infer_instance

/-- constraints `0 ≤ A x + B y + C`. -/
abbrev Cons := List (ℤ × ℤ × ℤ)

def inR (L : Cons) (p : ZP) : Prop := ∀ c ∈ L, 0 ≤ c.1 * p.1 + c.2.1 * p.2 + c.2.2
instance (L : Cons) (p : ZP) : Decidable (inR L p) := by unfold inR; infer_instance

def Rset (L : Cons) : Set (ℝ × ℝ) :=
  {z | ∀ c ∈ L, 0 ≤ (c.1 : ℝ) * z.1 + (c.2.1 : ℝ) * z.2 + (c.2.2 : ℝ)}

def pt (p : ZP) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

def H3 (o e w : ZP) : Set (ℝ × ℝ) := convexHull ℝ ({pt o, pt e, pt w} : Set (ℝ × ℝ))
def ZT.H (t : ZT) : Set (ℝ × ℝ) := H3 t.a t.b t.c

theorem cr_cast (o p q : ZP) : cr (pt o) (pt p) (pt q) = (zcr o p q : ℝ) := by
  simp only [cr, zcr, pt]; push_cast; ring

noncomputable def ZT.tri (t : ZT) (h : t.nd) : Tri :=
  TT (pt t.a) (pt t.b) (pt t.c) (by rw [cr_cast]; exact_mod_cast h)

theorem ZT.tri_carrier (t : ZT) (h : t.nd) : (t.tri h).carrier = Phi '' t.H := by
  unfold ZT.tri ZT.H H3
  exact TT_carrier _ _ _ _

/-! ## The region `Rset L` -/

theorem Rset_convex (L : Cons) : Convex ℝ (Rset L) := by
  intro x hx y hy s t hs ht hst
  intro c hc
  have h1 := hx c hc
  have h2 := hy c hc
  have e : (c.1 : ℝ) * (s • x + t • y).1 + (c.2.1 : ℝ) * (s • x + t • y).2 + (c.2.2 : ℝ)
      = s * ((c.1 : ℝ) * x.1 + (c.2.1 : ℝ) * x.2 + (c.2.2 : ℝ))
        + t * ((c.1 : ℝ) * y.1 + (c.2.1 : ℝ) * y.2 + (c.2.2 : ℝ)) := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have : t = 1 - s := by linarith
    subst this; ring
  rw [e]
  positivity

theorem inR_cast {L : Cons} {p : ZP} (h : inR L p) : pt p ∈ Rset L := by
  intro c hc
  have := h c hc
  simp only [pt]
  exact_mod_cast this

theorem H3_subset {L : Cons} {o e w : ZP} (ho : inR L o) (he : inR L e) (hw : inR L w) :
    H3 o e w ⊆ Rset L := by
  refine convexHull_min ?_ (Rset_convex L)
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact inR_cast ho
  · exact inR_cast he
  · exact inR_cast hw

/-! ## Separation -/

theorem sepE_sound (o e w : ZP) (t : ZT) (hnd : zcr o e w ≠ 0) (h : sepE o e w t) :
    Disjoint (interior (H3 o e w)) (interior t.H) := by
  obtain ⟨h1, h2, h3⟩ := h
  set σ : ℝ := (zcr o e w : ℝ) with hσ
  have hσ0 : σ ≠ 0 := by rw [hσ]; exact_mod_cast hnd
  set A : ℝ := -(σ * ((e.2 : ℝ) - o.2)) with hA
  set B : ℝ := σ * ((e.1 : ℝ) - o.1) with hB
  set c : ℝ := A * o.1 + B * o.2 with hc
  have hpos : 0 < A ^ 2 + B ^ 2 := by
    have hne : ((e.1 : ℝ) - o.1) ^ 2 + ((e.2 : ℝ) - o.2) ^ 2 ≠ 0 := by
      intro hz
      have a1 : (e.1 : ℝ) - o.1 = 0 := by nlinarith [sq_nonneg ((e.1 : ℝ) - o.1), sq_nonneg ((e.2 : ℝ) - o.2)]
      have a2 : (e.2 : ℝ) - o.2 = 0 := by nlinarith [sq_nonneg ((e.1 : ℝ) - o.1), sq_nonneg ((e.2 : ℝ) - o.2)]
      apply hnd
      simp only [zcr]
      have : ((e.1 - o.1 : ℤ) : ℝ) = 0 := by push_cast; exact a1
      have : ((e.2 - o.2 : ℤ) : ℝ) = 0 := by push_cast; exact a2
      have b1 : e.1 - o.1 = 0 := by exact_mod_cast ‹((e.1 - o.1 : ℤ) : ℝ) = 0›
      have b2 : e.2 - o.2 = 0 := by exact_mod_cast this
      rw [b1, b2]; ring
    have : A ^ 2 + B ^ 2 = σ ^ 2 * (((e.1 : ℝ) - o.1) ^ 2 + ((e.2 : ℝ) - o.2) ^ 2) := by
      rw [hA, hB]; ring
    rw [this]
    have h1' : 0 < σ ^ 2 := by positivity
    have h2' : 0 < ((e.1 : ℝ) - o.1) ^ 2 + ((e.2 : ℝ) - o.2) ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hne)
    positivity
  have key : ∀ q : ZP, A * (q.1 : ℝ) + B * (q.2 : ℝ) - c = σ * (zcr o e q : ℝ) := by
    intro q; rw [hc, hA, hB]; simp only [zcr]; push_cast; ring
  refine interior_disj_lin A B c hpos ?_ ?_
  · -- H3 o e w: c ≤ ℓ
    have := hull_ge (S := ({pt o, pt e, pt w} : Set (ℝ × ℝ))) A B c (by
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · have z : zcr o e o = 0 := by simp only [zcr]; ring
        have k0 : A * (o.1 : ℝ) + B * (o.2 : ℝ) - c = 0 := by rw [key o, z]; simp
        simp only [pt]; linarith
      · have z : zcr o e e = 0 := by simp only [zcr]; ring
        have k0 : A * (e.1 : ℝ) + B * (e.2 : ℝ) - c = 0 := by rw [key e, z]; simp
        simp only [pt]; linarith
      · have := key w; simp only [pt]
        rw [← hσ] at this
        nlinarith [sq_nonneg σ])
    exact this
  · have := hull_le (S := ({pt (t.a), pt (t.b), pt (t.c)} : Set (ℝ × ℝ))) A B c (by
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · have := key t.a; simp only [pt]
        have h1r : σ * (zcr o e t.a : ℝ) ≤ 0 := by rw [hσ]; exact_mod_cast h1
        linarith
      · have := key t.b; simp only [pt]
        have h1r : σ * (zcr o e t.b : ℝ) ≤ 0 := by rw [hσ]; exact_mod_cast h2
        linarith
      · have := key t.c; simp only [pt]
        have h1r : σ * (zcr o e t.c : ℝ) ≤ 0 := by rw [hσ]; exact_mod_cast h3
        linarith)
    exact this

theorem H3_rot (a b c : ZP) : H3 b c a = H3 a b c := by
  unfold H3; congr 1; ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

theorem sep_sound (s t : ZT) (hs : s.nd) (ht : t.nd) (h : sep s t) :
    Disjoint (interior s.H) (interior t.H) := by
  rcases h with h | h | h | h | h | h
  · exact sepE_sound _ _ _ _ hs h
  · have := sepE_sound s.b s.c s.a t (by
      have : zcr s.b s.c s.a = zcr s.a s.b s.c := by simp only [zcr]; ring
      rw [this]; exact hs) h
    rwa [H3_rot] at this
  · have := sepE_sound s.c s.a s.b t (by
      have : zcr s.c s.a s.b = zcr s.a s.b s.c := by simp only [zcr]; ring
      rw [this]; exact hs) h
    have e : H3 s.c s.a s.b = s.H := (H3_rot s.b s.c s.a).trans (H3_rot s.a s.b s.c)
    rwa [e] at this
  · exact (sepE_sound _ _ _ _ ht h).symm
  · have := sepE_sound t.b t.c t.a s (by
      have : zcr t.b t.c t.a = zcr t.a t.b t.c := by simp only [zcr]; ring
      rw [this]; exact ht) h
    have e : H3 t.b t.c t.a = t.H := H3_rot _ _ _
    rw [e] at this; exact this.symm
  · have := sepE_sound t.c t.a t.b s (by
      have : zcr t.c t.a t.b = zcr t.a t.b t.c := by simp only [zcr]; ring
      rw [this]; exact ht) h
    have e : H3 t.c t.a t.b = t.H := (H3_rot t.b t.c t.a).trans (H3_rot t.a t.b t.c)
    rw [e] at this; exact this.symm

/-! ## Membership in a triangle from three linear inequalities -/

def rcr (o p : ZP) (z : ℝ × ℝ) : ℝ := ((p.1 : ℝ) - o.1) * (z.2 - o.2) - ((p.2 : ℝ) - o.2) * (z.1 - o.1)

theorem memH (a b c : ZP) (s : ℝ) (z : ℝ × ℝ) (hD : 0 < s * (zcr a b c : ℝ))
    (h1 : 0 ≤ s * rcr b c z) (h2 : 0 ≤ s * rcr c a z) (h3 : 0 ≤ s * rcr a b z) :
    z ∈ H3 a b c := by
  refine mem_hull3' (s * (zcr a b c : ℝ)) (s * rcr b c z) (s * rcr c a z) (s * rcr a b z) hD h1 h2 h3 ?_ z ?_ ?_
  · simp only [rcr, zcr]; push_cast; ring
  · simp only [rcr, pt, zcr]; push_cast; ring
  · simp only [rcr, pt, zcr]; push_cast; ring

/-! ## The model tile -/

def modelZT : ZT := ⟨(0, 0), (0, 5), (6, -4)⟩
theorem modelZT_nd : modelZT.nd := by decide

noncomputable def M23 : Tri := modelZT.tri modelZT_nd

theorem ZT.congr_model (t : ZT) (h : t.nd) (hm : t.model) : (t.tri h).Congruent M23 := by
  obtain ⟨e1, e2, e3⟩ := hm
  unfold ZT.tri M23 ZT.tri
  refine TT_congruent _ _ _ _ _ _ _ _ ?_ ?_ ?_
  · simp only [pt, modelZT, zq] at *
    have : (2 * (t.a.1 - t.b.1) ^ 2 + 3 * (t.a.1 - t.b.1) * (t.a.2 - t.b.2) + 2 * (t.a.2 - t.b.2) ^ 2 : ℤ) = 50 := e1
    have h' : (2 * ((t.a.1 : ℝ) - t.b.1) ^ 2 + 3 * ((t.a.1 : ℝ) - t.b.1) * ((t.a.2 : ℝ) - t.b.2)
        + 2 * ((t.a.2 : ℝ) - t.b.2) ^ 2) = 50 := by exact_mod_cast this
    norm_num
    linarith
  · simp only [pt, modelZT, zq] at *
    have : (2 * (t.b.1 - t.c.1) ^ 2 + 3 * (t.b.1 - t.c.1) * (t.b.2 - t.c.2) + 2 * (t.b.2 - t.c.2) ^ 2 : ℤ) = 72 := e2
    have h' : (2 * ((t.b.1 : ℝ) - t.c.1) ^ 2 + 3 * ((t.b.1 : ℝ) - t.c.1) * ((t.b.2 : ℝ) - t.c.2)
        + 2 * ((t.b.2 : ℝ) - t.c.2) ^ 2) = 72 := by exact_mod_cast this
    norm_num
    linarith
  · simp only [pt, modelZT, zq] at *
    have : (2 * (t.c.1 - t.a.1) ^ 2 + 3 * (t.c.1 - t.a.1) * (t.c.2 - t.a.2) + 2 * (t.c.2 - t.a.2) ^ 2 : ℤ) = 32 := e3
    have h' : (2 * ((t.c.1 : ℝ) - t.a.1) ^ 2 + 3 * ((t.c.1 : ℝ) - t.a.1) * ((t.c.2 : ℝ) - t.a.2)
        + 2 * ((t.c.2 : ℝ) - t.a.2) ^ 2) = 32 := by exact_mod_cast this
    norm_num
    linarith

/-! ## The generic table theorem -/

/-- **A checked integer table is a region tiling.** -/
noncomputable def ztiling {n : ℕ} (tab : Fin n → ZT) (L : Cons)
    (hnd : ∀ i, (tab i).nd) (hmod : ∀ i, (tab i).model)
    (hsep : ∀ i j, i ≠ j → sep (tab i) (tab j))
    (hin : ∀ i, inR L (tab i).a ∧ inR L (tab i).b ∧ inR L (tab i).c)
    (hcov : ∀ z ∈ Rset L, ∃ i, z ∈ (tab i).H) :
    RTiling (Phi '' Rset L) M23 n where
  tile := fun i => (tab i).tri (hnd i)
  covers := by
    have e : ∀ i, ((tab i).tri (hnd i)).carrier = Phi '' (tab i).H := fun i => ZT.tri_carrier _ _
    simp only [e]
    rw [← Set.image_iUnion]
    congr 1
    apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun i => ?_
      obtain ⟨h1, h2, h3⟩ := hin i
      exact H3_subset h1 h2 h3
    · intro z hz
      obtain ⟨i, hi⟩ := hcov z hz
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
  disj := by
    intro i j hij
    show Disjoint (interior (((tab i).tri (hnd i)).carrier)) (interior (((tab j).tri (hnd j)).carrier))
    rw [ZT.tri_carrier, ZT.tri_carrier]
    exact disjoint_image (sep_sound _ _ (hnd i) (hnd j) (hsep i j hij))
  cong := fun i => ZT.congr_model _ _ (hmod i)

end Erdos634.Draft.Collar23
