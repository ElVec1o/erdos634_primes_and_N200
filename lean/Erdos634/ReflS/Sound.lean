import Erdos634.ReflS.Check
import Erdos634.ReflS.Zs
import Erdos634.CertNode
import Erdos634.SixPlacements
import Erdos634.PlacementCompletenessCone

/-! ReflS/Sound.lean -- soundness of the `ℤ[√21]` free-branch-point checker (`ReflS.checkNodeM_sound`).

PORT of `Refl/Sound.lean`, `SoundStage{1,2,3,5,6,7,10,12,13}.lean` (the parts used by the `CheckM` chain) and
`SoundM{1,2,3}.lean`, with `Int ↦ R = ℤ[√21]` and casts `ℤ → ℝ` replaced by the embedding `R → ℝ` of `ReflS/Zs.lean`.
The only mathematical change is in `fk_sound` (Farkas multipliers are nonnegative elements of `R`). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Erdos634.CertNode Erdos634.PlacementCompleteness Erdos634.SixPlacements
open Erdos634.Geometry (Plane cross)

namespace ReflS


/-! ### Sound -/

noncomputable def evalL (l : Lin) (X Y : ℝ) : ℝ := (l.α : ℝ) * X + (l.β : ℝ) * Y + (l.γ : ℝ)

def Sat (c : Lin × Bool) (X Y : ℝ) : Prop := if c.2 then 0 < evalL c.1 X Y else 0 ≤ evalL c.1 X Y

/-- Farkas: the certificate arithmetic forces `a X + b Y + g` to be `≥ 0` (resp. `> 0`),
    so a negative (resp. zero-with-strict) constant is a contradiction. -/
theorem fk_sound (X Y : ℝ) : ∀ (cs : List (Lin × Bool)) (ms : List R) (a b g : R) (st : Bool),
    (∀ c ∈ cs, Sat c X Y) →
    0 ≤ (a : ℝ) * X + b * Y + g → (st = true → 0 < (a : ℝ) * X + b * Y + g) →
    fk cs ms a b g st = true → False := by
  intro cs
  induction cs with
  | nil =>
    intro ms a b g st _ h0 hs hk
    cases ms <;> simp only [fk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hk <;>
    · obtain ⟨⟨rfl, rfl⟩, hg | ⟨hg, hst⟩⟩ := hk
      · simp at h0; have : (g : ℝ) < 0 := by exact_mod_cast hg
        linarith
      · simp at h0 hs; have := hs hst; simp [hg] at this
  | cons c cs ih =>
    intro ms a b g st hcs h0 hs hk
    cases ms with
    | nil =>
      simp only [fk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hk
      obtain ⟨⟨rfl, rfl⟩, hg | ⟨hg, hst⟩⟩ := hk
      · simp at h0; have : (g : ℝ) < 0 := by exact_mod_cast hg
        linarith
      · simp at h0 hs; have := hs hst; simp [hg] at this
    | cons m ms =>
      obtain ⟨l, s⟩ := c
      have hc := hcs (l, s) (by simp)
      simp only [fk, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨hm0, hk⟩ := hk
      have hm : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
      refine ih ms _ _ _ _ (fun c hc' => hcs c (by simp [hc'])) ?_ ?_ hk
      · have : 0 ≤ evalL l X Y := by
          unfold Sat at hc; split_ifs at hc <;> linarith
        push_cast
        nlinarith [mul_nonneg hm this, h0, show (a : ℝ) * X + b * Y + g + m * evalL l X Y
            = (a + m * l.α : ℝ) * X + (b + m * l.β : ℝ) * Y + (g + m * l.γ : ℝ) by unfold evalL; ring]
      · intro hst
        push_cast
        have hL : 0 ≤ evalL l X Y := by
          unfold Sat at hc; split_ifs at hc <;> linarith
        have e : (a : ℝ) * X + b * Y + g + m * evalL l X Y
            = (a + m * l.α : ℝ) * X + (b + m * l.β : ℝ) * Y + (g + m * l.γ : ℝ) := by unfold evalL; ring
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hst
        rcases hst with h | ⟨hs', hm0'⟩
        · have := hs h; nlinarith [mul_nonneg hm hL]
        · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0'
          have : 0 < evalL l X Y := by
            unfold Sat at hc; simp [hs'] at hc; exact hc
          nlinarith [mul_pos hmpos this]

theorem farkas_sound (X Y : ℝ) (cs : List (Lin × Bool)) (ms : List R)
    (hsat : ∀ c ∈ cs, Sat c X Y) (h : farkas cs ms = true) : False :=
  fk_sound X Y cs ms 0 0 0 false hsat (by simp) (by simp) h


/-! ## Homogeneous points and the CertNode vocabulary -/

/-- semantic X-coordinate `x/w` -/
noncomputable def Pt.X (p : Pt) : ℝ := (p.x : ℝ) / p.w
noncomputable def Pt.Y (p : Pt) : ℝ := (p.y : ℝ) / p.w

/-- the sign of the rational edge functional is the sign of the integer determinant -/
theorem det3_ef (a b c : Pt) (ha : (a.w : ℝ) ≠ 0) (hb : (b.w : ℝ) ≠ 0) (hc : (c.w : ℝ) ≠ 0) :
    (det3 a b c : ℝ) = a.w * b.w * c.w * ef a.X a.Y b.X b.Y c.X c.Y := by
  unfold det3 ef Pt.X Pt.Y
  push_cast
  field_simp
  ring

/-- an edge line evaluated at `(X, Y)` is `wa wb · ef` -/
theorem evalL_linOf (a b : Pt) (ha : (a.w : ℝ) ≠ 0) (hb : (b.w : ℝ) ≠ 0) (X Y : ℝ) :
    evalL (linOf a b) X Y = a.w * b.w * ef a.X a.Y b.X b.Y X Y := by
  unfold evalL linOf ef Pt.X Pt.Y
  push_cast
  field_simp
  ring



/-! ### Stage1 -/

/-- the plane point of a homogeneous point (same def as `SoundSkel`) -/
noncomputable def Pt.re (Dn : ℝ) (p : Pt) : Plane := rp Dn p.X p.Y

/-- the closed triangle spanned by three homogeneous points (same def as `SoundSkel`) -/
noncomputable def Tri.carr (Dn : ℝ) (t : Tri) : Set Plane :=
  convexHull ℝ {t.a.re Dn, t.b.re Dn, t.c.re Dn}

theorem Pt.w_ne (p : Pt) (h : 0 < p.w) : (p.w : ℝ) ≠ 0 := by
  have : (0 : ℝ) < p.w := by exact_mod_cast h
  exact this.ne'

theorem Pt.w_pos (p : Pt) (h : 0 < p.w) : (0 : ℝ) < p.w := by exact_mod_cast h

/-- `Tri.ok` gives a genuine coordinate triangle, and `carr` is its carrier. -/
theorem Tri.ok_sem (Dn : ℝ) (hD : 0 < Dn) (t : Tri) (h : t.ok = true) :
    ∃ hp : 0 < ef t.a.X t.a.Y t.b.X t.b.Y t.c.X t.c.Y,
      t.carr Dn = (rtri Dn hD t.a.X t.a.Y t.b.X t.b.Y t.c.X t.c.Y hp).carrier := by
  simp only [Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hdet⟩ := h
  have hd : (0 : ℝ) < (det3 t.a t.b t.c : ℝ) := by exact_mod_cast hdet
  rw [det3_ef _ _ _ (Pt.w_ne _ ha) (Pt.w_ne _ hb) (Pt.w_ne _ hc)] at hd
  have hpos : 0 < ef t.a.X t.a.Y t.b.X t.b.Y t.c.X t.c.Y := by
    have := mul_pos (mul_pos (Pt.w_pos _ ha) (Pt.w_pos _ hb)) (Pt.w_pos _ hc)
    exact (mul_pos_iff_of_pos_left this).mp hd
  refine ⟨hpos, ?_⟩
  show convexHull ℝ _ = convexHull ℝ _
  congr 1
  ext p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, rtri, Erdos634.CertCoord.mkTri_pts]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem Tri.vert_re_mem (Dn : ℝ) (t : Tri) (i : Nat) :
    (t.vert i).re Dn ∈ t.carr Dn := by
  apply subset_convexHull
  match i with
  | 0 => simp [Tri.vert]
  | 1 => simp [Tri.vert]
  | k + 2 => simp [Tri.vert]

/-- closed membership from determinant signs -/
theorem inClosed_sound (Dn : ℝ) (hD : 0 < Dn) (t : Tri) (p : Pt) (hp : 0 < p.w)
    (ht : t.ok = true) (h : inClosed t p = true) : p.re Dn ∈ t.carr Dn := by
  have ht' := ht
  simp only [Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at ht'
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, -⟩ := ht'
  obtain ⟨hpos, hcar⟩ := Tri.ok_sem Dn hD t ht
  rw [hcar]
  simp only [inClosed, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have wa := Pt.w_pos _ ha
  have wb := Pt.w_pos _ hb
  have wc := Pt.w_pos _ hc
  have wp := Pt.w_pos _ hp
  have e0 := det3_ef t.a t.b p (Pt.w_ne _ ha) (Pt.w_ne _ hb) (Pt.w_ne _ hp)
  have e1 := det3_ef t.b t.c p (Pt.w_ne _ hb) (Pt.w_ne _ hc) (Pt.w_ne _ hp)
  have e2 := det3_ef t.c t.a p (Pt.w_ne _ hc) (Pt.w_ne _ ha) (Pt.w_ne _ hp)
  have h0' : (0:ℝ) ≤ det3 t.a t.b p := by exact_mod_cast h0
  have h1' : (0:ℝ) ≤ det3 t.b t.c p := by exact_mod_cast h1
  have h2' : (0:ℝ) ≤ det3 t.c t.a p := by exact_mod_cast h2
  rw [e0] at h0'; rw [e1] at h1'; rw [e2] at h2'
  show rp Dn p.X p.Y ∈ _
  exact mem_rtri hD hpos
    ((mul_nonneg_iff_of_pos_left (mul_pos (mul_pos wa wb) wp)).mp h0')
    ((mul_nonneg_iff_of_pos_left (mul_pos (mul_pos wb wc) wp)).mp h1')
    ((mul_nonneg_iff_of_pos_left (mul_pos (mul_pos wc wa) wp)).mp h2')

/-- open membership from determinant signs -/
theorem inOpen_sound (Dn : ℝ) (hD : 0 < Dn) (t : Tri) (p : Pt) (hp : 0 < p.w)
    (ht : t.ok = true) (h : inOpen t p = true) : p.re Dn ∈ interior (t.carr Dn) := by
  have ht' := ht
  simp only [Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at ht'
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, -⟩ := ht'
  obtain ⟨hpos, hcar⟩ := Tri.ok_sem Dn hD t ht
  rw [hcar]
  simp only [inOpen, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have wa := Pt.w_pos _ ha
  have wb := Pt.w_pos _ hb
  have wc := Pt.w_pos _ hc
  have wp := Pt.w_pos _ hp
  have e0 := det3_ef t.a t.b p (Pt.w_ne _ ha) (Pt.w_ne _ hb) (Pt.w_ne _ hp)
  have e1 := det3_ef t.b t.c p (Pt.w_ne _ hb) (Pt.w_ne _ hc) (Pt.w_ne _ hp)
  have e2 := det3_ef t.c t.a p (Pt.w_ne _ hc) (Pt.w_ne _ ha) (Pt.w_ne _ hp)
  have h0' : (0:ℝ) < det3 t.a t.b p := by exact_mod_cast h0
  have h1' : (0:ℝ) < det3 t.b t.c p := by exact_mod_cast h1
  have h2' : (0:ℝ) < det3 t.c t.a p := by exact_mod_cast h2
  rw [e0] at h0'; rw [e1] at h1'; rw [e2] at h2'
  show rp Dn p.X p.Y ∈ _
  exact mem_interior_rtri hD hpos
    ((mul_pos_iff_of_pos_left (mul_pos (mul_pos wa wb) wp)).mp h0')
    ((mul_pos_iff_of_pos_left (mul_pos (mul_pos wb wc) wp)).mp h1')
    ((mul_pos_iff_of_pos_left (mul_pos (mul_pos wc wa) wp)).mp h2')

/-- a point of the (closed) triangle satisfies the three edge lines nonstrictly. -/
theorem Tri.edge_nonneg (Dn : ℝ) (hD : 0 < Dn) (t : Tri) (ht : t.ok = true) (X Y : ℝ)
    (hm : rp Dn X Y ∈ t.carr Dn) (i : Nat) (hi : i < 3) : 0 ≤ evalL (t.edge i) X Y := by
  have ht' := ht
  simp only [Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at ht'
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, -⟩ := ht'
  obtain ⟨hpos, hcar⟩ := Tri.ok_sem Dn hD t ht
  rw [hcar] at hm
  obtain ⟨n0, n1, n2⟩ := rtri_ef_nonneg hD hpos hm
  have wa := Pt.w_pos _ ha
  have wb := Pt.w_pos _ hb
  have wc := Pt.w_pos _ hc
  interval_cases i
  · simp only [Tri.edge, Tri.vert, Nat.zero_mod, Nat.reduceMod, Nat.reduceAdd]
    rw [evalL_linOf _ _ (Pt.w_ne _ ha) (Pt.w_ne _ hb)]
    exact mul_nonneg (mul_pos wa wb).le n0
  · simp only [Tri.edge, Tri.vert, Nat.reduceMod, Nat.reduceAdd]
    rw [evalL_linOf _ _ (Pt.w_ne _ hb) (Pt.w_ne _ hc)]
    exact mul_nonneg (mul_pos wb wc).le n1
  · simp only [Tri.edge, Tri.vert, Nat.reduceMod, Nat.reduceAdd]
    rw [evalL_linOf _ _ (Pt.w_ne _ hc) (Pt.w_ne _ ha)]
    exact mul_nonneg (mul_pos wc wa).le n2


/-! ### Stage2 -/

theorem evalL_neg (l : Lin) (X Y : ℝ) : evalL l.neg X Y = -evalL l X Y := by
  simp only [evalL, Lin.neg]; push_cast; ring

/-- three nonneg edge lines put the point in the triangle -/
theorem Tri.mem_of_edges (Dn : ℝ) (hD : 0 < Dn) (t : Tri) (ht : t.ok = true) (X Y : ℝ)
    (h : ∀ i, i < 3 → 0 ≤ evalL (t.edge i) X Y) : rp Dn X Y ∈ t.carr Dn := by
  have ht' := ht
  simp only [Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at ht'
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, -⟩ := ht'
  obtain ⟨hpos, hcar⟩ := Tri.ok_sem Dn hD t ht
  rw [hcar]
  have wa := Pt.w_pos _ ha
  have wb := Pt.w_pos _ hb
  have wc := Pt.w_pos _ hc
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  simp only [Tri.edge, Tri.vert, Nat.reduceMod, Nat.reduceAdd] at h0 h1 h2
  rw [evalL_linOf _ _ (Pt.w_ne _ ha) (Pt.w_ne _ hb)] at h0
  rw [evalL_linOf _ _ (Pt.w_ne _ hb) (Pt.w_ne _ hc)] at h1
  rw [evalL_linOf _ _ (Pt.w_ne _ hc) (Pt.w_ne _ ha)] at h2
  exact mem_rtri hD hpos ((mul_nonneg_iff_of_pos_left (mul_pos wa wb)).mp h0)
    ((mul_nonneg_iff_of_pos_left (mul_pos wb wc)).mp h1)
    ((mul_nonneg_iff_of_pos_left (mul_pos wc wa)).mp h2)

theorem bsp_sound (Dn : ℝ) (hD : 0 < Dn) (cfg : List Tri) (hcfg : ∀ t ∈ cfg, t.ok = true)
    (closedBase : List Lin) (extra : List (Lin × Bool)) (allowCell : Bool) :
    ∀ (b : Bsp) (cons : List (Lin × Bool)) (path : List Lin) (X Y : ℝ),
      Bsp.check cfg closedBase extra allowCell cons path b = true →
      (∀ c ∈ cons, Sat c X Y) → (∀ l ∈ path, 0 ≤ evalL l X Y) →
      (∃ t ∈ cfg, rp Dn X Y ∈ t.carr Dn) ∨
      (allowCell = true ∧ ((∀ l ∈ closedBase, 0 ≤ evalL l X Y) → ¬ ∀ e ∈ extra, Sat e X Y)) := by
  intro b
  induction b with
  | inf ms =>
    intro cons path X Y hk hs _
    exact (farkas_sound X Y cons ms hs (by simpa [Bsp.check] using hk)).elim
  | tile m f0 f1 f2 =>
    intro cons path X Y hk hs _
    simp only [Bsp.check] at hk
    cases hm : cfg[m]? with
    | none => rw [hm] at hk; simp at hk
    | some t =>
      rw [hm] at hk
      simp only [Bool.and_eq_true] at hk
      obtain ⟨⟨k0, k1⟩, k2⟩ := hk
      have htm : t ∈ cfg := List.mem_of_getElem? hm
      left
      refine ⟨t, htm, Tri.mem_of_edges Dn hD t (hcfg t htm) X Y ?_⟩
      have key : ∀ (i : Nat) (fs : List R),
          farkas (cons ++ [((t.edge i).neg, true)]) fs = true → 0 ≤ evalL (t.edge i) X Y := by
        intro i fs hf
        by_contra hneg
        push_neg at hneg
        refine farkas_sound X Y _ fs ?_ hf
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hs c hc
        · simp only [List.mem_singleton] at hc
          subst hc
          simp only [Sat, if_true, evalL_neg]
          linarith
      intro i hi
      interval_cases i
      · exact key 0 f0 k0
      · exact key 1 f1 k1
      · exact key 2 f2 k2
  | cell ms =>
    intro cons path X Y hk hs hp
    simp only [Bsp.check, Bool.and_eq_true] at hk
    obtain ⟨hall, hf⟩ := hk
    right
    refine ⟨hall, fun hcb hextra => ?_⟩
    refine farkas_sound X Y _ ms ?_ hf
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
      simp only [Sat, Bool.false_eq_true, if_false]
      rcases List.mem_append.mp hl with hl | hl
      · exact hcb l hl
      · exact hp l hl
    · exact hextra c hc
  | split m i l r ihl ihr =>
    intro cons path X Y hk hs hp
    simp only [Bsp.check] at hk
    cases hm : cfg[m]? with
    | none => rw [hm] at hk; simp at hk
    | some t =>
      rw [hm] at hk
      simp only [Bool.and_eq_true] at hk
      obtain ⟨kl, kr⟩ := hk
      by_cases hc : 0 ≤ evalL (t.edge i) X Y
      · refine ihl _ _ X Y kl ?_ ?_
        · intro c hc'
          rcases List.mem_append.mp hc' with h | h
          · exact hs c h
          · simp only [List.mem_singleton] at h; subst h; simpa [Sat] using hc
        · intro l' hl'
          rcases List.mem_append.mp hl' with h | h
          · exact hp l' h
          · simp only [List.mem_singleton] at h; subst h; exact hc
      · push_neg at hc
        refine ihr _ _ X Y kr ?_ ?_
        · intro c hc'
          rcases List.mem_append.mp hc' with h | h
          · exact hs c h
          · simp only [List.mem_singleton] at h; subst h
            simp only [Sat, if_true, evalL_neg]; linarith
        · intro l' hl'
          rcases List.mem_append.mp hl' with h | h
          · exact hp l' h
          · simp only [List.mem_singleton] at h; subst h
            rw [evalL_neg]; linarith


/-! ### Stage3 -/

theorem Tri.ok_w (t : Tri) (h : t.ok = true) : 0 < t.a.w ∧ 0 < t.b.w ∧ 0 < t.c.w := by
  simp only [Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, -⟩ := h
  exact ⟨ha, hb, hc⟩

theorem Tri.vert_w_pos (t : Tri) (h : t.ok = true) (i : Nat) : 0 < (t.vert i).w := by
  obtain ⟨a, b, c⟩ := Tri.ok_w t h
  match i with
  | 0 => exact a
  | 1 => exact b
  | k + 2 => exact c

/-- the rescaled edge form at a homogeneous point is the determinant over the weight -/
theorem evalL_linOf_det (a b q : Pt) (ha : 0 < a.w) (hb : 0 < b.w) (hq : 0 < q.w) :
    evalL (linOf a b) q.X q.Y * q.w = det3 a b q := by
  rw [evalL_linOf _ _ (Pt.w_ne _ ha) (Pt.w_ne _ hb), det3_ef _ _ _ (Pt.w_ne _ ha) (Pt.w_ne _ hb) (Pt.w_ne _ hq)]
  ring

/-- **escape**: a vertex on the wrong side of a target edge cannot lie in the target. -/
theorem esc_sound (Dn : ℝ) (hD : 0 < Dn) (tgt : Tri) (htok : tgt.ok = true) (e : Nat)
    (q : Pt) (hq : 0 < q.w)
    (hdet : det3 (tgt.vert (e % 3)) (tgt.vert ((e + 1) % 3)) q < 0)
    (hin : q.re Dn ∈ tgt.carr Dn) : False := by
  have h := Tri.edge_nonneg Dn hD tgt htok q.X q.Y hin (e % 3) (Nat.mod_lt _ (by norm_num))
  have hedge : tgt.edge (e % 3) = linOf (tgt.vert (e % 3)) (tgt.vert ((e + 1) % 3)) := by
    have h3 : (e % 3 + 1) % 3 = (e + 1) % 3 := by omega
    simp only [Tri.edge, Nat.mod_mod, h3]
  rw [hedge] at h
  have := evalL_linOf_det (tgt.vert (e % 3)) (tgt.vert ((e + 1) % 3)) q
    (Tri.vert_w_pos tgt htok _) (Tri.vert_w_pos tgt htok _) hq
  have hw : (0 : ℝ) < q.w := Pt.w_pos _ hq
  have hd : (det3 (tgt.vert (e % 3)) (tgt.vert ((e + 1) % 3)) q : ℝ) < 0 := by exact_mod_cast hdet
  nlinarith [mul_nonneg h hw.le]

/-- escape kill against a dissection -/
theorem esc_sound_D (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (htok : I.tgt.ok = true) {N : ℕ}
    (D : Erdos634.Geometry.CongruentDissection N)
    (htarget : D.target.carrier = I.tgt.carr Dn) (tri : Tri) (j : Fin N)
    (hj : (D.tile j).carrier = tri.carr Dn) (e : Nat) (q : Pt) (hq : 0 < q.w)
    (hqin : q.re Dn ∈ tri.carr Dn)
    (hdet : det3 (I.tgt.vert (e % 3)) (I.tgt.vert ((e + 1) % 3)) q < 0) : False := by
  refine esc_sound Dn hD I.tgt htok e q hq hdet ?_
  rw [← htarget]
  exact Erdos634.BaseSelection.tile_subset_target D.toDissection j (by rw [hj]; exact hqin)

/-- overlap kill: an explicit point in both interiors, two distinct tiles -/
theorem ovl_sound_D (Dn : ℝ) (hD : 0 < Dn) {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (tri U : Tri) (htri : tri.ok = true) (hU : U.ok = true) (i j : Fin N) (hij : i ≠ j)
    (hi : (D.tile i).carrier = U.carr Dn) (hj : (D.tile j).carrier = tri.carr Dn)
    (w : Pt) (hw : 0 < w.w) (h1 : inOpen tri w = true) (h2 : inOpen U w = true) : False :=
  by
  have hdis : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
    D.interiors_disjoint hij
  rw [hi, hj] at hdis
  exact Set.disjoint_left.mp hdis (inOpen_sound Dn hD U w hw hU h2) (inOpen_sound Dn hD tri w hw htri h1)

/-- a placement satisfying `placeOk` numerics gives a well-formed tile -/
theorem placeTri_ok (I : Inst) (v d : Pt) (p : Place) (hv : 0 < v.w) (hd : 0 < d.w)
    (hdu : d.x * d.x + I.Dn * d.y * d.y = d.w * d.w) (hDn : 0 < I.Dn)
    (h1 : 0 < p.l1) (hpd : 0 < p.pd) (hqd : 0 < p.qd) (hqn : 0 < p.qn) :
    (placeTri I v d p).ok = true := by
  have hdet : det3 v (placeTri I v d p).b (placeTri I v d p).c
      = p.l1 * p.pd * p.qn * v.w ^ 3 * (d.w * d.w) := by
    rw [← hdu]; simp only [placeTri, det3]; ring
  simp only [Tri.ok, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hv, ?_⟩, ?_⟩, ?_⟩
  · show 0 < v.w * d.w; positivity
  · show 0 < v.w * d.w * p.pd * p.qd; positivity
  · show 0 < det3 v _ _
    rw [hdet]; positivity


/-! ### Stage5 (excerpt) -/
def tgtLins (I : Inst) : List Lin := (List.range 3).map (fun i => I.tgt.edge i)

theorem tgtLins_sat (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (htok : I.tgt.ok = true) (X Y : ℝ)
    (h : rp Dn X Y ∈ I.tgt.carr Dn) : ∀ l ∈ tgtLins I, 0 ≤ evalL l X Y := by
  intro l hl
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
  exact Tri.edge_nonneg Dn hD I.tgt htok X Y h i (List.mem_range.mp hi)

theorem tri_carr_closed (Dn : ℝ) (hD : 0 < Dn) (t : Tri) (ht : t.ok = true) :
    IsClosed (t.carr Dn) := by
  obtain ⟨hp, hc⟩ := Tri.ok_sem Dn hD t ht
  rw [hc]; exact (rtri Dn hD _ _ _ _ _ _ hp).isCompact.isClosed


/-! ### Stage6 -/

theorem poly_min_bound (c s tn : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ tn) : min c 0 * tn ≤ c * s := by
  rcases le_total c 0 with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

theorem poly_max_bound (c s tn : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ tn) : c * s ≤ max c 0 * tn := by
  rcases le_total c 0 with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

theorem okPos_real (c0 c1 c2 tn td t : ℝ) (htn : 0 < tn) (htd : 0 < td) (ht0 : 0 < t)
    (ht : t * td ≤ tn)
    (H : (0 < c0 ∧ 0 < c0 * td * td + min c1 0 * tn * td + min c2 0 * tn * tn) ∨
         (c0 = 0 ∧ 0 < c1 ∧ 0 < c1 * td + min c2 0 * tn) ∨ (c0 = 0 ∧ c1 = 0 ∧ 0 ≤ c2)) :
    0 ≤ c0 + c1 * t + c2 * t ^ 2 := by
  have hs0 : 0 ≤ t * td := by positivity
  rcases H with ⟨h0, h⟩ | ⟨h0, h1, h⟩ | ⟨h0, h1, h⟩
  · have b1 := poly_min_bound c1 (t * td) tn hs0 ht
    have hss : (t * td) * (t * td) ≤ tn * tn := by nlinarith
    have b2 : min c2 0 * (tn * tn) ≤ c2 * ((t * td) * (t * td)) := by
      rcases le_total c2 0 with h' | h'
      · rw [min_eq_left h']; nlinarith
      · rw [min_eq_right h']; nlinarith [mul_nonneg h' (mul_self_nonneg (t * td))]
    have key : td ^ 2 * (c0 + c1 * t + c2 * t ^ 2)
        = c0 * td * td + (c1 * (t * td)) * td + c2 * ((t * td) * (t * td)) := by ring
    have : 0 ≤ td ^ 2 * (c0 + c1 * t + c2 * t ^ 2) := by
      rw [key]; nlinarith [mul_le_mul_of_nonneg_right b1 htd.le]
    exact nonneg_of_mul_nonneg_right this (by positivity) |> fun h => by
      by_contra hn; push_neg at hn; nlinarith [mul_pos (pow_pos htd 2) (neg_pos.mpr hn)]
  · subst h0
    have b2 := poly_min_bound c2 (t * td) tn hs0 ht
    have : 0 < t * (c1 * td + c2 * (t * td)) := by
      apply mul_pos ht0; nlinarith
    nlinarith
  · subst h0; subst h1; simp; positivity

theorem okNeg_real (c0 c1 c2 tn td t : ℝ) (htn : 0 < tn) (htd : 0 < td) (ht0 : 0 < t)
    (ht : t * td ≤ tn)
    (H : (c0 < 0 ∧ c0 * td * td + max c1 0 * tn * td + max c2 0 * tn * tn < 0) ∨
         (c0 = 0 ∧ c1 < 0 ∧ c1 * td + max c2 0 * tn < 0) ∨ (c0 = 0 ∧ c1 = 0 ∧ c2 < 0)) :
    c0 + c1 * t + c2 * t ^ 2 < 0 := by
  have hs0 : 0 ≤ t * td := by positivity
  rcases H with ⟨h0, h⟩ | ⟨h0, h1, h⟩ | ⟨h0, h1, h⟩
  · have b1 := poly_max_bound c1 (t * td) tn hs0 ht
    have hss : (t * td) * (t * td) ≤ tn * tn := by nlinarith
    have b2 : c2 * ((t * td) * (t * td)) ≤ max c2 0 * (tn * tn) := by
      rcases le_total c2 0 with h' | h'
      · rw [max_eq_right h']; nlinarith [mul_nonneg (neg_nonneg.mpr h') (mul_self_nonneg (t * td))]
      · rw [max_eq_left h']; nlinarith
    have key : td ^ 2 * (c0 + c1 * t + c2 * t ^ 2)
        = c0 * td * td + (c1 * (t * td)) * td + c2 * ((t * td) * (t * td)) := by ring
    have : td ^ 2 * (c0 + c1 * t + c2 * t ^ 2) < 0 := by
      rw [key]; nlinarith [mul_le_mul_of_nonneg_right b1 htd.le]
    by_contra hn; push_neg at hn
    nlinarith [mul_nonneg (pow_pos htd 2).le hn]
  · subst h0
    have b2 := poly_max_bound c2 (t * td) tn hs0 ht
    have : t * (c1 * td + c2 * (t * td)) < 0 := by
      apply mul_neg_of_pos_of_neg ht0; nlinarith
    nlinarith
  · subst h0; subst h1; simp; nlinarith [sq_nonneg t, pow_pos ht0 2]


theorem okPos_cast (c0 c1 c2 tn td : R) (h : okPos (c0, c1, c2) tn td = true) :
    (0 < (c0:ℝ) ∧ 0 < (c0:ℝ) * td * td + min (c1:ℝ) 0 * tn * td + min (c2:ℝ) 0 * tn * tn) ∨
    ((c0:ℝ) = 0 ∧ 0 < (c1:ℝ) ∧ 0 < (c1:ℝ) * td + min (c2:ℝ) 0 * tn) ∨
    ((c0:ℝ) = 0 ∧ (c1:ℝ) = 0 ∧ 0 ≤ (c2:ℝ)) := by
  unfold okPos at h
  simp only at h
  split_ifs at h with h1 h2 h3 h4
  · left
    simp only [decide_eq_true_eq] at h
    refine ⟨by exact_mod_cast h1, ?_⟩
    have : (0:ℝ) < ((c0 * td * td + min c1 0 * tn * td + min c2 0 * tn * tn : R) : ℝ) := by exact_mod_cast h
    push_cast at this; exact this
  · right; left
    simp only [decide_eq_true_eq] at h
    have hc0 : c0 = 0 := by simpa using h2
    refine ⟨by exact_mod_cast hc0, by exact_mod_cast h3, ?_⟩
    have : (0:ℝ) < ((c1 * td + min c2 0 * tn : R) : ℝ) := by exact_mod_cast h
    push_cast at this; exact this
  · right; right
    simp only [decide_eq_true_eq] at h
    have hc0 : c0 = 0 := by simpa using h2
    have hc1 : c1 = 0 := by simpa using h4
    exact ⟨by exact_mod_cast hc0, by exact_mod_cast hc1, by exact_mod_cast h⟩

theorem okNeg_cast (c0 c1 c2 tn td : R) (h : okNeg (c0, c1, c2) tn td = true) :
    ((c0:ℝ) < 0 ∧ (c0:ℝ) * td * td + max (c1:ℝ) 0 * tn * td + max (c2:ℝ) 0 * tn * tn < 0) ∨
    ((c0:ℝ) = 0 ∧ (c1:ℝ) < 0 ∧ (c1:ℝ) * td + max (c2:ℝ) 0 * tn < 0) ∨
    ((c0:ℝ) = 0 ∧ (c1:ℝ) = 0 ∧ (c2:ℝ) < 0) := by
  unfold okNeg at h
  simp only at h
  split_ifs at h with h1 h2 h3 h4
  · left
    simp only [decide_eq_true_eq] at h
    refine ⟨by exact_mod_cast h1, ?_⟩
    have : ((c0 * td * td + max c1 0 * tn * td + max c2 0 * tn * tn : R) : ℝ) < 0 := by exact_mod_cast h
    push_cast at this; exact this
  · right; left
    simp only [decide_eq_true_eq] at h
    have hc0 : c0 = 0 := by simpa using h2
    refine ⟨by exact_mod_cast hc0, by exact_mod_cast h3, ?_⟩
    have : ((c1 * td + max c2 0 * tn : R) : ℝ) < 0 := by exact_mod_cast h
    push_cast at this; exact this
  · right; right
    simp only [decide_eq_true_eq] at h
    have hc0 : c0 = 0 := by simpa using h2
    have hc1 : c1 = 0 := by simpa using h4
    exact ⟨by exact_mod_cast hc0, by exact_mod_cast hc1, by exact_mod_cast h⟩

/-- the edge form along the curve `t ↦ v + t (d + t √Dn d⊥)` in rescaled coordinates -/
theorem evalL_curve (I : Inst) (Dn : ℝ) (hDn : (I.Dn : ℝ) = Dn) (v d : Pt) (hv : 0 < v.w) (hd : 0 < d.w)
    (l : Lin) (t : ℝ) :
    evalL l (v.X + d.X * t - Dn * d.Y * t ^ 2) (v.Y + d.Y * t + d.X * t ^ 2)
      = (((quad I v d l).1 : ℝ) + ((quad I v d l).2.1 : ℝ) * t + ((quad I v d l).2.2 : ℝ) * t ^ 2)
          / ((v.w : ℝ) * d.w) := by
  have h1 := Pt.w_ne v hv
  have h2 := Pt.w_ne d hd
  unfold evalL quad Pt.X Pt.Y
  push_cast
  rw [hDn]
  field_simp
  ring

theorem okPos_sound (I : Inst) (Dn : ℝ) (hDn : (I.Dn : ℝ) = Dn) (v d : Pt) (hv : 0 < v.w) (hd : 0 < d.w)
    (l : Lin) (tn td : R) (htn : 0 < tn) (htd : 0 < td)
    (h : okPos (quad I v d l) tn td = true) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ (tn : ℝ) / td) :
    0 ≤ evalL l (v.X + d.X * t - Dn * d.Y * t ^ 2) (v.Y + d.Y * t + d.X * t ^ 2) := by
  rw [evalL_curve I Dn hDn v d hv hd]
  generalize quad I v d l = q at h ⊢
  obtain ⟨c0, c1, c2⟩ := q
  have htn' : (0:ℝ) < tn := by exact_mod_cast htn
  have htd' : (0:ℝ) < td := by exact_mod_cast htd
  have ht' : t * td ≤ tn := by rwa [le_div_iff₀ htd'] at ht
  have := okPos_real _ _ _ _ _ t htn' htd' ht0 ht' (okPos_cast _ _ _ _ _ h)
  have hw : (0:ℝ) < (v.w:ℝ) * d.w := mul_pos (Pt.w_pos _ hv) (Pt.w_pos _ hd)
  exact div_nonneg this hw.le

theorem okNeg_sound (I : Inst) (Dn : ℝ) (hDn : (I.Dn : ℝ) = Dn) (v d : Pt) (hv : 0 < v.w) (hd : 0 < d.w)
    (l : Lin) (tn td : R) (htn : 0 < tn) (htd : 0 < td)
    (h : okNeg (quad I v d l) tn td = true) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ (tn : ℝ) / td) :
    evalL l (v.X + d.X * t - Dn * d.Y * t ^ 2) (v.Y + d.Y * t + d.X * t ^ 2) < 0 := by
  rw [evalL_curve I Dn hDn v d hv hd]
  generalize quad I v d l = q at h ⊢
  obtain ⟨c0, c1, c2⟩ := q
  have htn' : (0:ℝ) < tn := by exact_mod_cast htn
  have htd' : (0:ℝ) < td := by exact_mod_cast htd
  have ht' : t * td ≤ tn := by rwa [le_div_iff₀ htd'] at ht
  have := okNeg_real _ _ _ _ _ t htn' htd' ht0 ht' (okNeg_cast _ _ _ _ _ h)
  have hw : (0:ℝ) < (v.w:ℝ) * d.w := mul_pos (Pt.w_pos _ hv) (Pt.w_pos _ hd)
  exact div_neg_of_neg_of_pos this hw


/-! ### Stage7 (excerpt) -/

theorem Tri.edge_mod (t : Tri) (e : Nat) : t.edge e = t.edge (e % 3) := by
  have h3 : (e % 3 + 1) % 3 = (e + 1) % 3 := by omega
  simp only [Tri.edge, Nat.mod_mod, h3]

theorem zip_all_ex {α β : Type} (P : α × β → Bool) :
    ∀ (xs : List α) (ys : List β), ys.length = xs.length → (xs.zip ys).all P = true →
      ∀ x ∈ xs, ∃ y, P (x, y) = true := by
  intro xs
  induction xs with
  | nil => intro ys _ _ x hx; simp at hx
  | cons a as ih =>
    intro ys hl h x hx
    cases ys with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨b, h.1⟩
      · exact ih bs (by simpa using hl) h.2 x hx'


/-! ### Stage10 -/

theorem placeOk_facts (I : Inst) (l1 l2 l3 : R) (p : Place) (h : placeOk I l1 l2 l3 p = true) :
    0 < p.l1 ∧ 0 < p.pd ∧ 0 < p.qd ∧ 0 < p.qn ∧ p.l1 = l1 ∧
    2 * l1 * p.pn = (l1 * l1 + l2 * l2 - l3 * l3) * p.pd ∧
    I.Dn * p.qn * p.qn * p.pd * p.pd = (l2 * l2 * p.pd * p.pd - p.pn * p.pn) * (p.qd * p.qd) := by
  simp only [placeOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

/-- **A `six_placements` outcome realises the checker's `placeTri`.** -/
theorem place_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (v d : Pt) (hvw : 0 < v.w) (hdw : 0 < d.w) (hdu : d.x * d.x + I.Dn * d.y * d.y = d.w * d.w)
    (l1 l2 l3 : R) (p : Place) (hp : placeOk I l1 l2 l3 p = true)
    (T : Erdos634.Geometry.Tri) {k₀ k₁ k₂ : Fin 3} (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂)
    (h0 : T.pts k₀ = v.re Dn) (h1 : T.pts k₁ = v.re Dn + (l1 : ℝ) • d.re Dn)
    (h2 : T.pts k₂ = placeThird (v.re Dn) (d.re Dn) l1 l2 l3) :
    T.carrier = (placeTri I v d p).carr Dn := by
  obtain ⟨pl1, ppd, pqd, pqn, pl, hpn, hq⟩ := placeOk_facts I l1 l2 l3 p hp
  have htok := placeTri_ok I v d p hvw hdw hdu (by exact_mod_cast (hDn ▸ hD : (0:ℝ) < I.Dn)) pl1 ppd pqd pqn
  obtain ⟨hpos, hcar⟩ := Tri.ok_sem Dn hD _ htok
  rw [hcar]
  have hvw' := Pt.w_pos _ hvw
  have hdw' := Pt.w_pos _ hdw
  have ppd' : (0:ℝ) < p.pd := by exact_mod_cast ppd
  have pqd' : (0:ℝ) < p.qd := by exact_mod_cast pqd
  have pqn' : (0:ℝ) < p.qn := by exact_mod_cast pqn
  have hl1 : (l1 : ℝ) = p.l1 := by rw [pl]
  have hl1pos : (0:ℝ) < l1 := by rw [hl1]; exact_mod_cast pl1
  -- the real numbers p, q
  have hpR : ((l1:ℝ) ^ 2 + (l2:ℝ) ^ 2 - (l3:ℝ) ^ 2) / (2 * l1) = (p.pn : ℝ) / p.pd := by
    rw [div_eq_div_iff (by positivity) ppd'.ne']
    have : (2 * l1 * p.pn : R) = (l1 * l1 + l2 * l2 - l3 * l3) * p.pd := hpn
    have := congrArg (fun z : R => (z : ℝ)) this
    push_cast at this; nlinarith
  have hqR : (l2:ℝ) ^ 2 - ((p.pn:ℝ) / p.pd) ^ 2 = Dn * ((p.qn : ℝ) / p.qd) ^ 2 := by
    have := congrArg (fun z : R => (z : ℝ)) hq
    push_cast at this
    rw [hDn] at this
    field_simp
    nlinarith [this]
  have hplace := placeThird_rp hD (v.X) (v.Y) (d.X) (d.Y) l1 l2 l3 ((p.pn:ℝ)/p.pd) ((p.qn:ℝ)/p.qd)
    hpR (by positivity) hqR
  have hvre : v.re Dn = rp Dn v.X v.Y := rfl
  have hdre : d.re Dn = rp Dn d.X d.Y := rfl
  rw [hvre] at h0 h1 h2
  rw [hdre] at h1 h2
  rw [hplace] at h2
  rw [rp_add_smul] at h1
  refine carrier_eq_rtri_of_pts hD T h01 h02 h12 (x₀ := v.X) (y₀ := v.Y)
    (x₁ := (placeTri I v d p).b.X) (y₁ := (placeTri I v d p).b.Y)
    (x₂ := (placeTri I v d p).c.X) (y₂ := (placeTri I v d p).c.Y) h0 ?_ ?_ ?_
  · rw [h1]
    have e1 : v.X + (l1:ℝ) * d.X = (placeTri I v d p).b.X := by
      simp only [placeTri, Pt.X, Pt.Y]; rw [hl1]; push_cast; field_simp
    have e2 : v.Y + (l1:ℝ) * d.Y = (placeTri I v d p).b.Y := by
      simp only [placeTri, Pt.X, Pt.Y]; rw [hl1]; push_cast; field_simp
    rw [e1, e2]
  · rw [h2]
    have e1 : v.X + (p.pn:ℝ) / p.pd * d.X - Dn * ((p.qn:ℝ) / p.qd) * d.Y = (placeTri I v d p).c.X := by
      simp only [placeTri, Pt.X, Pt.Y]; push_cast; rw [hDn]; field_simp
    have e2 : v.Y + (p.pn:ℝ) / p.pd * d.Y + (p.qn:ℝ) / p.qd * d.X = (placeTri I v d p).c.Y := by
      simp only [placeTri, Pt.X, Pt.Y]; push_cast; field_simp
    rw [e1, e2]


/-! ### Stage12 (excerpt) -/
def Sound (Dn : ℝ) (I : Inst) (M : Erdos634.Geometry.Tri) (cfg : List Tri) : Prop :=
  ∀ {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N),
    D.target.carrier = I.tgt.carr Dn → D.model.Congruent M →
    (∀ t ∈ cfg, ∃ i, (D.tile i).carrier = t.carr Dn) → False


theorem Inst_ok_facts (I : Inst) (h : I.ok = true) :
    I.tgt.ok = true ∧ 0 < I.Dn ∧ ∃ p1 p2 p3 p4 p5 p6 : Place,
      I.pl = [p1, p2, p3, p4, p5, p6] ∧
      placeOk I I.sides.1 I.sides.2.2 I.sides.2.1 p1 = true ∧
      placeOk I I.sides.2.2 I.sides.1 I.sides.2.1 p2 = true ∧
      placeOk I I.sides.1 I.sides.2.1 I.sides.2.2 p3 = true ∧
      placeOk I I.sides.2.1 I.sides.1 I.sides.2.2 p4 = true ∧
      placeOk I I.sides.2.2 I.sides.2.1 I.sides.1 p5 = true ∧
      placeOk I I.sides.2.1 I.sides.2.2 I.sides.1 p6 = true := by
  unfold Inst.ok at h
  generalize hs : I.sides = s at h
  obtain ⟨a, b, c⟩ := s
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨-, htok⟩, hDn⟩, hm⟩ := h
  refine ⟨htok, hDn, ?_⟩
  revert hm
  rcases hpl : I.pl with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [Bool.and_eq_true]
  all_goals first | (intro hm; simp at hm; done) | skip
  intro hm
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hm
  exact ⟨p1, p2, p3, p4, p5, p6, rfl, h1, h2, h3, h4, h5, h6⟩


/-! ### Stage13 (excerpt) -/
theorem unit_re (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn) (d : Pt) (hdw : 0 < d.w)
    (hdu : d.x * d.x + I.Dn * d.y * d.y = d.w * d.w) :
    (d.re Dn) 0 ^ 2 + (d.re Dn) 1 ^ 2 = 1 := by
  have h := congrArg (fun z : R => (z : ℝ)) hdu
  push_cast at h
  rw [hDn] at h
  have hw := Pt.w_pos d hdw
  show (rp Dn d.X d.Y) 0 ^ 2 + (rp Dn d.X d.Y) 1 ^ 2 = 1
  rw [rp_zero, rp_one, mul_pow, sr_sq hD]
  unfold Pt.X Pt.Y
  field_simp
  nlinarith [h]


/-! ### M1 -/

structure LocalFactsM (I : Inst) (cfg : List Tri) (n : NodeM) : Prop where
  vw : 0 < n.v.w
  dw : 0 < n.d.w
  unit : n.d.x * n.d.x + I.Dn * n.d.y * n.d.y = n.d.w * n.d.w
  tauN : 0 < n.tauN
  tauD : 0 < n.tauD
  flen : n.fedges.length = cfg.length
  gw : 0 < n.g.w
  eN : 0 < n.eN
  eD : 0 < n.eD
  dg : 0 < n.d.x * n.g.y - n.d.y * n.g.x
  r1 : Bsp.check cfg [] [] false (consM1 I n) [] n.t1 = true
  r2 : Bsp.check cfg [] [] false (consM2 I n) [] n.t2 = true
  tgtQ : ((tgtLinsM I).all fun l => okPos (quad I n.v n.d l) n.tauN n.tauD) = true
  tileQ : ((cfg.zip n.fedges).all fun x => okNeg (quad I n.v n.d (x.1.edge x.2)) n.tauN n.tauD) = true

theorem nodeLocalOkM_facts (I : Inst) (cfg : List Tri) (n : NodeM)
    (h : nodeLocalOkM I cfg n = true) : LocalFactsM I cfg n := by
  unfold nodeLocalOkM at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem tgtLinsM_eq (I : Inst) : tgtLinsM I = tgtLins I := rfl

theorem abs_le_of_sq_le' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : |a| ≤ b :=
  abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- the ray form, in the rational coordinates -/
theorem evalL_rayL (v d : Pt) (hv : 0 < v.w) (hd : 0 < d.w) (X Y : ℝ) :
    evalL (rayL v d) X Y = (v.w : ℝ) * d.w * (d.X * (Y - v.Y) - d.Y * (X - v.X)) := by
  have a := Pt.w_ne v hv
  have b := Pt.w_ne d hd
  unfold evalL rayL Pt.X Pt.Y
  push_cast
  field_simp
  ring

theorem cross_re (Dn : ℝ) (v d : Pt) (X Y : ℝ) :
    cross (d.re Dn) (rp Dn X Y - v.re Dn) = sr Dn * (d.X * (Y - v.Y) - d.Y * (X - v.X)) := by
  show cross (rp Dn d.X d.Y) (rp Dn X Y - rp Dn v.X v.Y) = _
  simp only [cross, PiLp.sub_apply, rp_zero, rp_one]
  ring

theorem boxL_sat (v : Pt) (hv : 0 < v.w) (eN eD : R) (heD : 0 < eD) (X Y : ℝ)
    (hX : |X - v.X| ≤ (eN : ℝ) / eD) (hY : |Y - v.Y| ≤ (eN : ℝ) / eD) :
    ∀ l ∈ boxL v eN eD, 0 ≤ evalL l X Y := by
  have hw := Pt.w_pos v hv
  have hwn := Pt.w_ne v hv
  have hD : (0 : ℝ) < eD := by exact_mod_cast heD
  obtain ⟨hX1, hX2⟩ := abs_le.mp hX
  obtain ⟨hY1, hY2⟩ := abs_le.mp hY
  have hwD : (0 : ℝ) < v.w * eD := mul_pos hw hD
  have ex : (v.x : ℝ) = v.X * v.w := by unfold Pt.X; field_simp
  have ey : (v.y : ℝ) = v.Y * v.w := by unfold Pt.Y; field_simp
  intro l hl
  simp only [boxL, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · have e : evalL ⟨v.w * eD, 0, eN * v.w - v.x * eD⟩ X Y
        = (v.w : ℝ) * eD * (X - v.X + (eN : ℝ) / eD) := by
      simp only [evalL]; push_cast; rw [ex]; field_simp; ring
    rw [e]; exact mul_nonneg hwD.le (by linarith)
  · have e : evalL ⟨-(v.w * eD), 0, eN * v.w + v.x * eD⟩ X Y
        = (v.w : ℝ) * eD * ((eN : ℝ) / eD - (X - v.X)) := by
      simp only [evalL]; push_cast; rw [ex]; field_simp; ring
    rw [e]; exact mul_nonneg hwD.le (by linarith)
  · have e : evalL ⟨0, v.w * eD, eN * v.w - v.y * eD⟩ X Y
        = (v.w : ℝ) * eD * (Y - v.Y + (eN : ℝ) / eD) := by
      simp only [evalL]; push_cast; rw [ey]; field_simp; ring
    rw [e]; exact mul_nonneg hwD.le (by linarith)
  · have e : evalL ⟨0, -(v.w * eD), eN * v.w + v.y * eD⟩ X Y
        = (v.w : ℝ) * eD * ((eN : ℝ) / eD - (Y - v.Y)) := by
      simp only [evalL]; push_cast; rw [ey]; field_simp; ring
    rw [e]; exact mul_nonneg hwD.le (by linarith)

/-- **cone**: near `v`, every unfilled point is on/left of `d` and on/right of `g`. -/
theorem cone_soundM (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (htok : I.tgt.ok = true)
    (cfg : List Tri) (hcfg : ∀ t ∈ cfg, t.ok = true) (n : NodeM) (F : LocalFactsM I cfg n)
    {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (htarget : D.target.carrier = I.tgt.carr Dn) (S : Finset (Fin N))
    (hS : ∀ t ∈ cfg, ∃ i ∈ S, (D.tile i).carrier = t.carr Dn) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ unfilled D.toDissection S, dist p (n.v.re Dn) < ε →
      0 ≤ cross (n.d.re Dn) (p - n.v.re Dn) ∧ 0 ≤ cross (p - n.v.re Dn) (n.g.re Dn) := by
  have heN : (0 : ℝ) < n.eN := by exact_mod_cast F.eN
  have heD : (0 : ℝ) < n.eD := by exact_mod_cast F.eD
  set e : ℝ := (n.eN : ℝ) / n.eD with he
  have hepos : 0 < e := div_pos heN heD
  have hsr : 0 < sr Dn := Real.sqrt_pos.mpr hD
  have hvw := Pt.w_pos n.v F.vw
  have hdw := Pt.w_pos n.d F.dw
  have hgw := Pt.w_pos n.g F.gw
  refine ⟨e * min 1 (sr Dn), mul_pos hepos (lt_min one_pos hsr), ?_⟩
  intro p hp hdist
  obtain ⟨X, Y, rfl⟩ := exists_rp hD p
  have hnt : ∀ t ∈ cfg, rp Dn X Y ∉ t.carr Dn := by
    intro t ht hpt
    obtain ⟨i, hi, hti⟩ := hS t ht
    exact hp.2 (Set.mem_iUnion₂.mpr ⟨i, hi, by rw [hti]; exact hpt⟩)
  have hpt : rp Dn X Y ∈ I.tgt.carr Dn := by rw [← htarget]; exact hp.1
  have hsatT := tgtLins_sat Dn hD I htok X Y hpt
  -- coordinate bounds from the distance
  have hd0 : 0 ≤ dist (rp Dn X Y) (n.v.re Dn) := dist_nonneg
  have hsq : dist (rp Dn X Y) (n.v.re Dn) ^ 2 = (X - n.v.X) ^ 2 + ((Y - n.v.Y) * sr Dn) ^ 2 := by
    rw [dist_sq_coord]
    show (rp Dn X Y 0 - rp Dn n.v.X n.v.Y 0) ^ 2 + (rp Dn X Y 1 - rp Dn n.v.X n.v.Y 1) ^ 2 = _
    simp only [rp_zero, rp_one]; ring
  have hm1 : e * min 1 (sr Dn) ≤ e := by
    have := min_le_left (1 : ℝ) (sr Dn); nlinarith
  have hm2 : e * min 1 (sr Dn) ≤ e * sr Dn := by
    have := min_le_right (1 : ℝ) (sr Dn); nlinarith
  have hX : |X - n.v.X| ≤ e := by
    have h1 : (X - n.v.X) ^ 2 ≤ dist (rp Dn X Y) (n.v.re Dn) ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg ((Y - n.v.Y) * sr Dn)]
    have := abs_le_of_sq_le' hd0 h1
    linarith
  have hY : |Y - n.v.Y| ≤ e := by
    have h1 : ((Y - n.v.Y) * sr Dn) ^ 2 ≤ dist (rp Dn X Y) (n.v.re Dn) ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg (X - n.v.X)]
    have h2 := abs_le_of_sq_le' hd0 h1
    rw [abs_mul, abs_of_pos hsr] at h2
    have h3 : |Y - n.v.Y| * sr Dn < e * sr Dn := by linarith
    exact (lt_of_mul_lt_mul_right h3 hsr.le).le
  have hbox := boxL_sat n.v F.vw n.eN n.eD F.eD X Y hX hY
  have hbase : ∀ c ∈ (tgtLinsM I ++ boxL n.v n.eN n.eD).map (fun l => (l, false)), Sat c X Y := by
    intro c hc
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
    rcases List.mem_append.mp hl with h | h
    · simpa [Sat] using hsatT l h
    · simpa [Sat] using hbox l h
  set K : ℝ := n.d.X * (Y - n.v.Y) - n.d.Y * (X - n.v.X) with hKdef
  set G : ℝ := n.g.X * (Y - n.v.Y) - n.g.Y * (X - n.v.X) with hGdef
  have eK : evalL (rayL n.v n.d) X Y = (n.v.w : ℝ) * n.d.w * K := evalL_rayL n.v n.d F.vw F.dw X Y
  have eG : evalL (rayL n.v n.g) X Y = (n.v.w : ℝ) * n.g.w * G := evalL_rayL n.v n.g F.vw F.gw X Y
  have hK : 0 ≤ K := by
    by_contra hneg
    push_neg at hneg
    rcases bsp_sound Dn hD cfg hcfg [] [] false n.t1 (consM1 I n) [] X Y F.r1 (by
        intro c hc
        rcases List.mem_append.mp hc with h | h
        · exact hbase c h
        · simp only [List.mem_singleton] at h; subst h
          have : 0 < evalL (rayL n.v n.d).neg X Y := by
            rw [evalL_neg, eK]
            have := mul_pos (mul_pos hvw hdw) (neg_pos.mpr hneg)
            linarith
          simpa [Sat] using this) (by simp) with ⟨t, ht, hm⟩ | ⟨h, _⟩
    · exact hnt t ht hm
    · simp at h
  have hG : G ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    rcases bsp_sound Dn hD cfg hcfg [] [] false n.t2 (consM2 I n) [] X Y F.r2 (by
        intro c hc
        rcases List.mem_append.mp hc with h | h
        · exact hbase c h
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
          rcases h with h | h
          · subst h
            have : 0 ≤ evalL (rayL n.v n.d) X Y := by
              rw [eK]; exact mul_nonneg (mul_pos hvw hdw).le hK
            simpa [Sat] using this
          · subst h
            have : 0 < evalL (rayL n.v n.g) X Y := by
              rw [eG]; exact mul_pos (mul_pos hvw hgw) hpos
            simpa [Sat] using this) (by simp) with ⟨t, ht, hm⟩ | ⟨h, _⟩
    · exact hnt t ht hm
    · simp at h
  refine ⟨?_, ?_⟩
  · rw [cross_re]; exact mul_nonneg hsr.le hK
  · rw [cross_anticomm, cross_re]
    have := mul_nonneg hsr.le (neg_nonneg.mpr hG)
    linarith


/-- the cone is pointed: `0 < cross d g` -/
theorem dg_re (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (cfg : List Tri) (n : NodeM)
    (F : LocalFactsM I cfg n) : 0 < cross (n.d.re Dn) (n.g.re Dn) := by
  have hsr : 0 < sr Dn := Real.sqrt_pos.mpr hD
  have hdw := Pt.w_pos n.d F.dw
  have hgw := Pt.w_pos n.g F.gw
  have h : (0 : ℝ) < (n.d.x : ℝ) * n.g.y - n.d.y * n.g.x := by exact_mod_cast F.dg
  show 0 < cross (rp Dn n.d.X n.d.Y) (rp Dn n.g.X n.g.Y)
  simp only [cross, rp_zero, rp_one]
  have e : n.d.X * (n.g.Y * sr Dn) - n.d.Y * sr Dn * n.g.X
      = sr Dn * (((n.d.x : ℝ) * n.g.y - n.d.y * n.g.x) / (n.d.w * n.g.w)) := by
    unfold Pt.X Pt.Y; field_simp
  rw [e]
  exact mul_pos hsr (div_pos h (mul_pos hdw hgw))

/-- **`hfree`** for `NodeM` (Stage 7 verbatim). -/
theorem hfree_soundM (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (htok : I.tgt.ok = true) (cfg : List Tri) (hcfg : ∀ t ∈ cfg, t.ok = true)
    (n : NodeM) (F : LocalFactsM I cfg n)
    {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (htarget : D.target.carrier = I.tgt.carr Dn) (S : Finset (Fin N))
    (hSt : ∀ i ∈ S, ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn) :
    ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      (n.v.re Dn) + t • ((n.d.re Dn) + s • perp (n.d.re Dn))
        ∈ unfilled D.toDissection S := by
  have hτ : (0:ℝ) < (n.tauN : ℝ) / n.tauD := by
    have a : (0:ℝ) < n.tauN := by exact_mod_cast F.tauN
    have b : (0:ℝ) < n.tauD := by exact_mod_cast F.tauD
    positivity
  refine hfree_of (Dn := Dn) (B := max 1 (sr Dn + 1)) hD (le_max_left _ _)
    (lt_of_lt_of_le (by linarith) (le_max_right _ _)) hτ _ _ _ ?_
  intro t ht0 htτ
  have hcurve := pt_ccw_rp Dn hD n.v.X n.v.Y n.d.X n.d.Y t
  show (rp Dn n.v.X n.v.Y) + t • ((rp Dn n.d.X n.d.Y) + (t * sr Dn) • perp (rp Dn n.d.X n.d.Y)) ∈ _
  rw [hcurve]
  set X := n.v.X + n.d.X * t - Dn * n.d.Y * t ^ 2
  set Y := n.v.Y + n.d.Y * t + n.d.X * t ^ 2
  rw [unfilled]
  refine ⟨?_, fun hU => ?_⟩
  · rw [htarget]
    refine Tri.mem_of_edges Dn hD I.tgt htok X Y ?_
    intro i hi
    have hall := List.all_eq_true.mp F.tgtQ (I.tgt.edge i)
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    exact okPos_sound I Dn hDn n.v n.d F.vw F.dw _ _ _ F.tauN F.tauD hall t ht0 htτ
  · obtain ⟨i, hi, hm⟩ := Set.mem_iUnion₂.mp hU
    obtain ⟨T, hT, hTc⟩ := hSt i hi
    rw [hTc] at hm
    obtain ⟨e, he⟩ := zip_all_ex _ cfg n.fedges F.flen F.tileQ T hT
    have hneg := okNeg_sound I Dn hDn n.v n.d F.vw F.dw _ _ _ F.tauN F.tauD he t ht0 htτ
    have hnn := Tri.edge_nonneg Dn hD T (hcfg T hT) X Y hm (e % 3) (Nat.mod_lt _ (by norm_num))
    rw [← Tri.edge_mod] at hnn
    linarith



/-! ### M2 -/

theorem killsSoundM (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (htok : I.tgt.ok = true) (v d : Pt) (hvw : 0 < v.w) (hdw : 0 < d.w)
    (hdu : d.x * d.x + I.Dn * d.y * d.y = d.w * d.w)
    (cfg : List Tri) (hcfgok : ∀ t ∈ cfg, t.ok = true)
    {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (htarget : D.target.carrier = I.tgt.carr Dn) (j : Fin N)
    (hreal : ∀ t ∈ cfg, ∃ i, i ≠ j ∧ (D.tile i).carrier = t.carr Dn)
    (R : NodeM → List Tri → Bool) :
    ∀ (ks : List Kill) (ps : List Place) (ch : List NodeM),
      (∀ p ∈ ps, 0 < p.l1 ∧ 0 < p.pd ∧ 0 < p.qd ∧ 0 < p.qn) →
      (∀ c p, p ∈ ps → R c (cfg ++ [placeTri I v d p]) = true →
        (D.tile j).carrier = (placeTri I v d p).carr Dn → False) →
      killsCheckM I cfg v d ks ps ch R = true →
      ∀ p ∈ ps, (D.tile j).carrier = (placeTri I v d p).carr Dn → False := by
  intro ks
  induction ks with
  | nil =>
    intro ps ch _ _ hk p hp
    cases ps with
    | nil => simp at hp
    | cons _ _ => simp [killsCheckM] at hk
  | cons k ks ih =>
    intro ps ch hpl hR hk p hp hj
    cases ps with
    | nil => simp [killsCheckM] at hk
    | cons p' ps =>
      have hpl' := hpl p' (List.mem_cons_self ..)
      obtain ⟨pl1, ppd, pqd, pqn⟩ := hpl'
      have htri := placeTri_ok I v d p' hvw hdw hdu (by exact_mod_cast (hDn ▸ hD : (0:ℝ) < I.Dn)) pl1 ppd pqd pqn
      have hwb : 0 < (placeTri I v d p').b.w := by
        show 0 < v.w * d.w; positivity
      have hwc : 0 < (placeTri I v d p').c.w := by
        show 0 < v.w * d.w * p'.pd * p'.qd; positivity
      by_cases hpp : p = p'
      · subst hpp
        -- the head kill applies
        cases k with
        | esc q e =>
          simp only [killsCheckM, killOk, Bool.and_eq_true, decide_eq_true_eq] at hk
          obtain ⟨hdet, -⟩ := hk
          cases q
          · simp only [Bool.false_eq_true, if_false] at hdet
            exact esc_sound_D Dn hD I htok D htarget _ j hj e _ hwb
              (Tri.vert_re_mem Dn (placeTri I v d p) 1) hdet
          · simp only [if_true] at hdet
            exact esc_sound_D Dn hD I htok D htarget _ j hj e _ hwc
              (Tri.vert_re_mem Dn (placeTri I v d p) 2) hdet
        | ovl m w =>
          simp only [killsCheckM, killOk] at hk
          cases hm : cfg[m]? with
          | none => rw [hm] at hk; simp at hk
          | some U =>
            rw [hm] at hk
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
            obtain ⟨⟨⟨hw, h1⟩, h2⟩, -⟩ := hk
            have hUm : U ∈ cfg := List.mem_of_getElem? hm
            obtain ⟨i, hij, hi⟩ := hreal U hUm
            exact ovl_sound_D Dn hD D _ U htri (hcfgok U hUm) i j hij hi hj w hw h1 h2
        | child =>
          simp only [killsCheckM] at hk
          cases ch with
          | nil => simp at hk
          | cons c cs =>
            simp only [Bool.and_eq_true] at hk
            exact hR c p (List.mem_cons_self ..) hk.1 hj
      · have hpps : p ∈ ps := (List.mem_cons.mp hp).resolve_left hpp
        have hpl2 : ∀ q ∈ ps, 0 < q.l1 ∧ 0 < q.pd ∧ 0 < q.qd ∧ 0 < q.qn :=
          fun q hq => hpl q (List.mem_cons_of_mem _ hq)
        have hR2 : ∀ c q, q ∈ ps → R c (cfg ++ [placeTri I v d q]) = true →
            (D.tile j).carrier = (placeTri I v d q).carr Dn → False :=
          fun c q hq => hR c q (List.mem_cons_of_mem _ hq)
        cases k with
        | esc q e =>
          simp only [killsCheckM, Bool.and_eq_true] at hk
          exact ih ps ch hpl2 hR2 hk.2 p hpps hj
        | ovl m w =>
          simp only [killsCheckM] at hk
          cases hm : cfg[m]? with
          | none => simp [killOk, hm] at hk
          | some U =>
            simp only [killOk, hm, Bool.and_eq_true] at hk
            exact ih ps ch hpl2 hR2 hk.2 p hpps hj
        | child =>
          simp only [killsCheckM] at hk
          cases ch with
          | nil => simp at hk
          | cons c cs =>
            simp only [Bool.and_eq_true] at hk
            exact ih ps cs hpl2 hR2 hk.2 p hpps hj


/-! ### M3 -/

theorem triEqM_eq (s t : Tri) (h : triEqM s t = true) : s = t := by
  rcases s with ⟨⟨x1, y1, w1⟩, ⟨x2, y2, w2⟩, ⟨x3, y3, w3⟩⟩
  rcases t with ⟨⟨x1', y1', w1'⟩, ⟨x2', y2', w2'⟩, ⟨x3', y3', w3'⟩⟩
  simp_all [triEqM, ptEqM]

theorem cfgSub_mem (c cfg : List Tri) (h : cfgSub c cfg = true) : ∀ t ∈ c, t ∈ cfg := by
  intro t ht
  have h1 := List.all_eq_true.mp h t ht
  obtain ⟨u, hu, he⟩ := List.any_eq_true.mp h1
  rw [triEqM_eq t u he]; exact hu

theorem checkNodeM_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (M : Erdos634.Geometry.Tri)
    (hMa : dist (M.pts 0) (M.pts 1) = I.sides.1) (hMb : dist (M.pts 1) (M.pts 2) = I.sides.2.1)
    (hMc : dist (M.pts 0) (M.pts 2) = I.sides.2.2)
    (hI : I.ok = true) (known : List (List Tri))
    (hk : ∀ c ∈ known, Sound Dn I M c) :
    ∀ (fuel : Nat) (cfg : List Tri) (n : NodeM), (∀ t ∈ cfg, t.ok = true) →
      checkNodeM I known fuel cfg n = true → Sound Dn I M cfg := by
  obtain ⟨htok, hDpos, p1, p2, p3, p4, p5, p6, hpl, o1, o2, o3, o4, o5, o6⟩ := Inst_ok_facts I hI
  intro fuel
  induction fuel with
  | zero => intro cfg n _ h; simp [checkNodeM] at h
  | succ fuel ih =>
    intro cfg n hcfgok hchk N D htg hm hreal
    classical
    by_cases hst : (n.tauN == 0) = true
    · simp only [checkNodeM, hst, if_true] at hchk
      obtain ⟨c, hc, hce⟩ := List.any_eq_true.mp hchk
      exact hk c hc D htg hm (fun t ht => hreal t (cfgSub_mem c cfg hce t ht))
    have hne : (n.tauN == 0) = false := by simpa using hst
    simp only [checkNodeM, hne, Bool.false_eq_true, if_false, Bool.and_eq_true] at hchk
    obtain ⟨hloc, hkills⟩ := hchk
    have F := nodeLocalOkM_facts I cfg n hloc
    set S : Finset (Fin N) := Finset.univ.filter (fun i => ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn) with hSdef
    have hS : ∀ t ∈ cfg, ∃ i ∈ S, (D.tile i).carrier = t.carr Dn := by
      intro t ht
      obtain ⟨i, hi⟩ := hreal t ht
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, hi⟩, hi⟩
    have hSt : ∀ i ∈ S, ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hcone := cone_soundM Dn hD I htok cfg hcfgok n F D htg S hS
    have hfree := hfree_soundM Dn hD I hDn htok cfg hcfgok n F D htg S hSt
    have hdg := dg_re Dn hD I cfg n F
    have hunit := unit_re Dn hD I hDn n.d F.dw F.unit
    obtain ⟨j, hjS, k0, k1, k2, h01, h02, h12, hk0, ⟨c', hc', hk1⟩, hk2⟩ :=
      placement_completeness_cone D.toDissection S (n.v.re Dn) (n.d.re Dn) (n.g.re Dn) hunit hdg
        hcone hfree
    have hcong : (D.tile j).Congruent M := (D.tiles_congruent j).trans hm
    have hsix := six_placements hcong hMa hMb hMc hunit h01 h02 h12 hk0 hc' hk1 hk2
    -- the numerics of every placement
    have hpos : ∀ p ∈ I.pl, 0 < p.l1 ∧ 0 < p.pd ∧ 0 < p.qd ∧ 0 < p.qn := by
      intro p hp
      rw [hpl] at hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · have := placeOk_facts I _ _ _ _ o1; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o2; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o3; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o4; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o5; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o6; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
    -- one of the six placements is realised by tile `j`
    have hrealj : ∃ p ∈ I.pl, (D.tile j).carrier = (placeTri I n.v n.d p).carr Dn := by
      have key := fun (l1 l2 l3 : R) (p : Place) (hp : placeOk I l1 l2 l3 p = true)
          (h1 : (D.tile j).pts k1 = n.v.re Dn + (l1 : ℝ) • n.d.re Dn)
          (h2 : (D.tile j).pts k2 = placeThird (n.v.re Dn) (n.d.re Dn) l1 l2 l3) =>
        place_sound Dn hD I hDn n.v n.d F.vw F.dw F.unit l1 l2 l3 p hp (D.tile j) h01 h02 h12 hk0 h1 h2
      rcases hsix with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨p1, by simp [hpl], key _ _ _ p1 o1 h1 h2⟩
      · exact ⟨p2, by simp [hpl], key _ _ _ p2 o2 h1 h2⟩
      · exact ⟨p3, by simp [hpl], key _ _ _ p3 o3 h1 h2⟩
      · exact ⟨p4, by simp [hpl], key _ _ _ p4 o4 h1 h2⟩
      · exact ⟨p5, by simp [hpl], key _ _ _ p5 o5 h1 h2⟩
      · exact ⟨p6, by simp [hpl], key _ _ _ p6 o6 h1 h2⟩
    obtain ⟨pj, hpj, hjc⟩ := hrealj
    have hreal' : ∀ t ∈ cfg, ∃ i, i ≠ j ∧ (D.tile i).carrier = t.carr Dn := by
      intro t ht
      obtain ⟨i, hiS, hi⟩ := hS t ht
      exact ⟨i, fun h => hjS (h ▸ hiS), hi⟩
    refine killsSoundM Dn hD I hDn htok n.v n.d F.vw F.dw F.unit cfg hcfgok D htg j hreal'
      (fun c cfg' => checkNodeM I known fuel cfg' c) n.kills I.pl n.children hpos ?_ hkills pj hpj hjc
    intro c p hp hrec hj
    obtain ⟨pl1, ppd, pqd, pqn⟩ := hpos p hp
    have htri := placeTri_ok I n.v n.d p F.vw F.dw F.unit hDpos pl1 ppd pqd pqn
    refine ih (cfg ++ [placeTri I n.v n.d p]) c ?_ hrec D htg hm ?_
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hcfgok t h
      · simp only [List.mem_singleton] at h; subst h; exact htri
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hreal t h
      · simp only [List.mem_singleton] at h; subst h; exact ⟨j, hj⟩


theorem checkAllM_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (M : Erdos634.Geometry.Tri)
    (hMa : dist (M.pts 0) (M.pts 1) = I.sides.1) (hMb : dist (M.pts 1) (M.pts 2) = I.sides.2.1)
    (hMc : dist (M.pts 0) (M.pts 2) = I.sides.2.2) (known : List (List Tri))
    (hk : ∀ c ∈ known, Sound Dn I M c) (fuel : Nat) (n : NodeM)
    (h : I.checkAllM known fuel n = true) : Sound Dn I M [] := by
  unfold Inst.checkAllM at h
  simp only [Bool.and_eq_true] at h
  exact checkNodeM_sound Dn hD I hDn M hMa hMb hMc h.1 known hk fuel [] n (by simp) h.2



end ReflS

#print axioms ReflS.checkNodeM_sound
#print axioms ReflS.checkAllM_sound
