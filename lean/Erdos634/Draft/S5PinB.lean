/-
Draft/S5PinB.lean -- the apex of the first `c`-tile of a side is straddled from the far side of its upper edge.

Setting: a wall `w` of the target from a corner `w.a` of angle `α + β`, its ordered edge chain `E 0, …, E (n-1)`, and the
FIRST `c`-edge `E j` of the chain.  Let `C` be its tile, `W` the west end of the edge, `G` the apex of `C`.

* `cascade_east`: every tile before `E j` presents `γ` at its east end.
* `far_edge_exact`: if neither `W` nor `G` is straddled from the far side of the line `W G`, another tile has an edge
  exactly `[W, G]` (using that `|W G| ∈ {a, b}` is not a word of two or more letters).
* `no_shared_upper`: no other tile has an edge exactly `[W, G]` (the pinned end: corner figure `(1,1,0)`, or
  junction figure `(1,1,1)` and supplementary angles).
* `apex_straddled`: hence `G` is straddled from the far side of the line `W G`.

No sorry, no native_decide.
-/
import Erdos634.Draft.S5PinA

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Placement Erdos634.GLI Erdos634.BaseChain
  Erdos634.SideWall Erdos634.Draft.TraceCovering Set

namespace Erdos634.Draft.S5Pin

variable {N : ℕ}

/-- length of a tile edge -/
noncomputable def elen (D : CongruentDissection N) (p : Fin N × Fin 3) : ℝ :=
  dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1))

/-! ## The two ends of a chain edge, as vertex indices -/

theorem east_other {D : Dissection N} (w : Wall D) {E : ℕ → Fin N × Fin 3} {n : ℕ} (Ch : IsChain w E n)
    {m : ℕ} (hm : m < n) :
    ∃ kP kQ : Fin 3, ((kP = (E m).2 ∧ kQ = (E m).2 + 1) ∨ (kP = (E m).2 + 1 ∧ kQ = (E m).2)) ∧
      (D.tile (E m).1).pts kP = edgeWest D w.dir (E m) ∧ (D.tile (E m).1).pts kQ = edgeEast D w.dir (E m) ∧
      w.g ((D.tile (E m).1).pts kP) = 0 ∧ w.g ((D.tile (E m).1).pts kQ) = 0 ∧
      w.dir ((D.tile (E m).1).pts kP) < w.dir ((D.tile (E m).1).pts kQ) := by
  have hwm := (mem_wallList D w.g 0 (E m)).mp (Ch.mem m hm)
  have hnd := Ch.nondeg m hm
  rw [← dir_edgeWest, ← dir_edgeEast] at hnd
  by_cases h : w.dir ((D.tile (E m).1).pts (E m).2) ≤ w.dir ((D.tile (E m).1).pts ((E m).2 + 1))
  · have hW : edgeWest D w.dir (E m) = (D.tile (E m).1).pts (E m).2 := by rw [edgeWest, if_pos h]
    have hE : edgeEast D w.dir (E m) = (D.tile (E m).1).pts ((E m).2 + 1) := by rw [edgeEast, if_pos h]
    refine ⟨(E m).2, (E m).2 + 1, Or.inl ⟨rfl, rfl⟩, hW.symm, hE.symm, hwm.1, hwm.2, ?_⟩
    rw [hW, hE] at hnd; exact hnd
  · have hW : edgeWest D w.dir (E m) = (D.tile (E m).1).pts ((E m).2 + 1) := by rw [edgeWest, if_neg h]
    have hE : edgeEast D w.dir (E m) = (D.tile (E m).1).pts (E m).2 := by rw [edgeEast, if_neg h]
    refine ⟨(E m).2 + 1, (E m).2, Or.inr ⟨rfl, rfl⟩, hW.symm, hE.symm, hwm.2, hwm.1, ?_⟩
    rw [hW, hE] at hnd; exact hnd

/-! ## The cascade (Lemma 8) -/

theorem cascade_east {D : CongruentDissection N} {α β γ a b c : ℝ} (X : Ctx D α β γ a b c)
    (w : Wall D.toDissection) {E : ℕ → Fin N × Fin 3} {n : ℕ} (Ch : IsChain w E n) (ka : Fin 3)
    (hwa : w.a = D.target.pts ka)
    (hcorner : cornerAngle (D.target.pts (ka + 1)) (D.target.pts ka) (D.target.pts (ka + 2)) < γ)
    {j : ℕ} (hj : j ≤ n) (hfirst : ∀ m, m < j → elen D (E m) ≠ c) :
    ∀ m, m < j → (D.tile (E m).1).localAngle (edgeEast D.toDissection w.dir (E m)) = γ := by
  obtain ⟨⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩, -⟩ := Erdos634.CornerPara.angleFacts X.hA
  have hgam : ∀ m, m < j →
      ((D.tile (E m).1).localAngle (edgeWest D.toDissection w.dir (E m)) = γ ∧
          (D.tile (E m).1).localAngle (edgeEast D.toDissection w.dir (E m)) ≠ γ) ∨
      ((D.tile (E m).1).localAngle (edgeEast D.toDissection w.dir (E m)) = γ ∧
          (D.tile (E m).1).localAngle (edgeWest D.toDissection w.dir (E m)) ≠ γ) := by
    intro m hm
    obtain ⟨jj, hjj⟩ := exists_matching_side D (E m).1 (E m).2
    have hne2 : jj ≠ 2 := by
      intro h2
      rw [h2, X.hs2] at hjj
      exact hfirst m hm hjj
    have hg := gamma_at_one_endpoint D α β γ X.hα' X.hβ' X.hγ' X.scalene hαγ hβγ (E m).1 (E m).2 jj hne2 hjj
    rcases localAngle_edgeWest_edgeEast D.toDissection w.dir (E m).1 (E m).2 with ⟨hW, hE⟩ | ⟨hW, hE⟩
    · rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [hW, hE]; exact ⟨h1, h2⟩
      · right; rw [hW, hE]; exact ⟨h1, h2⟩
    · rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; rw [hW, hE]; exact ⟨h1, h2⟩
      · left; rw [hW, hE]; exact ⟨h1, h2⟩
  intro m
  induction m with
  | zero =>
    intro hm
    rcases hgam 0 hm with ⟨h1, _⟩ | ⟨h1, _⟩
    · exfalso
      rw [Ch.west0, hwa] at h1
      have hle := Erdos634.Geometry.Dissection.localAngle_le_corner D.toDissection (E 0).1 ka
      linarith
    · exact h1
  | succ m ih =>
    intro hm
    have ihm := ih (by omega)
    rcases hgam (m + 1) hm with ⟨h1, _⟩ | ⟨h1, _⟩
    · exfalso
      have hjunc := Ch.junc m (by omega)
      have hnv := Ch.junction_boundary (m := m) (by omega)
      rw [← hjunc] at h1
      exact Erdos634.Geometry.Dissection.congruentDissection_no_double_gamma D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
        hγπ hγ0 hπ0 X.hA.hγdef X.hA.hrel X.hA.hirr X.hα' X.hβ' X.hγ' hnv.1 hnv.2 (E m).1 (E (m + 1)).1
        (Ch.tile_ne (by omega) (by omega) (by omega)) ihm h1
    · exact h1

/-! ## The line of an upper edge -/

/-- the line through two vertices `kW`, `kG` of a triangle is the zero set of the third barycentric coordinate -/
theorem line_facts (T : Tri) (kW kE kG : Fin 3) (hWE : kW ≠ kE) (hEG : kE ≠ kG) :
    (T.basis.coord kE).linear ≠ 0 ∧ (T.basis.coord kE).linear (T.pts kW) = -(T.basis.coord kE 0) ∧
    (T.basis.coord kE).linear (T.pts kG - T.pts kW) = 0 ∧
    (∀ y, (T.basis.coord kE).linear y = -(T.basis.coord kE 0) ↔ T.basis.coord kE y = 0) := by
  have hAW : T.basis.coord kE (T.pts kW) = 0 := Erdos634.Draft.NearBaseVertex.coord_other T hWE.symm
  have hAG : T.basis.coord kE (T.pts kG) = 0 := Erdos634.Draft.NearBaseVertex.coord_other T hEG
  have hAV : T.basis.coord kE (T.pts kE) = 1 := Erdos634.Draft.NearBaseVertex.coord_self T kE
  have hfc : ∀ y, (T.basis.coord kE).linear y = -(T.basis.coord kE 0) ↔ T.basis.coord kE y = 0 := by
    intro y
    rw [aff_apply (T.basis.coord kE) y]
    constructor <;> intro h <;> linarith
  refine ⟨?_, (hfc _).mpr hAW, ?_, hfc⟩
  · intro h
    have h1 := aff_sub (T.basis.coord kE) (T.pts kE) (T.pts kW)
    rw [h, hAV, hAW] at h1
    simp at h1
  · rw [aff_sub, hAG, hAW, sub_zero]

theorem param_mem (W G : Plane) {ℓ x : ℝ} (hℓ : 0 < ℓ) (hx0 : 0 < x) (hx1 : x < ℓ) :
    W + x • (ℓ⁻¹ • (G - W)) ∈ openSegment ℝ W G := by
  rw [openSegment_eq_image']
  exact ⟨x / ℓ, ⟨div_pos hx0 hℓ, (div_lt_one hℓ).mpr hx1⟩, by simp only [smul_smul, div_eq_mul_inv]⟩

/-! ## Lemma 5 + Lemma 10: an exact cover of the upper edge is a single edge -/

theorem far_edge_exact {D : CongruentDissection N} {α β γ a b c : ℝ} (X : Ctx D α β γ a b c)
    (i : Fin N) (kW kE kG : Fin 3) (hWE : kW ≠ kE) (hWG : kW ≠ kG) (hEG : kE ≠ kG)
    (hℓ : dist ((D.tile i).pts kW) ((D.tile i).pts kG) = a ∨ dist ((D.tile i).pts kW) ((D.tile i).pts kG) = b)
    (hint : openSegment ℝ ((D.tile i).pts kW) ((D.tile i).pts kG) ⊆ interior D.target.carrier)
    (hW : ¬ Straddled D.toDissection ((D.tile i).basis.coord kE).linear (-((D.tile i).basis.coord kE 0))
      ((D.tile i).pts kW))
    (hG : ¬ Straddled D.toDissection ((D.tile i).basis.coord kE).linear (-((D.tile i).basis.coord kE 0))
      ((D.tile i).pts kG)) :
    ∃ e : Fin N × Fin 3, e.1 ≠ i ∧
      (((D.tile e.1).pts e.2 = (D.tile i).pts kW ∧ (D.tile e.1).pts (e.2 + 1) = (D.tile i).pts kG) ∨
       ((D.tile e.1).pts e.2 = (D.tile i).pts kG ∧ (D.tile e.1).pts (e.2 + 1) = (D.tile i).pts kW)) := by
  obtain ⟨hf, hX, hu', hfc⟩ := line_facts (D.tile i) kW kE kG hWE hEG
  generalize hfdef : ((D.tile i).basis.coord kE).linear = f at hf hX hu' hfc hW hG
  generalize hcdef : -((D.tile i).basis.coord kE 0) = c0 at hX hfc hW hG
  generalize hWdef : (D.tile i).pts kW = W at *
  generalize hGdef : (D.tile i).pts kG = G at *
  have hWG' : W ≠ G := by
    rw [← hWdef, ← hGdef]; exact (D.tile i).indep.injective.ne hWG
  have hℓpos : 0 < dist W G := dist_pos.mpr hWG'
  generalize hℓdef : dist W G = ℓ at hℓ hℓpos
  have hu1 : ‖ℓ⁻¹ • (G - W)‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hℓpos, ← dist_eq_norm, dist_comm, hℓdef]
    exact inv_mul_cancel₀ hℓpos.ne'
  have hu0 : ℓ⁻¹ • (G - W) ≠ 0 := ne_zero_of_norm hu1
  have hG_eq : G = W + ℓ • (ℓ⁻¹ • (G - W)) := by
    rw [smul_smul, mul_inv_cancel₀ hℓpos.ne', one_smul]; abel
  have hu : f (ℓ⁻¹ • (G - W)) = 0 := by rw [map_smul, hu', smul_zero]
  have hgd : ∀ y, f y = c0 ↔ f y = c0 := fun _ => Iff.rfl
  -- the edge `[W, G]` of tile `i`
  have hedge : segment ℝ W G ⊆ (D.tile i).edge (kE + 1) := by
    rw [Tri.edge, (fin3_shift kE).1, ← hWdef, ← hGdef]
    rcases fin3_other kE kW kG hWE.symm hEG hWG with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, segment_symm]
  have hint' : ∀ x ∈ Ioo 0 ℓ, W + x • (ℓ⁻¹ • (G - W)) ∈ interior D.target.carrier :=
    fun x hx => hint (param_mem W G hℓpos hx.1 hx.2)
  have hwall : ∀ x ∈ Ioo 0 ℓ, ∀ i', W + x • (ℓ⁻¹ • (G - W)) ∉ interior (D.toDissection.tile i').carrier :=
    fun x hx i' => D.toDissection.edge_point_not_interior
      (hedge (openSegment_subset_segment ℝ W G (param_mem W G hℓpos hx.1 hx.2))) i'
  have hs : ¬ Straddled D.toDissection f c0 (W + (0 : ℝ) • (ℓ⁻¹ • (G - W))) := by
    rw [zero_smul, add_zero]; exact hW
  have ht : ¬ Straddled D.toDissection f c0 (W + ℓ • (ℓ⁻¹ • (G - W))) := by
    rw [← hG_eq]; exact hG
  have hsum := wall_sum (D := D.toDissection) hf hgd hf hX hu hu1 hℓpos.le hint' hwall hs ht
  rw [sub_zero] at hsum
  generalize hSdef : (D.toDissection.lineChain f c0).filter
      (fun e => (D.toDissection.tile e.1).edge e.2
        ⊆ segment ℝ (W + (0 : ℝ) • (ℓ⁻¹ • (G - W))) (W + ℓ • (ℓ⁻¹ • (G - W)))) = S at hsum
  obtain ⟨x, y, hcard, hsumw⟩ := sum_abc S
    (fun e => dist ((D.toDissection.tile e.1).pts e.2) ((D.toDissection.tile e.1).pts (e.2 + 1))) a b c
    (fun e _ => X.len_cases e.1 e.2)
  have hS1 : S.card = 1 := by
    rw [← hcard]
    rcases hℓ with h | h
    · exact X.hwa x y _ (by rw [← hsumw, hsum]; exact h.symm)
    · exact X.hwb x y _ (by rw [← hsumw, hsum]; exact h.symm)
  obtain ⟨e0, he0⟩ := Finset.card_eq_one.mp hS1
  have hmem : e0 ∈ S := by rw [he0]; exact Finset.mem_singleton_self _
  rw [← hSdef, Finset.mem_filter] at hmem
  obtain ⟨he0L, hins⟩ := hmem
  rw [he0, Finset.sum_singleton] at hsum
  obtain ⟨hlo, hhi⟩ := (inside_iff hgd hf hX hu hu0 he0L hℓpos.le).mp hins
  obtain ⟨h0, h1⟩ := onLine hgd he0L
  obtain ⟨hlt, -, -, hdist⟩ := edge_data (D := D.toDissection) (X := W) hf hX hu hu0 h0 h1
  have hd := hdist hu1
  rw [hsum] at hd
  have hlo0 : lo D.toDissection W (ℓ⁻¹ • (G - W)) e0 = 0 := by linarith
  have hhiℓ : hi D.toDissection W (ℓ⁻¹ • (G - W)) e0 = ℓ := by linarith
  have e0' := par_spec (exists_param hf hX hu hu0 h0)
  have e1' := par_spec (exists_param hf hX hu hu0 h1)
  refine ⟨e0, ?_, ?_⟩
  · -- the far tile is not `i`: its vertices have `coord kE ≤ 0`
    intro heq
    have hall := (Dissection.mem_lineChain.mp he0L).2.2 kE
    rw [heq] at hall
    have hAV : (D.tile i).basis.coord kE ((D.tile i).pts kE) = 1 :=
      Erdos634.Draft.NearBaseVertex.coord_self (D.tile i) kE
    have h2 := aff_apply ((D.tile i).basis.coord kE) ((D.tile i).pts kE)
    rw [hfdef, hAV] at h2
    have h3 : f ((D.toDissection.tile i).pts kE) ≤ c0 := hall
    have h4 : f ((D.toDissection.tile i).pts kE) = f ((D.tile i).pts kE) := rfl
    linarith
  · simp only [lo, hi] at hlo0 hhiℓ
    rcases le_total (par W (ℓ⁻¹ • (G - W)) ((D.toDissection.tile e0.1).pts e0.2))
        (par W (ℓ⁻¹ • (G - W)) ((D.toDissection.tile e0.1).pts (e0.2 + 1))) with h | h
    · rw [min_eq_left h] at hlo0
      rw [max_eq_right h] at hhiℓ
      left
      refine ⟨?_, ?_⟩
      · have : (D.toDissection.tile e0.1).pts e0.2 = W := by rw [e0', hlo0, zero_smul, add_zero]
        exact this
      · have : (D.toDissection.tile e0.1).pts (e0.2 + 1) = G := by rw [e1', hhiℓ, ← hG_eq]
        exact this
    · rw [min_eq_right h] at hlo0
      rw [max_eq_left h] at hhiℓ
      right
      refine ⟨?_, ?_⟩
      · have : (D.toDissection.tile e0.1).pts e0.2 = G := by rw [e0', hhiℓ, ← hG_eq]
        exact this
      · have : (D.toDissection.tile e0.1).pts (e0.2 + 1) = W := by rw [e1', hlo0, zero_smul, add_zero]
        exact this

/-! ## The west end is not straddled from above -/

theorem not_straddled_at_wall {D : CongruentDissection N} (w : Wall D.toDissection)
    (i : Fin N) (kW kE kG : Fin 3) (hWE : kW ≠ kE) (hWG : kW ≠ kG) (hEG : kE ≠ kG)
    (hW0 : w.g ((D.tile i).pts kW) = 0) (hGneg : w.g ((D.tile i).pts kG) < 0) :
    ¬ Straddled D.toDissection ((D.tile i).basis.coord kE).linear (-((D.tile i).basis.coord kE 0))
      ((D.tile i).pts kW) := by
  obtain ⟨hf, hX, hu, hfc⟩ := line_facts (D.tile i) kW kE kG hWE hEG
  have hu0 : (D.tile i).pts kG - (D.tile i).pts kW ≠ 0 :=
    sub_ne_zero.mpr ((D.tile i).indep.injective.ne hWG.symm)
  have key := not_straddled_of_outside_before (D := D.toDissection)
    (g := ((D.tile i).basis.coord kE).linear) (d := -((D.tile i).basis.coord kE 0))
    (fun _ => Iff.rfl) hf hX hu hu0 (x₀ := 0) (by
      intro t ht hmem
      have hle := w.hwall _ hmem
      have hlin : w.g.linear ((D.tile i).pts kW + t • ((D.tile i).pts kG - (D.tile i).pts kW))
          = w.g.linear ((D.tile i).pts kW) + t * (w.g ((D.tile i).pts kG) - w.g ((D.tile i).pts kW)) := by
        rw [map_add, map_smul, aff_sub, smul_eq_mul]
      have h1 := aff_apply w.g ((D.tile i).pts kW + t • ((D.tile i).pts kG - (D.tile i).pts kW))
      have h2 := aff_apply w.g ((D.tile i).pts kW)
      rw [hlin, hW0] at h1
      rw [hW0] at h2
      rw [sub_zero] at h1
      have h4 : 0 < t * w.g ((D.tile i).pts kG) := mul_pos_of_neg_of_neg ht hGneg
      linarith)
  rw [zero_smul, add_zero] at key
  exact key

/-! ## The open upper edge is interior to the target -/

theorem mem_side_of_coord_zero (T : Tri) (ia ib ic : Fin 3) (hab : ia ≠ ib) (hac : ia ≠ ic) (hbc : ib ≠ ic)
    {y : Plane} (hy : y ∈ T.carrier) (h0 : T.basis.coord ib y = 0) :
    y ∈ segment ℝ (T.pts ia) (T.pts ic) := by
  have hw : wallFun T (ib + 1) y = 0 := by
    show -(T.basis.coord (ib + 1 + 2) y) = 0
    rw [(fin3_shift ib).2.2.2, h0, neg_zero]
  have h := hface_wallFun T (ib + 1) y hy hw
  rw [(fin3_shift ib).1] at h
  rcases fin3_other ib ia ic hab.symm hbc hac with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at h; exact h
  · rw [h1, h2, segment_symm] at h; exact h

theorem angle_ray {A B C V G : Plane} (hV : V ∈ segment ℝ A B) (hVA : V ≠ A) (hG : G ∈ segment ℝ A C)
    (hGA : G ≠ A) : cornerAngle V A G = cornerAngle B A C := by
  rw [segment_eq_image'] at hV hG
  obtain ⟨s, ⟨hs0, -⟩, hVeq⟩ := hV
  obtain ⟨t, ⟨ht0, -⟩, hGeq⟩ := hG
  have hs : 0 < s := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hVA; rw [← hVeq, ← h]; simp
  have ht : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hGA; rw [← hGeq, ← h]; simp
  have e1 : V - A = s • (B - A) := by rw [← hVeq]; simp
  have e2 : G - A = t • (C - A) := by rw [← hGeq]; simp
  unfold cornerAngle EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  rw [e1, e2, InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
    InnerProductGeometry.angle_smul_right_of_pos _ _ ht]

theorem upper_edge_interior {D : CongruentDissection N} {α β γ a b c : ℝ} (X : Ctx D α β γ a b c)
    (w : Wall D.toDissection) (ka kb kc : Fin 3) (hkab : ka ≠ kb) (hkac : ka ≠ kc) (hkbc : kb ≠ kc)
    (hwa : w.a = D.target.pts ka) (hwb : w.b = D.target.pts kb)
    (hwg : ∀ y, w.g y = -(D.target.basis.coord kc y))
    (hcorner : cornerAngle (D.target.pts kb) (D.target.pts ka) (D.target.pts kc) = α + β)
    (i : Fin N) (kW kE kG : Fin 3) (hWE : kW ≠ kE) (hWG : kW ≠ kG) (hEG : kE ≠ kG)
    (hW0 : w.g ((D.tile i).pts kW) = 0) (hE0 : w.g ((D.tile i).pts kE) = 0)
    (hGneg : w.g ((D.tile i).pts kG) < 0) (hWb : (D.tile i).pts kW ≠ w.b)
    (hangW : (D.tile i).localAngle ((D.tile i).pts kW) = α ∨ (D.tile i).localAngle ((D.tile i).pts kW) = β) :
    openSegment ℝ ((D.tile i).pts kW) ((D.tile i).pts kG) ⊆ interior D.target.carrier := by
  have hα := X.hA.hα
  have hβ := X.hA.hβ
  have hcar : ∀ m, (D.tile i).pts m ∈ D.target.carrier := fun m =>
    Erdos634.BaseSelection.tile_subset_target D.toDissection i
      (subset_convexHull ℝ _ (Set.mem_range_self m))
  have hnn : ∀ m j, 0 ≤ D.target.basis.coord j ((D.tile i).pts m) := by
    intro m j
    have h := hcar m
    rw [D.target.carrier_eq_nonneg_coord] at h
    exact h j
  have hcW : D.target.basis.coord kc ((D.tile i).pts kW) = 0 := by
    have := hwg ((D.tile i).pts kW); rw [hW0] at this; linarith
  have hcG : 0 < D.target.basis.coord kc ((D.tile i).pts kG) := by
    have := hwg ((D.tile i).pts kG); linarith
  have haW : 0 < D.target.basis.coord ka ((D.tile i).pts kW) := by
    rcases (hnn kW ka).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hWb
      rw [hwb]
      apply eq_vertex_of_coords
      intro jj hjj
      rcases fin3_cover ka kb kc hkab hkac hkbc jj with rfl | rfl | rfl
      · exact h.symm
      · exact absurd rfl hjj
      · exact hcW
  intro y hy
  rw [Tri.mem_interior_iff_coord_pos]
  intro m
  obtain ⟨s, t, hs, ht, -, hco⟩ := coord_openSegment D.target m hy
  rw [hco]
  rcases fin3_cover ka kb kc hkab hkac hkbc m with rfl | rfl | rfl
  · have := mul_pos hs haW
    have := mul_nonneg ht.le (hnn kG m)
    linarith
  · -- the side through the corner `w.a`
    by_cases hbW : 0 < D.target.basis.coord m ((D.tile i).pts kW)
    · have := mul_pos hs hbW
      have := mul_nonneg ht.le (hnn kG m)
      linarith
    · have hbW0 : D.target.basis.coord m ((D.tile i).pts kW) = 0 := le_antisymm (not_lt.mp hbW) (hnn kW m)
      have hWa : (D.tile i).pts kW = D.target.pts ka := by
        apply eq_vertex_of_coords
        intro jj hjj
        rcases fin3_cover ka m kc hkab hkac hkbc jj with rfl | rfl | rfl
        · exact absurd rfl hjj
        · exact hbW0
        · exact hcW
      have hbG : 0 < D.target.basis.coord m ((D.tile i).pts kG) := by
        rcases (hnn kG m).lt_or_eq with h | h
        · exact h
        · exfalso
          have hGseg := mem_side_of_coord_zero D.target ka m kc hkab hkac hkbc (hcar kG) h.symm
          have hEseg : (D.tile i).pts kE ∈ segment ℝ (D.target.pts ka) (D.target.pts m) := by
            have := w.hface _ (hcar kE) hE0
            rw [hwa, hwb] at this
            exact this
          have hEne : (D.tile i).pts kE ≠ D.target.pts ka := by
            rw [← hWa]; exact (D.tile i).indep.injective.ne hWE.symm
          have hGne : (D.tile i).pts kG ≠ D.target.pts ka := by
            rw [← hWa]; exact (D.tile i).indep.injective.ne hWG.symm
          have hang := angle_ray hEseg hEne hGseg hGne
          rw [hcorner, ← hWa, ← localAngle_three (D.tile i) kW kE kG hWE hWG hEG] at hang
          rcases hangW with h1 | h1 <;> rw [h1] at hang <;> linarith
      have := mul_nonneg hs.le (hnn kW m)
      have := mul_pos ht hbG
      linarith
  · rw [hcW]
    have := mul_pos ht hcG
    linarith

/-! ## The pinned end: no other tile has the edge `[W, G]` -/

theorem no_shared_upper {D : CongruentDissection N} {α β γ a b c : ℝ} (X : Ctx D α β γ a b c)
    (w : Wall D.toDissection) {E : ℕ → Fin N × Fin 3} {n : ℕ} (Ch : IsChain w E n) (ka : Fin 3)
    (hwa : w.a = D.target.pts ka)
    (hcorner : cornerAngle (D.target.pts (ka + 1)) (D.target.pts ka) (D.target.pts (ka + 2)) = α + β)
    {j : ℕ} (hj : j < n) (hfirst : ∀ m, m < j → elen D (E m) ≠ c)
    (i : Fin N) (hi : (E j).1 = i) (kW kE kG : Fin 3) (hWE : kW ≠ kE) (hWG : kW ≠ kG) (hEG : kE ≠ kG)
    (hkW : (D.tile i).pts kW = edgeWest D.toDissection w.dir (E j))
    (hE0 : w.g ((D.tile i).pts kE) = 0) (hdir : w.dir ((D.tile i).pts kW) < w.dir ((D.tile i).pts kE))
    (hGneg : w.g ((D.tile i).pts kG) < 0)
    (hθW : (D.tile i).localAngle ((D.tile i).pts kW) = α ∨ (D.tile i).localAngle ((D.tile i).pts kW) = β)
    (y : Fin N) (hy : y ≠ i) (mW mG : Fin 3)
    (hyW : (D.tile y).pts mW = (D.tile i).pts kW) (hyG : (D.tile y).pts mG = (D.tile i).pts kG)
    (hyang : (D.tile y).localAngle ((D.tile i).pts kW) = (D.tile i).localAngle ((D.tile i).pts kW) ∨
      (D.tile y).localAngle ((D.tile i).pts kW) = γ) : False := by
  obtain ⟨⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩, -⟩ := Erdos634.CornerPara.angleFacts X.hA
  have hα := X.hA.hα
  have hβ := X.hA.hβ
  have hsum := X.sum_pi
  have hγ := X.gpos
  have hpi := Real.pi_pos
  have two : ∀ {S : Finset (Fin N)}, S.card = 1 → ∀ {p q : Fin N}, p ∈ S → q ∈ S → p = q :=
    fun h _ _ hp hq => Finset.card_le_one.mp h.le _ hp _ hq
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · -- the west end is the corner `w.a`: figure `(1, 1, 0)`
    subst h0
    have hWa : (D.tile i).pts kW = D.target.pts ka := by rw [hkW, Ch.west0, hwa]
    rw [hWa] at hyang hθW
    obtain ⟨-, hfig, -⟩ := Erdos634.Draft.LemmaCFigures.corner_figure D α β γ X.hα' X.hβ' X.hγ' hαβ hαγ hβγ
      hα hβ hγ (by linarith) (by linarith) (by linarith) ka
    rw [hcorner] at hfig
    obtain ⟨hcα, hcβ, hcγ⟩ := corner_fig_arith X.hA _ _ _ hfig
    rcases hyang with h | h
    · rcases hθW with h1 | h1
      · rw [h1] at h
        exact hy (two hcα (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
          (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h1))
      · rw [h1] at h
        exact hy (two hcβ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
          (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h1))
    · have hmem : y ∈ ({i | (D.tile i).localAngle (D.target.pts ka) = γ} : Finset (Fin N)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h
      rw [Finset.card_eq_zero.mp hcγ] at hmem
      simp at hmem
  · -- the west end is a junction where the previous tile presents `γ`: figure `(1, 1, 1)`
    have hj1 : j - 1 + 1 = j := by omega
    have hjunc := Ch.junc (j - 1) (by omega)
    rw [hj1] at hjunc
    have hcasc := cascade_east X w Ch ka hwa (by rw [hcorner, X.hA.hγdef]; linarith) hj.le hfirst (j - 1)
      (by omega)
    have hnv := Ch.junction_boundary (m := j - 1) (by omega)
    rw [hjunc, ← hkW] at hcasc hnv
    rcases Erdos634.Geometry.Dissection.congruentDissection_boundary_figure_cases_at_vertex D α β γ hαβ hαγ hαπ hα0
      hβγ hβπ hβ0 hγπ hγ0 hπ0 X.hA.hγdef X.hA.hrel X.hA.hirr X.hα' X.hβ' X.hγ' hnv.1 hnv.2 (E (j - 1)).1
      (Or.inr (Or.inr hcasc)) with ⟨-, -, hc0⟩ | ⟨hcα, hcβ, hcγ⟩
    · have hmem : (E (j - 1)).1 ∈ ({i' | (D.tile i').localAngle ((D.tile i).pts kW) = γ} : Finset (Fin N)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hcasc
      rw [Finset.card_eq_zero.mp hc0] at hmem
      simp at hmem
    · rcases hyang with h | h
      · rcases hθW with h1 | h1
        · rw [h1] at h
          exact hy (two hcα (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
            (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h1))
        · rw [h1] at h
          exact hy (two hcβ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
            (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h1))
      · -- `y` is the previous base tile; its angle at `W` is supplementary to that of tile `i`
        have hyT : y = (E (j - 1)).1 :=
          two hcγ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
            (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hcasc)
        obtain ⟨kP, kQ, hPQ, hkP, hkQ, hP0, hQ0, hdPQ⟩ := east_other w Ch (m := j - 1) (by omega)
        rw [← hyT] at hkP hkQ hP0 hQ0 hdPQ
        rw [hjunc, ← hkW] at hkQ
        have hPQne : kP ≠ kQ := by
          rcases hPQ with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; exact (fin3_ne _).1
          · rw [h1, h2]; exact (fin3_ne _).1.symm
        have hmWQ : mW = kQ := (D.tile y).indep.injective (hyW.trans hkQ.symm)
        have hmGP : mG ≠ kP := by
          intro heq; rw [heq] at hyG; rw [hyG] at hP0; linarith
        have hmGQ : mG ≠ kQ := by
          intro heq; rw [heq] at hyG; rw [hyG] at hQ0; linarith
        have hangY := localAngle_three (D.tile y) kQ kP mG hPQne.symm hmGQ.symm hmGP.symm
        rw [hkQ, hyG, h] at hangY
        have hangC := localAngle_three (D.tile i) kW kE kG hWE hWG hEG
        -- `W` strictly between `P` and `V'` on the wall line
        have hW0 : w.g ((D.tile i).pts kW) = 0 := by rw [← hkQ]; exact hQ0
        have hdP : w.dir ((D.tile y).pts kP) < w.dir ((D.tile i).pts kW) := by rw [← hkQ]; exact hdPQ
        set t : ℝ := (w.dir ((D.tile i).pts kW) - w.dir ((D.tile y).pts kP)) /
          (w.dir ((D.tile i).pts kE) - w.dir ((D.tile y).pts kP)) with htdef
        have hden : 0 < w.dir ((D.tile i).pts kE) - w.dir ((D.tile y).pts kP) := by linarith
        have ht0 : 0 < t := div_pos (by linarith) hden
        have ht1 : t < 1 := by rw [htdef, div_lt_one hden]; linarith
        have hPE : (D.tile y).pts kP ≠ (D.tile i).pts kE := by
          intro heq; rw [heq] at hden; linarith
        have hWeq : (D.tile i).pts kW = (D.tile y).pts kP + t • ((D.tile i).pts kE - (D.tile y).pts kP) := by
          have hv := w.hker ((D.tile i).pts kW - (D.tile y).pts kP - t • ((D.tile i).pts kE - (D.tile y).pts kP))
            (by rw [map_sub, map_smul, aff_sub, aff_sub, hW0, hP0, hE0]; simp)
            (by rw [map_sub, map_smul, map_sub, map_sub, smul_eq_mul, htdef]; field_simp; ring)
          have := sub_eq_zero.mp hv
          rw [sub_eq_iff_eq_add] at this
          rw [this]; abel
        have hsupp := supp_angle (G := (D.tile i).pts kG) ht0 ht1 hPE hWeq
        rw [← hangY, ← hangC] at hsupp
        rcases hθW with h1 | h1 <;> rw [h1] at hsupp <;> linarith

/-! ## The apex is straddled -/

theorem apex_straddled {D : CongruentDissection N} {α β γ a b c : ℝ} (X : Ctx D α β γ a b c)
    (w : Wall D.toDissection) {E : ℕ → Fin N × Fin 3} {n : ℕ} (Ch : IsChain w E n)
    (ka kb kc : Fin 3) (hkab : ka ≠ kb) (hkac : ka ≠ kc) (hkbc : kb ≠ kc)
    (hwa : w.a = D.target.pts ka) (hwb : w.b = D.target.pts kb)
    (hwg : ∀ y, w.g y = -(D.target.basis.coord kc y))
    (hcorner : cornerAngle (D.target.pts (ka + 1)) (D.target.pts ka) (D.target.pts (ka + 2)) = α + β)
    {j : ℕ} (hj : j < n) (hcj : elen D (E j) = c) (hfirst : ∀ m, m < j → elen D (E m) ≠ c) :
    ∃ kW kE : Fin 3, ((kW = (E j).2 ∧ kE = (E j).2 + 1) ∨ (kW = (E j).2 + 1 ∧ kE = (E j).2)) ∧
      (D.tile (E j).1).pts kW = edgeWest D.toDissection w.dir (E j) ∧
      Straddled D.toDissection ((D.tile (E j).1).basis.coord kE).linear
        (-((D.tile (E j).1).basis.coord kE 0)) ((D.tile (E j).1).pts ((E j).2 + 2)) := by
  obtain ⟨⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩, -⟩ := Erdos634.CornerPara.angleFacts X.hA
  obtain ⟨kW, kE, hWEcase, hkW, hkE, hW0, hE0, hdir⟩ := east_other w Ch hj
  have hGneg := w.hthird (E j) (Ch.mem j hj)
  refine ⟨kW, kE, hWEcase, hkW, ?_⟩
  generalize hi : (E j).1 = i at *
  generalize hk : (E j).2 = k at *
  have hWE : kW ≠ kE := by
    rcases hWEcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact (fin3_ne k).1
    · rw [h1, h2]; exact (fin3_ne k).1.symm
  have hWG : kW ≠ k + 2 := by
    rcases hWEcase with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact (fin3_ne k).2.1
    · rw [h1]; exact (fin3_ne k).2.2
  have hEG : kE ≠ k + 2 := by
    rcases hWEcase with ⟨-, h2⟩ | ⟨-, h2⟩
    · rw [h2]; exact (fin3_ne k).2.2
    · rw [h2]; exact (fin3_ne k).2.1
  -- the angles of the `c`-tile at the two ends of its `c`-edge
  have hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 2 := by
    rw [X.hs2, ← hcj]; simp only [elen, hi, hk]
  obtain ⟨hk0, hk1, hkne⟩ := c_edge_endpoints D α β γ X.hα' X.hβ' X.hγ' X.scalene hαβ hαγ hβγ i k hlen
  have e0 : TilePlacement.angleAt (D.tile i) k = (D.tile i).localAngle ((D.tile i).pts k) := by
    unfold TilePlacement.angleAt; exact (Tri.localAngle_vertex _ _).symm
  have e1 : TilePlacement.angleAt (D.tile i) (k + 1) = (D.tile i).localAngle ((D.tile i).pts (k + 1)) := by
    unfold TilePlacement.angleAt; exact (Tri.localAngle_vertex _ _).symm
  rw [e0] at hk0 hkne
  rw [e1] at hk1 hkne
  have hθ : ((D.tile i).localAngle ((D.tile i).pts kW) = α ∨ (D.tile i).localAngle ((D.tile i).pts kW) = β) ∧
      ((D.tile i).localAngle ((D.tile i).pts kE) = α ∨ (D.tile i).localAngle ((D.tile i).pts kE) = β) ∧
      (D.tile i).localAngle ((D.tile i).pts kW) ≠ (D.tile i).localAngle ((D.tile i).pts kE) := by
    rcases hWEcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨hk0, hk1, hkne⟩
    · rw [h1, h2]; exact ⟨hk1, hk0, hkne.symm⟩
  obtain ⟨hθW, hθE, hθne⟩ := hθ
  -- the length of the upper edge `[W, G]` and the angle at the other end
  have hℓ : ((D.tile i).localAngle ((D.tile i).pts kE) = α ∧
        dist ((D.tile i).pts kW) ((D.tile i).pts (k + 2)) = a) ∨
      ((D.tile i).localAngle ((D.tile i).pts kE) = β ∧
        dist ((D.tile i).pts kW) ((D.tile i).pts (k + 2)) = b) := by
    rcases X.opp_of_angle' i kE kW (k + 2) hWE.symm hEG hWG with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases hθE with h1 | h1
      · exact hαγ (h1.symm.trans h.1)
      · exact hβγ (h1.symm.trans h.1)
  by_contra hns
  -- `W` is not the far corner
  have hWb : (D.tile i).pts kW ≠ w.b := by
    intro heq
    have hEseg := w.hface _ (Erdos634.BaseSelection.tile_subset_target D.toDissection i
      (subset_convexHull ℝ _ (Set.mem_range_self kE))) hE0
    rw [segment_eq_image'] at hEseg
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := hEseg
    have h1 : w.dir ((D.tile i).pts kE) = w.dir w.a + s * (w.dir w.b - w.dir w.a) := by
      rw [← hs]; simp only [map_add, map_smul, map_sub, smul_eq_mul]
    have h2 := w.hdirab
    rw [heq] at hdir
    nlinarith
  have hint := upper_edge_interior X w ka kb kc hkab hkac hkbc hwa hwb hwg
    (by rw [← hcorner, ← localAngle_three D.target ka kb kc hkab hkac hkbc, Tri.localAngle_vertex])
    i kW kE (k + 2) hWE hWG hEG hW0 hE0 hGneg hWb hθW
  have hnsW := not_straddled_at_wall w i kW kE (k + 2) hWE hWG hEG hW0 hGneg
  obtain ⟨e, hei, hends⟩ := far_edge_exact X i kW kE (k + 2) hWE hWG hEG
    (by rcases hℓ with h | h
        · exact Or.inl h.2
        · exact Or.inr h.2) hint hnsW hns
  -- the far tile's angle at `W` is not the angle of tile `i` at the other end
  have hown : TilePlacement.angleAt (D.tile e.1) e.2 ≠ (D.tile i).localAngle ((D.tile i).pts kE) ∧
      TilePlacement.angleAt (D.tile e.1) (e.2 + 1) ≠ (D.tile i).localAngle ((D.tile i).pts kE) := by
    have hd : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = dist ((D.tile i).pts kW) ((D.tile i).pts (k + 2)) := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, dist_comm]
    rcases hℓ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
      exact edge_excludes_own_angle D α β γ X.hα' X.hβ' X.hγ' X.scalene hαβ hαγ hβγ e.1 e.2 0 α (by simp)
        (by rw [hd, h2, X.hs0])
    · rw [h1]
      exact edge_excludes_own_angle D α β γ X.hα' X.hβ' X.hγ' X.scalene hαβ hαγ hβγ e.1 e.2 1 β (by simp)
        (by rw [hd, h2, X.hs1])
  have f0 : TilePlacement.angleAt (D.tile e.1) e.2 = (D.tile e.1).localAngle ((D.tile e.1).pts e.2) := by
    unfold TilePlacement.angleAt; exact (Tri.localAngle_vertex _ _).symm
  have f1 : TilePlacement.angleAt (D.tile e.1) (e.2 + 1) = (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 1)) := by
    unfold TilePlacement.angleAt; exact (Tri.localAngle_vertex _ _).symm
  rw [f0, f1] at hown
  -- name the far tile's vertices at `W` and `G`
  obtain ⟨mW, mG, hmW, hmG⟩ : ∃ mW mG : Fin 3, (D.tile e.1).pts mW = (D.tile i).pts kW ∧
      (D.tile e.1).pts mG = (D.tile i).pts (k + 2) := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨e.2, e.2 + 1, h1, h2⟩
    · exact ⟨e.2 + 1, e.2, h2, h1⟩
  have hYne : (D.tile e.1).localAngle ((D.tile i).pts kW) ≠ (D.tile i).localAngle ((D.tile i).pts kE) := by
    rcases hends with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [← h1]; exact hown.1
    · rw [← h2]; exact hown.2
  have hYcases := X.opp_of_angle e.1 mW
  rw [hmW] at hYcases
  have hyang : (D.tile e.1).localAngle ((D.tile i).pts kW) = (D.tile i).localAngle ((D.tile i).pts kW) ∨
      (D.tile e.1).localAngle ((D.tile i).pts kW) = γ := by
    rcases hYcases with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · left
      rcases hθW with h1 | h1
      · rw [h, h1]
      · exfalso
        rcases hθE with h2 | h2
        · exact hYne (h.trans h2.symm)
        · exact hθne (h1.trans h2.symm)
    · left
      rcases hθW with h1 | h1
      · exfalso
        rcases hθE with h2 | h2
        · exact hθne (h1.trans h2.symm)
        · exact hYne (h.trans h2.symm)
      · rw [h, h1]
    · exact Or.inr h
  exact no_shared_upper X w Ch ka hwa hcorner hj hfirst i hi kW kE (k + 2) hWE hWG hEG hkW hE0 hdir hGneg hθW
    e.1 hei mW mG hmW hmG hyang

end Erdos634.Draft.S5Pin

#print axioms Erdos634.Draft.S5Pin.apex_straddled
