import Erdos634.Refl.SoundN
import Erdos634.Refl.CheckPoly
import Erdos634.PlacementCompletenessConeR

/-! Refl/RegionP.lean -- the free-branch-point checker for a CONVEX POLYGON target.

The target of `CheckM`/`CheckN` is the triangle `I.tgt`.  Here the region is `I.tgt ∩ ⋂ ext`, the triangle cut by the
extra closed half-planes `ext : List Lin` (so a parallelogram is a triangle through two of its side lines, cut by the other
two).  The dissected object is a `CongruentRegionDissection` (`RegionDissection.lean`), and placement completeness is
`PlacementCompletenessR.placement_completeness_cone`.

Changes against `CheckN`:
* the local certificates and the `tgtQ` test use `tgtLinsP I ext = tgtLinsM I ++ ext`;
* `Kill.esc b e` with `e ≥ 3` is an escape across the extra line `ext[e-3]` (`escX`).
Everything else (BSP certificates, overlap kills, placements, nogood stubs) is `CheckN`, and the soundness proof is a
transcription of `SoundM1`, `SoundM2`, `SoundN`.  Needed for `thm:dichotomy`.  No sorry. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.SixPlacements
open Erdos634.PlacementCompleteness (perp dist_sq_coord cross_anticomm)
open Erdos634.PlacementCompletenessR (unfilled)
open Erdos634.Geometry (Plane cross)

namespace Refl

/-- the closed region cut out by the extra lines -/
def extSet (Dn : ℝ) (ext : List Lin) : Set Plane := {p | ∀ l ∈ ext, p ∈ halfL Dn l}

/-- soundness statement for a polygon target -/
def SoundP (Dn : ℝ) (I : Inst) (ext : List Lin) (M : Erdos634.Geometry.Tri) (cfg : List _root_.Tri) : Prop :=
  ∀ {N : ℕ} (D : Erdos634.RegionDissection.CongruentRegionDissection N),
    D.region = I.tgt.carr Dn ∩ extSet Dn ext → D.model.Congruent M →
    (∀ t ∈ cfg, ∃ i, (D.tile i).carrier = t.carr Dn) → False

/-- overlap kill against a region dissection (`ovl_sound_D`) -/
theorem ovl_sound_R (Dn : ℝ) (hD : 0 < Dn) {N : ℕ} (D : Erdos634.RegionDissection.CongruentRegionDissection N)
    (tri U : _root_.Tri) (htri : tri.ok = true) (hU : U.ok = true) (i j : Fin N) (hij : i ≠ j)
    (hi : (D.tile i).carrier = U.carr Dn) (hj : (D.tile j).carrier = tri.carr Dn)
    (w : Pt) (hw : 0 < w.w) (h1 : inOpen tri w = true) (h2 : inOpen U w = true) : False := by
  have hdis : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
    D.interiors_disjoint hij
  rw [hi, hj] at hdis
  exact Set.disjoint_left.mp hdis (inOpen_sound Dn hD U w hw hU h2) (inOpen_sound Dn hD tri w hw htri h1)

theorem escX_sound (Dn : ℝ) (hD : 0 < Dn) (l : Lin) (q : Pt) (hq : 0 < q.w) (h : escX l q < 0)
    (hin : q.re Dn ∈ halfL Dn l) : False := by
  have h1 : 0 ≤ evalL l q.X q.Y := (mem_halfL_rp Dn hD l q.X q.Y).mp hin
  have hw := Pt.w_pos q hq
  have hwn := Pt.w_ne q hq
  have e : evalL l q.X q.Y * q.w = ((escX l q : Int) : ℝ) := by
    unfold evalL escX Pt.X Pt.Y
    push_cast
    field_simp
  have h2 : ((escX l q : Int) : ℝ) < 0 := by exact_mod_cast h
  nlinarith [mul_nonneg h1 hw.le]

structure LocalFactsP (I : Inst) (ext : List Lin) (cfg : List _root_.Tri) (n : NodeM) : Prop where
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
  r1 : Bsp.check cfg [] [] false (consP1 I ext n) [] n.t1 = true
  r2 : Bsp.check cfg [] [] false (consP2 I ext n) [] n.t2 = true
  tgtQ : ((tgtLinsP I ext).all fun l => okPos (quad I n.v n.d l) n.tauN n.tauD) = true
  tileQ : ((cfg.zip n.fedges).all fun x => okNeg (quad I n.v n.d (x.1.edge x.2)) n.tauN n.tauD) = true

theorem nodeLocalOkP_facts (I : Inst) (ext : List Lin) (cfg : List _root_.Tri) (n : NodeM)
    (h : nodeLocalOkP I ext cfg n = true) : LocalFactsP I ext cfg n := by
  unfold nodeLocalOkP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩


/-- **cone**: near `v`, every unfilled point is on/left of `d` and on/right of `g`. -/
theorem cone_soundP (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (ext : List Lin) (htok : I.tgt.ok = true)
    (cfg : List _root_.Tri) (hcfg : ∀ t ∈ cfg, t.ok = true) (n : NodeM) (F : LocalFactsP I ext cfg n)
    {N : ℕ} (D : Erdos634.RegionDissection.CongruentRegionDissection N)
    (htarget : D.region = I.tgt.carr Dn ∩ extSet Dn ext) (S : Finset (Fin N))
    (hS : ∀ t ∈ cfg, ∃ i ∈ S, (D.tile i).carrier = t.carr Dn) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ unfilled D.toRegionDissection S, dist p (n.v.re Dn) < ε →
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
  have hreg : rp Dn X Y ∈ I.tgt.carr Dn ∩ extSet Dn ext := by rw [← htarget]; exact hp.1
  have hsatT0 := tgtLins_sat Dn hD I htok X Y hreg.1
  have hsatT : ∀ l ∈ tgtLinsP I ext, 0 ≤ evalL l X Y := by
    intro l hl
    rcases List.mem_append.mp hl with h | h
    · exact hsatT0 l h
    · exact (mem_halfL_rp Dn hD l X Y).mp (hreg.2 l h)
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
  have hbase : ∀ c ∈ (tgtLinsP I ext ++ boxL n.v n.eN n.eD).map (fun l => (l, false)), Sat c X Y := by
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
    rcases bsp_sound Dn hD cfg hcfg [] [] false n.t1 (consP1 I ext n) [] X Y F.r1 (by
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
    rcases bsp_sound Dn hD cfg hcfg [] [] false n.t2 (consP2 I ext n) [] X Y F.r2 (by
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
theorem dg_reP (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (ext : List Lin) (cfg : List _root_.Tri) (n : NodeM)
    (F : LocalFactsP I ext cfg n) : 0 < cross (n.d.re Dn) (n.g.re Dn) := by
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
theorem hfree_soundP (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (ext : List Lin) (hDn : (I.Dn : ℝ) = Dn)
    (htok : I.tgt.ok = true) (cfg : List _root_.Tri) (hcfg : ∀ t ∈ cfg, t.ok = true)
    (n : NodeM) (F : LocalFactsP I ext cfg n)
    {N : ℕ} (D : Erdos634.RegionDissection.CongruentRegionDissection N)
    (htarget : D.region = I.tgt.carr Dn ∩ extSet Dn ext) (S : Finset (Fin N))
    (hSt : ∀ i ∈ S, ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn) :
    ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      (n.v.re Dn) + t • ((n.d.re Dn) + s • perp (n.d.re Dn))
        ∈ unfilled D.toRegionDissection S := by
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
    refine ⟨?_, ?_⟩
    · refine Tri.mem_of_edges Dn hD I.tgt htok X Y ?_
      intro i hi
      have hall := List.all_eq_true.mp F.tgtQ (I.tgt.edge i)
        (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
      exact okPos_sound I Dn hDn n.v n.d F.vw F.dw _ _ _ F.tauN F.tauD hall t ht0 htτ
    · intro l hl
      refine (mem_halfL_rp Dn hD l X Y).mpr ?_
      have hall := List.all_eq_true.mp F.tgtQ l (List.mem_append_right _ hl)
      exact okPos_sound I Dn hDn n.v n.d F.vw F.dw _ _ _ F.tauN F.tauD hall t ht0 htτ
  · obtain ⟨i, hi, hm⟩ := Set.mem_iUnion₂.mp hU
    obtain ⟨T, hT, hTc⟩ := hSt i hi
    rw [hTc] at hm
    obtain ⟨e, he⟩ := zip_all_ex _ cfg n.fedges F.flen F.tileQ T hT
    have hneg := okNeg_sound I Dn hDn n.v n.d F.vw F.dw _ _ _ F.tauN F.tauD he t ht0 htτ
    have hnn := Tri.edge_nonneg Dn hD T (hcfg T hT) X Y hm (e % 3) (Nat.mod_lt _ (by norm_num))
    rw [← Tri.edge_mod] at hnn
    linarith


theorem killsSoundP (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (ext : List Lin) (hDn : (I.Dn : ℝ) = Dn)
    (htok : I.tgt.ok = true) (v d : Pt) (hvw : 0 < v.w) (hdw : 0 < d.w)
    (hdu : d.x * d.x + I.Dn * d.y * d.y = d.w * d.w)
    (cfg : List _root_.Tri) (hcfgok : ∀ t ∈ cfg, t.ok = true)
    {N : ℕ} (D : Erdos634.RegionDissection.CongruentRegionDissection N)
    (htarget : D.region = I.tgt.carr Dn ∩ extSet Dn ext) (j : Fin N)
    (hreal : ∀ t ∈ cfg, ∃ i, i ≠ j ∧ (D.tile i).carrier = t.carr Dn)
    (R : NodeM → List _root_.Tri → Bool) :
    ∀ (ks : List Kill) (ps : List Place) (ch : List NodeM),
      (∀ p ∈ ps, 0 < p.l1 ∧ 0 < p.pd ∧ 0 < p.qd ∧ 0 < p.qn) →
      (∀ c p, p ∈ ps → R c (cfg ++ [placeTri I v d p]) = true →
        (D.tile j).carrier = (placeTri I v d p).carr Dn → False) →
      killsCheckP I ext cfg v d ks ps ch R = true →
      ∀ p ∈ ps, (D.tile j).carrier = (placeTri I v d p).carr Dn → False := by
  intro ks
  induction ks with
  | nil =>
    intro ps ch _ _ hk p hp
    cases ps with
    | nil => simp at hp
    | cons _ _ => simp [killsCheckP] at hk
  | cons k ks ih =>
    intro ps ch hpl hR hk p hp hj
    cases ps with
    | nil => simp [killsCheckP] at hk
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
          simp only [killsCheckP, Bool.and_eq_true] at hk
          obtain ⟨hko, -⟩ := hk
          have hsub : (placeTri I v d p).carr Dn ⊆ I.tgt.carr Dn ∩ extSet Dn ext := by
            rw [← htarget, ← hj]
            exact Erdos634.PlacementCompletenessR.tile_subset_region D.toRegionDissection j
          by_cases he3 : e < 3
          · simp only [killOkP, he3, if_true, killOk, decide_eq_true_eq] at hko
            cases q
            · simp only [Bool.false_eq_true, if_false] at hko
              exact esc_sound Dn hD I.tgt htok e _ hwb hko (hsub (Tri.vert_re_mem Dn (placeTri I v d p) 1)).1
            · simp only [if_true] at hko
              exact esc_sound Dn hD I.tgt htok e _ hwc hko (hsub (Tri.vert_re_mem Dn (placeTri I v d p) 2)).1
          · simp only [killOkP, he3, if_false] at hko
            cases hl : ext[e - 3]? with
            | none => rw [hl] at hko; simp at hko
            | some l =>
              rw [hl] at hko
              simp only [decide_eq_true_eq] at hko
              have hlm : l ∈ ext := List.mem_of_getElem? hl
              cases q
              · simp only [Bool.false_eq_true, if_false] at hko
                exact escX_sound Dn hD l _ hwb hko
                  ((hsub (Tri.vert_re_mem Dn (placeTri I v d p) 1)).2 l hlm)
              · simp only [if_true] at hko
                exact escX_sound Dn hD l _ hwc hko
                  ((hsub (Tri.vert_re_mem Dn (placeTri I v d p) 2)).2 l hlm)
        | ovl m w =>
          simp only [killsCheckP, killOkP, killOk] at hk
          cases hm : cfg[m]? with
          | none => rw [hm] at hk; simp at hk
          | some U =>
            rw [hm] at hk
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
            obtain ⟨⟨⟨hw, h1⟩, h2⟩, -⟩ := hk
            have hUm : U ∈ cfg := List.mem_of_getElem? hm
            obtain ⟨i, hij, hi⟩ := hreal U hUm
            exact ovl_sound_R Dn hD D _ U htri (hcfgok U hUm) i j hij hi hj w hw h1 h2
        | child =>
          simp only [killsCheckP] at hk
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
          simp only [killsCheckP, Bool.and_eq_true] at hk
          exact ih ps ch hpl2 hR2 hk.2 p hpps hj
        | ovl m w =>
          simp only [killsCheckP] at hk
          cases hm : cfg[m]? with
          | none => simp [killOkP, killOk, hm] at hk
          | some U =>
            simp only [killOkP, killOk, hm, Bool.and_eq_true] at hk
            exact ih ps ch hpl2 hR2 hk.2 p hpps hj
        | child =>
          simp only [killsCheckP] at hk
          cases ch with
          | nil => simp at hk
          | cons c cs =>
            simp only [Bool.and_eq_true] at hk
            exact ih ps cs hpl2 hR2 hk.2 p hpps hj


theorem checkNodeP_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (ext : List Lin) (hDn : (I.Dn : ℝ) = Dn)
    (M : Erdos634.Geometry.Tri)
    (hMa : dist (M.pts 0) (M.pts 1) = I.sides.1) (hMb : dist (M.pts 1) (M.pts 2) = I.sides.2.1)
    (hMc : dist (M.pts 0) (M.pts 2) = I.sides.2.2)
    (hI : I.ok = true) (known : List (List _root_.Tri))
    (hk : ∀ c ∈ known, SoundP Dn I ext M c) (hkok : ∀ c ∈ known, ∀ t ∈ c, t.ok = true) :
    ∀ (fuel : Nat) (cfg : List _root_.Tri) (n : NodeM), (∀ t ∈ cfg, t.ok = true) →
      checkNodeP I ext known fuel cfg n = true → SoundP Dn I ext M cfg := by
  obtain ⟨htok, hDpos, p1, p2, p3, p4, p5, p6, hpl, o1, o2, o3, o4, o5, o6⟩ := Inst_ok_facts I hI
  intro fuel
  induction fuel with
  | zero => intro cfg n _ h; simp [checkNodeP] at h
  | succ fuel ih =>
    intro cfg n hcfgok hchk N D htg hm hreal
    classical
    by_cases hst : (n.tauN == 0) = true
    · simp only [checkNodeP, hst, if_true] at hchk
      obtain ⟨c, hc, hce⟩ := List.any_eq_true.mp hchk
      refine hk c hc D htg hm (fun t ht => ?_)
      obtain ⟨u, hu, htu⟩ := cfgSubV_mem c cfg hce t ht
      obtain ⟨i, hi⟩ := hreal u hu
      exact ⟨i, by rw [hi, triEqv_carr Dn t u (hkok c hc t ht) (hcfgok u hu) htu]⟩
    have hne : (n.tauN == 0) = false := by simpa using hst
    simp only [checkNodeP, hne, Bool.false_eq_true, if_false, Bool.and_eq_true] at hchk
    obtain ⟨hloc, hkills⟩ := hchk
    have F := nodeLocalOkP_facts I ext cfg n hloc
    set S : Finset (Fin N) := Finset.univ.filter (fun i => ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn) with hSdef
    have hS : ∀ t ∈ cfg, ∃ i ∈ S, (D.tile i).carrier = t.carr Dn := by
      intro t ht
      obtain ⟨i, hi⟩ := hreal t ht
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, hi⟩, hi⟩
    have hSt : ∀ i ∈ S, ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hcone := cone_soundP Dn hD I ext htok cfg hcfgok n F D htg S hS
    have hfree := hfree_soundP Dn hD I ext hDn htok cfg hcfgok n F D htg S hSt
    have hdg := dg_reP Dn hD I ext cfg n F
    have hunit := unit_re Dn hD I hDn n.d F.dw F.unit
    obtain ⟨j, hjS, k0, k1, k2, h01, h02, h12, hk0, ⟨c', hc', hk1⟩, hk2⟩ :=
      Erdos634.PlacementCompletenessR.placement_completeness_cone D.toRegionDissection S (n.v.re Dn) (n.d.re Dn) (n.g.re Dn) hunit hdg
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
      have key := fun (l1 l2 l3 : Int) (p : Place) (hp : placeOk I l1 l2 l3 p = true)
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
    refine killsSoundP Dn hD I ext hDn htok n.v n.d F.vw F.dw F.unit cfg hcfgok D htg j hreal'
      (fun c cfg' => checkNodeP I ext known fuel cfg' c) n.kills I.pl n.children hpos ?_ hkills pj hpj hjc
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


#print axioms Refl.checkNodeP_sound

end Refl
