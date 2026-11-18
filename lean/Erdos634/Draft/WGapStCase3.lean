/-
Draft/WGapStCase3.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.3).
Not imported by any aggregate.  STATION port of `WGapCase3d` (lattice origin `x`, absolute levels, floor `J0`); see WGapStInv1.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapCase3d
import Erdos634.Draft.WGapStCase1

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapSt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set Erdos634.Draft.WGapStmt

variable {N : ℕ} {D : CongruentDissection N}


open Erdos634.Draft.WGapStmt hiding sj BotClamp Inv Unfl Flip utm_cast nearOK_inv level_known inv_hint_wall level_data ha_succ hDp_succ unfl_utm inv_step top_pt top_clamp hthird_of_inv ub ClampB FlipAt Bst bst_self ub_norm ub_ne clampB_outside clampB_tile claim_S run_hint_wall case3_supplier

section case3

variable {e f : ℕ} {α β γ L ax ay : ℝ} {x : ℝ} {J0 : ℕ}

set_option maxHeartbeats 2000000 in
theorem claim_S (S : SetupG D e f α β γ L ax ay) {c js m : ℕ} (hm1 : 1 ≤ m) (hmf : m ≤ f - 1)
    (hflip : FlipAt D e f x c js) (hCl : ClampB D e f x c js)
    (hint : openSegment ℝ (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f x c js) (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ)) ⊆
      interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f x c js) (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ)),
      ∀ i, y ∉ interior (D.tile i).carrier) :
    ∃ ed ∈ D.lineChain (crossL (ub e f x c js)) (cross (ub e f x c js) (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ))),
      Straddles ((D.tile ed.1).edge ed.2) (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f x c js - ub e f x c js)
        (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f x c js) (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ)) := by
  by_contra hno
  push_neg at hno
  have he0 := S.e0
  have hef := S.hef'
  have hb0 := S.b_pos
  have hf2 := S.c_pos
  have hν0 := nuG_pos he0 hef
  have hν1 := nuG_lt_one he0 hef
  have hνs := nuG_spec he0 hef
  obtain ⟨O, E1, E2, hm⟩ := mpG_affine_x he0 hef x
  obtain ⟨φ, hφ⟩ := hflip
  set X₀ := mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) with hX₀
  set u := ub e f x c js with hu
  set ν := nuG (e : ℝ) f with hν
  have hu0 : u ≠ 0 := ub_ne S c js
  set F := crossL u with hF
  set cc := cross u X₀ with hcc
  have hFX : F X₀ = cc := crossL_apply _ _
  have hFu : F u = 0 := by rw [hF, crossL_apply]; simp [cross]; ring
  have hFl : ∀ s : ℝ, F (X₀ + s • u) = cc := by
    intro s; rw [map_add, map_smul, hFu, hFX]; simp
  have hC0 : mpG (e : ℝ) f 1 x (c : ℝ) ((js : ℝ) + 1 / ν) = X₀ - (1 / ν) • u := by
    rw [hX₀, hu]; unfold ub; simp only [hm]
    ext i; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  set C0 := mpG (e : ℝ) f 1 x (c : ℝ) ((js : ℝ) + 1 / ν) with hC0def
  set B0 := mpG (e : ℝ) f 1 x ((c : ℝ) + ν) (js : ℝ) with hB0
  have hFC0 : F C0 = cc := by
    have := hFl (-(1 / ν)); rw [hC0]; simpa [sub_eq_add_neg] using this
  have hFB0 : F B0 ≤ cc := by
    have hcr : cross u (B0 - X₀) < 0 := by
      rw [hu, hX₀, hB0]; unfold ub
      rw [cross_mpG he0 hef]
      have := kapG_pos he0 hef
      have e1 : ((c : ℝ) - (c : ℝ)) * ((js : ℝ) - (js : ℝ)) - ((js : ℝ) - ((js : ℝ) + 1)) * ((c : ℝ) + ν - (c : ℝ)) = ν := by ring
      rw [e1]; nlinarith
    have h1 : F B0 = cross u (B0 - X₀) + cc := by
      rw [hF, crossL_apply, hcc, ← cross_add_right]; congr 1; abel
    linarith
  -- the tile phi and its edge [X0, C0]
  obtain ⟨k, hk, hkpts⟩ := hasV_edge_pts (hφ.rot.rot.swap : HasV D φ X₀ C0 B0)
  have hmemφ : (φ, k) ∈ D.lineChain F cc := by
    rw [Dissection.mem_lineChain]
    have hall : ∀ i, F ((D.tile φ).pts i) ≤ cc :=
      hφ.all (P := fun z => F z ≤ cc) (le_of_eq hFX) hFB0 (le_of_eq hFC0)
    refine ⟨?_, ?_, hall⟩
    · rcases hkpts with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only [] <;> rw [h1] <;> [exact hFX; exact hFC0]
    · rcases hkpts with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp only [] <;> rw [h1] <;> [exact hFC0; exact hFX]
  have hdistC : dist X₀ C0 = (f : ℝ) ^ 2 :=
    dist_mpG he0 hef x hf2.le (qf_flip1 he0 hef (c : ℝ) (js : ℝ))
  have hdedge : dist ((D.tile φ).pts k) ((D.tile φ).pts (k + 1)) = (f : ℝ) ^ 2 := by
    rcases hkpts with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hdistC
    · rw [h1, h2, dist_comm]; exact hdistC
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hY : X₀ - (m : ℝ) • u = X₀ + (-(m : ℝ)) • u := by rw [sub_eq_add_neg, neg_smul]
  have hseg1 : (D.tile φ).edge k = segment ℝ X₀ C0 := hk
  by_cases hcase : 1 / ν ≤ (m : ℝ)
  · -- the c-edge lies inside the run: contradiction with (A1)
    have hfP : F (X₀ - (m : ℝ) • u) = cc := by rw [hY]; exact hFl _
    have hfP' : F (X₀ - (m : ℝ) • u - u) = cc := by
      have := hFl (-((m : ℝ) + 1)); convert this using 2; ext i; simp [sub_eq_add_neg]; ring
    have hfQ' : F (X₀ + u) = cc := by simpa using hFl 1
    have hPQ : X₀ - (m : ℝ) • u ≠ X₀ := by
      intro h
      have : (m : ℝ) • u = 0 := by
        have := congrArg (fun z => X₀ - z) h
        simpa using this
      rcases smul_eq_zero.mp this with h0 | h0
      · exact hmpos.ne' h0
      · exact hu0 h0
    have hP' : X₀ - (m : ℝ) • u ∈ openSegment ℝ (X₀ - (m : ℝ) • u - u) X₀ := by
      refine ⟨(m : ℝ) / (m + 1), 1 / (m + 1), by positivity, by positivity, (by first | (field_simp; done) | (field_simp; ring)), ?_⟩
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp; ring
    have hQ' : X₀ ∈ openSegment ℝ (X₀ - (m : ℝ) • u) (X₀ + u) := by
      refine ⟨1 / (1 + m), (m : ℝ) / (1 + m), by positivity, by positivity, (by first | (field_simp; done) | (field_simp; ring)), ?_⟩
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp; ring
    have hdPQ : dist (X₀ - (m : ℝ) • u) X₀ = (m : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hmpos, hu, ub_norm S c js]
    have hC0mem : C0 ∈ segment ℝ (X₀ - (m : ℝ) • u) X₀ := by
      rw [hC0]
      have := lin_seg X₀ u (a := (m : ℝ)) (b := 0) (t := 1 / ν) hmpos.ne' (Or.inl ⟨by linarith [one_div_pos.mpr hν0], hcase⟩)
      simpa using this
    have hsub : (D.tile φ).edge k ⊆ segment ℝ (X₀ - (m : ℝ) • u) X₀ := by
      rw [hseg1]
      exact (convex_segment _ _).segment_subset (right_mem_segment ℝ _ _) hC0mem
    have hQ := hCl (m : ℝ) hmpos
    have := chain_edge_len_b S hm1 hmf F (Erdos634.Geometry.crossL_ne_zero hu0) cc hPQ hfP hFX hfP' hfQ' hP' hQ' hint hwall
      (hno) (by intro ed hed; exact hQ ed hed) hdPQ hmemφ hsub
    rw [hdedge] at this
    nlinarith [pow_pos he0 2]
  · -- the c-edge sticks out beyond Y: it straddles Y
    push_neg at hcase
    have hν1' : (0 : ℝ) < 1 / ν - m := by linarith
    set δ : ℝ := min 1 (1 / ν - m) / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; have := lt_min one_pos hν1'; linarith
    have hδ1 : δ < 1 := by rw [hδ]; have := min_le_left (1 : ℝ) (1 / ν - m); linarith
    have hδ2 : δ < 1 / ν - m := by rw [hδ]; have := min_le_right (1 : ℝ) (1 / ν - m); linarith [lt_min one_pos hν1']
    refine absurd ?_ (hno (φ, k) hmemφ)
    refine ⟨⟨X₀ - ((m : ℝ) + δ) • u, ?_, ?_⟩, ⟨X₀ - ((m : ℝ) / 2) • u, ?_, ?_⟩⟩
    · show _ ∈ (D.tile φ).edge k
      rw [hseg1, hC0]
      have := lin_seg X₀ u (a := 0) (b := 1 / ν) (t := (m : ℝ) + δ) (by have := one_div_pos.mpr hν0; linarith)
        (Or.inr ⟨by linarith, by linarith⟩)
      simpa using this
    · have := lin_openSeg X₀ u (a := (m : ℝ) + 1) (b := (m : ℝ)) (t := (m : ℝ) + δ) (by linarith) (Or.inl ⟨by linarith, by linarith⟩)
      convert this using 2
      ext i; simp [sub_eq_add_neg]; ring
    · show _ ∈ (D.tile φ).edge k
      rw [hseg1, hC0]
      have := lin_seg X₀ u (a := 0) (b := 1 / ν) (t := (m : ℝ) / 2) (by have := one_div_pos.mpr hν0; linarith)
        (Or.inr ⟨by linarith, by linarith⟩)
      simpa using this
    · have := lin_openSeg X₀ u (a := (m : ℝ)) (b := 0) (t := (m : ℝ) / 2) hmpos.ne' (Or.inl ⟨by linarith, by linarith⟩)
      simpa using this

set_option maxHeartbeats 2000000 in
theorem run_hint_wall (S : SetupG D e f α β γ L ax ay) {c js m : ℕ} (hc1 : 1 ≤ c) (hm1 : 1 ≤ m)
    (hflip : FlipAt D e f x c js)
    (hnear : ∀ i' : ℕ, js ≤ i' → i' < js + m → DTM D (e : ℝ) f 1 x ((c - 1 : ℕ) : ℝ) (i' : ℝ)) :
    openSegment ℝ (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f x c js) (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ)) ⊆
      interior D.target.carrier ∧
    ∀ y ∈ openSegment ℝ (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) - (m : ℝ) • ub e f x c js) (mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨O, E1, E2, hm⟩ := mpG_affine_x he0 hef x
  obtain ⟨φ, hφ⟩ := hflip
  set X₀ := mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) with hX₀
  set u := ub e f x c js with hu
  have hc1' : ((c - 1 : ℕ) : ℝ) + 1 = (c : ℝ) := by rw [Nat.cast_sub hc1]; simp
  have hpt : ∀ t : ℝ, mpG (e : ℝ) f 1 x (c : ℝ) ((js : ℝ) + t) = X₀ - t • u := by
    intro t
    rw [hX₀, hu]; unfold ub; simp only [hm]
    ext i; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  -- near tiles in raw form
  have hnr : ∀ i : ℕ, i < m → ∃ t, HasV D t (X₀ - (i : ℝ) • u) (mpG (e : ℝ) f 1 x ((c : ℝ) - 1) ((js : ℝ) + i + 1))
      (X₀ - ((i : ℝ) + 1) • u) := by
    intro i hi
    obtain ⟨t, ht⟩ := hnear (js + i) (by omega) (by omega)
    refine ⟨t, ?_⟩
    have hcs : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by rw [Nat.cast_sub hc1]; simp
    rw [hcs] at ht
    push_cast at ht
    refine hasV_congr ht ?_ ?_ ?_
    · rw [← hpt]; exact mpG_congr' (by ring) (by ring)
    · exact mpG_congr' rfl (by ring)
    · rw [← hpt]; exact mpG_congr' (by ring) (by ring)
  have hX0t : X₀ ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := hnr 0 (by omega)
    simpa using ht.mem₁
  have hYt : X₀ - (m : ℝ) • u ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := hnr (m - 1) (by omega)
    have := ht.mem₃
    have e1 : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by rw [Nat.cast_sub hm1]; simp
    rwa [e1] at this
  -- the wall
  have hwall : ∀ y ∈ openSegment ℝ (X₀ - (m : ℝ) • u) X₀, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    have hy' : y ∈ openSegment ℝ X₀ (X₀ + (m : ℝ) • (-u)) := by
      rw [openSegment_symm]
      convert hy using 2
      ext i; simp [sub_eq_add_neg]
    obtain ⟨i, hi, hyi⟩ := chord_point_step X₀ (-u) hm1 hy'
    obtain ⟨t, ht⟩ := hnr i hi
    have hseg : y ∈ segment ℝ (X₀ - (i : ℝ) • u) (X₀ - ((i : ℝ) + 1) • u) := by
      convert hyi using 2 <;> (first | (ext i; simp [sub_eq_add_neg]; done) | (ext i; simp [sub_eq_add_neg]; ring))
    obtain ⟨k, m', j', hkm, hkj, hmj, hk, hm', hj'⟩ := ht
    refine seg_wall D.toDissection (t := t) hkj ?_
    rw [hk, hj']; exact hseg
  refine ⟨?_, hwall⟩
  -- the interior point z
  obtain ⟨t0, ht0⟩ := hnr 0 (by omega)
  simp only [Nat.cast_zero, zero_smul, sub_zero, zero_add, one_smul] at ht0
  set z : Plane := X₀ - (1 / 2 : ℝ) • u with hz
  have hzn : z ∈ openSegment ℝ (X₀ - u) X₀ := by
    have := lin_openSeg X₀ u (a := 1) (b := 0) (t := 1 / 2) one_ne_zero (Or.inl ⟨by norm_num, by norm_num⟩)
    rw [hz]; simpa using this
  have hzf : z ∈ openSegment ℝ X₀ (mpG (e : ℝ) f 1 x (c : ℝ) ((js : ℝ) + 1 / nuG (e : ℝ) f)) := by
    have hν0 := nuG_pos he0 hef
    have hν1 := nuG_lt_one he0 hef
    have := lin_openSeg X₀ u (a := 0) (b := 1 / nuG (e : ℝ) f) (t := 1 / 2)
      (by have := one_div_pos.mpr hν0; linarith) (Or.inr ⟨by norm_num, by rw [lt_div_iff₀ hν0]; linarith⟩)
    rw [hpt, hz]; simpa using this
  have hana : (D.tile t0).localAngle z = Real.pi := hasV_localAngle_pi ht0.rot hzn
  have hanb : (D.tile φ).localAngle z = Real.pi := hasV_localAngle_pi hφ.swap hzf
  have hν0 := nuG_pos he0 hef
  have hne : t0 ≠ φ := by
    obtain ⟨i, hi⟩ := hasV_second ht0
    refine HasV.ne_of_vertex hφ hi ?_ ?_ ?_
    · intro h; obtain ⟨h1, -⟩ := mpG_inj he0 hef h; linarith
    · intro h; obtain ⟨h1, -⟩ := mpG_inj he0 hef h; linarith
    · intro h; obtain ⟨h1, -⟩ := mpG_inj he0 hef h; linarith
  have hC0t : mpG (e : ℝ) f 1 x (c : ℝ) ((js : ℝ) + 1 / nuG (e : ℝ) f) ∈ D.target.carrier := hφ.mem₃
  have hzt : z ∈ D.target.carrier := D.target.convex.openSegment_subset hX0t hC0t hzf
  have hzint : z ∈ interior D.target.carrier := by
    refine interior_of_sum D.toDissection hzt {t0, φ} ?_
    rw [Finset.sum_pair hne, hana, hanb]
    linarith [Real.pi_pos]
  have hzr : z ∈ range (AffineMap.lineMap (X₀ - (m : ℝ) • u) X₀ : ℝ → Plane) := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    refine ⟨1 - 1 / (2 * m), ?_⟩
    rw [hz, AffineMap.lineMap_apply]
    ext i
    simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    ring
  intro y hy
  rcases openSegment_subset_union _ _ hzr hy with h | h | h
  · rw [h]; exact hzint
  · rw [openSegment_symm] at h
    exact openSeg_interior D.toDissection hzint hYt h
  · exact openSeg_interior D.toDissection hzint hX0t h

set_option maxHeartbeats 2000000 in
theorem case3_supplier (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ J0 + (f - 1))
    (hU : ∀ j : ℕ, J0 ≤ j → j < J → UTG D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ))
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) :
    ∀ j c : ℕ, Inv D e f x J0 (Bst D e f x J0) j c → j < J → c + J0 < j → (∀ i : ℕ, 1 ≤ i → i < c → Unfl D e f x j i) →
        BotClamp D e f x (j + 1) c ∧ Bst D e f x J0 (j + 1) c := by
  intro j c I hjJ hcj _
  have hj1 : J0 + 1 ≤ j := by have := I.c1; omega
  obtain ⟨js, hJs, hjs, hflip, hCl, hD⟩ := I.hb hcj
  have hnear : ∀ i' : ℕ, js ≤ i' → c + i' + 1 ≤ j + 1 → DTM D (e : ℝ) f 1 x ((c - 1 : ℕ) : ℝ) (i' : ℝ) := by
    intro i' h1 h2
    by_cases h3 : c + i' + 1 ≤ j
    · exact hD i' h1 h3
    · have hi' : i' = j - c := by omega
      subst hi'
      have h := (level_data S hJf hU hT hj1 hjJ I).1 (c - 1) (by have := I.c1; omega)
      have e1 : j - 1 - (c - 1) = j - c := by have := I.c1; omega
      rw [e1] at h
      exact h
  refine ⟨?_, fun _ => ⟨js, hJs, by omega, hflip, hCl, hnear⟩⟩
  -- the clamp
  set m : ℕ := j + 1 - c - js with hm
  have hm1 : 1 ≤ m := by omega
  have hmf : m ≤ f - 1 := by omega
  obtain ⟨hint, hwall⟩ := run_hint_wall S I.c1 hm1 hflip (fun i' h1 h2 => hnear i' h1 (by omega))
  obtain ⟨ed₀, hed₀, hstr⟩ := claim_S S hm1 hmf hflip hCl hint hwall
  intro ed _
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨O, E1, E2, hmp⟩ := mpG_affine_x he0 hef x
  set X₀ := mpG (e : ℝ) f 1 x (c : ℝ) (js : ℝ) with hX₀
  set u := ub e f x c js with hu
  have hu0 : u ≠ 0 := ub_ne S c js
  set Y := X₀ - (m : ℝ) • u with hY
  -- the chord end equals Y
  have hjm : (js : ℝ) + m = (j : ℝ) + 1 - c := by
    have : js + m + c = j + 1 := by omega
    have h' : ((js + m + c : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) := by rw [this]
    push_cast at h'; linarith
  have hYeq : mpG (e : ℝ) f 1 x 0 ((j + 1 : ℕ) : ℝ) + (c : ℝ) • sj e f x (j + 1) = Y := by
    rw [hY, hX₀, hu]; unfold sj ub; simp only [hmp]
    have := hjm
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    push_cast
    have hmr : (m : ℝ) = (j : ℝ) + 1 - c - js := by linarith
    rw [hmr]; ring
  -- straddle data
  have hFu : crossL u u = 0 := by rw [crossL_apply]; simp [cross]; ring
  have hFl : ∀ s : ℝ, crossL u (X₀ + s • u) = cross u X₀ := by
    intro s; rw [map_add, map_smul, hFu, crossL_apply]; simp
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hfP : crossL u Y = cross u X₀ := by
    have := hFl (-(m : ℝ)); rw [hY]; simpa [sub_eq_add_neg] using this
  have hfP' : crossL u (Y - u) = cross u X₀ := by
    have := hFl (-((m : ℝ) + 1)); rw [hY]
    convert this using 2; ext i; simp [sub_eq_add_neg]; ring
  have hPQ : Y ≠ X₀ := by
    intro h
    have : (m : ℝ) • u = 0 := by
      have := congrArg (fun z => X₀ - z) h
      simpa [hY] using this
    rcases smul_eq_zero.mp this with h0 | h0
    · exact hmpos.ne' h0
    · exact hu0 h0
  have hP' : Y ∈ openSegment ℝ (Y - u) X₀ := by
    refine ⟨(m : ℝ) / (m + 1), 1 / (m + 1), by positivity, by positivity, by field_simp, ?_⟩
    rw [hY]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp; ring
  obtain ⟨-, -, hpush⟩ := straddle_data D.toDissection (crossL u) (Erdos634.Geometry.crossL_ne_zero hu0) (cross u X₀) hPQ hfP
    (crossL_apply _ _) hfP' hP' hed₀ hstr
  -- F s' < 0
  have hFs : crossL u (sj e f x (j + 1)) < 0 := by
    rw [crossL_apply, hu]; unfold ub sj
    rw [cross_mpG he0 hef]
    have := kapG_pos he0 hef
    have e1 : ((c : ℝ) - (c : ℝ)) * ((((j + 1 : ℕ) : ℝ) - 1) - ((j + 1 : ℕ) : ℝ)) -
        ((js : ℝ) - ((js : ℝ) + 1)) * ((1 : ℝ) - 0) = 1 := by ring
    rw [e1]; nlinarith
  obtain ⟨ε₀, hε₀, hpush'⟩ := hpush (sj e f x (j + 1)) hFs
  refine not_straddles_short D.toDissection (j := ed₀.1) (δ := ε₀) (ρ := (c : ℝ)) hε₀
    (by exact_mod_cast I.c1) ?_ ?_ ed.1 ed.2
  · ext i; simp; ring
  · intro ε h0 h1
    have := hpush' ε h0 h1
    convert this using 1
    rw [← hYeq]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
end case3

end Erdos634.Draft.WGapSt
