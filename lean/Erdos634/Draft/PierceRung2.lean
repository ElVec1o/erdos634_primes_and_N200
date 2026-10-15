/-
Draft/PierceRung2.lean -- the second rung of the pierce argument at every scale, on the scale-free frame of `PierceScale`.

In the configuration of `PierceScale.thm_pierce_scale` (frame `F : PierceScale.SFrame`): on the mismatch ray, `T₁`'s `b`-edge is
`[A, X]`, `X = A + b·uR`, and `T₂`'s `c`-edge is `[A, V]`, `V = A + c·uR`; the piercer is the tile edge on `T₁`'s
side of the ray that has `V` in its relative interior.

* `T1_edge`: `T₁`'s `b`-edge as a chain edge of the far side, with parameters `[0, b]`.
* `not_pstr_ends`: an end of a chain edge is not in the relative interior of a chain edge of the same side.
* `rung2`: the piercer starts at `A + (t + 1) b · uR` for a natural `t` with `t b < e²`; the far-side edges between
  the T-junction `X` and that point are `t` in number; and `t = 0` when `2e² < f²` (outside the super-thick
  regime).
* `b_piercer_alpha`: if the piercer starts at the T-junction and is a `b`-edge, its tile presents `α` there (the
  figure at `X` offers `α` or `β`, a `b`-edge has `α` and `γ` at its ends).
* `rung2_45`: at `(e, f) = (4, 5)` the piercer starts at distance `9` or `18` from the apex.  No sorry, no native_decide.
-/
import Erdos634.Draft.PierceScale

open scoped Classical

namespace Erdos634.Draft.PierceScale

open Erdos634.Geometry Erdos634.Placement Erdos634.TilePlacement Erdos634.WallEndpoints
  Erdos634.BridgeC Erdos634.BaseBetaWalkArith
open Erdos634.SideWall Erdos634.Draft.ApexPlacement Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.ApexLegWord Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.R1Frame
open Erdos634.CertCoord Erdos634.Draft.NearBaseVertex

variable {N : ℕ}

/-- **Ends of chain edges are not crossed from their own side.** -/
theorem not_pstr_ends {D : Dissection N} {X u : Plane} {f g : Plane →ₗ[ℝ] ℝ} {c d : ℝ}
    (hg : g ≠ 0) (hgd : ∀ y, g y = d ↔ f y = c) (hf : f ≠ 0) (hX : f X = c) (hu : f u = 0)
    (hu0 : u ≠ 0) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g d) :
    ¬ TraceCovering.PStr (D.lineChain g d) (TraceCovering.lo D X u) (TraceCovering.hi D X u)
        (TraceCovering.lo D X u e) ∧
    ¬ TraceCovering.PStr (D.lineChain g d) (TraceCovering.lo D X u) (TraceCovering.hi D X u)
        (TraceCovering.hi D X u e) := by
  obtain ⟨h0, h1⟩ := TraceCovering.onLine hgd he
  obtain ⟨hlt, -, -, -⟩ := TraceCovering.edge_data (D := D) hf hX hu hu0 h0 h1
  constructor
  · rintro ⟨e', he', h1', h2'⟩
    have hne : e ≠ e' := by
      intro h; rw [← h] at h1'; exact lt_irrefl _ h1'
    have hsub := TraceCovering.meet hg hgd hf hX hu hu0 e he e' he' hne
    have hm1 : TraceCovering.lo D X u e ∈ Set.Icc (TraceCovering.lo D X u e) (TraceCovering.hi D X u e) ∩
        Set.Icc (TraceCovering.lo D X u e') (TraceCovering.hi D X u e') :=
      ⟨⟨le_rfl, hlt.le⟩, ⟨h1'.le, h2'.le⟩⟩
    have hm2 : min (TraceCovering.hi D X u e) (TraceCovering.hi D X u e') ∈
        Set.Icc (TraceCovering.lo D X u e) (TraceCovering.hi D X u e) ∩
        Set.Icc (TraceCovering.lo D X u e') (TraceCovering.hi D X u e') :=
      ⟨⟨(lt_min hlt h2').le, min_le_left _ _⟩, ⟨(lt_trans h1' (lt_min hlt h2')).le, min_le_right _ _⟩⟩
    exact absurd (hsub hm1 hm2) (ne_of_lt (lt_min hlt h2'))
  · rintro ⟨e', he', h1', h2'⟩
    have hne : e ≠ e' := by
      intro h; rw [← h] at h2'; exact lt_irrefl _ h2'
    have hsub := TraceCovering.meet hg hgd hf hX hu hu0 e he e' he' hne
    have hm1 : max (TraceCovering.lo D X u e) (TraceCovering.lo D X u e') ∈
        Set.Icc (TraceCovering.lo D X u e) (TraceCovering.hi D X u e) ∩
        Set.Icc (TraceCovering.lo D X u e') (TraceCovering.hi D X u e') :=
      ⟨⟨le_max_left _ _, (max_lt hlt h1').le⟩, ⟨le_max_right _ _, (lt_trans (max_lt hlt h1') h2').le⟩⟩
    have hm2 : TraceCovering.hi D X u e ∈ Set.Icc (TraceCovering.lo D X u e) (TraceCovering.hi D X u e) ∩
        Set.Icc (TraceCovering.lo D X u e') (TraceCovering.hi D X u e') :=
      ⟨⟨hlt.le, le_rfl⟩, ⟨h1'.le, h2'.le⟩⟩
    exact absurd (hsub hm1 hm2) (ne_of_lt (max_lt hlt h1'))

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {k : Fin 3}

/-- **`T₁`'s `b`-edge on the ray**: a chain edge of the far side with parameters `[0, b]`. -/
theorem T1_edge (F : SFrame D e f α β γ k) :
    ∃ (i1 : Fin N) (m : Fin 3),
      Set.range (D.tile i1).pts = {F.A, F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR, F.Rf} ∧
      (i1, m) ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A)) ∧
      TraceCovering.lo D.toDissection F.A F.uR (i1, m) = 0 ∧
      TraceCovering.hi D.toDissection F.A F.uR (i1, m) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  classical
  have hef := F.hef
  have he := F.he
  have hu1 : ‖F.uR‖ = 1 := F.huR
  have hu0 : F.uR ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hgd₂ : ∀ y, (-F.h) y = -(F.h F.A) ↔ F.h y = F.h F.A := TraceCovering.neg_iff
  have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have heR : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hb_pos : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hA0 : F.A + (0 : ℝ) • F.uR = F.A := by rw [zero_smul, add_zero]
  obtain ⟨i1, hi1⟩ := F.hT1
  set Bp := F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR with hBp
  obtain ⟨kA1, hkA1⟩ := MarchInduction.mem_range_of_eq hi1 (Set.mem_insert _ _)
  have hfin1 : kA1 + 2 + 1 = kA1 := by fin_cases kA1 <;> rfl
  have hfin2 : kA1 + 2 + 2 = kA1 + 1 := by fin_cases kA1 <;> rfl
  obtain ⟨m, hm01', hm2⟩ : ∃ m : Fin 3,
      (((D.tile i1).pts m = F.A ∧ (D.tile i1).pts (m + 1) = Bp) ∨
        ((D.tile i1).pts m = Bp ∧ (D.tile i1).pts (m + 1) = F.A)) ∧
      (D.tile i1).pts (m + 2) = F.Rf := by
    rcases MarchInduction.vertex_data_of_range hi1 hkA1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨kA1, Or.inl ⟨hkA1, h1⟩, h2⟩
    · exact ⟨kA1 + 2, Or.inr ⟨h2, by rw [hfin1, hkA1]⟩, by rw [hfin2, h1]⟩
  have hhB : F.h Bp = F.h F.A := TraceCovering.f_param rfl F.hhuR _
  have hhRf : F.h F.A < F.h F.Rf := F.hhRf
  have he1 : (i1, m) ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A)) := by
    rw [Dissection.mem_lineChain]
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    refine ⟨?_, ?_, fun i => ?_⟩
    · rcases hm01' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhB]
    · rcases hm01' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhB]
    · rcases h3 i m with rfl | rfl | rfl
      · rcases hm01' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhB]
      · rcases hm01' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhB]
      · rw [hm2]; simp only [LinearMap.neg_apply, neg_le_neg_iff]; exact hhRf.le
  have hdist1 : dist ((D.tile i1).pts m) ((D.tile i1).pts (m + 1))
      = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have hdb : dist F.A Bp = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [hBp, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one,
        Real.norm_of_nonneg hb_pos.le]
    rcases hm01' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hdb
    · rw [dist_comm]; exact hdb
  -- parameters of the edge
  obtain ⟨h0e, h1e⟩ := TraceCovering.onLine hgd₂ he1
  obtain ⟨hlt, -, -, hlen⟩ := TraceCovering.edge_data (D := D.toDissection) F.hh0 rfl F.hhuR hu0 h0e h1e
  have hlen' := hlen hu1
  rw [hdist1] at hlen'
  have hAmem : F.A + (0 : ℝ) • F.uR ∈ (D.tile i1).edge m := by
    rw [hA0, Tri.edge]
    rcases hm01' with ⟨h1, -⟩ | ⟨-, h1⟩ <;> rw [← h1]
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hBmem : F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR ∈ (D.tile i1).edge m := by
    rw [Tri.edge]
    rcases hm01' with ⟨-, h1⟩ | ⟨h1, -⟩ <;> rw [← hBp, ← h1]
    · exact right_mem_segment ℝ _ _
    · exact left_mem_segment ℝ _ _
  have hA' := (TraceCovering.mem_edge_iff hgd₂ F.hh0 rfl F.hhuR hu0 he1 0).mp hAmem
  have hB' := (TraceCovering.mem_edge_iff hgd₂ F.hh0 rfl F.hhuR hu0 he1 _).mp hBmem
  exact ⟨i1, m, hi1, he1, by linarith [hA'.1, hB'.2], by linarith [hA'.1, hB'.2]⟩

/-- **`prop:rung2`.**  The piercer `ε` starts at `A + (t + 1) b · uR` with `t b < e²`; the far-side edges lying
between the T-junction and that point are `t` in number; and `t = 0` if `2e² < f²`. -/
theorem rung2 (F : SFrame D e f α β γ k) :
    ∃ (ε : Fin N × Fin 3) (t : ℕ), ε ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A)) ∧
      F.V ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) ∧
      (F.A + (((t : ℝ) + 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • F.uR = (D.tile ε.1).pts ε.2 ∨
        F.A + (((t : ℝ) + 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • F.uR = (D.tile ε.1).pts (ε.2 + 1)) ∧
      t * (f ^ 2 - e ^ 2) < e ^ 2 ∧ (2 * e ^ 2 < f ^ 2 → t = 0) ∧
      ((D.toDissection.lineChain (-F.h) (-(F.h F.A))).filter
        (fun e' : Fin N × Fin 3 => (D.toDissection.tile e'.1).edge e'.2 ⊆
          segment ℝ (F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR)
            (F.A + (((t : ℝ) + 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • F.uR))).card = t := by
  classical
  have hef := F.hef
  have he := F.he
  have hu1 : ‖F.uR‖ = 1 := F.huR
  have hu0 : F.uR ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hgd₂ : ∀ y, (-F.h) y = -(F.h F.A) ↔ F.h y = F.h F.A := TraceCovering.neg_iff
  have hh' : (-F.h : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => F.hh0 (neg_eq_zero.mp h)
  have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have heR1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hb_pos : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hc_pos : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  set b : ℝ := (f : ℝ) ^ 2 - (e : ℝ) ^ 2 with hbdef
  obtain ⟨i1, m, -, he1, hlo1, hhi1⟩ := T1_edge F
  -- the piercer
  have hp := V_pierced F
  have hp' := hp
  rw [F.hV, TraceCovering.str_iff hgd₂ F.hh0 rfl F.hhuR hu0] at hp'
  obtain ⟨ε, hε, hlo, hhi⟩ := hp'
  have hVε : F.V ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) := by
    obtain ⟨h0e, h1e⟩ := TraceCovering.onLine hgd₂ hε
    rw [(TraceCovering.edge_data (D := D.toDissection) F.hh0 rfl F.hhuR hu0 h0e h1e).2.2.1, F.hV]
    exact ⟨_, ⟨hlo, hhi⟩, rfl⟩
  set L := TraceCovering.lo D.toDissection F.A F.uR ε with hL
  -- the piercer is not `T₁`'s edge, and starts at or after `b`
  have hne : (i1, m) ≠ ε := by
    intro h
    rw [← h, hhi1] at hhi
    have : b < (f : ℝ) ^ 2 := by rw [hbdef]; nlinarith
    linarith
  have hLb : b ≤ L := by
    by_contra hcon
    push_neg at hcon
    have hsub := TraceCovering.meet hh' hgd₂ F.hh0 rfl F.hhuR hu0 (i1, m) he1 ε hε hne
    have hbc : b < (f : ℝ) ^ 2 := by rw [hbdef]; nlinarith
    have hm1 : max L 0 ∈ Set.Icc (TraceCovering.lo D.toDissection F.A F.uR (i1, m))
          (TraceCovering.hi D.toDissection F.A F.uR (i1, m)) ∩
        Set.Icc (TraceCovering.lo D.toDissection F.A F.uR ε) (TraceCovering.hi D.toDissection F.A F.uR ε) := by
      rw [hlo1, hhi1]
      exact ⟨⟨le_max_right _ _, (max_lt hcon hb_pos).le⟩, ⟨le_max_left _ _, (max_lt (by linarith) (by linarith)).le⟩⟩
    have hm2 : b ∈ Set.Icc (TraceCovering.lo D.toDissection F.A F.uR (i1, m))
          (TraceCovering.hi D.toDissection F.A F.uR (i1, m)) ∩
        Set.Icc (TraceCovering.lo D.toDissection F.A F.uR ε) (TraceCovering.hi D.toDissection F.A F.uR ε) := by
      rw [hlo1, hhi1]
      exact ⟨⟨hb_pos.le, le_rfl⟩, ⟨hcon.le, by linarith⟩⟩
    exact absurd (hsub hm1 hm2) (ne_of_lt (max_lt hcon hb_pos))
  -- the stretch `[X, start]` of the ray: interior, a wall, ends not crossed from the far side
  have hint : ∀ x ∈ Set.Ioo b L, F.A + x • F.uR ∈ interior D.target.carrier :=
    fun x hx => F.hrint x (lt_trans hb_pos hx.1) (lt_trans hx.2 hlo)
  obtain ⟨i2, m2, -, hm01, -⟩ := T2_indexed F
  have hedgeAV : (D.tile i2).edge m2 = segment ℝ F.A F.V := by
    rw [Tri.edge]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    exact segment_symm ℝ _ _
  have hA0 : F.A + (0 : ℝ) • F.uR = F.A := by rw [zero_smul, add_zero]
  have hwall : ∀ x ∈ Set.Ioo b L, ∀ i, F.A + x • F.uR ∉ interior (D.tile i).carrier := by
    intro x hx i
    have hmem : F.A + x • F.uR ∈ (D.tile i2).edge m2 := by
      rw [hedgeAV, F.hV]
      have hs := TraceCovering.segment_param (X := F.A) (u := F.uR) 0 ((f : ℝ) ^ 2)
      rw [hA0, min_eq_left hc_pos.le, max_eq_right hc_pos.le] at hs
      rw [hs]
      exact ⟨x, ⟨(lt_trans hb_pos hx.1).le, (lt_trans hx.2 hlo).le⟩, rfl⟩
    exact D.toDissection.edge_point_not_interior hmem i
  have hsX : ¬ TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A)) (F.A + b • F.uR) := by
    have hhi1' : TraceCovering.hi D.toDissection F.A F.uR (i1, m) = b := hhi1
    rw [TraceCovering.str_iff hgd₂ F.hh0 rfl F.hhuR hu0, ← hhi1']
    exact (not_pstr_ends hh' hgd₂ F.hh0 rfl F.hhuR hu0 he1).2
  have hsL : ¬ TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A)) (F.A + L • F.uR) := by
    rw [TraceCovering.str_iff hgd₂ F.hh0 rfl F.hhuR hu0]
    exact (not_pstr_ends hh' hgd₂ F.hh0 rfl F.hhuR hu0 hε).1
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hh' hgd₂ F.hh0 rfl F.hhuR hu1 hLb
    hint hwall hsX hsL
  obtain ⟨P', Q', R', hPQR, hcard⟩ := sum_three_values
    ((D.toDissection.lineChain (-F.h) (-(F.h F.A))).filter
      (fun e' => (D.toDissection.tile e'.1).edge e'.2 ⊆
        segment ℝ (F.A + b • F.uR) (F.A + L • F.uR)))
    (fun e' => dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε' _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε'.1 ε'.2)
  rw [hsum] at hPQR
  -- `P a + Q b + R c = L − b < e²` forces `P = R = 0`
  have hlt : (P' : ℝ) * ((e : ℝ) * f) + (Q' : ℝ) * b + (R' : ℝ) * (f : ℝ) ^ 2 < (e : ℝ) ^ 2 := by
    rw [hPQR, hbdef]; linarith
  have ha_big : (e : ℝ) ^ 2 < (e : ℝ) * f := by nlinarith
  have hc_big : (e : ℝ) ^ 2 < (f : ℝ) ^ 2 := by nlinarith
  have hQnn : (0 : ℝ) ≤ (Q' : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb_pos.le
  have hPnn : (0 : ℝ) ≤ (P' : ℝ) * ((e : ℝ) * f) := by positivity
  have hRnn : (0 : ℝ) ≤ (R' : ℝ) * (f : ℝ) ^ 2 := by positivity
  have hP0 : P' = 0 := by
    by_contra h
    have h1 : (1 : ℝ) ≤ P' := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    have h2 : (e : ℝ) * f ≤ (P' : ℝ) * ((e : ℝ) * f) := by nlinarith
    linarith
  have hR0 : R' = 0 := by
    by_contra h
    have h1 : (1 : ℝ) ≤ R' := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    have h2 : (f : ℝ) ^ 2 ≤ (R' : ℝ) * (f : ℝ) ^ 2 := by nlinarith
    linarith
  subst hP0; subst hR0
  simp only [Nat.cast_zero, zero_mul, zero_add, add_zero] at hPQR hlt hcard
  have hLeq : L = ((Q' : ℝ) + 1) * b := by linarith
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hQlt : Q' * (f ^ 2 - e ^ 2) < e ^ 2 := by
    have : ((Q' * (f ^ 2 - e ^ 2) : ℕ) : ℝ) < ((e ^ 2 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hee]
      exact hlt
    exact_mod_cast this
  -- the start of the piercer is one of its ends
  have hend : F.A + L • F.uR = (D.tile ε.1).pts ε.2 ∨ F.A + L • F.uR = (D.tile ε.1).pts (ε.2 + 1) := by
    obtain ⟨h0e, h1e⟩ := TraceCovering.onLine hgd₂ hε
    have e0 := TraceCovering.par_spec (TraceCovering.exists_param F.hh0 rfl F.hhuR hu0 h0e)
    have e1 := TraceCovering.par_spec (TraceCovering.exists_param F.hh0 rfl F.hhuR hu0 h1e)
    rw [hL]
    unfold TraceCovering.lo
    rcases min_choice (TraceCovering.par F.A F.uR ((D.tile ε.1).pts ε.2))
      (TraceCovering.par F.A F.uR ((D.tile ε.1).pts (ε.2 + 1))) with h | h
    · left; rw [h]; exact e0.symm
    · right; rw [h]; exact e1.symm
  refine ⟨ε, Q', hε, hVε, ?_, hQlt, ?_, ?_⟩
  · rw [← hLeq]; exact hend
  · intro hthin
    by_contra hQ
    have h1 : 1 ≤ Q' := Nat.one_le_iff_ne_zero.mpr hQ
    have h2 : f ^ 2 - e ^ 2 ≤ Q' * (f ^ 2 - e ^ 2) := Nat.le_mul_of_pos_left _ h1
    omega
  · rw [← hLeq]
    exact hcard.symm

/-- **A `b`-piercer starting at the T-junction presents `α` there.** -/
theorem b_piercer_alpha (F : SFrame D e f α β γ k) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A)))
    (hV : F.V ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    (hstart : F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR = (D.tile ε.1).pts ε.2 ∨
      F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR = (D.tile ε.1).pts (ε.2 + 1))
    (hlen : dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) :
    (D.tile ε.1).localAngle (F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) = α := by
  classical
  obtain ⟨hab, hac, hbc⟩ := sides_distinct1 F.hco F.he F.hef
  have hA := F.hAng
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -, -, -⟩ := angle_facts hA
  have hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m' := by
    have h01 : sideOpp D.model 0 ≠ sideOpp D.model 1 := by rw [F.hM.hs0, F.hM.hs1]; exact hab
    have h02 : sideOpp D.model 0 ≠ sideOpp D.model 2 := by rw [F.hM.hs0, F.hM.hs2]; exact hac
    have h12 : sideOpp D.model 1 ≠ sideOpp D.model 2 := by rw [F.hM.hs1, F.hM.hs2]; exact hbc
    intro m m' hmm
    fin_cases m <;> fin_cases m' <;> first | exact absurd rfl hmm | exact h01 | exact h02 | exact h12 | exact h01.symm | exact h02.symm | exact h12.symm
  have hends := b_edge_endpoints D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' hscalene hαβ hαγ hβγ ε.1 ε.2
    (by rw [hlen, F.hM.hs1])
  -- the angle of the piercer's tile at `X` is `α` or `γ`
  have hXang : (D.tile ε.1).localAngle (F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) = α ∨
      (D.tile ε.1).localAngle (F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) = γ := by
    rcases hstart with h | h
    · rw [h, (D.tile ε.1).localAngle_vertex ε.2]; exact hends.1
    · rw [h, (D.tile ε.1).localAngle_vertex (ε.2 + 1)]; exact hends.2.1
  rcases hXang with h | h
  · exact h
  · -- `γ` is impossible: `T₁` is the only tile presenting `γ` at `X`
    exfalso
    obtain ⟨-, ⟨i1', hi1', hγ1⟩, -, -, -, hcγ, -⟩ := junction_figure F
    obtain ⟨i1, m, hi1, he1, hlo1, hhi1⟩ := T1_edge F
    have hu0 : F.uR ≠ 0 := TraceCovering.ne_zero_of_norm F.huR
    have hgd₂ : ∀ y, (-F.h) y = -(F.h F.A) ↔ F.h y = F.h F.A := TraceCovering.neg_iff
    -- the tile of the piercer is not a tile presenting `γ` at `X` other than itself; and it is not `i1'`
    have hneq : ε.1 ≠ i1' := by
      intro heq
      -- then the tile `i1'` has `V` in the relative interior of an edge, but its vertices are `A, X, Rf`
      have hVmem : F.V ∈ (D.tile i1').carrier := by
        rw [← heq]
        exact (D.tile ε.1).edge_subset_carrier ε.2 (openSegment_subset_segment ℝ _ _ hV)
      -- `h V = h A`, while the tile lies in `h ≥ h A` with only `A`, `X` on the line: `V` is on segment `A X`
      have hVπ : (D.tile ε.1).localAngle F.V = Real.pi := by
        have e1 : ε.2 + 2 + 1 = ε.2 := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) _
        have e2 : ε.2 + 2 + 2 = ε.2 + 1 := (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) _
        apply Erdos634.RouteOne.openSegment_localAngle_pi (D.tile ε.1) (ε.2 + 2)
        rw [e1, e2]; exact hV
      -- the edge through `V` of tile `i1'` is on the line and has length at most the sides; but
      -- its two ends are among `A`, `X`, `Rf`, and `Rf` is off the line: the edge is `[A, X]`, which
      -- does not contain `V` (parameter `c > b`)
      obtain ⟨h0e, h1e⟩ := TraceCovering.onLine hgd₂ hε
      have hpts : ∀ j, (D.tile ε.1).pts j ∈ ({F.A, F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR, F.Rf} : Set Plane) := by
        intro j; rw [heq, ← hi1']; exact ⟨j, rfl⟩
      have hRfoff : F.h F.Rf ≠ F.h F.A := ne_of_gt F.hhRf
      have hon : ∀ j, F.h ((D.tile ε.1).pts j) = F.h F.A →
          (D.tile ε.1).pts j = F.A ∨ (D.tile ε.1).pts j = F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR := by
        intro j hj
        have := hpts j
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
        rcases this with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
        · rw [h1] at hj; exact absurd hj hRfoff
      have hlo' := (TraceCovering.str_iff hgd₂ F.hh0 rfl F.hhuR hu0 ((f : ℝ) ^ 2)).mp
        (by rw [← F.hV]; exact ⟨ε, hε, hV⟩)
      -- parameters of the two ends are in `{0, b}`, so the edge lies in `[0, b]`, but `c` is beyond
      have hpar : ∀ j, F.h ((D.tile ε.1).pts j) = F.h F.A →
          TraceCovering.par F.A F.uR ((D.tile ε.1).pts j) ≤ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
        intro j hj
        have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by have := F.hef; omega)
        have heR1 : (1 : ℝ) ≤ e := by exact_mod_cast F.he
        have hefR : (e : ℝ) < f := by exact_mod_cast F.hef
        have hb_pos : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
        rcases hon j hj with h1 | h1
        · rw [h1]
          have : TraceCovering.par F.A F.uR F.A = 0 := by
            have := TraceCovering.par_add (X := F.A) (u := F.uR) hu0 0
            rwa [zero_smul, add_zero] at this
          rw [this]; exact hb_pos.le
        · rw [h1, TraceCovering.par_add hu0]
      have hhi_le : TraceCovering.hi D.toDissection F.A F.uR ε ≤ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
        unfold TraceCovering.hi
        exact max_le (hpar _ h0e) (hpar _ h1e)
      have hstr : TraceCovering.PStr (D.toDissection.lineChain (-F.h) (-(F.h F.A)))
          (TraceCovering.lo D.toDissection F.A F.uR) (TraceCovering.hi D.toDissection F.A F.uR)
          ((f : ℝ) ^ 2) → False := by
        intro _
        -- use the piercing edge itself
        have hVparam := hV
        rw [(TraceCovering.edge_data (D := D.toDissection) F.hh0 rfl F.hhuR hu0 h0e h1e).2.2.1, F.hV,
          (TraceCovering.lm_injective hu0).mem_set_image] at hVparam
        have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by have := F.hef; omega)
        have heR1 : (1 : ℝ) ≤ e := by exact_mod_cast F.he
        nlinarith [hVparam.2, hhi_le]
      exact hstr hlo'
    -- two distinct tiles presenting `γ` at `X` contradict the count `1`
    have hsub : ({ε.1, i1'} : Finset (Fin N)) ⊆
        ({i | (D.tile i).localAngle (F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) = γ} : Finset (Fin N)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [h]
      · simp [hγ1]
    have hcard2 := Finset.card_le_card hsub
    rw [Finset.card_pair hneq, hcγ] at hcard2
    omega

/-- at `(e, f) = (4, 5)` (super-thick: `25 ≤ 32`), `t (f² − e²) < e²` leaves `t ∈ {0, 1}`: the piercer starts at
distance `9` or `18` from the apex -/
theorem rung2_45 {t : ℕ} (h : t * (5 ^ 2 - 4 ^ 2) < 4 ^ 2) : t = 0 ∨ t = 1 := by omega

end Erdos634.Draft.PierceScale

#print axioms Erdos634.Draft.PierceScale.rung2
#print axioms Erdos634.Draft.PierceScale.b_piercer_alpha
