/-
Draft/W2E1HalfTurn.lean -- Stage 2 of the formalization of `prop:w2e1`: the half-turn lemma H and the corner lemma C
for the base tiles of `W_2(1,n)`, and the rules R-H2, R-H1, R-C.

* `Setup.c2_partner` / `Setup.c1_partner` (lemma H, from `half_turn`): a `C2` tile that is first or follows a tile
  showing `γ` (a `C1` tile followed by a tile showing `γ`) has a partner on its `b`-edge, a second tile with the
  vertices `V_α` and `G` that shows `γ` at `V_α`.  The hypothesis of H is `Setup.c2_hno` / `Setup.c1_hno`: no
  other tile has both `G` and `V_β` as vertices (angle sums at `V_β`).
* `Setup.c1_corner` (lemma C, from `partner`): the last tile, if of type `C1`, has such a partner; here the
  `b`-edge is clamped by the side `BA` of the target.
* `Setup.c2_right`, `Setup.c1_left`: the base tile beyond `V_α` shows `β` there (vertex figure at `V_α`).
* `Setup.rule_H2`, `Setup.rule_H1`, `Setup.rule_C`.

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.W2E1Frame

namespace Erdos634.Draft.W2E1

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Set

namespace Setup

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ : ℝ}

/-- a base tile lies over the side `QB` -/
theorem baseTile_range (S : Setup D n α β γ) {i : Fin N} {t : Ty} {x : ℝ}
    (h : BaseTile D n i t x) : 0 ≤ x ∧ x + t.lenR n ≤ Lw n := by
  obtain ⟨k, m, j, -, -, -, hk, hm, -, -⟩ := h
  have h1 := (S.pts_mem i k).2.1
  have h2 := (S.pts_mem i m).2.2
  rw [hk, gQA_mk] at h1
  rw [hm, gBA_mk] at h2
  have hr := rt_pos S.f1.le
  have hb := S.b_pos
  constructor
  · by_contra hneg
    push Not at hneg
    nlinarith [mul_pos hr (neg_pos.mpr hneg)]
  · by_contra hneg
    push Not at hneg
    nlinarith [mul_pos (mul_pos hb hr) (sub_pos.mpr hneg)]

/-- a tile with an `a`-edge `[P, V]` shows `γ` or `β` at `V` -/
theorem angle_of_a_edge (S : Setup D n α β γ) {i : Fin N} {k m : Fin 3} (hkm : k ≠ m)
    (hd : dist ((D.tile i).pts k) ((D.tile i).pts m) = n) :
    (D.tile i).localAngle ((D.tile i).pts m) = γ ∨ (D.tile i).localAngle ((D.tile i).pts m) = β := by
  obtain ⟨j, hjk, hjm⟩ := fin3_third k m hkm
  have hA := angle_at_vertex D S.f2 S.hM i (Ne.symm hkm) (Ne.symm hjm) (Ne.symm hjk)
  rcases sides_of_a_edge D S.f2 S.hM i hkm (Ne.symm hjk) (Ne.symm hjm) hd with ⟨h1, -⟩ | ⟨h1, -⟩
  · left; exact hA.2.2 (by rw [dist_comm]; exact h1)
  · right; exact hA.2.1 (by rw [dist_comm]; exact h1)

/-- a tile with a `b`-edge `[P, V]` shows `γ` or `α` at `V` -/
theorem angle_of_b_edge (S : Setup D n α β γ) {i : Fin N} {k m : Fin 3} (hkm : k ≠ m)
    (hd : dist ((D.tile i).pts k) ((D.tile i).pts m) = (n:ℝ) ^ 2 - 1) :
    (D.tile i).localAngle ((D.tile i).pts m) = γ ∨ (D.tile i).localAngle ((D.tile i).pts m) = α := by
  obtain ⟨j, hjk, hjm⟩ := fin3_third k m hkm
  have hA := angle_at_vertex D S.f2 S.hM i (Ne.symm hkm) (Ne.symm hjm) (Ne.symm hjk)
  rcases sides_of_b_edge D S.f2 S.hM i hkm (Ne.symm hjk) (Ne.symm hjm) hd with ⟨h1, -⟩ | ⟨h1, -⟩
  · right; exact hA.1 (by rw [dist_comm]; exact h1)
  · left; exact hA.2.2 (by rw [dist_comm]; exact h1)

/-- the polynomial behind the abscissa comparisons: `(n²−1)(2n+1)(n−1) > 0` -/
theorem poly_pos (S : Setup D n α β γ) : (0:ℝ) < ((n:ℝ) ^ 2 - 1) * ((2 * n + 1) * ((n:ℝ) - 1)) :=
  mul_pos S.b_pos (mul_pos (by linarith [S.f0]) (by linarith [S.f1]))

theorem uu_ne_half (S : Setup D n α β γ) : uu (n:ℝ) ≠ 1 / 2 := by
  intro h
  have hu := uu_spec S.f1
  rw [h] at hu
  nlinarith [S.f3]

/-! ## The tiles of type `C2` -/

/-- **The hypothesis of the half-turn lemma for a `C2` tile**: if the tile is first, or follows a tile showing
`γ`, no other tile has both its apex `G` and its `β`-end as vertices. -/
theorem c2_hno (S : Setup D n α β γ) {it : Fin N} {x : ℝ} (h : BaseTile D n it Ty.C2 x)
    (hprev : x = 0 ∨ ∃ (jp : Fin N) (t' : Ty) (xp : ℝ),
      BaseTile D n jp t' xp ∧ xp + t'.lenR n = x ∧ t'.gR)
    {T' : Fin N} (hT : T' ≠ it) {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile T').pts k = mkPt (x + uu n) (hh n)) (hm : (D.tile T').pts m = mkPt x 0) :
    False := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hαβ := S.alpha_lt_beta
  obtain ⟨kb, ka, kg, hba, hbg, hag, hVb, hVa, hG, hda, hdb⟩ := S.c2_data h
  have hTang := S.angle_of_a_edge (i := T') hkm (by rw [hk, hm]; exact hda)
  rw [hm] at hTang
  have hit : (D.tile it).localAngle (mkPt x 0) = β := (S.angles h).1
  rcases hprev with hx | ⟨jp, t', xp, hp, hxp, hgR⟩
  · subst hx
    have h2 := two_angles_le D.toDissection (mkPt 0 0) hT
    rw [S.angle_Q, hit] at h2
    rcases hTang with h3 | h3 <;> rw [h3] at h2 <;> linarith
  · have hxr := S.baseTile_range h
    have hpr := S.baseTile_range hp
    have hl := Ty.lenR_pos S.f2 t'
    have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by have := S.f0; positivity
    have hx0 : 0 < x := by linarith [hpr.1]
    have hxL : x < Lw n := by
      have h3 : x + (n:ℝ) ^ 2 ≤ Lw n := hxr.2
      linarith
    have hjp := (S.angles hp).2
    rw [hxp, Ty.aR_of_gR α β γ hgR] at hjp
    have hjpit : jp ≠ it := S.baseTile_ne hp h (by intro h0; linarith)
    have hTjp : T' ≠ jp := by
      intro hTj
      rw [hTj] at hk
      obtain ⟨p, -, hp1, -, hpR, hpe, huniq⟩ := S.apex hp
      have hGp : mkPt (x + uu n) (hh n) = p :=
        huniq _ ⟨k, hk⟩ (by rw [mkPt_one]; exact (hh_pos S.f1).ne')
      rw [← hGp, hxp, hda] at hpR
      rcases hgR with rfl | rfl
      · have h5 : (n:ℝ) = (n:ℝ) ^ 2 - 1 := hpR
        nlinarith [S.f3]
      · rw [← hGp, mkPt_zero] at hpe
        have e : 2 * ((n:ℝ) ^ 2 - 1) * (x + uu n - xp)
            = ((n:ℝ) ^ 2) ^ 2 - (n:ℝ) ^ 2 + ((n:ℝ) ^ 2 - 1) ^ 2 := hpe
        have hxp' : xp + ((n:ℝ) ^ 2 - 1) = x := hxp
        have key : ((n:ℝ) ^ 2 - 1) * (2 * uu n - 1) = 0 := by
          linear_combination e + 2 * ((n:ℝ) ^ 2 - 1) * hxp'
        rcases mul_eq_zero.mp key with h0 | h0
        · exact absurd h0 S.b_pos.ne'
        · exact S.uu_ne_half (by linarith)
    have h3 := three_angles_le D.toDissection (mkPt x 0) hT hTjp (Ne.symm hjpit)
    rw [hit, hjp, S.angle_base hx0 hxL] at h3
    rcases hTang with h4 | h4 <;> rw [h4] at h3 <;> linarith

/-- **The half-turn lemma for a `C2` tile**: a second tile has the vertices `V_α`, `G` and shows `γ` at `V_α`. -/
theorem c2_partner (S : Setup D n α β γ) {it : Fin N} {x : ℝ} (h : BaseTile D n it Ty.C2 x)
    (hprev : x = 0 ∨ ∃ (jp : Fin N) (t' : Ty) (xp : ℝ),
      BaseTile D n jp t' xp ∧ xp + t'.lenR n = x ∧ t'.gR) :
    x + (n:ℝ) ^ 2 < Lw n ∧ ∃ ts : Fin N, ts ≠ it ∧
      (D.tile ts).localAngle (mkPt (x + (n:ℝ) ^ 2) 0) = γ ∧
      ∃ m : Fin 3, (D.tile ts).pts m = mkPt (x + uu n) (hh n) := by
  obtain ⟨kb, ka, kg, hba, hbg, hag, hVb, hVa, hG, hda, hdb⟩ := S.c2_data h
  have hxr := S.baseTile_range h
  have hx0 : 0 ≤ x := hxr.1
  have hxc : x + (n:ℝ) ^ 2 ≤ Lw n := hxr.2
  have hxL : x + (n:ℝ) ^ 2 < Lw n := by
    rcases lt_or_eq_of_le hxc with h1 | h1
    · exact h1
    · exfalso
      rcases S.rule_B h h1 with h2 | h2 <;> cases h2
  have hr := rt_pos S.f1.le
  have hb := S.b_pos
  have hhp := hh_pos S.f1
  have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by have := S.f0; positivity
  have mG : mkPt (x + uu n) (hh n) ∈ D.target.carrier := by
    rw [← hG]; exact pts_mem_target D.toDissection it kg
  have mVb : mkPt x 0 ∈ D.target.carrier := by
    rw [← hVb]; exact pts_mem_target D.toDissection it kb
  have mVa : mkPt (x + (n:ℝ) ^ 2) 0 ∈ D.target.carrier := by
    rw [← hVa]; exact pts_mem_target D.toDissection it ka
  have hG1 : 0 < (mkPt (x + uu n) (hh n)) 1 := by rw [mkPt_one]; exact hhp
  have hint1 : openSegment ℝ (mkPt (x + uu n) (hh n)) (mkPt x 0)
      ⊆ interior D.target.carrier := by
    refine S.interior_seg mG mVb (Or.inl hG1) (Or.inl ?_) (Or.inr ?_)
    · rw [gQA_mk]
      have h1 := ruh S.f1
      nlinarith [mul_nonneg hr.le hx0]
    · rw [gBA_mk]
      nlinarith [mul_pos (mul_pos hb hr) (show (0:ℝ) < Lw n - x by linarith)]
  have hint2 : openSegment ℝ (mkPt (x + (n:ℝ) ^ 2) 0) (mkPt (x + uu n) (hh n))
      ⊆ interior D.target.carrier := by
    refine S.interior_seg mVa mG (Or.inr hG1) (Or.inl ?_) (Or.inl ?_)
    · rw [gQA_mk]
      nlinarith [mul_pos hr (show (0:ℝ) < x + (n:ℝ) ^ 2 by linarith)]
    · rw [gBA_mk]
      nlinarith [mul_pos (mul_pos hb hr) (show (0:ℝ) < Lw n - (x + (n:ℝ) ^ 2) by linarith)]
  have htG : (D.tile it).localAngle (mkPt (x + uu n) (hh n)) = γ := by
    have h1 := (angle_at_vertex D S.f2 S.hM it (Ne.symm hbg) (Ne.symm hag) hba).2.2
      (by rw [hVb, hVa]; exact dist_mkPt_base x _ hn2.le)
    rw [hG] at h1; exact h1
  obtain ⟨ts, hts, k, m, j, hkm, -, -, hk, hm, -, -, hang, -⟩ :=
    half_turn D S.hn3 S.hM S.hA hba hbg hag hVb hVa hG hda hdb htG hint1 hint2
      (S.below_out (mkPt_one _ _) hG1) (S.below_out (mkPt_one _ _) hG1)
      (fun T' hT ⟨k, m, hkm, hk, hm⟩ => S.c2_hno h hprev hT hkm hk hm)
  exact ⟨hxL, ts, hts, hang, m, hm⟩

/-- **The base tile to the right of a `C2` tile with a partner shows `β`.** -/
theorem c2_right (S : Setup D n α β γ) {it : Fin N} {x : ℝ} (h : BaseTile D n it Ty.C2 x)
    (hxL : x + (n:ℝ) ^ 2 < Lw n) {ts : Fin N}
    (hang : (D.tile ts).localAngle (mkPt (x + (n:ℝ) ^ 2) 0) = γ) {k : Fin 3}
    (hk : (D.tile ts).pts k = mkPt (x + uu n) (hh n)) {jn : Fin N} {t' : Ty}
    (hn : BaseTile D n jn t' (x + (n:ℝ) ^ 2)) : t' = Ty.A1 ∨ t' = Ty.C2 := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hxr := S.baseTile_range h
  have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by have := S.f0; positivity
  have hx0 : 0 < x + (n:ℝ) ^ 2 := by linarith [hxr.1]
  have hit : (D.tile it).localAngle (mkPt (x + (n:ℝ) ^ 2) 0) = α := (S.angles h).2
  have hjn := (S.angles hn).1
  have hne : jn ≠ it := S.baseTile_ne hn h (by intro h0; linarith)
  obtain ⟨kb, ka, kg, hba, hbg, hag, hVb, hVa, hG, hda, hdb⟩ := S.c2_data h
  have hGne : (mkPt (x + uu n) (hh n)) 1 ≠ 0 := by rw [mkPt_one]; exact (hh_pos S.f1).ne'
  have htwo : ∀ jn' : Fin N, jn' ≠ ts →
      (D.tile jn').localAngle (mkPt (x + (n:ℝ) ^ 2) 0) = γ → False := by
    intro jn' hne' hγ'
    have h2 := two_angles_le D.toDissection (mkPt (x + (n:ℝ) ^ 2) 0) hne'
    rw [hγ', hang, S.angle_base hx0 hxL] at h2
    linarith
  cases t'
  · exact Or.inl rfl
  · exfalso
    have hjn' : (D.tile jn).localAngle (mkPt (x + (n:ℝ) ^ 2) 0) = γ := hjn
    by_cases hjt : jn = ts
    · rw [← hjt] at hk
      obtain ⟨p, -, hp1, hpL, -, hpe, huniq⟩ := S.apex hn
      have hGp : mkPt (x + uu n) (hh n) = p := huniq _ ⟨k, hk⟩ hGne
      rw [← hGp, mkPt_zero] at hpe
      have e : 2 * (n:ℝ) * (x + uu n - (x + (n:ℝ) ^ 2))
          = ((n:ℝ) ^ 2 - 1) ^ 2 - ((n:ℝ) ^ 2) ^ 2 + (n:ℝ) ^ 2 := hpe
      have hu := uu_spec S.f1
      have key : ((n:ℝ) ^ 2 - 1) * ((2 * n + 1) * ((n:ℝ) - 1)) = 0 := by
        linear_combination hu - (n:ℝ) * e
      have := S.poly_pos
      linarith
    · exact htwo jn hjt hjn'
  · exfalso
    exact S.gamma_alpha_alpha hx0 hxL hang hit hjn (Ne.symm hne)
  · exfalso
    have hjn' : (D.tile jn).localAngle (mkPt (x + (n:ℝ) ^ 2) 0) = γ := hjn
    by_cases hjt : jn = ts
    · rw [← hjt] at hk
      obtain ⟨p, -, hp1, hpL, -, -, huniq⟩ := S.apex hn
      have hGp : mkPt (x + uu n) (hh n) = p := huniq _ ⟨k, hk⟩ hGne
      rw [← hGp, dist_comm, hdb] at hpL
      have h5 : (n:ℝ) ^ 2 - 1 = (n:ℝ) := hpL
      nlinarith [S.f3]
    · exact htwo jn hjt hjn'
  · exfalso
    exact S.gamma_alpha_alpha hx0 hxL hang hit hjn (Ne.symm hne)
  · exact Or.inr rfl

/-- **R-H2**: a `C2` tile that is first or follows a tile showing `γ` is not last, and the next base tile is of
type `A1` or `C2`. -/
theorem rule_H2 (S : Setup D n α β γ) {it : Fin N} {x : ℝ} (h : BaseTile D n it Ty.C2 x)
    (hprev : x = 0 ∨ ∃ (jp : Fin N) (t' : Ty) (xp : ℝ),
      BaseTile D n jp t' xp ∧ xp + t'.lenR n = x ∧ t'.gR) :
    x + (n:ℝ) ^ 2 < Lw n ∧ ∀ (jn : Fin N) (t' : Ty), BaseTile D n jn t' (x + (n:ℝ) ^ 2) →
      t' = Ty.A1 ∨ t' = Ty.C2 := by
  obtain ⟨hxL, ts, -, hang, m, hm⟩ := S.c2_partner h hprev
  exact ⟨hxL, fun jn t' hn => S.c2_right h hxL hang hm hn⟩

/-! ## The tiles of type `C1` -/

/-- **The hypothesis of the half-turn lemma for a `C1` tile** followed by a tile showing `γ`: no other tile has
both its apex `G` and its `β`-end as vertices. -/
theorem c1_hno (S : Setup D n α β γ) {it : Fin N} {x : ℝ} (h : BaseTile D n it Ty.C1 x)
    {jn : Fin N} {t' : Ty} (hn : BaseTile D n jn t' (x + (n:ℝ) ^ 2)) (hgL : t'.gL)
    {T' : Fin N} (hT : T' ≠ it) {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile T').pts k = mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n))
    (hm : (D.tile T').pts m = mkPt (x + (n:ℝ) ^ 2) 0) : False := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hαβ := S.alpha_lt_beta
  obtain ⟨ka, kb, kg, hab, hag, hbg, hVa, hVb, hG, hda, hdb⟩ := S.c1_data h
  have hTang := S.angle_of_a_edge (i := T') hkm (by rw [hk, hm]; exact hda)
  rw [hm] at hTang
  have hit : (D.tile it).localAngle (mkPt (x + (n:ℝ) ^ 2) 0) = β := (S.angles h).2
  have hxr := S.baseTile_range h
  have hnr := S.baseTile_range hn
  have hl := Ty.lenR_pos S.f2 t'
  have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by have := S.f0; positivity
  have hx0 : 0 < x + (n:ℝ) ^ 2 := by linarith [hxr.1]
  have hxL : x + (n:ℝ) ^ 2 < Lw n := by linarith [hnr.2]
  have hjn := (S.angles hn).1
  rw [Ty.aL_of_gL α β γ hgL] at hjn
  have hjnit : jn ≠ it := S.baseTile_ne hn h (by intro h0; linarith)
  have hTjn : T' ≠ jn := by
    intro hTj
    rw [hTj] at hk
    obtain ⟨p, -, hp1, hpL, -, hpe, huniq⟩ := S.apex hn
    have hGp : mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n) = p :=
      huniq _ ⟨k, hk⟩ (by rw [mkPt_one]; exact (hh_pos S.f1).ne')
    rw [← hGp, hda] at hpL
    rcases hgL with rfl | rfl
    · have h5 : (n:ℝ) = (n:ℝ) ^ 2 - 1 := hpL
      nlinarith [S.f3]
    · rw [← hGp, mkPt_zero] at hpe
      have e : 2 * ((n:ℝ) ^ 2 - 1) * (x + (n:ℝ) ^ 2 - uu n - (x + (n:ℝ) ^ 2))
          = (n:ℝ) ^ 2 - ((n:ℝ) ^ 2) ^ 2 + ((n:ℝ) ^ 2 - 1) ^ 2 := hpe
      have key : ((n:ℝ) ^ 2 - 1) * (2 * uu n - 1) = 0 := by
        linear_combination (-1 : ℝ) * e
      rcases mul_eq_zero.mp key with h0 | h0
      · exact absurd h0 S.b_pos.ne'
      · exact S.uu_ne_half (by linarith)
  have h3 := three_angles_le D.toDissection (mkPt (x + (n:ℝ) ^ 2) 0) hT hTjn (Ne.symm hjnit)
  rw [hit, hjn, S.angle_base hx0 hxL] at h3
  rcases hTang with h4 | h4 <;> rw [h4] at h3 <;> linarith

/-- the facts about a `C1` tile that both partner lemmas use -/
theorem c1_common (S : Setup D n α β γ) {it : Fin N} {x : ℝ} (h : BaseTile D n it Ty.C1 x)
    {ka kb kg : Fin 3} (hab : ka ≠ kb) (hag : ka ≠ kg) (hbg : kb ≠ kg)
    (hVa : (D.tile it).pts ka = mkPt x 0) (hVb : (D.tile it).pts kb = mkPt (x + (n:ℝ) ^ 2) 0)
    (hG : (D.tile it).pts kg = mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) :
    0 < (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) 1 ∧
    (D.tile it).localAngle (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = γ ∧
    openSegment ℝ (mkPt x 0) (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) ⊆ interior D.target.carrier := by
  have hxr := S.baseTile_range h
  have hx0 : 0 ≤ x := hxr.1
  have hxc : x + (n:ℝ) ^ 2 ≤ Lw n := hxr.2
  have hr := rt_pos S.f1.le
  have hb := S.b_pos
  have hhp := hh_pos S.f1
  have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by have := S.f0; positivity
  have mG : mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n) ∈ D.target.carrier := by
    rw [← hG]; exact pts_mem_target D.toDissection it kg
  have mVa : mkPt x 0 ∈ D.target.carrier := by
    rw [← hVa]; exact pts_mem_target D.toDissection it ka
  have hG1 : 0 < (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) 1 := by rw [mkPt_one]; exact hhp
  refine ⟨hG1, ?_, ?_⟩
  · have h1 := (angle_at_vertex D S.f2 S.hM it (Ne.symm hag) (Ne.symm hbg) hab).2.2
      (by rw [hVa, hVb]; exact dist_mkPt_base x _ hn2.le)
    rw [hG] at h1; exact h1
  · refine S.interior_seg mVa mG (Or.inr hG1) (Or.inr ?_) (Or.inl ?_)
    · rw [gQA_mk]
      have h1 := ruh S.f1
      have h2 := two_hh_lt S.f1
      nlinarith [mul_nonneg hr.le hx0]
    · rw [gBA_mk]
      nlinarith [mul_pos (mul_pos hb hr) (show (0:ℝ) < Lw n - x by linarith)]

/-- **The half-turn lemma for a `C1` tile** followed by a tile showing `γ`: a second tile has the vertices
`V_α = (x, 0)` and `G` and shows `γ` at `V_α`. -/
theorem c1_partner (S : Setup D n α β γ) {it : Fin N} {x : ℝ} (h : BaseTile D n it Ty.C1 x)
    {jn : Fin N} {t' : Ty} (hn : BaseTile D n jn t' (x + (n:ℝ) ^ 2)) (hgL : t'.gL) :
    ∃ ts : Fin N, ts ≠ it ∧ (D.tile ts).localAngle (mkPt x 0) = γ ∧
      ∃ m : Fin 3, (D.tile ts).pts m = mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n) := by
  obtain ⟨ka, kb, kg, hab, hag, hbg, hVa, hVb, hG, hda, hdb⟩ := S.c1_data h
  obtain ⟨hG1, htG, hint2⟩ := S.c1_common h hab hag hbg hVa hVb hG
  have hxr := S.baseTile_range h
  have hnr := S.baseTile_range hn
  have hl := Ty.lenR_pos S.f2 t'
  have hx0 : 0 ≤ x := hxr.1
  have hxL : x + (n:ℝ) ^ 2 < Lw n := by linarith [hnr.2]
  have hr := rt_pos S.f1.le
  have hb := S.b_pos
  have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by have := S.f0; positivity
  have mG : mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n) ∈ D.target.carrier := by
    rw [← hG]; exact pts_mem_target D.toDissection it kg
  have mVb : mkPt (x + (n:ℝ) ^ 2) 0 ∈ D.target.carrier := by
    rw [← hVb]; exact pts_mem_target D.toDissection it kb
  have hint1 : openSegment ℝ (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) (mkPt (x + (n:ℝ) ^ 2) 0)
      ⊆ interior D.target.carrier := by
    refine S.interior_seg mG mVb (Or.inl hG1) (Or.inr ?_) (Or.inr ?_)
    · rw [gQA_mk]
      nlinarith [mul_pos hr (show (0:ℝ) < x + (n:ℝ) ^ 2 by linarith)]
    · rw [gBA_mk]
      nlinarith [mul_pos (mul_pos hb hr) (show (0:ℝ) < Lw n - (x + (n:ℝ) ^ 2) by linarith)]
  obtain ⟨ts, hts, k, m, j, hkm, -, -, hk, hm, -, -, hang, -⟩ :=
    half_turn D S.hn3 S.hM S.hA (Ne.symm hab) hbg hag hVb hVa hG hda hdb htG hint1 hint2
      (S.below_out (mkPt_one _ _) hG1) (S.below_out (mkPt_one _ _) hG1)
      (fun T' hT ⟨k, m, hkm, hk, hm⟩ => S.c1_hno h hn hgL hT hkm hk hm)
  exact ⟨ts, hts, hang, m, hm⟩

/-- the apex of the last `C1` tile lies on the side `BA` -/
theorem last_apex_eq (S : Setup D n α β γ) :
    mkPt (Lw n - uu n) (hh n)
      = mkPt (Lw n - 1 / (2 * (n:ℝ) ^ 2) * (3 * (n:ℝ) ^ 2 - 1))
          (1 / (2 * (n:ℝ) ^ 2) * (((n:ℝ) ^ 2 - 1) * rt n)) :=
  mkPt_congr (by unfold uu; ring) (by unfold hh; ring)

/-- **The corner lemma**: the last base tile, if of type `C1`, has a partner on its `b`-edge: a second tile with
the vertices `V_α = (L − c, 0)` and `G`, showing `γ` at `V_α`; its third vertex is at the distances `a`, `c` from
`V_α`, `G`, on the side of the line `V_α G` away from `B`. -/
theorem c1_corner (S : Setup D n α β γ) {it : Fin N} {x : ℝ} (h : BaseTile D n it Ty.C1 x)
    (hx : x + (n:ℝ) ^ 2 = Lw n) :
    ∃ ts : Fin N, ts ≠ it ∧ ∃ k m j : Fin 3, k ≠ m ∧ k ≠ j ∧ m ≠ j ∧
      (D.tile ts).pts k = mkPt x 0 ∧ (D.tile ts).pts m = mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n) ∧
      dist ((D.tile ts).pts j) (mkPt x 0) = n ∧
      dist ((D.tile ts).pts j) (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = (n:ℝ) ^ 2 ∧
      (D.tile ts).localAngle (mkPt x 0) = γ ∧
      0 ≤ cross (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n) - mkPt x 0) ((D.tile ts).pts j - mkPt x 0)
        * cross (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n) - mkPt x 0)
            (mkPt x 0 - mkPt (x + (n:ℝ) ^ 2) 0) := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  obtain ⟨ka, kb, kg, hab, hag, hbg, hVa, hVb, hG, hda, hdb⟩ := S.c1_data h
  obtain ⟨hG1, htG, hint2⟩ := S.c1_common h hab hag hbg hVa hVb hG
  have hr := rt_pos S.f1.le
  have hb := S.b_pos
  have hf0 := S.f0
  have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by positivity
  -- the apex is on `BA`
  have hGB : gBA n (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = 0 := by
    rw [gBA_mk, hx]
    have h1 := bru S.f1
    linear_combination h1
  have hVaB : 0 < gBA n (mkPt x 0) := by
    rw [gBA_mk]
    nlinarith [mul_pos (mul_pos hb hr) (show (0:ℝ) < Lw n - x by linarith)]
  have hGπ : D.target.localAngle (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = Real.pi := by
    rw [hx, S.last_apex_eq]
    refine S.angle_BA (by positivity) ?_
    rw [div_lt_one (by positivity)]
    nlinarith
  obtain ⟨ts, hts, k, m, j, hkm, hkj, hmj, hk, hm, hd1, hd2, hang, hside⟩ :=
    partner D S.hn3 S.hM hag hab (Ne.symm hbg) hVa hG hdb hint2
      (S.below_out (mkPt_one _ _) hG1) (Or.inl (S.BA_out hGB hVaB))
      (fun i' hi' hγ' => by
        have h2 := two_angles_le D.toDissection (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) hi'
        rw [hγ', htG, hGπ] at h2
        linarith)
  rw [hVb] at hside
  exact ⟨ts, hts, k, m, j, hkm, hkj, hmj, hk, hm, hd1, hd2, hang, hside⟩

/-- **The base tile to the left of a `C1` tile with a partner shows `β`**; in particular the tile is not first. -/
theorem c1_left (S : Setup D n α β γ) {it : Fin N} {x : ℝ} (h : BaseTile D n it Ty.C1 x)
    {ts : Fin N} (hts : ts ≠ it) (hang : (D.tile ts).localAngle (mkPt x 0) = γ) {k : Fin 3}
    (hk : (D.tile ts).pts k = mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) :
    0 < x ∧ ∀ (jp : Fin N) (t' : Ty) (xp : ℝ), BaseTile D n jp t' xp → xp + t'.lenR n = x →
      t' = Ty.A2 ∨ t' = Ty.C1 := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hxr := S.baseTile_range h
  have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by have := S.f0; positivity
  have hit : (D.tile it).localAngle (mkPt x 0) = α := (S.angles h).1
  have hx0 : 0 < x := by
    rcases lt_or_eq_of_le hxr.1 with h1 | h1
    · exact h1
    · exfalso
      rw [← h1] at hang hit
      have h2 := two_angles_le D.toDissection (mkPt 0 0) hts
      rw [S.angle_Q, hang, hit] at h2
      linarith
  have hxL : x < Lw n := by
    have h3 : x + (n:ℝ) ^ 2 ≤ Lw n := hxr.2
    linarith
  refine ⟨hx0, fun jp t' xp hp hxp => ?_⟩
  have hl := Ty.lenR_pos S.f2 t'
  have hjp := (S.angles hp).2
  rw [hxp] at hjp
  have hne : jp ≠ it := S.baseTile_ne hp h (by intro h0; linarith)
  obtain ⟨ka, kb, kg, hab, hag, hbg, hVa, hVb, hG, hda, hdb⟩ := S.c1_data h
  have hGne : (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) 1 ≠ 0 := by
    rw [mkPt_one]; exact (hh_pos S.f1).ne'
  have htwo : ∀ jp' : Fin N, jp' ≠ ts → (D.tile jp').localAngle (mkPt x 0) = γ → False := by
    intro jp' hne' hγ'
    have h2 := two_angles_le D.toDissection (mkPt x 0) hne'
    rw [hγ', hang, S.angle_base hx0 hxL] at h2
    linarith
  cases t'
  · exfalso
    have hjp' : (D.tile jp).localAngle (mkPt x 0) = γ := hjp
    by_cases hjt : jp = ts
    · rw [← hjt] at hk
      obtain ⟨p, -, hp1, -, -, hpe, huniq⟩ := S.apex hp
      have hGp : mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n) = p := huniq _ ⟨k, hk⟩ hGne
      rw [← hGp, mkPt_zero] at hpe
      have e : 2 * (n:ℝ) * (x + (n:ℝ) ^ 2 - uu n - xp)
          = ((n:ℝ) ^ 2) ^ 2 - ((n:ℝ) ^ 2 - 1) ^ 2 + (n:ℝ) ^ 2 := hpe
      have hxp' : xp + (n:ℝ) = x := hxp
      have hu := uu_spec S.f1
      have key : ((n:ℝ) ^ 2 - 1) * ((2 * n + 1) * ((n:ℝ) - 1)) = 0 := by
        linear_combination hu + (n:ℝ) * e + 2 * (n:ℝ) ^ 2 * hxp'
      have := S.poly_pos
      linarith
    · exact htwo jp hjt hjp'
  · exact Or.inl rfl
  · exfalso
    have hjp' : (D.tile jp).localAngle (mkPt x 0) = γ := hjp
    by_cases hjt : jp = ts
    · rw [← hjt] at hk
      obtain ⟨p, -, hp1, -, hpR, -, huniq⟩ := S.apex hp
      have hGp : mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n) = p := huniq _ ⟨k, hk⟩ hGne
      rw [← hGp, hxp, dist_comm, hdb] at hpR
      have h5 : (n:ℝ) ^ 2 - 1 = (n:ℝ) := hpR
      nlinarith [S.f3]
    · exact htwo jp hjt hjp'
  · exfalso
    exact S.gamma_alpha_alpha hx0 hxL hang hit hjp (Ne.symm hne)
  · exact Or.inr rfl
  · exfalso
    exact S.gamma_alpha_alpha hx0 hxL hang hit hjp (Ne.symm hne)

/-- **R-H1**: a `C1` tile followed by a tile showing `γ` is not first, and the previous base tile is of type `A2`
or `C1`. -/
theorem rule_H1 (S : Setup D n α β γ) {it : Fin N} {x : ℝ} (h : BaseTile D n it Ty.C1 x)
    {jn : Fin N} {t' : Ty} (hn : BaseTile D n jn t' (x + (n:ℝ) ^ 2)) (hgL : t'.gL) :
    0 < x ∧ ∀ (jp : Fin N) (t'' : Ty) (xp : ℝ), BaseTile D n jp t'' xp → xp + t''.lenR n = x →
      t'' = Ty.A2 ∨ t'' = Ty.C1 := by
  obtain ⟨ts, hts, hang, m, hm⟩ := S.c1_partner h hn hgL
  exact S.c1_left h hts hang hm

/-- **R-C**: if the last base tile is of type `C1`, the previous one is of type `A2` or `C1`. -/
theorem rule_C (S : Setup D n α β γ) {it : Fin N} {x : ℝ} (h : BaseTile D n it Ty.C1 x)
    (hx : x + (n:ℝ) ^ 2 = Lw n) :
    0 < x ∧ ∀ (jp : Fin N) (t'' : Ty) (xp : ℝ), BaseTile D n jp t'' xp → xp + t''.lenR n = x →
      t'' = Ty.A2 ∨ t'' = Ty.C1 := by
  obtain ⟨ts, hts, k, m, j, -, -, -, -, hm, -, -, hang, -⟩ := S.c1_corner h hx
  exact S.c1_left h hts hang hm

end Setup

end Erdos634.Draft.W2E1

#print axioms Erdos634.Draft.W2E1.Setup.c2_partner
#print axioms Erdos634.Draft.W2E1.Setup.c1_partner
#print axioms Erdos634.Draft.W2E1.Setup.c1_corner
#print axioms Erdos634.Draft.W2E1.Setup.rule_H2
#print axioms Erdos634.Draft.W2E1.Setup.rule_H1
#print axioms Erdos634.Draft.W2E1.Setup.rule_C
