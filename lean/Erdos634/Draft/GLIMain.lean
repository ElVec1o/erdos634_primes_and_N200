import Mathlib.Tactic
import Erdos634.Draft.GLICorner
import Erdos634.Draft.GLIG2
import Erdos634.Draft.GLIApex
import Erdos634.Draft.GLIRev
import Erdos634.Draft.GLCArith

/-!
# `leafG_of_dissection`: leaf G for a real `CongruentDissection` (assembly)

`leafG_core`: for target vertices `p, q` of angle `α` and apex `r` (angle `π − 2α`), three oriented walls `La : p → r`, `Lb : q → r`,
`Ba : p → q` with their chains, the apex condition (`La` ends with `α`, `Lb` with `β`), and the leaf-G side lengths, the
`GLG.Model` of the three side chains and `GStar` of `Lb` hold, so `GLG.leafG_closed` gives `False`.
`leafG_of_dissection`: for a `CongruentDissection` whose tile is `s·(k², 2k+1, k(k+1))` (`γ = 2α`, `α ∉ ℚπ`), `k ≥ 3`, whose target has base angles `α` at
`pts 0`, `pts 1` and leg `|pts 1 - pts 2| = s · 2k(2k+1)`, `False`.
-/

namespace Erdos634.GLI

open Erdos634.Geometry Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.GLG
  Erdos634.BaseChain

variable {N : ℕ}

theorem corner_both_sym (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hab : a ≠ b) (hac : a ≠ c)
    (hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1)
    (k : Fin 3) (hk : D.target.angleAt k = α)
    (hA1 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ b)
    (hA2 : dist (D.target.pts k) (D.target.pts (k + 1)) ≠ c)
    (hB1 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ b)
    (hB2 : dist (D.target.pts k) (D.target.pts (k + 2)) ≠ c)
    {w1 w2 : Wall D.toDissection} {E1 E2 : ℕ → Fin N × Fin 3} {n1 n2 : ℕ}
    (C1 : IsChain w1 E1 n1) (C2 : IsChain w2 E2 n2)
    (h1a : w1.a = D.target.pts k) (h2a : w2.a = D.target.pts k)
    (h12 : (w1.b = D.target.pts (k + 1) ∧ w2.b = D.target.pts (k + 2)) ∨
      (w1.b = D.target.pts (k + 2) ∧ w2.b = D.target.pts (k + 1))) :
    ∃ (i : Fin N) (j : Fin 3) (P1 P2 : Plane), (D.tile i).pts j = D.target.pts k ∧
      (D.tile i).angleAt j = α ∧ SideAt D α w1 E1 n1 i j P1 ∧ SideAt D α w2 E2 n2 i j P2 ∧
      ((tyE D.toDissection a b (E1 0) = TT.b ∧ tyE D.toDissection a b (E2 0) = TT.c) ∨
       (tyE D.toDissection a b (E1 0) = TT.c ∧ tyE D.toDissection a b (E2 0) = TT.b)) ∧
      ((P1 = (D.tile i).pts (j + 1) ∧ P2 = (D.tile i).pts (j + 2)) ∨
       (P1 = (D.tile i).pts (j + 2) ∧ P2 = (D.tile i).pts (j + 1))) := by
  rcases h12 with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · exact corner_both D hα h hab hac hword k hk hA1 hA2 hB1 hB2 C1 C2 h1a hb1 h2a hb2
  · obtain ⟨i, j, Pa, Pb, hij, hjα, SA, SB, ty, alt⟩ :=
      corner_both D hα h hab hac hword k hk hA1 hA2 hB1 hB2 C2 C1 h2a hb2 h1a hb1
    refine ⟨i, j, Pb, Pa, hij, hjα, SB, SA, ?_, ?_⟩
    · rcases ty with ⟨x, y⟩ | ⟨x, y⟩
      · exact Or.inr ⟨y, x⟩
      · exact Or.inl ⟨y, x⟩
    · rcases alt with ⟨x, y⟩ | ⟨x, y⟩
      · exact Or.inr ⟨y, x⟩
      · exact Or.inl ⟨y, x⟩

theorem sides_ne (k : ℕ) (hk : 3 ≤ k) {s b c : ℝ} (hs : 0 < s) (hb : b = s * (2 * k + 1))
    (hc : c = s * (k * (k + 1))) :
    s * ((2 * k * (2 * k + 1) : ℕ) : ℝ) ≠ b ∧ s * ((2 * k * (2 * k + 1) : ℕ) : ℝ) ≠ c ∧
    s * ((2 * (k + 1) * (2 * k + 1) : ℕ) : ℝ) ≠ b ∧ s * ((2 * (k + 1) * (2 * k + 1) : ℕ) : ℝ) ≠ c := by
  have hk0 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; rw [hb] at h
    have := mul_left_cancel₀ hs.ne' h; push_cast at this; nlinarith
  · intro h; rw [hc] at h
    have := mul_left_cancel₀ hs.ne' h; push_cast at this; nlinarith
  · intro h; rw [hb] at h
    have := mul_left_cancel₀ hs.ne' h; push_cast at this; nlinarith
  · intro h; rw [hc] at h
    have := mul_left_cancel₀ hs.ne' h; push_cast at this; nlinarith

theorem leafG_core (D : CongruentDissection N) {α a b c s : ℝ} (k : ℕ) (hk : 3 ≤ k) (hs : 0 < s)
    (ha : a = s * (k : ℝ) ^ 2) (hb : b = s * (2 * k + 1)) (hc : c = s * (k * (k + 1)))
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : D.target.angleAt p = α) (hq : D.target.angleAt q = α)
    (hr : D.target.angleAt r = Real.pi - 2 * α)
    (dpr : dist (D.target.pts p) (D.target.pts r) = s * ((2 * k * (2 * k + 1) : ℕ) : ℝ))
    (dqr : dist (D.target.pts q) (D.target.pts r) = s * ((2 * k * (2 * k + 1) : ℕ) : ℝ))
    (dpq : dist (D.target.pts p) (D.target.pts q) = s * ((2 * (k + 1) * (2 * k + 1) : ℕ) : ℝ))
    {wLa wLb wBa : Wall D.toDissection} {ELa ELb EBa : ℕ → Fin N × Fin 3} {nLa nLb nBa : ℕ}
    (CLa : IsChain wLa ELa nLa) (CLb : IsChain wLb ELb nLb) (CBa : IsChain wBa EBa nBa)
    (hWLa : wLa.a = D.target.pts p ∧ wLa.b = D.target.pts r)
    (hWLb : wLb.a = D.target.pts q ∧ wLb.b = D.target.pts r)
    (hWBa : wBa.a = D.target.pts p ∧ wBa.b = D.target.pts q)
    (hap : eAng D.toDissection wLa.dir (ELa (nLa - 1)) = α ∧
      eAng D.toDissection wLb.dir (ELb (nLb - 1)) = Real.pi - 3 * α) : False := by
  have hk2 : 2 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hπ := Real.pi_pos
  obtain ⟨hαpos, -, -⟩ := Row4.model_sides D h
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  obtain ⟨n1, n2, n3, n4⟩ := sides_ne k hk hs hb hc
  have hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1 := by
    intro x y z hh
    rw [ha, hb, hc] at hh
    exact GLC.hword_a_real k hk2 hs x y z hh
  have hN : 0 < N := Fin.pos (EBa 0).1
  obtain ⟨ERB, nRB, CRB⟩ := (Wall.rev wBa).exists_chain hN
  obtain ⟨hn', R1, R2⟩ := CBa.rev_zero CRB
  have hn1 : nBa - 1 < nBa := by have := CBa.n_pos; omega
  -- side lengths at every corner
  have dist_vals : ∀ u v : Fin 3, u ≠ v →
      dist (D.target.pts u) (D.target.pts v) = s * ((2 * k * (2 * k + 1) : ℕ) : ℝ) ∨
      dist (D.target.pts u) (D.target.pts v) = s * ((2 * (k + 1) * (2 * k + 1) : ℕ) : ℝ) := by
    intro u v huv
    have hc6 : (u = p ∧ v = q) ∨ (u = q ∧ v = p) ∨ (u = p ∧ v = r) ∨ (u = r ∧ v = p) ∨
        (u = q ∧ v = r) ∨ (u = r ∧ v = q) :=
      (by decide : ∀ p q r u v : Fin 3, p ≠ q → p ≠ r → q ≠ r → u ≠ v →
        (u = p ∧ v = q) ∨ (u = q ∧ v = p) ∨ (u = p ∧ v = r) ∨ (u = r ∧ v = p) ∨
        (u = q ∧ v = r) ∨ (u = r ∧ v = q)) p q r u v hpq hpr hqr huv
    rcases hc6 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr dpq
    · exact Or.inr (by rw [dist_comm]; exact dpq)
    · exact Or.inl dpr
    · exact Or.inl (by rw [dist_comm]; exact dpr)
    · exact Or.inl dqr
    · exact Or.inl (by rw [dist_comm]; exact dqr)
  have cornerNe : ∀ κ : Fin 3,
      dist (D.target.pts κ) (D.target.pts (κ + 1)) ≠ b ∧ dist (D.target.pts κ) (D.target.pts (κ + 1)) ≠ c ∧
      dist (D.target.pts κ) (D.target.pts (κ + 2)) ≠ b ∧ dist (D.target.pts κ) (D.target.pts (κ + 2)) ≠ c := by
    intro κ
    have e1 := dist_vals κ (κ + 1) ((by decide : ∀ y : Fin 3, y ≠ y + 1) κ)
    have e2 := dist_vals κ (κ + 2) ((by decide : ∀ y : Fin 3, y ≠ y + 2) κ)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases e1 with e | e <;> rw [e] <;> assumption
    · rcases e1 with e | e <;> rw [e] <;> assumption
    · rcases e2 with e | e <;> rw [e] <;> assumption
    · rcases e2 with e | e <;> rw [e] <;> assumption
  have perm : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
      (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by decide
  -- the corner at `p`: walls `Ba`, `La`
  obtain ⟨iP, jP, P1, P2, hijP, hjP, SBa, SLa, tyP, -⟩ := corner_both_sym D hα h hab hac hword p hp
    (cornerNe p).1 (cornerNe p).2.1 (cornerNe p).2.2.1 (cornerNe p).2.2.2 CBa CLa hWBa.1 hWLa.1 (by
      rcases perm p q r hpq hpr hqr with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [hWBa.2, h1], by rw [hWLa.2, h2]⟩
      · exact Or.inr ⟨by rw [hWBa.2, h1], by rw [hWLa.2, h2]⟩)
  -- the corner at `q`: walls `Lb`, `Ba` reversed
  obtain ⟨iQ, jQ, Q1, Q2, hijQ, hjQ, SLb, SRB, tyQ, altQ⟩ := corner_both_sym D hα h hab hac hword q hq
    (cornerNe q).1 (cornerNe q).2.1 (cornerNe q).2.2.1 (cornerNe q).2.2.2 CLb CRB hWLb.1
    (show (Wall.rev wBa).a = D.target.pts q from hWBa.2) (by
      rcases perm q r p hqr hpq.symm hpr.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [hWLb.2, h1], by
          show wBa.a = _
          rw [hWBa.1, h2]⟩
      · exact Or.inr ⟨by rw [hWLb.2, h1], by
          show wBa.a = _
          rw [hWBa.1, h2]⟩)
  -- the model
  have hRB0 : ERB 0 = EBa (nBa - 1) := R1
  have hdirne : wBa.dir ((D.tile (EBa (nBa - 1)).1).pts (EBa (nBa - 1)).2) ≠
      wBa.dir ((D.tile (EBa (nBa - 1)).1).pts ((EBa (nBa - 1)).2 + 1)) := CBa.dir_ne hn1
  have hEnd0 : eAng D.toDissection wBa.dir (EBa (nBa - 1)) = α := by
    have h1 := SRB.ang0
    rw [hRB0] at h1
    exact (wAng_rev D.toDissection wBa.dir (EBa (nBa - 1)) hdirne).symm.trans h1
  have hEnd1 : 1 < nBa → eAng D.toDissection wBa.dir (EBa (nBa - 2)) = α := by
    intro h1n
    have h1 := SRB.ang1
    rw [R2 h1n] at h1
    exact (wAng_rev D.toDissection wBa.dir (EBa (nBa - 2)) (CBa.dir_ne (by omega))).symm.trans h1
  have d1 : α ≠ Real.pi - 3 * α := fun e => hα ⟨1 / 4, by push_cast; linarith⟩
  have clsBe : clsA α (Real.pi - 3 * α) = Ang.be := by simp [clsA, d1.symm]
  have hmodel : Model k (sideOf D α a b wLa.dir ELa nLa) (sideOf D α a b wLb.dir ELb nLb)
      (sideOf D α a b wBa.dir EBa nBa) := by
    refine ⟨?_, ?_, ?_, sideOf_V D hα h CLa, sideOf_V D hα h CLb, sideOf_V D hα h CBa,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact sum_lenK_nat D k hs hα h ha hb hc CLa _ (by rw [hWLa.1, hWLa.2, dpr])
    · exact sum_lenK_nat D k hs hα h ha hb hc CLb _ (by rw [hWLb.1, hWLb.2, dqr])
    · exact sum_lenK_nat D k hs hα h ha hb hc CBa _ (by rw [hWBa.1, hWBa.2, dpq])
    · rw [sa_eq D hα h wLa.dir ELa nLa 0, SLa.ang0, al_cls]
    · rw [sa_eq D hα h wLb.dir ELb nLb 0, SLb.ang0, al_cls]
    · rw [sa_eq D hα h wBa.dir EBa nBa 0, SBa.ang0, al_cls]
    · rw [na_eq D hα h wLa.dir ELa nLa]
      show clsA α (eAng D.toDissection wLa.dir (ELa (nLa - 1))) = Ang.al
      rw [hap.1, al_cls]
    · rw [na_eq D hα h wLb.dir ELb nLb]
      show clsA α (eAng D.toDissection wLb.dir (ELb (nLb - 1))) = Ang.be
      rw [hap.2, clsBe]
    · rw [na_eq D hα h wBa.dir EBa nBa]
      show clsA α (eAng D.toDissection wBa.dir (EBa (nBa - 1))) = Ang.al
      rw [hEnd0, al_cls]
    · intro _; rw [sa_eq D hα h wLa.dir ELa nLa 1, SLa.ang1, al_cls]
    · intro _; rw [sa_eq D hα h wLb.dir ELb nLb 1, SLb.ang1, al_cls]
    · intro _; rw [sa_eq D hα h wBa.dir EBa nBa 1, SBa.ang1, al_cls]
    · intro h1n
      rw [na_eq D hα h wBa.dir EBa nBa]
      show clsA α (eAng D.toDissection wBa.dir (EBa (nBa - 2))) = Ang.al
      rw [hEnd1 h1n, al_cls]
    · rcases tyP with ⟨x, y⟩ | ⟨x, y⟩
      · exact Or.inr ⟨y, x⟩
      · exact Or.inl ⟨y, x⟩
    · rcases tyQ with ⟨x, y⟩ | ⟨x, y⟩
      · exact Or.inl ⟨x, by
          show tyE D.toDissection a b (EBa (nBa - 1)) = TT.c
          rw [← hRB0]; exact y⟩
      · exact Or.inr ⟨x, by
          show tyE D.toDissection a b (EBa (nBa - 1)) = TT.b
          rw [← hRB0]; exact y⟩
  have hG : GStar (sideOf D α a b wLb.dir ELb nLb) := by
    intro htc h11 _
    have htb : tyE D.toDissection a b (ERB 0) = TT.b := by
      rcases tyQ with ⟨x, y⟩ | ⟨x, y⟩
      · exact absurd (htc.symm.trans x) (by decide)
      · exact y
    have hLX : 2 * c < dist wLb.a wLb.b := by
      rw [hWLb.1, hWLb.2, dqr, hc]; push_cast; nlinarith [mul_pos hs (mul_pos hk0 hk0)]
    have hLY : 2 * b < dist (Wall.rev wBa).a (Wall.rev wBa).b := by
      show 2 * b < dist wBa.b wBa.a
      rw [hWBa.1, hWBa.2, dist_comm, dpq, hb]; push_cast
      nlinarith [mul_pos hs (mul_pos hk0 (by positivity : (0:ℝ) < 2 * k + 1))]
    have := corner_G2_core D k hk2 hs ha hb hc hα h q hq (cornerNe q).1 (cornerNe q).2.1
      (cornerNe q).2.2.1 (cornerNe q).2.2.2 CLb CRB hijQ hjQ SLb SRB altQ htc htb hLX hLY h11
    rw [sa_eq D hα h wLb.dir ELb nLb 2, this.2, al_cls]
  exact leafG_closed k hk ⟨_, _, _, hmodel, hG⟩

end Erdos634.GLI

#print axioms Erdos634.GLI.leafG_core
